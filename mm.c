/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = 1792;    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;

    union {
        struct {
            struct block * prev;
            struct block * next;
        };
        /*
        * We don't know how big the payload will be.  Declaring it as an
        * array of size 0 allows computing its starting address using
        * pointer notation.
        */
        char payload[0];
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t * heap_start = NULL;

/* Pointer to first free block */
static block_t * free_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

// Additional Helper Functions
static void print_blocks();
static void print_free_list();
static void add_to_free_list(block_t * block);
static void update_free_start();
static void prepend_to_free_list(block_t * block);
static void remove_from_free_list(block_t * block);
static size_t extract_prev_alloc(word_t word);
static void set_prev_alloc(block_t * block, bool state);

// Heap Checks
static bool correct_num_free_blocks();
static bool detect_cycle();
static bool checkAllPrevAllocBits();
static bool no_adjacent_free_blocks();

/*
 * mm_init initializes the memory allocator and the heap_start and free_start
 * pointers. It will run once at the beginning of execution.
 * 
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true);  // Prologue footer
    start[1] = pack(0, true);  // Epilogue header
    
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    set_prev_alloc(heap_start, true);

    // Initialize first_start pointer 
    free_start = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

    return true;
}

/*
 * malloc allocates a block of some size (at least min_block_size)
 * It makes sure that the size is rounded up to a multiple of 16 so that
 * the blocks are 16-byte-algined. If it fails, it will return null but 
 * otherwise, it should return a pointer to the newly allocated block
 */
void *malloc(size_t size) 
{
    //dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        //dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    if (asize < min_block_size) {
        asize = min_block_size;
    }

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    //dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * free deallocates a previously allocated block without changing its size. It
 * will be coalesced if there are other free blocks to its left or right.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    int alloc_bit = extract_prev_alloc(block->header);

    write_header(block, size, false);
    write_footer(block, size, false);

    set_prev_alloc(block, alloc_bit);

    coalesce(block);
}

/*
 * realloc allocates a new region of memory, copies pre-existing data to that 
 * new space and frees the old block associated with the pre-existing data
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc is identical to malloc except that all bits are set to zero in the 
 * newly allocated space before a pointer to that block is returned 
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/


/*
 * Extends the heap with given size and returns a pointer to that newly created 
 * block.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);

    size_t alloc_bit = extract_prev_alloc(block->header);

    write_header(block, size, false);
    write_footer(block, size, false);

    set_prev_alloc(block, alloc_bit);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    block = coalesce(block);

    return block;
}

/*
 * Coalesce determines if the blocks to the left or right (or both) of a newly 
 * freed block are also free and combines them into one block. 
 */
static block_t *coalesce(block_t * block) 
{
    // fill me in
    size_t blockSize = get_size(block);

    block_t * left = find_prev(block);
    block_t * right = find_next(block);

    bool isLeftFree;
    size_t leftSize;

    bool isRightFree;
    size_t rightSize;
    
    // null pointer 
    if (!left) {
        leftSize = 0;
        isLeftFree = false;
    } else {
        leftSize = get_size(left);
        isLeftFree = !extract_prev_alloc(block->header);  
    }

    if (!right) {
        rightSize = 0;
        isRightFree = false;
    } else {
        isRightFree = !(get_alloc(right));
    }

    /*
    * There are four cases: 
    * 1) Nothing can be coalesced
    * 2) Left can be coalesced
    * 3) Right can be coalesced
    * 4) Both can be coalesced
    * 
    */

   if (isLeftFree && isRightFree) {

        leftSize = get_size(left);
        rightSize = get_size(right);

        // retain prev_alloc of left block
        size_t alloc_bit = extract_prev_alloc(left->header);

        // setting prev_alloc of next to reflect the current free operation
         set_prev_alloc(find_next(right), false);

        remove_from_free_list(left);
        remove_from_free_list(right);

        write_header(left, leftSize+blockSize+rightSize,false);
        write_footer(left, leftSize+blockSize+rightSize,false);

        // Carry prev_alloc of left block
        set_prev_alloc(left, alloc_bit);

        prepend_to_free_list(left);
        return left;

   } else if (isLeftFree) {

        leftSize = get_size(left);

        remove_from_free_list(left);

        // retain prev_alloc of left block
        size_t alloc_bit = extract_prev_alloc(left->header);

        write_header(left, leftSize+blockSize,false);
        write_footer(left, leftSize+blockSize,false);

        // Carry prev_alloc of left block
        set_prev_alloc(left, alloc_bit);

         // setting prev_alloc of next to reflect the current free operation
         set_prev_alloc(right, false);

        prepend_to_free_list(left);
        return left;

   } else if(isRightFree) {

        rightSize = get_size(right);

        // setting prev_alloc of next to reflect the current free operation
        set_prev_alloc(find_next(right), false);

        remove_from_free_list(right);

        // retain prev_alloc of current block
        size_t alloc_bit = extract_prev_alloc(block->header);

        write_header(block, blockSize+rightSize,false);
        write_footer(block, blockSize+rightSize,false);

        // Carry prev_alloc of current block
        set_prev_alloc(block, alloc_bit);

        prepend_to_free_list(block);
        return block;

   } else {
        
        prepend_to_free_list(block);

         // setting prev_alloc of next to reflect the current free operation
         set_prev_alloc(right, false);
         

        return block;
   }
   
}

/*
 * place writes to the block passes as the parameter. If the payload leaves  
 * space within that block, the rest of the block is split and marked as 
 * unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
        // retaining prev_alloc for the first block
        int alloc_bit = extract_prev_alloc(block->header);

        write_header(block, asize, true);
        //write_footer(block, asize, true);

        // carry prev_alloc for first block
        set_prev_alloc(block, alloc_bit);

        remove_from_free_list(block);

        block_t *block_next;
        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        set_prev_alloc(block_next, true);
        coalesce(block_next);
    
    }
    else
    { 
        
        // retaining prev_alloc for the current block
        int alloc_bit = extract_prev_alloc(block->header);

        write_header(block, csize, true);
        //write_footer(block, csize, true);

        // carry prev_alloc for current block
        set_prev_alloc(block, alloc_bit);

        // setting prev_alloc of next to reflect the current free operation
         set_prev_alloc(find_next(block), true);

        remove_from_free_list(block);
    }
}

/*
 * find_fit implements an nth fit policy. The heap is searched for n free blocks
 * that can accomodate the payload. The block that fits the best is returned.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    block_t * smallestFit = NULL;
    
    int n = 0;
    for (block = free_start; block != NULL;
                             block = block->next)
    {
        // if we find a fit
        if (!(get_alloc(block)) && (asize <= get_size(block)))
        {
            n++;
            if (smallestFit != NULL) {
                if (extract_size((smallestFit)->header) 
                    > extract_size((block)->header)) {
                    smallestFit = block;
                }
            } else {
                smallestFit = block;
            }

            if (n>=18) {
                break; 
            }
        }
    }

    return smallestFit;
}

/* 
 * The heap checker verifies that certain heap invariants have not been violated
 * It calls an assortment of helper function for modularity.
 */
bool mm_checkheap(int line)  
{ 
    // Coalesce: Making sure there are no adjacent free blocks
    if (!no_adjacent_free_blocks()) {
        printf("Line %d: Two adjacent free blocks!\n", line);
        return false;
    }

    // Explicit List: Making sure there are no cycles in free doubly linked list
    if (!detect_cycle()) {
        printf("Line %d: Cycle in free list!\n", line);
        return false;
    }

    // Explicit List: Making sure explicit list matches implicit list
    if (!correct_num_free_blocks()) {
        printf("Line %d: Explicit-Implicit Count Mismatch!\n", line);
        return false;
    }

    // Removing Footers: Checking that prev alloc bits are correct
        if (!checkAllPrevAllocBits()) {
        printf("Line %d: Prev alloc bit mismatch!\n", line);
        return false;
    }

    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

static size_t extract_prev_alloc(word_t word)
{
    size_t alloc_bit = (word & prev_alloc_mask);
    return alloc_bit;
}

static void set_prev_alloc(block_t * block, bool state) {

    if (block != NULL) {
        if (state==true) {
            block->header = (block->header | prev_alloc_mask);

        } else {
            block->header = (block->header & ~(prev_alloc_mask));
        }
    }

}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/*
* Helper function that prints all the blocks in the implicit list along with 
* their size, allocation and potentially their prev and next pointers if they
* are free
*/
static void print_blocks() {

    block_t * current = heap_start;

    word_t * prologueFooter = find_prev_footer(current);
    size_t PF_size = extract_size(*prologueFooter);
    bool PF_alloc = extract_alloc(*prologueFooter);

    printf("%s %s %zu %s %d\n", 
            "prologue footer","size:", PF_size, "alloc:", PF_alloc);

    size_t size = extract_size((current)->header);
    bool alloc = extract_alloc((current)->header);

    int count = 0;

    // while we haven't reached the epilogue header block
    while(!(size==0 && alloc==1)) {
        
        printf("%s %p ", "Block", current);
        printf("%s: %zu ","Size",size);
        printf("%s: %d ","Alloc",alloc);

        if (alloc == 0) {
            if (current->prev == NULL) {
                printf("%s: %s ","Prev", "null");
            } else {
                printf("%s: %p ","Prev", current->prev);
            }

            if (current->next == NULL) {
                printf("%s: %s ","Next", "null");
            } else {
                printf("%s: %p ","Next", current->next);
            }

        } else {
            printf("%s: %s ","Prev", "PAYLOAD");
            printf("%s: %s ","Next", "PAYLOAD");

        }

        size_t alloc_bit = extract_prev_alloc(current->header);
        printf("%s %zu", "Prev Alloc:", alloc_bit);

        if (current == free_start) {
            printf("<- free start\n");
        } else {
            printf("\n");
            }

        count++;
        current = find_next(current);
        size = extract_size((current)->header);
        alloc = extract_alloc((current)->header);
    }

    block_t * epilogueHeader = current;
    size_t EH_size = extract_size((epilogueHeader)->header);
    bool EH_alloc = extract_alloc((epilogueHeader)->header);

    printf("%s %s %zu %s %d\n", 
            "epilogue header","size:", EH_size, "alloc:", EH_alloc);
    printf("\n");

}

/*
* Helper function that strictly prints all free blocks along with their prev
* and next pointers
*/
static void print_free_list() {
    printf("free list: ");
    
    block_t * current = free_start;
    int count = 0;
    printf("%p -> ", current);

    while (current != NULL) {
        if (count > 10) {
            break;
        }
        printf("%p ->", current->next);
        count++;

        current = current->next;
    }
    printf("\n");


}

/*
* prepend_to_free_list takes a pointer to a block that it proceeds to insert 
* into the free list. This new block is now the head of the list (free_start)
*/
static void prepend_to_free_list(block_t * block) {

    if (free_start==NULL) {
        block->prev = NULL;
        block->next = NULL;
        free_start = block;
    } else {
        block->prev = NULL;
        block->next = free_start;
        free_start->prev = block;
        free_start = block;
    }

}

/*
* remove_from+free_list takes a pointer to a block that it proceeds to remove 
* from the free list by redirecting the prev and next pointers of the blocks to
* its left and right
*/
static void remove_from_free_list(block_t * block) {

    if (free_start == NULL) {
        return;
    }

    block_t * prev = block->prev;
    block_t * next = block->next;

    if (prev == NULL && next == NULL) {
        free_start = NULL;
    }
    else if (prev == NULL && next != NULL) {
        free_start = next;
        free_start->prev = NULL;
    }
    else if (prev != NULL && next == NULL) {
        (block->prev)->next = NULL;
    }
    else if (prev != NULL && next != NULL) {
        prev->next = next;
        next->prev = prev;

    }
 
}

// Heap Checks

/*
* Makes sure that there do not exist any adjacent free blocks as they must have
* been coalesced
*/
static bool no_adjacent_free_blocks() {

    block_t * current = heap_start;
    size_t size = extract_size((current)->header);
    bool alloc = extract_alloc((current)->header);

    // while we haven't reached the epilogue header block
    while(!(size==0 && alloc==1)) {

        if (alloc == 0 && extract_alloc((find_next(current))->header) == 0) {
            return 0;
        }

        current = find_next(current);
        size = extract_size((current)->header);
        alloc = extract_alloc((current)->header);

    }
    return 1;

}

/*
* Makes sure that the number of blocks marked as unallocated in the implicit 
* list are equal to the number of blocks in the free list
*/
static bool correct_num_free_blocks() {

    int implicit_count = 0;
    int explicit_count = 0;

    block_t * implicit_current = heap_start;
    size_t size = extract_size((implicit_current)->header);
    bool alloc = extract_alloc((implicit_current)->header);

    // while we haven't reached the epilogue header block
    while(!(size==0 && alloc==1)) {
        if (alloc == 0) {
            implicit_count++;
        }
        
        implicit_current = find_next(implicit_current);
        size = extract_size((implicit_current)->header);
        alloc = extract_alloc((implicit_current)->header);
    }

    block_t * explicit_current = free_start;

    while (explicit_current != NULL) {
        explicit_count++;
        explicit_current = explicit_current->next;
    }

    if (explicit_count == implicit_count) {
        return 1;
    }

    return 1;


}

/*
* Detects a cycle in the doubly linked free list. 
*/
static bool detect_cycle() {
    
    block_t * slow = free_start;
    block_t * fast = free_start;

    while (slow && fast && fast->next) {
        slow = slow->next;
        fast = fast->next->next;
        if (slow == fast) {
            printf("====== Found Cycle ======\n");
            return 1;
        }
    }
    
    return 0;
    
}

/*
* Makes sure that all the prev alloc bits are identical to the alloc bit of the 
* previous block
*/
static bool checkAllPrevAllocBits() {

     block_t * current = heap_start;

    size_t size = extract_size((current)->header);
    bool alloc = extract_alloc((current)->header);
    size_t prev_alloc_raw = extract_prev_alloc((current)->header);

    // while we haven't reached the epilogue header block
    while(!(size==0 && alloc==1)) {

        bool prev_alloc;
        if (prev_alloc_raw == 2) {
            prev_alloc = 1;
        } else {
            prev_alloc = 0;
        }

        word_t * prev_footer = find_prev_footer(current);
        bool actual_prev_alloc = extract_alloc(*prev_footer);

        if (prev_alloc != actual_prev_alloc) {
            printf("current: %p\n", current);
            printf("prev: %p\n", find_prev(current));
            printf("prev alloc: %d\n", prev_alloc);
            printf("actual prev alloc: %d\n", actual_prev_alloc);
            return 0;
        }

        current = find_next(current);
        size = extract_size((current)->header);
        alloc = extract_alloc((current)->header);
        prev_alloc_raw = extract_prev_alloc((current)->header);

    }
    return 1;
   

}
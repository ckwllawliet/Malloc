/*
 * mm.c
 * Name:
 * Andrew ID: 
 * This program using segregated free lists and first fit to store and
 * allocte blocks.
 * First, the program will initialize the heap, including prologue,
 * epilougue and empty segreated list. When ask for some size,
 * based on the size searching from corresponding segregated list entry,
 * allocte the first block with enough size to user. Decide whether to 
 * split this block based on its remaining size.
 * If can't find a suitable block, extend the heap. Initialize epilogue
 * again. After allocating a block, check if coalesce is needed.  
 * When free the block, set header and footer last bit to be zeros, check
 * if coalesce is needed.
 * By printing out the required block size, I arranged segregated list with
 * size of 3 * DSIZE, 6 * DSIZE, 9 * DSIZE(bytes) and so on. It becomes 
 * sparse as the block size increasing. 
 * mm_checkheap and other related functions are used to debug the malloc.
 * It checks the performance of the blocks. More specific explanation is
 * in the header of mm_checkheap function.
 * Each block needs to have at least 24 bytes. Data structures are:
 * Allocated                  Free
 *   [Header: size, 1]         [Header: size, 0]
 *   [....Payload....]         [Ptr to PrevFRBK]
 *   [Footer: size, 1]         [Ptr to NextFRBK]
 *                             [ ............. ]
 *                             [Footer: size, 0]
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   168		/* Extend heap by this amount (bytes) */
#define MINIMUM		24		/* Minimum block size head + foot = 8, 
                               prev + next = 16. Total 24(bytes).*/


/*** Macros ***/
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp,compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp,compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp))) 
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

/* Given block ptr bp, compute address of next and previous free blocks */
#define NEXT_FRPT(bp) (*(void **)(bp + DSIZE))
#define PREV_FRPT(bp) (*(void **)(bp))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* Get the enrty pointer in seg list, also define seg length*/
#define SEG_ENTRY(seg_list, i)		(*(void **)(seg_list + i * DSIZE))
#define SEG_NUM		14
/*** Macros End ***/

/* Seg number, bsaed on minimum size of blocks and distribution
 * of sizes appear in the program. For example, 3 represents 3 * 
 * DSIZE of a block, which is equal to MINIMUM.
 */
#define SIZE0	3
#define SIZE1	6
#define SIZE2	9
#define SIZE3	12
#define SIZE4	15
#define SIZE5	30
#define SIZE6	60
#define SIZE7	120
#define SIZE8	240
#define SIZE9	480
#define SIZE10	960
#define SIZE11	1920
#define SIZE12	3840

/*** Declaration ***/
static void *coalesce(void *ptr);
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void delete_block(void *bp);
static void *add_block(void *bp);
static unsigned int get_list_number(size_t size);
static void check_block(void *bp);
static void print_block(void *bp);
static void check_free();
static int in_heap(const void *p);
static int aligned(const void *p);
/*** Declaration End ***/

/* Global Variables: seg_list, heap_listp */
static char *seg_list = 0; /* Pointer to first seg */
static char *heap_listp = 0;


/* Malloc Routine: init, malloc, free, realloc, calloc */
/* 
 * mm_init
 * Initialize: return -1 on error, 0 on success.
 * Initialize segregated list first. Set every entry in segeregated list 
 * point to NULL.
 * Then set prologue header, footer and Epilogue head for the heap.
 */
int mm_init(void) {
	/* Initialize seg list frist */
	if ((seg_list = mem_sbrk(SEG_NUM * DSIZE)) == NULL){
		return -1;
	}

	for (int i = 0; i < SEG_NUM; i++){
		SEG_ENTRY(seg_list, i) = NULL;
	}

	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == NULL){
		return -1;
	}
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (DSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /*Epilogue head */

	heap_listp += (DSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
		return -1;
	}
    return 0;
}


/*
 * malloc
 * First align block size. Each block must has at least 24 bytes.
 * Find if there is a free block for current requirement.
 * If can't find a suitable block, extende the heap.
 */
void *malloc (size_t size) {
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if not fit */
	char *bp;

	if (heap_listp == 0){
		mm_init();
	}

	if (size <= 0){
		return NULL;
	}

	asize = MAX(ALIGN(size + DSIZE), MINIMUM);

	/* find if there is a free block to allocate */
	if ((bp = find_fit(asize))) {
		place(bp, asize);
		return bp;
	}
	/* If free block does not exist, extend the heap */
	else if ((bp = find_fit(asize))== NULL) {
		extendsize = MAX(asize, CHUNKSIZE);
		if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
			return NULL;
		}
		place(bp, asize);
	}

	return bp;
}

/*
 * free
 * Set current header and footer allocated bit to 0;
 * Add this block back to free block list;
 * Check if need to coalesce.
 */
void free (void *ptr) {
	if (ptr == 0){
		return;
	}

	size_t size = GET_SIZE(HDRP(ptr));

	if (heap_listp == 0){
		mm_init();
	}

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));

	ptr = add_block(ptr);
}

/*
 * realloc
 * Simplest way to reallocte the blocks.
 */
void *realloc(void *ptr, size_t size) {
	size_t oldsize;
	void *newptr;
	size_t asize = MAX(ALIGN(size) + DSIZE, MINIMUM);
	/* If size <= 0 then this is just free, and we return NULL. */
	if(size <= 0) {
		free(ptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return malloc(size);
	}

	/* Get the size of the original block */
	oldsize = GET_SIZE(HDRP(ptr));
	
	/* If the size doesn't need to be changed, return orig pointer */
	if (asize == oldsize)
		return ptr;
	
	/* If the size needs to be decreased, shrink the block and 
	 * return the same pointer */
	if(asize <= oldsize)
	{
		size = asize;

		/* If a new block couldn't fit in the remaining space, 
		 * return the pointer */
		if(oldsize - size <= MINIMUM)
			return ptr;
		PUT(HDRP(ptr), PACK(size, 1));
		PUT(FTRP(ptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize-size, 1));
		free(NEXT_BLKP(ptr));
		return ptr;
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	if(size < oldsize) oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	free(ptr);

	return newptr;

}

/*
 * calloc
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}




/* Helper functions: Coalesce, extend, find fit, place,
 *			   add block, delete block, get seg number.
 */

/* coalesce
 * para: current pointer ptr to a free block.
 * Check if the adjacent blocks are free.
 * If any of the previous or next block is free,
 * coalesce those blocks.
 */
static void *coalesce(void *ptr) {
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
	size_t size = GET_SIZE(HDRP(ptr));

	if (prev_alloc && next_alloc) {
		/* pre block and next block both been allocated */
		return ptr;
	}

	if (prev_alloc && !next_alloc){
		/* next block not allocated */
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
		delete_block(NEXT_BLKP(ptr));
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc){
		/* previous block not allocated */
		ptr = PREV_BLKP(ptr);
		size += GET_SIZE(HDRP(ptr));
		delete_block(ptr);
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	}

	else if(!prev_alloc && !next_alloc){
		/* Both blocks not allocated */
		size = size + GET_SIZE(HDRP(PREV_BLKP(ptr))) 
		+ GET_SIZE(FTRP(NEXT_BLKP(ptr)));
		delete_block(PREV_BLKP(ptr));
		delete_block(NEXT_BLKP(ptr));
		PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
		ptr = PREV_BLKP(ptr);
	}

	return ptr;
}

/* extend_heap
 * When find fit can't find a free block to allocate, extend the heap.
 * Initialize header, footer and epilougue header.
 * Add new free block to the list, and coalesce.
 */
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if (size < MINIMUM){
		size = MINIMUM;
	}
	if ((long)(bp = mem_sbrk(size)) == -1){
		return NULL;
	}
 
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	bp = add_block(bp);
	/* coalesce if the previous block was free */
	return bp;
}

/* find fit
 * para: required size.
 * Using first fit, search from the most close segregate to the 
 * largest one, if there is a fit, return the pointer to the free block.
 */
static void *find_fit(size_t size)
{
	void *bp;

	unsigned int entry_num = get_list_number(size/DSIZE);

	for (int i = entry_num; i < SEG_NUM; i++){
		for (bp = SEG_ENTRY(seg_list, i); 
			(bp != NULL) && GET_SIZE(HDRP(bp)) > 0; 
			bp = NEXT_FRPT(bp)){
			if (size <= (size_t)GET_SIZE(HDRP(bp))){
				return bp;
			}
		}
	}
	return NULL;
}
/* place
 * para: current pointer bp, block size.
 * Place block at begining of a free block. Split if 
 * remaining block is larger than minimum size. Otherwise
 * allocte entire free block.
 */
static void place(void *bp, size_t asize)
{
	/* 
	 *Get the size of the allocated block 
	 * Decide whether to split the block
	 */
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= MINIMUM){
		/* Split */
		delete_block(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		bp = add_block(bp);
	}
	else {
		/* Allocate entire block */
		delete_block(bp);
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* add_block
 * para: pointer to current block
 * Coalesce first, then check the size of the block.
 * LIFO, add free block to suitable segregated list.
 * Handle the condition that this is the first block in this list.
 */
static void *add_block(void *bp)
{
	bp = coalesce(bp);

	int size = GET_SIZE(HDRP(bp));
	unsigned int seg_number = get_list_number(size/DSIZE);

	/* Handle the case this is the first block ever added to current seg */
	if (SEG_ENTRY(seg_list, seg_number) == NULL){
		NEXT_FRPT(bp) = NULL;
		PREV_FRPT(bp) = NULL;
		SEG_ENTRY(seg_list, seg_number) = bp;
	}
	else if (SEG_ENTRY(seg_list, seg_number)){
		NEXT_FRPT(bp) = SEG_ENTRY(seg_list, seg_number);
		PREV_FRPT(bp) = NULL;
		PREV_FRPT(SEG_ENTRY(seg_list, seg_number)) = bp;
		SEG_ENTRY(seg_list, seg_number) = bp;
	}


	return bp;
}

/* delete_block
 * para: pointer to current block
 * Remove the allocated block from the free blocks list
 * Check the condition, whether previous or next pointer is pointed
 * to other free blocks.
 */
static void delete_block(void *bp)
{
	int size = GET_SIZE(HDRP(bp));
	unsigned int seg_number = get_list_number(size/DSIZE);


	if (bp == SEG_ENTRY(seg_list, seg_number))
	{
		SEG_ENTRY(seg_list, seg_number) = NEXT_FRPT(bp);
	}

	if (PREV_FRPT(bp) && NEXT_FRPT(bp)){
		NEXT_FRPT(PREV_FRPT(bp)) = NEXT_FRPT(bp);
		PREV_FRPT(NEXT_FRPT(bp)) = PREV_FRPT(bp);
		PREV_FRPT(bp) = NULL;
		NEXT_FRPT(bp) = NULL;
	}

	else if (PREV_FRPT(bp) && !NEXT_FRPT(bp)){
		NEXT_FRPT(PREV_FRPT(bp)) = NEXT_FRPT(bp);
		PREV_FRPT(bp) = NULL;
	}

	else if (!PREV_FRPT(bp) && NEXT_FRPT(bp)){
		PREV_FRPT(NEXT_FRPT(bp)) = PREV_FRPT(bp);
		NEXT_FRPT(bp) = NULL;
	}
}


/* 
 * Based on different sizes allocte blocks.
 * get the entrance of segregated list.
 * para: size = required size/ DSIZE.
 */
static unsigned int get_list_number(size_t size)
{
	if (size <= SIZE0)
		return 0;
	else if (size <= SIZE1)
		return 1;
	else if (size <= SIZE2)
		return 2;
	else if (size <= SIZE3)
		return 3;
	else if (size <= SIZE4)
		return 4;
	else if (size <= SIZE5)
		return 5;
	else if (size <= SIZE6)
		return 6;
	else if (size <= SIZE7)
		return 7;
	else if (size <= SIZE8)
		return 8;
	else if (size <= SIZE9)
		return 9;
	else if (size <= SIZE10)
		return 10;
	else if (size <= SIZE11)
		return 11;
	else if (size <= SIZE12)
		return 12;
	else
		return 13;
}

/* Check functions */
/*
 * mm_checkheap
 * Call checkheap with non zero numbers.
 * When checkheap is called, check Prologue, Epilogue of the heap. 
 * Also, check whether each block is in heap, whether block size is aligned.
 * If lineno = 2, print the segregated list. Check the content in segregated
 * list.
 * If lineno = 3, print free blocks, check their location in segregated list.
 * check whether blocks are allocated to right segregate. Check header and 
 * footer are consistent.
 * If lineno = 4, check if there is any block that is not coalesced right.
 * If lineno = 5, print allocated blocks.
 * If lineno = 6, check free lists, whether they are consistent, check total
 * number of free blocks.
 */
void mm_checkheap(int lineno) {
	void *bp = heap_listp;
	if (lineno){
		if ((GET_SIZE(HDRP(heap_listp))!=DSIZE)||
			!GET_ALLOC(HDRP(heap_listp))){
	        printf("Prologue header error\n");
	    }
		for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
			check_block(bp);
		}
		/* when bp is point to the end of the list, check epilogue */
		if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	    {
	        printf("Epilogue header error \n");
	    }
	}

	/* Case 2, print the seg list */
	if (lineno == 2){
		for (int i = 1; i < SEG_NUM; i++){
			printf("seg entry(%d): %p, max size: %d\n", 
				i, SEG_ENTRY(seg_list, i), i * 16);
		}
	}
	/* Case 3, print every free block */
	if (lineno == 3){
		for (int i = 0; i < SEG_NUM; i++){
			for(bp = SEG_ENTRY(seg_list, i); bp != NULL; bp = NEXT_FRPT(bp)){
				printf("block in seg %d\n", i);
				print_block(bp);
				if ((int)get_list_number(GET_SIZE(HDRP(bp))/DSIZE) != i){
					printf("Not allocated to right seg!\n");
					return;
				}
			}
		}
	}
	/* Case 4, Check if coalesce not work */
	if (lineno == 4){
		for(int i = 0; i < SEG_NUM; i++){
			for(bp = SEG_ENTRY(seg_list, i); bp != NULL; bp = NEXT_FRPT(bp)){
				if(GET_ALLOC(HDRP(bp)) == 0 && NEXT_BLKP(bp)!=NULL 
					&& GET_ALLOC(HDRP(NEXT_BLKP(bp))) ==0 ){
					printf("Warn: Coalesce is not working!\n");
					return;
				}
			}
		}
	}

	/* Case 5, print every allocated block */
	if (lineno == 5){
		for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
			print_block(bp);
		}
	}

	/* Case 6, check free list */
	if (lineno == 6){
		check_free();
	}
}

/* 
 * Basic block checks: Check whether the block is in heap,
 * check whether the block is correctly aligned
 * para: bp, pointer of the current block.
 * Print out error information, return nothing.
 */
static void check_block(void *bp)
{
	if (!in_heap(bp)){
		printf("(%p) Error: not in heap!!\n", bp);
	}
	if (!aligned(bp)){
		printf("(%p) Error: not aligned!!\n", bp);
	}
	return;
}

/* 
 * Print block infromation, check if the information in 
 * footer and header are consistent.
 * para: bp, pointer of the current block.
 * If parameters in header and footer not consistent, 
 * print error message.
 */
static void print_block(void *bp)
{
	int head_size, head_alloc, foot_size, foot_alloc;

	head_size = GET_SIZE(HDRP(bp));
	head_alloc = GET_ALLOC(HDRP(bp));
	foot_size = GET_SIZE(FTRP(bp));
	foot_alloc = GET_ALLOC(HDRP(bp));

	if (head_size != foot_size || head_alloc != foot_alloc){
		printf("Error! Header and Footer are different!\n");
		return;
	}
	printf("(%p) Head size: %d, Foot size: %d", bp, head_size, foot_size);
	printf(" Head: %s, Foot: %s\n", (head_alloc ? "allocated" : "free"),
	 (foot_alloc ? "allocated" : "free"));

}

/* check_free
 * Check if free blocks are consistent
 * Check if the number of free blocks in segregated list equals to
 * free blocks count from the start of the heap.
 */
static void check_free()
{
	unsigned int count_seg = 0;
	unsigned int count_all = 0;
	void *bp;

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if(!GET_ALLOC(HDRP(bp))) {
			count_all++;
		}
    }

    for (int i = 0; i < SEG_NUM; i++)
    {
        for (bp = SEG_ENTRY(seg_list, i); bp!=NULL
          && (GET_SIZE(HDRP(bp)) > 0);bp = NEXT_FRPT(bp)){
            count_seg++;
        }
    }
    if (count_all != count_seg){
    	printf("Free list amount doesn't match!\n");
    	return;
    }

    for (int i = 0; i < SEG_NUM; i++){
        for (bp = SEG_ENTRY(seg_list, i); bp!=NULL && (GET_SIZE(HDRP(bp))>0);
        	bp = NEXT_FRPT(bp)){
            void *next = NEXT_FRPT(bp);
            void *prev = PREV_FRPT(bp);

            if(next != NULL && PREV_FRPT(next) != bp){
                printf("Prev not match!\n");
                return;
            }

            if(prev != NULL && NEXT_FRPT(prev) != bp){
                printf("Next not match!\n");
                return;
            }
        } 
    }
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}
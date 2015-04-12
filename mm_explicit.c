/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
#define CHUNKSIZE   128			/* Extend heap by this amount (bytes) */
#define MINIMUM		24		/* Minimum block size head + foot = 8, prev + next = 16. */


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

static void *coalease(void *ptr);
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void coaleasefp(void *bp);
static void LIFOfp(void *bp);
static void checkBloack(void *bp);
static void printBlock(void *bp);


static char *free_listp = 0;
static char *heap_listp = 0;

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(2 * MINIMUM)) == NULL){
		return -1;
	}
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /*Epilogue head */


	heap_listp += (2*WSIZE);

	free_listp = heap_listp + DSIZE;
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
    return 0;
}


/*
 * malloc
 */
void *malloc (size_t size) {
	//mm_checkheap(1);
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if not fit */
	char *bp;

	if (size <= 0){
		return NULL;
	}

	asize = MAX(ALIGN(size) + DSIZE, MINIMUM);

	if ((bp = find_fit(asize))) {
		place(bp, asize);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);

	if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
		return NULL;
	}

	place(bp, asize);
	return bp;
}

/*
 * free
 */
void free (void *ptr) {
	if (ptr == 0){
		return;
	}

	size_t size = GET_SIZE(HDRP(ptr));

	//if (heap_listp == 0){
	//	mm_init();
	//}

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalease(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
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
 * calloc - you may want to look at mm-naive.c
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
//static int aligned(const void *p) {
//    return (size_t)ALIGN(p) == (size_t)p;
//}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	void *bp = heap_listp;
	if (lineno){
		printf("Heap %p: \n", heap_listp);
		printf("Free list: %p\n", free_listp);
		checkBloack(bp);
		for (bp = free_listp; GET_ALLOC(HDRP(bp))==0; bp = NEXT_FRPT(bp))
		{
			printBlock(bp);
		}
	}
	if (lineno == 2){
		for(bp = heap_listp; GET_SIZE(HDRP(bp))> 0; bp = NEXT_BLKP(bp)){
			printBlock(bp);
		}
	}
}

/* Helper functions */
static void *coalease(void *ptr) {
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))) || PREV_BLKP(ptr) == ptr;
	// previous block is not allocated and current is not the first block;
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
	size_t size = GET_SIZE(HDRP(ptr));

	//if (prev_alloc && next_alloc) {
	//	return ptr;
	//}

	if (prev_alloc && !next_alloc){
		/* next block not allocated */
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
		coaleasefp(NEXT_BLKP(ptr));
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc){
		/* previous block not allocated */
		ptr = PREV_BLKP(ptr);
		size += GET_SIZE(HDRP(ptr));
		coaleasefp(ptr);
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	}

	else if(!prev_alloc && !next_alloc){
		size = size + GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
		coaleasefp(PREV_BLKP(ptr));
		coaleasefp(NEXT_BLKP(ptr));
		ptr = PREV_BLKP(ptr);
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
	}
	LIFOfp(ptr);
	return ptr;
}

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

	/* Coalease if the previous block was free */
	return coalease(bp);
}

static void *find_fit(size_t size)
{
	void *bp;
	for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FRPT(bp)){
		if (size <= (size_t)GET_SIZE(HDRP(bp))){
			return bp;
		}
	}
	return NULL;
}

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	if ((csize - asize) >= MINIMUM){
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp),PACK(asize, 1));
		coaleasefp(bp);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		coalease(bp);
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		coaleasefp(bp);
	}
}

static void LIFOfp(void *bp)
{
	NEXT_FRPT(bp) = free_listp;
	PREV_FRPT(free_listp) = bp;
	PREV_FRPT(bp) = NULL;
	free_listp = bp;
}

static void coaleasefp(void *bp)
{
	if (PREV_FRPT(bp))
	{
		NEXT_FRPT(PREV_FRPT(bp)) = NEXT_FRPT(bp);
	}
	else {
		free_listp = NEXT_FRPT(bp);
	}
	PREV_FRPT(NEXT_FRPT(bp)) = PREV_FRPT(bp);
}

static void checkBloack(void *bp)
{
	if (!in_heap(bp)){
		printf("(%p) Error: not in heap!!\n", bp);
	}
	return;
}

static void printBlock(void *bp)
{
	int hsize, halloc, fsize, falloc;

	/* Basic header and footer information */
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) 
	{
		printf("%p: EOL\n", bp);
		return;
	}
	
	/* Prints out header and footer info if it's an allocated block.
	 * Prints out header and footer info and next and prev info
	 * if it's a free block.
	*/
	if (halloc)
		printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp,
			hsize, (halloc ? 'a' : 'f'),
			fsize, (falloc ? 'a' : 'f'));
	else
		printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n",
			bp, hsize, (halloc ? 'a' : 'f'), PREV_FRPT(bp),
			NEXT_FRPT(bp), fsize, (falloc ? 'a' : 'f'));
}

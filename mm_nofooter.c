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
#define CHUNKSIZE   168		/* Extend heap by this amount (bytes) */
#define MINIMUM		16		/* Minimum block size head + foot = 8, prev + next = 16. */


#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc, prev_alloc)  ((size) | (alloc) | (prev_alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)	(GET(p) & 0x2) /* second bit store previous be allocated */
	

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

/* Get the enrty pointer in seg list*/
#define SEG_ENTRY(seg_list, i)		(*(void **)(seg_list + i * DSIZE))
#define SEG_NUM		14

static void *coalease(void *ptr);
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static void place(void *bp, size_t size);
static void delete_block(void *bp);
static void *add_block(void *bp);
static unsigned int get_list_number(size_t size);
static void check_bloack(void *bp);
static void print_block(void *bp);


static char *seg_list = 0; /* Pointer to first seg */
static char *heap_listp = 0;

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	heap_listp = NULL;
	seg_list = NULL;

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
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1)); /*Epilogue head */

	heap_listp += (2*WSIZE);


	//free_listp = heap_listp + DSIZE;
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
		return -1;
	}
    return 0;
}


/*
 * malloc
 */
void *malloc (size_t size) {
	//mm_checkheap(2);
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
 */
void free (void *ptr) {
	if (ptr == 0){
		return;
	}

	size_t size = GET_SIZE(HDRP(ptr));

	if (heap_listp == 0){
		mm_init();
	}

	size_t alloc = GET_PREV_ALLOC(ptr);
	PUT(HDRP(ptr), PACK(size, 0, alloc));


	//PUT(FTRP(ptr), PACK(size, 0));

	ptr = coalease(ptr);
	ptr = add_block(ptr);	
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) 
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
		return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = *SIZE_PTR(oldptr);
	if(size < oldsize){
		oldsize = size;
	}
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

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
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	void *bp = heap_listp;
	if (lineno){
		printf("Heap %p: \n", heap_listp);
		for (int i = 1; i < SEG_NUM; i ++){
			printf("seg entry(%d): %p, max size: %d\n", i, SEG_ENTRY(seg_list, i), i * 16);
		}
		check_bloack(bp);
	}
	if (lineno == 2){
		for(bp = heap_listp; GET_SIZE(HDRP(bp))> 0; bp = NEXT_BLKP(bp)){
			print_block(bp);
		}
	}
}

/* Helper functions */
static void *coalease(void *ptr) {
	//size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
	size_t prev_alloc = GET_PREV_ALLOC(ptr);
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
	size_t size = GET_SIZE(HDRP(ptr));

	if (prev_alloc && next_alloc) {
		return ptr;
	}

	if (prev_alloc && !next_alloc){
		/* next block not allocated */
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
		delete_block(NEXT_BLKP(ptr));
		PUT(HDRP(ptr), PACK(size, 0, 1));
		//PUT(FTRP(ptr), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc){
		/* previous block not allocated */
		ptr = PREV_BLKP(ptr);
		size_t alloc = GET_PREV_ALLOC(ptr);
		size += GET_SIZE(HDRP(ptr));
		printf("\nPrev block allocated %d\n", GET_PREV_ALLOC(PREV_BLKP(ptr)));
		printf("current block head %p", HDRP(ptr));
		delete_block(ptr);
		PUT(HDRP(ptr), PACK(size, 0, alloc));
		//PUT(FTRP(ptr), PACK(size, 0));
	}

	else if(!prev_alloc && !next_alloc){
		/* Both block not allocated */
		size = size + GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
		delete_block(PREV_BLKP(ptr));
		delete_block(NEXT_BLKP(ptr));
		size_t alloc = GET_PREV_ALLOC(PREV_BLKP(ptr));
		PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0, alloc));
		ptr = PREV_BLKP(ptr);
	}

	return ptr;
}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	//if (size < MINIMUM){
	//	size = MINIMUM;
	//}
	if ((long)(bp = mem_sbrk(size)) == -1){
		return NULL;
	}
 
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0, 1)); /* Free block header */
	//PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 1)); /* New epilogue header */

	bp = coalease(bp);
	bp = add_block(bp);
	/* Coalease if the previous block was free */
	return bp;
}

static void *find_fit(size_t size)
{
	void *bp;
	unsigned int entry_num = get_list_number(size);

	for (int i = entry_num; i < SEG_NUM; i++){
		for (bp = SEG_ENTRY(seg_list, i); (bp != NULL) && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_FRPT(bp)){
			if (size <= (size_t)GET_SIZE(HDRP(bp))){
				return bp;
			}
		}
	}
	return NULL;
}

/* Place block at begining of a free block. Split if 
 * remaining block is larger than minimum size
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
		size_t alloc = GET_PREV_ALLOC(bp);
		PUT(HDRP(bp), PACK(asize, 1, alloc));
		//PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0, 1));
		//PUT(FTRP(bp), PACK(csize - asize, 0));
		bp = coalease(bp);
		bp = add_block(bp);
	}
	else {
		/* Allocate entire block */
		delete_block(bp);
		size_t alloc = GET_PREV_ALLOC(bp);
		PUT(HDRP(bp), PACK(csize, 1, alloc));
		//PUT(FTRP(bp), PACK(csize, 1));
	}
}

static void *add_block(void *bp)
{
	/* Coalease first then allocate to seg list */
	//bp = coalease(bp);

	int size = GET_SIZE(HDRP(bp));
	unsigned int seg_number = get_list_number(size);

	if (SEG_ENTRY(seg_list, seg_number) == NULL){
		NEXT_FRPT(bp) = NULL;
		PREV_FRPT(bp) = NULL;
	}
	else if (SEG_ENTRY(seg_list, seg_number)){
		NEXT_FRPT(bp) = SEG_ENTRY(seg_list, seg_number);
		PREV_FRPT(bp) = NULL;
		PREV_FRPT(SEG_ENTRY(seg_list, seg_number)) = bp;
	}
	SEG_ENTRY(seg_list, seg_number) = bp;

	return bp;
}

static void delete_block(void *bp)
{
	int size = GET_SIZE(HDRP(bp));
	unsigned int seg_number = get_list_number(size);

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

static void check_bloack(void *bp)
{
	if (!in_heap(bp)){
		printf("(%p) Error: not in heap!!\n", bp);
	}
	if (!aligned(bp)){
		printf("(%p) Error: not alinged!!\n", bp);
	}
	return;
}

static void print_block(void *bp)
{
	int hsize, halloc, fsize, falloc, prev_alloc;

	/* Basic header and footer information */
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));
	prev_alloc = GET_PREV_ALLOC(bp);

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
			prev_alloc, (falloc ? 'a' : 'f'));
	else
		printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n",
			bp, hsize, (halloc ? 'a' : 'f'), PREV_FRPT(bp),
			NEXT_FRPT(bp), prev_alloc, (falloc ? 'a' : 'f'));
}

static unsigned int get_list_number(size_t size)
{
	if (size <= 8)
		return 0;
	else if (size <= 16)
		return 1;
	else if (size <= 24)
		return 2;
	else if (size <= 32)
		return 3;
	else if (size <= 56)
		return 4;
	else if (size <= 72)
		return 5;
	else if (size <= 128)
		return 6;
	else if (size <= 256)
		return 7;
	else if (size <= 512)
		return 8;
	else if (size <= 1024)
		return 9;
	else if (size <= 2048)
		return 10;
	else if (size <= 4096)
		return 11;
	else if (size <= 8192)
		return 12;
	else
		return 13;
}

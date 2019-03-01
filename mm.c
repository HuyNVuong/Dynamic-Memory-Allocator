/*
 * mm-handout.c -  Simple allocator based on implicit free lists and
 *                 first fit placement (similar to lecture4.pptx).
 *                 It does not use boundary tags and does not perform
 *                 coalescing. Thus, it tends to run out of memory
 *                 when used to allocate objects in large traces
 *                 due to external fragmentation.
 *
 * Each block has a header of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                         end
 * heap                                                          heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) |   pad   | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *    four  | prologue |  four   |                       | epilogue |
 *    bytes | block    |  bytes  |                       | block    |
 *
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"


/* Team structure */
team_t team = {
	/* Team name */
	" 10% bonus TO-GO",
	/* note that we will add a 10% bonus for
	* working alone */
	/* the maximum number of members per team
	 * is four */
	/* First member's full name */
	" Huy Vuong ",
	/* First member's email address */
	" hvuong3@unl.edu ",
	/* Second member's full name (leave
	* blank if none) */
	"",
	/* Second member's email address
	* (leave blank if none) */
	""
};


/* $begin mallocmacros */
/* Basic constants and macros */

/* You can add more macros and constants in this section */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    4       /* overhead of header (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header*/
#define HDRP(bp)	((char *)(bp) - WSIZE)
/* BONUS : computer address of block pointer footer */
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* A good way to access block predecessor and successor */
#define PRED_PTR(bp)	(*(char **)(bp))
#define SUCC_PTR(bp)	(*(char **)(bp + WSIZE))
// #define PRED(bp)	(*(char **)(bp))
// #define SUCC(bp)	(*(char **)(SUCC_PTR(bp)))


/* Given block ptr bp, compute address of next block */
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))


/* Get and set the first node in a free list of list_num */
#define GET_ROOT(heap, list)              ((char *)GET((heap) + ((list) * WSIZE)))
#define SET_ROOT(heap, list, new_root)    (PUT((heap) + ((list) * WSIZE), (new_root)))

/* $end mallocmacros */


/* Global variables */
static char *heap_listp;  /* pointer to first block */
static char *free_listp;  /* pointer to the first free block */
/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void printblock(void *bp);
static void *coalesce(void *bp, size_t size);
// static int get_block_size(size_t size);
static void delete_block(void *bp);
/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{
   /* create the initial empty heap */
   if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
		return -1;
   PUT(heap_listp, KEY);               /* alignment padding */
   PUT(heap_listp+WSIZE, PACK(DSIZE, 0));  /* prologue header */
   PUT(heap_listp+DSIZE, PACK(0, 0));  /* empty word*/
   PUT(heap_listp+DSIZE+WSIZE, PACK(0, 0));   /* epilogue header */
   heap_listp += (DSIZE);


   /* Extend the empty heap with a free block of CHUNKSIZE bytes */
   if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
   return (int) heap_listp;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
//    printf("Calling malloc...");
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;
	//	printf("call mm_malloc\n");

    /* Ignore spurious requests */
    if (size <= 0)
		return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= WSIZE)
		asize = WSIZE + OVERHEAD;
    else
		asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
	 //printf("asize = %d\n", asize);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
	 //printf("extendsize = %d\n", extendsize);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    {
 	printf("mm_malloc = NULL\n");
	return NULL;
    }
	 //printf("return address = %p\n", bp);
    place(bp, asize);
	 //mm_checkheap(1);
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
// static int get_block_size(size_t size)
// {
// 	int block = size / DSIZE;
// 	if (block <= 4) { return 0; }
// 	else if (block <= 8) { return 1; }
// 	else if (block <= 16) { return 2; }
// 	else if (block <= 32) { return 3; }
// 	else if (block <= 64) { return 4; }
// 	else if (block <= 128) { return 5; }
// 	else if (block <= 256) { return 6; }
// 	else if (block <= 512) { return 7; }
// 	else if (block <= 1024) { return 8; }
// 	else return 9;
// }

/* Support function to delete a block in a segregrated free list */
static void delete_block(void *bp)
{
	// printf("Deletting block\n");
	// printf("%p\n", bp);
	// // printf("%p\n", SUCC_PTR(PRED_PTR(bp)));
	// printf("%p\n", SUCC_PTR(bp));
	/* if the previous block is free. Set the pointer of the previous block to the next block */
	if (PRED_PTR(bp))
	{
		SUCC_PTR(PRED_PTR(bp)) = SUCC_PTR(bp);
	}

	else
	{
		free_listp = SUCC_PTR(bp);
	}
	// printf("%p\n", free_listp);
	PRED_PTR(SUCC_PTR(bp)) = PRED_PTR(bp);
}

void mm_free(void *bp)
{
	// if the pointer is not exist, then there's nothing to free
	if (!bp)
	{
		return;
	}

	size_t size = GET_SIZE(HDRP(bp));
	// if (heap_listp == 0) mm_init();
	PUT(HDRP(bp), PACK(size, 1)); // free block header
	PUT(FTRP(bp), PACK(size, 1)); // free block footer, avoid internal fragmentation
	// Immediate coalescing : coelesce each time free is called
	// char *prev_blk = PREV_BLKP(bp);
	// char *next_blk = NEXT_BLKP(bp);
	// // printf("NEXT_BLKP(bp) : %p  ---- next_blk : %p\n", next_blk, NEXT_BLKP(bp));
	// size_t prev_alloc = GET_ALLOC(FTRP(prev_blk)) || PREV_BLKP(bp) == bp;
	// size_t next_alloc = GET_ALLOC(HDRP(next_blk));
	// if (next_alloc) {
	// 	size += GET_SIZE(HDRP(next_blk));
	// 	PUT(HDRP(bp), PACK(size, 1));
	// }

	coalesce(bp, size);

}

static void *coalesce(void *bp, size_t size)
{
	// Immediate coalescing : coelesce each time free is called
	char *prev_blk = PREV_BLKP(bp);
	char *next_blk = NEXT_BLKP(bp);
	// printf("NEXT_BLKP(bp) : %p  ---- next_blk : %p\n", next_blk, NEXT_BLKP(bp));
	size_t prev_alloc = GET_ALLOC(FTRP(prev_blk)) || PREV_BLKP(bp) == bp;
	size_t next_alloc = GET_ALLOC(HDRP(next_blk));
	if (prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(next_blk));
		// /* Delete blocks from the segregated list */
		// printf("got here\n");
		// delete_block(next_blk);
		PUT(HDRP(bp), PACK(size, 1));
		PUT(FTRP(bp), PACK(size, 1));
	}
	/* Case 2 : free block in between allocated at front and freed block at end */
	else if (prev_alloc && !next_alloc)
	{


		// PUT(FTRP(bp), PACK(size, 0));

	}
	/* Case 3 : head alloc is freed and foot alloc is allocated */
	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(next_blk));
		// /* Delete blocks from the segregated list */
		// printf("got here\n");
		// delete_block(next_blk);
		PUT(HDRP(bp), PACK(size, 1));
		PUT(FTRP(bp), PACK(size, 1));
	}
	/* Case 4 : both end are freed */
	else
	{

	}
	int i = 0;
	char* hp = heap_listp;
	while(((int)NEXT_BLKP(hp) <(int)bp) && ((int)hp<(int)mem_heap_hi)){
	//	printf("%d\n", i);
	//	printf("no\n");
		hp = NEXT_BLKP(hp);
		i++;
	}
	//	printf("yes\n");
	//	printf("%p  %p\n",hp, bp);
	//	printf("%p  %p\n",NEXT_BLKP(hp),bp);
        if(GET_ALLOC(HDRP(hp)) == 1) {
                //bp = NEXT_BLKP(bp);
		PUT(HDRP(hp),PACK(size+=GET_SIZE(HDRP(hp)),1));
        //      printf("front got coalsed\n");
		//PUT(HDRP(bp),PACK((size+=GET_SIZE(HDRP(NEXT_BLKP(bp)))),1));

        } else {
		//printf("didnt do it\n");
	}
	return bp;
}

/* $end mmfree */


/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
//	printf("Calling re-alloc...");
	// If pointer does not exist, then it is a malloc
	if (ptr == NULL)
	{
		return mm_malloc(size);
	}

	// If the newly allocated size is 0, then it is a free
	if (size <= 0)
	{
		mm_free(ptr);
	}

	// define new pointer to return
	size_t old_size = GET_SIZE(HDRP(ptr));
	char * new_bp = mm_malloc(size);

	size_t asize; /* Adjusted block size */
	//	size_t extendsize; /* amount to extend heap if no fit */
	if (size <= WSIZE)
		asize = WSIZE + OVERHEAD;
    else
		asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
	// asize = (size <= WSIZE) ? (WSIZE + OVERHEAD) : (DSIZE + ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE));

	/* new size need more blocks */
	if (asize <= old_size)
	{
//		extendsize = MAX(asize, CHUNKSIZE);
		/* if newly allocated space is smaller than old space, just use the old space */
		mm_free(new_bp);
		place(ptr, asize);
		return ptr;
	}
	else
	{
		// mm_free(new_bp);
		// // mm_free(ptr);
		// size_t adj_old_size;
		// if (old_size <= WSIZE)
		// 	adj_old_size = WSIZE + OVERHEAD;
	    // else
		// 	adj_old_size = DSIZE * ((old_size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
		// /* if the newly allocated place is not enough, then we allocate to a new block pointers
		// 	then free the old pointers
		// 	*/
		// /* Search the free list for a fit */
	    // if ((new_bp = find_fit(adj_old_size)) != NULL)
		// {
		// 	memcpy(new_bp, ptr, adj_old_size);
		// 	mm_free(ptr);
		// 	return new_bp;
		// }
		// /* No fit found. Get more memory and place the block */
	    // size_t extendsize = MAX(adj_old_size,CHUNKSIZE);
		//  //printf("extendsize = %d\n", extendsize);
	    // if ((new_bp = extend_heap(extendsize/WSIZE)) == NULL)
	    // {
		//  	printf("mm_realloc = NULL\n");
		// 	return NULL;
	    // }
		//
		// memcpy(new_bp, ptr, adj_old_size);
		// mm_free(ptr);
		memcpy(new_bp, ptr, old_size);
		mm_free(ptr);
		return new_bp;
	}

	// mm_free(ptr);
	/* You need to implement this function. */
	return new_bp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose)
{
	char *bp = heap_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);
	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
	}

	if (verbose)
		printblock(bp);
	if ((GET_SIZE(HDRP(bp)) != 0) || (GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
		return NULL;

    /* Initialize free block header and the epilogue header */
    PUT(HDRP(bp), PACK(size, 1));         /* free block header */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0)); /* new epilogue header */
    return bp;
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
	size_t csize = GET_SIZE(HDRP(bp));
	// printf("csize = %d\n", csize);
	if ((csize - asize) >= (DSIZE))
	{
		PUT(HDRP(bp), PACK(asize, 0));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 1));
	}
	else
	{
		PUT(HDRP(bp), PACK(csize, 0));
	}
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(bp-WSIZE) > 0; bp = NEXT_BLKP(bp)) {
		if (GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    	return bp;
		}
    }
    return NULL; /* no fit */
}
static void printblock(void *bp)
{
	    size_t hsize, halloc;

		hsize = GET_SIZE(HDRP(bp));
		halloc = GET_ALLOC(HDRP(bp));

		if (hsize == 0) {
			printf("%p: EOL\n", bp);
			return;
		}

		printf("%p: header: [%zu:%c]\n", bp, hsize, (halloc ? 'f' : 'a'));
}

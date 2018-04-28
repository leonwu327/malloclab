/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define PRINT_HEAD_AND_TAIL() \
    do {\
        if (debug) { \
            printf("head: %p, tail: %p\n", head_free_listp, tail_free_listp); \
        } \
    } while(0) \

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */

#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1<<12)   /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))
#define PUT_PTR(p, val) (*(char **)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PREV_PTR(bp) ((char **)((char *)(bp)))
#define NEXT_PTR(bp) ((char **)((char *)(bp) + DSIZE))

static void *heap_listp;
static void *head_free_listp = NULL;
static void *tail_free_listp = NULL;

static int debug = 1;

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        /* ���߶��е������ */
        PUT_PTR(PREV_PTR(bp), NULL);            /* Prev block */
        PUT_PTR(NEXT_PTR(bp), head_free_listp); /* Next block */
        printf("%p, %p, %p\n", PREV_PTR(bp), NEXT_PTR(bp), bp);
        head_free_listp = bp;
        if (tail_free_listp == NULL) {
            tail_free_listp = head_free_listp;
        }
        
    } else if (prev_alloc && !next_alloc) {
        PUT_PTR(PREV_PTR(bp), *PREV_PTR(NEXT_BLKP(bp)));   /* Prev block */
        PUT_PTR(NEXT_PTR(bp), *NEXT_PTR(NEXT_BLKP(bp)));   /* Next block */

        size += (GET_SIZE(HDRP(NEXT_BLKP(bp))));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        void *nextptr = *NEXT_PTR(NEXT_BLKP(bp));
        if (nextptr == NULL) {
            assert(NEXT_BLKP(bp) == tail_free_listp);
            tail_free_listp = PREV_BLKP(bp);
        } else {
            PUT_PTR(PREV_PTR(nextptr), PREV_BLKP(bp)); 
        }
        PUT_PTR(NEXT_PTR(PREV_BLKP(bp)), nextptr);   
        
        size += (GET_SIZE(HDRP(NEXT_BLKP(bp)))) + 
                (GET_SIZE(HDRP(PREV_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words) 
{
    void *bp;
    size_t size;

    /* Alloc an even number of words to maintain alignment */
    size = words % 2 ? ((words + 1) * WSIZE) : (words * WSIZE); 

    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    
    PUT(HDRP(bp), PACK(size, 0));             /* Prologue header */
    PUT(FTRP(bp), PACK(size, 0));             /* Prologue footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));     /* Epilogue header */

    return coalesce(bp);
}
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    mem_init();
    
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((tail_free_listp = extend_heap(CHUNKSIZE / WSIZE)) == NULL) {
        return -1;
    }
    
    PRINT_HEAD_AND_TAIL();
    
    return 0;
}

void *find_fit(size_t asize) {
    void *ptr = head_free_listp;
    
    while (ptr && (GET_SIZE(HDRP(ptr)) > 0)) {
        if ((!GET_ALLOC(HDRP(ptr))) && GET_SIZE(HDRP(ptr)) >= asize) {
            return ptr;
        }
        ptr = *NEXT_PTR(ptr);
    }

    return NULL;
}

void place(void *ptr, size_t asize) {
    size_t presize;
    
    presize = GET_SIZE(HDRP(ptr));
    
    if ((presize - asize) >= 4 * DSIZE) {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(presize - asize, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(presize - asize, 0));
        
        PUT_PTR(NEXT_PTR(NEXT_BLKP(ptr)), *NEXT_PTR(ptr));
        PUT_PTR(PREV_PTR(NEXT_BLKP(ptr)), *PREV_PTR(ptr));
        
        if (head_free_listp == ptr) {
            head_free_listp = NEXT_BLKP(ptr);
        }
        if (tail_free_listp == ptr) {
            tail_free_listp = NEXT_BLKP(ptr);
        }

    } else {
        PUT(HDRP(ptr), PACK(presize, 1));
        PUT(FTRP(ptr), PACK(presize, 1));
        
        void *prevptr = *PREV_PTR(ptr);
        void *nextptr = *NEXT_PTR(ptr);

        if (prevptr) {
            PUT_PTR(NEXT_PTR(prevptr), nextptr);
        } else {
            assert(head_free_listp == ptr);
            head_free_listp = nextptr;
        }
        if (nextptr) {
            PUT_PTR(PREV_PTR(nextptr), prevptr);
        } else {
            assert(tail_free_listp == ptr);
            tail_free_listp = prevptr;
        }
    }
    PRINT_HEAD_AND_TAIL();
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void  *ptr;

    if (0 == size) {
        return NULL;
    }

    if (size < DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    if ((ptr = find_fit(asize)) != NULL) {
        place(ptr, asize);
        return ptr;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    
    place(ptr, asize);
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((void *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

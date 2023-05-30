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


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Basic constants and macros
#define WSIZE 4 //Word and header/footer size (bytes)
#define DSIZE 8 //Double word size(bytes)
#define CHUNKSIZE (1 <<12) //Extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y) ? (x):(y))
//pack a size and allocated bit into a word
#define PACK(size,alloc) ((size) | (alloc))

//Read and write a word at address p
#define GET(p)     (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

//Read the size adn allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//Given block ptr bp, compute address of its header and footer
#define GET_HD_BLK_SIZE(p) GET_SIZE(HDRP(p))
#define GET_FT_BLK_SIZE(p) GET_SIZE(FTRP(p))

//Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

#define PREDP(bp)  (*(void **)(bp))
#define SUCC(bp)  (*(void **)((bp)+WSIZE))

/* 
 * mm_init - initialize the malloc package.
 */

// static char *mem_heap; //points to first byte of heap
// static char *mem_brk; //points to last byte of heap plus 1
// static char *mem_max_addr; //max legal heap addr plus 1
static char *heap_listp;
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void list_remove(void *bp);
static void list_add(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) //case 1
        ;
    else if(prev_alloc && !next_alloc){ //case 2
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){//case 3
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else if(!prev_alloc && !next_alloc) { //case  4
        list_remove(PREV_BLKP(bp));
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    list_add(bp);
    return bp;
}
static void *find_fit(size_t asize){
    void *bp;
    for (bp = SUCC(heap_listp); !GET_ALLOC(HDRP(bp)); bp = SUCC(bp)){
        if (asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL; //No fit
}
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    list_remove(bp);
    if((csize-asize >= (2*DSIZE))){
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        list_add(bp);  
    }
    else{
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
          
    }
}
void mm_free(void*bp){
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    //allocate an even number of words to maintain alignment
    size = (words % 2) ? (words+1) * DSIZE : words * DSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    //initialize free block header.footer and the epilogue header
    PUT(HDRP(bp), PACK(size,0)); //Free block header
    PUT(FTRP(bp), PACK(size,0)); //Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); //New epilogue header
    
    //Coalesce if the previous block was free
    return coalesce(bp);
}
static void list_add(void *bp){
    SUCC(bp) = SUCC(heap_listp);
    PREDP(bp) = heap_listp;
    PREDP(SUCC(heap_listp)) = bp;
    SUCC(heap_listp) = bp;
}
static void list_remove(void *bp){
    SUCC(PREDP(bp)) = SUCC(bp);
    PREDP(SUCC(bp)) = PREDP(bp);
}
int mm_init(void)
{
    //Create the initial empty heap
    mem_init(); 
    if((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp,0);                          //Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(2 * DSIZE,1));  //Prologue header
    PUT(heap_listp + (2*WSIZE), heap_listp+(3*WSIZE)); //Predecessor points successor
    PUT(heap_listp + (3*WSIZE), heap_listp+(2*WSIZE)); //Successor points predecessor
    PUT(heap_listp + (4*WSIZE), PACK(2 * DSIZE,1));  //Prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0,1));      //Epilogue header
    heap_listp += 2*WSIZE;

    //Extend the empty heap with a free block of CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE/DSIZE) == NULL)
        return -1;
    return 0;
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// void *mem_sbrk(int incr){
//     char *old_brk = mem_brk;

//     if((incr<0) || ((mem_brk+incr)> mem_max_addr)){
//         errno = ENOMEM;
//         fprintf(stderr, "Error0\n");
//         return(void *) -1;
//     }
//     mem_brk += incr;
//     return(void *) old_brk;
// }
void *mm_malloc(size_t size)
{
    size_t asize; //adjusted block size
    size_t extendsize; // amount to extend heap if no fit
    char *bp;

    //Ignore spurious requests
    if(size == 0){
        return NULL;
    }

    //Adjusted block size to inlcude overhead and alignment reqs.
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size+(DSIZE) + (DSIZE-1)) / DSIZE);
    }

    //search the free list for a fit
    if((bp =find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    
    //No fit found
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/DSIZE)) == NULL){
        return NULL;
    }
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */

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
    copySize = GET_SIZE(HDRP(oldptr));
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
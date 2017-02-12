/*
 * mm.c 
 * In this approach, we used segrated lists and each list has blocks
 * of size class 2^n to 2^(n+1)-1. Free blocks are managed in this seg_list.
 * seg_listp is a global pointer to the first element of seg list.
 * The seg_lists is of size COUNT*WSIZE, each entry stores the address 
 * of first block in a size class,and the entire seg_lists is on the bottom of heap. 
 * inserted or removed from/to seg_lists when freed or malloced. Min-block-size = 4*WSIZE
 * All blocks have footer and header, packed with size and allocation bit,
 * free block stores the ptr to prev and next block in the same seg_list in
 * the payload. A block is allocated by finding the best-fit block in seg_lists,
 * optimized for binary sizes using first-fit. Blocks are coalesced whenever 
 * they are freed. Realloc is implemented in-place, first searching the next 
 * block, try to minimize the use of memcpy. 
 *
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
    "Wildcats",
    /* First member's full name */
    "Wille",
    /* First member's email address */
    ""
    /* Second member's full name (leave blank if none) */
    "Wildcat",
    /* Second member's email address (leave blank if none) */
    ""
};

/*  EMPTY BLOCK
 *  -----------------------------------------------*
 *  |HEADER:    block size   |     |     |alloc bit|
 *  |----------------------------------------------|
 *  | pointer to prev free block in this size list |
 *  |----------------------------------------------|
 *  | pointer to next free block in this size list |
 *  |----------------------------------------------|
 *  |FOOTER:    block size   |     |     |alloc bit|
 *  ------------------------------------------------
 */

/*  Allocated BLOCK
 *   -----------------------------------------------*
 *   |HEADER:    block size   |     |     |alloc bit|
 *   |----------------------------------------------|
 *   |               Data                           |
 *   |----------------------------------------------|
 *   |               Data                           |
 *   |----------------------------------------------|
 *   |FOOTER:    block size   |     |     |alloc bit|
 *   ------------------------------------------------
 */

/*Basic constants and macros */
#define WSIZE 4  /*word and header/footer size (bytes) */
#define DSIZE 8  /*Double word size (bytes) */
#define CHUNKSIZE (1<<6) /*extend heap by this amount (bytes) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/*read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/*read the size, allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given bock ptr bp, compute address of its header and footer */
#define HDRP(bp)   ((char *)(bp) - WSIZE)
#define FTRP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*global variables */
static char *heap_listp = 0;
#define SEG_LIST_COUNT  20     /*number of segregated lists*/
static void * seg_listp;       /*pointer pointing to start of seg_list (ptr to head of first list)*/

/*helper macros for seg list */
/*set the prev and next field of bp to address nbp*/
#define PUT_PTR(p, ptr)  (*(unsigned int *)(p) = (unsigned int)(ptr))

/*get address of the prev/next field of a free block in a seg_list with pointer bp */
#define GET_PREV(bp)       ((char *)bp)
#define GET_NEXT(bp)        ((char *)(bp) + WSIZE)

/*get the address of the pre/next block in a seg_list (actual address) */
#define GET_PREV_BLK(bp)   (*(char **)(bp))
#define GET_NEXT_BLK(bp)   (*(char **)(GET_NEXT(bp)))

/*helper macro for seg-listst*/
#define SEG_LIST(ptr, index)  *((char **)ptr+index)

/* Function prototypes */    
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void * bp, size_t asize);
static void insert_free_block(void *bp, size_t block_size);
static void remove_free_block(void *bp);
static int mm_check(void);


/*
 * mm_init - initialize the malloc package, first put seg_lists on heap,
 * then create prolouge and epilogue headers/footers.
 */
int mm_init(void)
{
  int list_number; 
  seg_listp = mem_sbrk(SEG_LIST_COUNT*WSIZE);
 
  /* initialize the seg_lists */
  for (list_number = 0; list_number < SEG_LIST_COUNT; list_number++) {
    SEG_LIST(seg_listp, list_number)= NULL;
  }

  /* create the initial empty heap */
  if ((heap_listp = mem_sbrk(4*WSIZE))==(void *) -1)
	return -1; 
  PUT(heap_listp, 0);				/*Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  /*Prologue header */
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  /*Prologue footer */
  PUT(heap_listp + (3*WSIZE), PACK(0,1));       /* Epilogue header*/
  heap_listp += (2*WSIZE);

  /*Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
  	return -1;
  return 0;
}

/*
 * extend_heap: extend the heap by requesting words space from heap
 */ 
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /*Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1)*WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
  	return NULL;

  /*initialize free block header/footer and the epilogue header*/
  PUT(HDRP(bp), PACK(size, 0));   	/*Free Block header*/
  PUT(FTRP(bp), PACK(size, 0));   	/*Free Block footer*/
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*New Epilogue header*/
  insert_free_block(bp, size); 

  /*coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * find_fit -return a ptr to a free block that can accommodate asize
 * implemented with best-fit strategy, scanning through the list for
 * the smallest block that can fit asize 
 *
 */
static void *find_fit(size_t asize)
{   
    size_t size = asize;
    int list_number = 0;
    void *list_ptr = NULL;
 
    while (list_number < SEG_LIST_COUNT) {
	
     if ((list_number == SEG_LIST_COUNT - 1) || ((size <= 1) && (SEG_LIST(seg_listp, list_number)!= NULL))) {
       list_ptr  = SEG_LIST(seg_listp, list_number);

        // locate the smallest block that can fit
	while ((list_ptr != NULL) && (asize > GET_SIZE(HDRP(list_ptr)))){
          list_ptr = GET_PREV_BLK(list_ptr);
        }
        if (list_ptr != NULL) {
         break;
        }
      }
      list_number++;
      size = size >> 1;
    }
    return list_ptr;  
}

/*
 * place - occupy asize of block pointed by bp, coalesce the remaining free
 * space if the block size is larger than allocated size.
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    void *np = NULL;
    remove_free_block(bp);
    
    /* if the remaining free space is larger than min-block-size, coalesce*/
    if ((csize - asize) >= (2*DSIZE)) {
      if ((csize - asize) >= 200){
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        np = NEXT_BLKP(bp);
        PUT(HDRP(np), PACK(asize, 1));
        PUT(FTRP(np), PACK(asize, 1));
        insert_free_block(bp, csize - asize);
        return np;  
      }
      else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        np = NEXT_BLKP(bp);
        PUT(HDRP(np), PACK(csize - asize, 0));
        PUT(FTRP(np), PACK(csize - asize, 0));
        insert_free_block(np, csize - asize);
      }
    }
    else {
       PUT(HDRP(bp), PACK(csize, 1));
       PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;
}

/* 
 * mm_malloc- malloc block by finding a block that fits (call find_fit),
 * if no fit, extend the heap for more space, then call place to place
 * the block. 
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;  /*adjusted block size */
    size_t extendsize; /*amount ot extend heap if no fit */
    char *bp;
    char *ptr;

    /*ignore spurious requests */
    if (size == 0)
      return NULL;
    
    /*adjusted block size to include overhead and alignment reqs*/
    if (size <= DSIZE)
      asize = 2*DSIZE;
    else
      asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
      ptr =  place(bp, asize);
      return ptr;
    }
    
    /*no fit found, get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
      return NULL;
    ptr =  place(bp, asize);
    return ptr;
}

/*
 * mm_free - Freeing a block by update allocation bit, and insert 
 * into the seg_list for reuse. Coalesce if possible.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_free_block(bp, size);
    coalesce(bp);
}

/*
 * coalesce - check four cases and try to merge the freed block at *bp with previous and next block
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
   
  if (prev_alloc && next_alloc) {		/*case 1 - both prev and next block allocated, no coalesce*/
    return bp;
  } 
  else if (prev_alloc && !next_alloc) {		/*case 2 - prev block allocated, next not, coalesce with next*/
    remove_free_block(bp);
    remove_free_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  else if (!prev_alloc && next_alloc) { 	/*case 3 - prev block free, next allocated, coalesce with prev*/
    remove_free_block(bp);
    remove_free_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  else {					/*case 4- both prev and next free, coalsce three blocks into one*/
    remove_free_block(PREV_BLKP(bp));
    remove_free_block(bp);
    remove_free_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  /*put the coalesced block into the seg_list for reuse*/
  insert_free_block(bp, size);
  return bp;
}

 
/*
 * mm_realloc - implementaed with optimzation on every case:
 * First check edge cases: ptr = null, size = 0, oldptr size = new size
 * If none of those trivial cases, we consider 3 special cases:
 * Case 1: If we are shrinking (new size requested < size of oldptr)
 *         We can shrink the size of oldptr, update header footer,
 *         and free & coalesce the remaining free space 
 * If we are getting a larger size, we consider case 2 & 3.
 * Case 2: Check in-place if next block in memory after ptr is free
 * 	   and can fit the new size, if yes, then combine the two
 * Case 3: Last option, to allocate a new block of size by calling
 *   	   mm_malloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    void * nextptr;
    size_t copySize, asize, nsize;
   
    /*if size = 0, we want to free ptr*/
    if (size == 0) {
      mm_free(oldptr);
      return NULL;
    }   

    /*if oldptr is null, we want to call malloc(size) */
    if (oldptr == NULL) {
      return mm_malloc(size);
    }
    asize = ALIGN(size);

    /*realloc ptr with size*/
   copySize =GET_SIZE(HDRP(oldptr))-DSIZE;
  
    if (asize == copySize) {
      return oldptr;
    }

    /*Case 1: */
    /*if size < oldptr size, the oldptr can hold the new size*/
    if (asize < copySize) {
      //if the remaining space is not enough to store anything, return oldptr
      if (copySize - asize - DSIZE <= DSIZE)
	return oldptr;
      PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
      PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
      newptr = oldptr;
      oldptr = NEXT_BLKP(newptr);
      /*free the space emptied*/
      PUT(HDRP(oldptr), PACK(copySize - asize, 0));
      PUT(FTRP(oldptr), PACK(copySize - asize, 0));
      insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
      coalesce(oldptr);
      return newptr; 
    }

    /*Case 2: */
    /*if size > oldptr size, we need to either find a new block, or take the space of next blk*/
    nextptr = NEXT_BLKP(oldptr);
    /*now check if the next block after oldptr block, in-place, is free*/
    if (nextptr != NULL && !GET_ALLOC(HDRP(nextptr))) {
       nsize = GET_SIZE(HDRP(nextptr));	
      if (nsize + copySize >= asize) {
	remove_free_block(nextptr);
	if (nsize + copySize - asize <= DSIZE) {
  	  //if remaining space in next block cannot hold any value, just use it all
  	  PUT(HDRP(oldptr), PACK(copySize + DSIZE + nsize, 1));
          PUT(FTRP(oldptr), PACK(copySize + DSIZE + nsize, 1));
          return oldptr;
	}
 	else{    //coalecse the reamming free sapce after
          PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
          PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
	  newptr = oldptr;
	  oldptr = NEXT_BLKP(newptr);
	  PUT(HDRP(oldptr), PACK(copySize + nsize - asize, 0));
      	  PUT(FTRP(oldptr), PACK(copySize + nsize - asize, 0));
      	  insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
      	  coalesce(oldptr);
      	  return newptr;
	}
      } 
    }

    /*Case 3: */
    /*now we have our last option, which is to allocate a completely new block to fit the size*/ 
    newptr = mm_malloc(size); 
    if (newptr == NULL)
      return NULL;
    /*copy over the data from oldptr*/
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * insert_free_block - takes a pointer to a block bp and add it to the seg list
 * each individual list of the same size class is sorted by actual block size
 */
static void insert_free_block(void *bp, size_t block_size)
{
  void *list_ptr = NULL;
  void *insert_loc = NULL;
  /*find the list number / index for this block*/
  int list_number = 0; 
  while ((list_number < (SEG_LIST_COUNT - 1)) && (block_size > 1)) {
    block_size = block_size >> 1;
    list_number++;
  }

  list_ptr = SEG_LIST(seg_listp, list_number);
  /*find the location to insert, so that the list  will be sorted by block size*/
  while ((list_ptr != NULL) && (block_size > GET_SIZE(HDRP(list_ptr)))) {
    insert_loc = list_ptr;
    list_ptr = GET_PREV_BLK(list_ptr);
  }
   
  /*insert the free block based on the condition of insert_loc and list_ptr*/
  if (list_ptr) {
    if (insert_loc) {  //in between insert_loc and list_ptr
       PUT_PTR(GET_PREV(insert_loc), bp);
       PUT_PTR(GET_NEXT(bp), insert_loc);
       PUT_PTR(GET_PREV(bp), list_ptr);
       PUT_PTR(GET_NEXT(list_ptr), bp); 
    }
    else {    //  bp smaller than first item in list_ptr, insert at start
       PUT_PTR(GET_NEXT(list_ptr), bp);
       PUT_PTR(GET_PREV(bp), list_ptr);
       PUT_PTR(GET_NEXT(bp), NULL);
       SEG_LIST(seg_listp, list_number)=bp;
    }
  }
  else {     
    if (insert_loc) {
      PUT_PTR(GET_NEXT(bp), insert_loc);
      PUT_PTR(GET_PREV(insert_loc), bp);
      PUT_PTR(GET_PREV(bp), NULL);    
    }
    else {
      SEG_LIST(seg_listp, list_number)= bp;
      PUT_PTR(GET_PREV(bp), NULL);
      PUT_PTR(GET_NEXT(bp), NULL);
      return;
    }
  }
  return; 
}

/*
 * remove_free_block- remove a free block bp from seg_list
 * update the prev/next pointers 
 */
static void remove_free_block(void *bp)
{ 
  int list_number = 0; 
  size_t block_size = GET_SIZE(HDRP(bp));
  
  /*if bp is the head of a seg_list*/
  if (GET_NEXT_BLK(bp) == NULL) {
  // find the list number / index for this block
    while (list_number < (SEG_LIST_COUNT - 1) && block_size > 1) {
      block_size = block_size >> 1;
      list_number++;
    }
    SEG_LIST(seg_listp, list_number)= GET_PREV_BLK(bp);
    if (SEG_LIST(seg_listp, list_number) != NULL) {
      PUT_PTR(GET_NEXT(SEG_LIST(seg_listp, list_number)), NULL);
    }
    return;
  }
  
  /*if bp is not the head of a seg_list, simply update the
   next pointer of prev block and prev pointer of next block*/
  PUT_PTR(GET_PREV(GET_NEXT_BLK(bp)), GET_PREV_BLK(bp)); 
  if (GET_PREV_BLK(bp) != NULL) {
    PUT_PTR(GET_NEXT(GET_PREV_BLK(bp)), GET_NEXT_BLK(bp));
  } 
}

/*
 * mm_check - check heap consistency, return 0 if all correct, -1 if not
 * Also print out the error
 */ 
static int mm_check(void) 
{
  int errorcode = 0;  //set to -1 if see any error
  int list_number = 0; 
  void *blk_ptr = NULL; //point to the current blk examing
  void *nxt_ptr = NULL; //point to the next blk examing
  void *help_ptr = NULL;  //used to help compare a blk_ptr to every block in seg_list

 /*loop through seg_list*/
  while (list_number < SEG_LIST_COUNT) {
      blk_ptr = SEG_LIST(seg_listp, list_number);
      while (blk_ptr != NULL) {    
      /*check if every block in seg_list marked free*/
        if (GET_ALLOC(blk_ptr)) {
          printf("Free block not marked free\n");
	  errorcode = -1;
        }
        blk_ptr = GET_PREV_BLK(blk_ptr);
      }
      list_number++;
  }

  /*loop through every block*/   
  nxt_ptr = NULL;
  blk_ptr = heap_listp;
  while (!(GET_SIZE(HDRP(blk_ptr))==0) && !GET_ALLOC(HDRP(blk_ptr))== 1) {
    nxt_ptr = NEXT_BLKP(blk_ptr);
   
    /*check if footer/header information match*/
    if (GET_SIZE(HDRP(blk_ptr)) != GET_SIZE(FTRP(blk_ptr))) {
      printf("Header/Footer size field not match\n");
      errorcode = -1;
    }    
    if (GET_ALLOC(HDRP(blk_ptr)) != GET_ALLOC(FTRP(blk_ptr))) {
      printf("Header/Footer allocation info not match\n");
      errorcode = -1;
    }
    /*ALIGHTMENT check if block is 8-byte aligned*/
    if ((unsigned int)blk_ptr % DSIZE) {
      errorcode = -1;
      printf("Block is not DSIZE (8 byte) aligned\n");
    }
   
    /*check if two continuous free blocks escaped coalescing*/
    if (!(GET_ALLOC(HDRP(blk_ptr)) | GET_ALLOC(HDRP(nxt_ptr)))) {
      errorcode = -1;
      printf("Two continuous blocks escaped coalescing\n");
    } 

    /*if this is a free block, check if it is in seg_list*/
    if (!GET_ALLOC(HDRP(blk_ptr))) {
      list_number = 0;
      //search for the block in seg_list
      while (list_number < SEG_LIST_COUNT) {
        //loop through every block in this seg_list
        help_ptr = SEG_LIST(seg_listp, list_number);
        while (help_ptr != NULL){
          //check if this free block is the same as list_ptr
          if (help_ptr == blk_ptr) {
 	    break; 
          }
          help_ptr = GET_PREV_BLK(help_ptr);
	}
	if (help_ptr == blk_ptr)
	  break;
        list_number++;
       }
 	if (help_ptr != blk_ptr) {
          errorcode = -1;
	  printf("free block not in the seg_list\n");
        }
    }

    blk_ptr = NEXT_BLKP(blk_ptr);
 }
  return errorcode;

}

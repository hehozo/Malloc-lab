# Malloc-lab
CSAPP Malloc-lab: design and implement my own dynamic memory allocator in C, with a 91% evaluation score.
The mm.c file is included. The code is well-commented and readable.

## Design Logic

* In this approach, we used segrated lists and each list has blocks of size class 2^n to 2^(n+1)-1. Free blocks are managed in this seg_list. 

* seg_listp is a global pointer to the first element of seg list.

* The seg_lists is of size COUNT*WSIZE, each entry stores the address of first block in a size class,and the entire seg_lists is on the bottom of heap. 

* Blocks are inserted or removed from/to seg_lists when freed or malloced. 

* Min-block-size = 4*WSIZE

* All blocks have footer and header, packed with size and allocation bit.

* Free block stores the ptr to prev and next block in the same seg_list in the payload. 

* A block is allocated by finding the best-fit block in seg_lists, optimized for binary sizes using first-fit. 

* Blocks are coalesced whenever they are freed. Realloc is implemented in-place, first searching the next block, try to minimize the use of memcpy. 


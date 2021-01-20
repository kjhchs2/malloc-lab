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
	"WEEK06",
	/* First member's full name */
	"Jeongmin",
	/* First member's email address */
	"kim9099i@hanmail.net",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""
};
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// MACROS
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 1<<12
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLK(bp) ((char *)(bp)-GET_SIZE(HDRP(bp) - WSIZE))
#define NEXT_PTR(bp) (*(char **)(bp + WSIZE))
#define PREV_PTR(bp) (*(char **)(bp))
static char *heap_listp = 0;
static char *free_list = 0;
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void del_free(void* bp);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	heap_listp = mem_sbrk(4 * DSIZE);
	if (heap_listp == (void*)-1) return -1;
	PUT(heap_listp, 0);										// padding
	PUT(heap_listp + WSIZE, PACK(3* DSIZE, 1));				// header
	PUT(heap_listp + 2 * WSIZE, 0);							// prev
	PUT(heap_listp + 3 * WSIZE, 0);							// next
	PUT(heap_listp + 6 * WSIZE, PACK(3 * DSIZE, 1));		// footer
	PUT(heap_listp + 7 * WSIZE, PACK(0, 1));				// epilogue
	free_list = heap_listp + DSIZE;
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;
	return 0;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size)
{
	size_t asize;
	size_t extendsize;
	char* bp;
	if (size == 0) return NULL;
	if (size <= DSIZE) asize = 2 * DSIZE;
	else asize = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);
    bp = find_fit(asize);
	if (bp != NULL) {
		place(bp, asize);
		return bp;
	}
	extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize/WSIZE);
	if (bp == NULL) return NULL;
	place(bp, asize);
	return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void* bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc(void* bp, size_t size)
{
	if (size == 0) {
		mm_free(bp);
		return NULL;
	}
	size_t cur_size = GET_SIZE(HDRP(bp))-2*WSIZE;
	void* new_bp;
	size_t copy_len;           
	if(size < cur_size)	copy_len = size;
	else copy_len = cur_size;
	new_bp = mm_malloc(size);
	memcpy(new_bp, bp, copy_len);
	mm_free(bp);
	return new_bp;
}
// 힙 확장
static void *extend_heap(size_t words)
{
	char* bp;
	size_t size;
	size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE;
	bp = mem_sbrk(size);
	if((long)(bp == -1)) return NULL;
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(NEXT_BLK(bp)), PACK(0, 1));
	return coalesce(bp);
}
// 힙 병합
static void* coalesce(void* bp) {
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLK(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLK(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	// 다음 블록 병합
	if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLK(bp)));
		del_free(NEXT_BLK(bp));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	// 이전 블록 병합
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(FTRP(PREV_BLK(bp)));
		bp = PREV_BLK(bp);
		del_free(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	// 이전 다음 블록 병합
	else if (!prev_alloc && !next_alloc) {
		size += (GET_SIZE(FTRP(PREV_BLK(bp))) + GET_SIZE(HDRP(NEXT_BLK(bp))));
		del_free(PREV_BLK(bp));
		del_free(NEXT_BLK(bp));
		bp = PREV_BLK(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	NEXT_PTR(bp) = free_list;
	PREV_PTR(free_list) = bp;
	PREV_PTR(bp) = NULL;
	free_list = bp;
	return bp;
}
static void del_free(void* bp) {
	if (PREV_PTR(bp) != NULL) {
		NEXT_PTR(PREV_PTR(bp)) = NEXT_PTR(bp);
	}
	else {
		free_list = NEXT_PTR(bp);
	}
	PREV_PTR(NEXT_PTR(bp)) =  PREV_PTR(bp);
    bp = NEXT_PTR(bp);
}
static void* find_fit(size_t asize) {
	void* bp;
	for (bp = free_list; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_PTR(bp)) {
		if (GET_SIZE(HDRP(bp)) >= asize) {
            return (char*)bp;
        }
	}
	return NULL;
}
static void* find_fit2(size_t asize) {
	void* bp;
    int cnt =0;
    void* high = mem_heap_hi();
    printf("mem_brk : %p\n", high);
	for (bp = free_list; bp != NULL; bp = NEXT_PTR(bp)) {
		// if (GET_SIZE(HDRP(bp)) >= asize) {
        //     printf("find fit addr %p\n", bp);
        //     return (char*)bp;
        // }
        cnt++;
        printf("cnt : %d\n", cnt);
	}
	return NULL;
}
static void place(void* bp, size_t asize) {
	size_t size = GET_SIZE(HDRP(bp));
    del_free(bp);
	if (size - asize >= 2 * DSIZE) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLK(bp);
		PUT(HDRP(bp), PACK(size - asize, 0));
		PUT(FTRP(bp), PACK(size - asize, 0));
		coalesce(bp);
	}
	else {
		PUT(HDRP(bp), PACK(size, 1));
		PUT(FTRP(bp), PACK(size, 1));
	}
}
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
    "jungle_week06_03",
    /* First member's full name */
    "gojae",
    /* First member's email address */
    "fighting@fighting.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
/* 우리는 더블워드 사이즈인 8을 ALIGNMENT에 정의 */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)   // ALIGNMENT와 가장 근접한 8배수(ALLIGNMENT배수)로 반올림 

/* 기본 상수 및 매크로 설정 */
#define WSIZE 4     // 워드사이즈로 헤더&푸터의 사이즈와 같음
#define DSIZE 8           // 더블 워드 사이즈 = ALIGNMENT 사이즈
#define CHUNKSIZE (1<<12)         // 초기 최대 힙 사이즈
#define MINIMUM 24

/* MAX함수 정의 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 사이즈와 할당 여부 넣어주기 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에 대해 읽기/쓰기 */
#define GET(p) (*(int *)(p))                   // p는 보통 void 포인터이기 때문에 사이즈를 나타내기 위해
#define PUT(p, val) (*(int*)(p) = (val))       // unsigned int 포인터로 형변환을 시켜주고 값을 가리킴

/* 블록 사이즈와 할당 여부 확인 */
#define GET_SIZE(p)   (GET(p) & ~0x7)       //~0x7은 "111....000"의 숫자가 된다. 즉, 헤더 정보에 있는 사이즈의 크기만 쉽게 가져옴
#define GET_ALLOC(p)  (GET(p) & 0x1)        //0x1은 할당 정보를 갖고 있는 뒷자리 "~~~"와 비교하여 할당 여부만 가져옴

/* 블록포인터(bp)로 헤더와 푸터의 주소를 계산 */
#define HDRP(bp)    ((void *)(bp) - WSIZE)                           // 헤더의 bp는 bp에서 WSIZE 값을 뺀 만큼
#define FTRP(bp)    ((void *)(bp) + GET_SIZE(HDRP(bp))-DSIZE)        // 푸터의 bp는 bp에서 내 사이즈를 더하고 DSIZE 값을 뺀 만큼

/* 블록포인터(bp)로 이전 블록과 다음 블록의 주소를 계산 */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)))     // 다음 블록 bp로 이동
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(HDRP(bp)-WSIZE))     // 이전 블록 bp로 이동

/* freeList의 이전 포인터와 다음 포인터 계산 */
#define NEXT_FLP(bp)  (*(void **)(bp + WSIZE))      // 다음 free list의 bp를 가져옴
#define PREV_FLP(bp)  (*(void **)(bp))              // 다음 free list의 bp를 가져옴

static char *heap_listp = 0;
static char *free_listp = 0;

static void *extendHeap(size_t words);
static void place(void *bp, size_t asize);
static void *findFit(size_t asize);
static void *coalesce(void* bp);
static void removeBlock(void *bp);

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(2*MINIMUM)) == NULL)
    {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1));
    PUT(heap_listp + (2 * WSIZE), 0);
    PUT(heap_listp + (3 * WSIZE), 0);
    PUT(heap_listp + MINIMUM, PACK(MINIMUM,1));
    PUT(heap_listp + WSIZE + MINIMUM, PACK(0,1));
    
    free_listp = heap_listp + DSIZE;
    if (extendHeap(CHUNKSIZE / WSIZE) == NULL) {
        return -1; 
    }
    return 0;
}

void * mm_malloc (size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if ( size<=0)
    {
        return NULL;
    }
    asize = MAX(ALIGN(size)+DSIZE, MINIMUM);
    if ((bp = findFit(asize)))
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp=extendHeap(extendsize/WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    if (!bp)
    {
        return ;
    }
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));

    coalesce(bp);
}


//realloc 다시
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;
    
    new_bp = mm_malloc(size);
    if (new_bp == NULL)
      return NULL;
    
    copySize = GET_SIZE(HDRP(old_bp)) - DSIZE ;

    if (size < copySize)
      copySize = size;
    
    memcpy(new_bp, old_bp, copySize);

    mm_free(old_bp);
    
    return new_bp;
}

static void *extendHeap(size_t words)
{
    char* bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if (size< MINIMUM)
    {
        size = MINIMUM;
    }
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize-asize)>=MINIMUM)
    {
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        removeBlock(bp);
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
        removeBlock(bp);
    }
}

static void *findFit(size_t asize)
{
    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp))==0; bp = NEXT_FLP(bp))
    {
        if (asize<=(size_t)GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

static void *coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        removeBlock(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc)
    {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))));
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    NEXT_FLP(bp) = free_listp;
    PREV_FLP(free_listp) = bp ;
    PREV_FLP(bp) = NULL;
    free_listp = bp ;

    return bp;
}

static void removeBlock(void* bp)
{
    if (PREV_FLP(bp))
    {
        NEXT_FLP(PREV_FLP(bp)) = NEXT_FLP(bp);
    }
    else
    {
        free_listp = NEXT_FLP(bp);
    }
    PREV_FLP(NEXT_FLP(bp)) = PREV_FLP(bp);
}
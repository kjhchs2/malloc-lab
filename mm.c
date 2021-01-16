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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)   // ALIGNMENT와 가장 근접한 8배수(ALLIGNMENT배수)로 반올림 
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))     //size_t를 통해 size 결정 *size_t는 64비트 환경에서 64비트

/* 기본 상수 및 매크로 설정 */
#define WSIZE 4                  // 워드사이즈로 헤더&푸터의 사이즈와 같음
#define DSIZE 8                  // 더블 워드 사이즈 = ALIGNMENT 사이즈
#define CHUNKSIZE (1<<12)        // 초기 최대 힙 사이즈

/* MAX함수 정의 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 사이즈와 할당 여부 넣어주기 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에 대해 읽기/쓰기 */
#define GET(p) (*(unsigned int *)(p))                   // p는 보통 void 포인터이기 때문에 사이즈를 나타내기 위해
#define PUT(p, val) (*(unsigned int*)(p) = (val))       // unsigned int 포인터로 형변환을 시켜주고 값을 가리킴

/* 블록 사이즈와 할당 여부 확인 */
#define GET_SIZE(p)   (GET(p) & ~0x7)       //~0x7은 "111....000"의 숫자가 된다. 즉, 헤더 정보에 있는 사이즈의 크기만 쉽게 가져옴
#define GET_ALLOC(p)  (GET(p) & 0x1)        //0x1은 할당 정보를 갖고 있는 뒷자리 "~~~"와 비교하여 할당 여부만 가져옴

/* 블록포인터(bp)로 헤더와 푸터의 주소를 계산 */
#define HDRP(bp)    ((char*)(bp) - WSIZE)                           // 헤더의 bp는 bp에서 WSIZE 값을 뺀 만큼
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp))-DSIZE)        // 푸터의 bp는 bp에서 내 사이즈를 더하고 DSIZE 값을 뺀 만큼

/* 블록포인터(bp)로 이전 블록과 다음 블록의 주소를 계산 */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE)))     // 다음 블록 bp로 이동
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp)-DSIZE)))     // 이전 블록 bp로 이동

/* The only global variable is a pointer to the first block */
static char* heap_listp;
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t adjust_size);
static void place(void* bp, size_t adjust_size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    /* 빈 힙 영역을 만들어보자 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1; {
        return 0;
    }
}

static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;
    // 정렬을 유지하기 위해 짝수 번호를 할당시킴
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // free한 block 앞, 뒤에 모두 할당 되어있는 block이 있는 경우
    if (prev_alloc && next_alloc) {
        return bp;
    }
    // free한 블록 뒤에만 free 되어있는 block이 있는 경우
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // free한 블록 앞에만 free 되어있는 block이 있는 경우
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // free한 block 앞, 뒤에 모두 free 되어있는 block이 있는 경우
    else {
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}


static void* find_fit(size_t adjust_size){
    char *bp = heap_listp;
    while ( GET_SIZE(HDRP(NEXT_BLKP(bp))) < adjust_size || GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 )
    {
        bp += GET_SIZE(HDRP(bp));

        if (GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0){        //Epilogue를 만났을 때
            return NULL;
        }
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t adjust_size;           // 블록 사이즈 조정
    size_t extend_size;           // 힙 확장 사이즈
    char* bp;
    if (size == 0)
    {
        return NULL;
    }
    if (size <= DSIZE)
    {
        adjust_size = DSIZE * 2;
    }
    else 
    {
    adjust_size = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);
    }
    // 사이즈에 맞는 위치 탐색
    if ((bp = find_fit(adjust_size)) != NULL)
    {
        place(bp, adjust_size);
        return bp;
    }
    // 사이즈에 맞는 위치가 없는 경우, 추가적으로 힙 영역 요청 및 배치
    extend_size = MAX(adjust_size, CHUNKSIZE);
    if ((bp = extend_haep(extend_size / WSIZE)) == NULL)
    {
        return NULL;
    } 
    place(bp, adjust_size);
    return bp;
}

static void place(void* bp, size_t adjust_size){

    int cur_size = GET_SIZE(HDRP(bp));

    if (cur_size - adjust_size < 2*DSIZE){      // 메모리를 할당하고 남은 공간이 16byte 미만일 때는 따로 뒤에 헤더, 푸터를 만들어주지 않는다.
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
    }
    else{
        PUT(HDRP(bp), PACK(adjust_size, 1));
        PUT(FTRP(bp), PACK(adjust_size, 1));
        PUT(HDR(NEXT_BLKP(bp)), PACK(cur_size - adjust_size, 0));
        PUT(FTR(NEXT_BLKP(bp)), PACK(cur_size - adjust_size, 0));
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }

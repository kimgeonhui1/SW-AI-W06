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
    "Team 4",
    /* First member's full name */
    "Kim geonhui",
    /* First member's email address */
    "kimgunhee6@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) WSIZE or double word (8) DSIZE */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) // 힙 공간 최소 할당 단위(2^12이니 4096byte -> 4KB)

// 두 숫자 중 더 큰 숫자를 찾음
#define MAX(x,y)    ((x) > (y) ? (x) : (y))

// Header/Footer 저장용 블록의 크기와 할당 여부를 저자함
#define PACK(size, alloc)   ((size) | (alloc))

// GET 함수 -> p에서 4바이트를 읽어옴(header / footer를 가져옴)
#define GET(p)              (*(unsigned int *)(p))
// PUT 함수 -> p에서 4바이트를 읽어와서(header/ footer 를 읽어와서) 그 공간에 val을 넣어
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

// GET_SIZE -> 블록의 크기 가져옴
#define GET_SIZE(p)         (GET(p) & ~0x7)
// GET_ALLOC -> p블록이 할당중인지를 가져옴(할당중이면 1, 아니면 0)
#define GET_ALLOC(p)        (GET(p) & 0x1)

// HDRP -> header를 가져옴
#define HDRP(bp)            ((char *)(bp) - WSIZE)
// FTRP -> footer를 가져옴
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// NEXT_BLKP -> 다음 블록(의 bp)을 가리킴
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
// PREV_BLKP -> 전 블록(의 bp)을 가리킴
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 입력받은 size를 8의 배수로 올림(블록의 크기가 8의 배수여야 하기에)
// 예: ALIGN(1) -> 8, ALIGN(7) -> 8, ALIGN(9) -> 16
// 주소나 블록 크기를 8바이트 경계(Alignment)에 딱 맞추기 위해 사용함.#define ALIGN(size) (((size) + (DSIZE - 1)) & ~0x7)
#define ALIGN(size) (((size) + (DSIZE - 1)) & ~0x7)

// 헤더의 크기(64비트 컴퓨터면 8byte, 32비트 컴퓨터면 4byte)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
void *mm_realloc(void *ptr, size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *imp_realloc(void *ptr, size_t size);


// bp
static char *heap_listp = 0;
// Next Fit을 위한 변수
static char *last_bp = 0;

/*
 * mm_init - initialize the malloc package.
 */
// 초기 셋팅(Prologue header/footer, Epilogue header 등 ..) 함수 mm_init
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) return -1;

    PUT(heap_listp , 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // Prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1)); // Epilogue header

    // Heap의 시작점을 가리키던 heap_listp를 8을 더하여 (Padding 4byte, Header 4byte)
    // bp(heap_listp)를 Prologue header의 바로 뒤로 이동시킴
    heap_listp += (2 * WSIZE);
    last_bp = heap_listp; 

    // 힙을 늘릴 수 없으면 return -1(에러 발생)
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 인자로 받은 크기가 홀수면 1을 더해서 word만큼(4만큼) 곱합. 짝수면 그냥 word만큼(4만큼)곱합
    // 왜 ? 8의 배수여야 하기에 ?
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // 힙 공간을 늘릴 수 없으면(size가 0 미만이거나, heap이 size만큼 늘릴 수 없으면) NULL 반환
    // 늘릴 수 있으면 그냥 늘리기(빈 블록 생성)
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;
    
    // 빈 블록에서 header와 footer 정의(아직 할당 안 했기에 할당중이 아님)
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // Epilogue header 최신화 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    // 병합(앞/뒤에 있는 빈 블록들과 합체) 작업 후 bp 리턴
    return coalesce(bp);

}

void *mm_malloc(size_t size)
{
    size_t asize; // 필요한 블록의 크기(header, footer, padding(옵션)을 포함)(8의 배수로 올림)
    size_t extendsize; // 필요한 블록의 크기 만큼의 크기의 빈 공간(블록)이 없을 때 힙 공간을 늘릴 크기
    char *bp; // bp

    // 할당할 공간의 크기가 0이라면 NULL 반환(오류)
    if(size == 0) return NULL;

    // 할당할 공간의 크기를 8의 배수로 올림(크기 + DSIZE(header, footer)한 거를 8의 배수로 올림)
    asize = ALIGN(size + DSIZE);

    // 방금 계산한 크기를 담을 수 있는 크기의 빈 블록이 있으면 거기에 할당하고
    // 그 블록의 시작점(header 직후)으로 bp 최신화
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // heap에 내가 할당하고 싶은 크기의 빈 블록이 없을 경우
    // 4096(4kb)와 내가 할당하고 싶은 크기 중 큰 크기로 heap을 늘림(늘리는 최소 단위가 4kb이기에)
    extendsize = MAX(asize, CHUNKSIZE);
    // 할당하고 싶은 만큼의 크기의 빈 블록만큼 heap을 늘려서 공간을 만듦(공간 할당 불가한 경우엔 NULL 반환)
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;

    // heap을 늘린 공간(블록)에 할당
    place(bp, asize);
    // bp 반환
    return bp;

    /*
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */
}

static void *find_fit(size_t asize){
    //first fit / next fit / best fit 방법으로 할당시킬 블록을 선택
    // first fit
    // char *bp;
    // // 블록들을 돌면서 할당중이지 않고, 빈 블록의 크기가 할당에 필요한 크기보다 같거나 크다면 해당 블록의 주소 반환
    // for(bp = heap_listp; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)){

    //     if((GET_ALLOC(HDRP(bp)) == 0) && (asize <= GET_SIZE(HDRP(bp)))) return bp;
    
    // }

    // next fit
    char *bp = last_bp;
    // 1. 마지막으로 할당했던 위치부터 끝까지 쭉 찾기
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp; // 찾으면 그 위치 기억!
            return bp;
        }
    }

    // 2. 끝까지 갔는데 없으면? 힙의 맨 앞부터 아까 출발했던 곳까지만 다시 찾기
    for (bp = heap_listp; bp < last_bp; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp; // 찾으면 그 위치 기억!
            return bp;
        }
    }
    // best fit

    // 찾지 못했을 때 (할당시켜야 할 만큼의 블록이 없을 때)
    return NULL;
}

static void place(void *bp, size_t asize){
    // 할당시킨 후 남은 블록의 크기가 16바이트 이상이면 빈 블록으로 만듦.
    // 할당 후 남은 블록의 크기가 16바이트 미만이면 전체를 다 할당시켜줌
    
    // 빈 블록의 크기
    size_t size = GET_SIZE(HDRP(bp)) ;
    // 할당하고 남은 크기
    size_t size_left = size - asize;

    // 할당 후 남은 크기가 16바이트 이상일 때
    if (size_left >= 2 * DSIZE){
        // 할당한 블록의 Header/Footer 정의
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        // 남은 칸으로 새 블록 생성 후 Header/Footer 정의
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(size_left, 0)); 
        PUT(FTRP(bp), PACK(size_left, 0)); 
    }
    // 할당 후 남은 크기가 16바이트 미만일 때
    else{  
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }


}


/*
 * mm_free - Freeing a block does nothing.
 */
// free해주는 함수 mm_free
void mm_free(void *bp)
{
    // free하는 블록의 크기를 가져옴
    size_t size = GET_SIZE(HDRP(bp)); 

    // header와 footer 최신화
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 앞/뒤 블록과 병합하는 coalesce 함수
static void *coalesce(void *bp){

    size_t prev_alloc  = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc  = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1 : 이전 블록과 다음 블록 모두 할당중일 때(병합할 게 없을 때)
    if(prev_alloc && next_alloc) {
        
        return bp;
    }
    // Case 2 : 이전 블록이 할당 중이고(병합 불가), 다음 블록이 비어 있을 때(병합 가능)
    else if(prev_alloc && !next_alloc){
        // 다음 블록의 크기와 내 블록의 크기를 더함
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // header, footer 최신화
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // Case 3 : 이전 블록이 비어 있고(병합 가능), 다음 블록이 할당중일 때(병합 불가)    
    else if(!prev_alloc && next_alloc){
        // 다음 블록의 크기와 내 블록의 크기를 더함
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        // header, footer 최신화
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // bp 최신화
        bp = PREV_BLKP(bp);
    }

    // Case 4 : 이전 블록, 다음 블록 모두 비어 있을 경우(병합이 다 가능한 경우)
    else{
        // 다음 블록의 크기와 내 블록의 크기를 더함
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        // header, footer 최신화
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        // bp 최신화
        bp = PREV_BLKP(bp);
    }

    if ((last_bp > (char *)bp) && (last_bp < NEXT_BLKP(bp))) {
        last_bp = bp; // 합쳐진 거대한 블록의 시작점으로 last_bp 당겨주기
    }


    // 블록의 시작점(bp) return
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 처음에는 조금만 필요한 것 같아 메모리를 조금만 할당했는데
// 나중가서 보니 메모리가 더 필요해서 realloc으로 블록의 크기를 늘려주는 작업
void *mm_realloc(void *ptr, size_t size)
{
    return imp_realloc(ptr, size);
}
// 암묵적 가용 리스트 방법
static void *imp_realloc(void *ptr, size_t size){
    void *oldptr;
    void *newptr;
    size_t asize;
    size_t old_size;
    size_t copySize;
    size_t prev_alloc, prev_size, next_alloc, next_size, total_size;


    last_bp = heap_listp;

    oldptr = ptr;
    old_size = GET_SIZE(HDRP(oldptr));
    
    copySize = old_size - DSIZE;
    if (size < copySize) copySize = size;

    asize = ALIGN(size + DSIZE);

    // 이미 충분한 경우
    if (asize <= old_size) return oldptr;

    // 주변 블록 상태
    prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(oldptr)));
    prev_size  = GET_SIZE(FTRP(PREV_BLKP(oldptr)));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));
    next_size  = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));

    // Case 1 : 이전 블록과 병합
    if (!prev_alloc && next_alloc && (old_size + prev_size >= asize)) {
        total_size = old_size + prev_size;
        newptr = PREV_BLKP(oldptr);

        memmove(newptr, oldptr, copySize);
        
        PUT(HDRP(newptr), PACK(total_size, 1));
        PUT(FTRP(newptr), PACK(total_size, 1));

        // place(newptr, asize);

        return newptr;
    }

    // Case 2 : 다음 블록과 병합
    if (prev_alloc && !next_alloc && (old_size + next_size >= asize)) {
        total_size = old_size + next_size;
        
        PUT(HDRP(oldptr), PACK(total_size, 1));
        PUT(FTRP(oldptr), PACK(total_size, 1)); 
    
        // place(oldptr, asize);

        return oldptr;  
    }

    // Case 3 : 앞/뒤 블록과 모두 병합
    if (!prev_alloc && !next_alloc && (old_size + next_size + prev_size >= asize)) {
        total_size = old_size + next_size + prev_size;
        newptr = PREV_BLKP(oldptr);

        memmove(newptr, oldptr, copySize);

        PUT(HDRP(newptr), PACK(total_size, 1));
        PUT(FTRP(newptr), PACK(total_size, 1)); 
        
        // place(newptr, asize);
        
        return newptr;  
    }

    // Case 4 : 기존 방식 (새로 할당)
    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    // place(newptr, asize);
    
    return newptr;
}
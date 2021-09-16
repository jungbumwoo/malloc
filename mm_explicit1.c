/*
2020 - SW Jungle
malloc lab explicit method
mail = chotjd329@gmail.com
blog = https://velog.io/@chosh
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
  * https://github.com/Tongky-HGU/InTheJungle/blob/master/JG_W5%20malloc/mm_explicit.c
  ********************************************************/
team_t team = {
    /* Team name */
    "team_jungle",
    /* First member's full name */
    "JB",
    /* First member's email address */
    "secret@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Third member's full name (leave blank if none) */
};

/*------------------------------------------------------------------------------------------------------------------------------------------------------*/

#define WSIZE 4             // [bytes] word, header, footer size
#define DSIZE 8             // [bytes] double, word, size
#define CHUNKSIZE (1 << 12) // [bytes] extend heap by this amount 하나의 페이지는 4[kb]

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // max 값 반환

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // size 뒤의 000 공간에 allocation 여부를 붙여준다.

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              // 주소값에서 값을 역참조해옴       /* 그럼 p는 이중포인터인가..? 값이 주소값인데 그 값에 들어가면 포인터가 또?*/
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 p가 가리키는 곳에 val 을 넣어줌

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 블록 사이즈를 읽어옴
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 여부를 읽어옴

/*
*    hdr    bp                          ftr 
* +------+------+------+------+------+-------+
* | 24/0 | NULL | NULL | NULL | NULL | 24/0  |
* +------+------+------+------+------+-------+
*           
*/

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 헤더의 주소값을 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터의 주소값을 반환, 헤더에서 사이즈를 안 다음, double word를 빼줌

/* Given block ptr bp, compute adress of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 주소값을 반환
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 주소값을 반환

/* for explict malloc */
#define GET_PTR(p) ((char *)*(unsigned int *)(p))      // GET과 동일하지만 엄격하게 형 제한 (주소값을 받아옴)
#define PUT_PTR(p) (*(unsigned int *)(p) = (int)(val)) // PUT과 동일하지만 엄격하게 형 제한

#define NEXT_FREE_BLKP(bp) (GET_P((char *)(bp) + WSIZE)) // 오잉1
#define PREV_FREE_BLKP(bp) (GET_P((char *)(bp)))         // 오잉2

#define CHANGE_PREV(bp, val) (PUT_P(PREVRP(bp), val)) //블록의 PREV word 에 주소값 val을 넣어줌
#define CHANGE_NEXT(bp, val) (PUT_P(NEXTRP(bp), val)) // 블록의 NEXT word에 주소값 val을 넣어줌

/* functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* for explict malloc func */
static void cut_link(void *bp);
static void push_first(void *bp);

static char *heap_listp;

int mm_init(void) // 메모리 처음 만들기
{
    /*
     *  pdding   hdr    prev   next    ftr  epilogue
     * +------+------+------+------+------+-------+
     * |  0   | 16/1 | NULL | NULL | 16/1 |  0/1  |
     * +------+------+------+------+------+-------+
     *                                              왜 이거 1씩 차 있고 할당되었다고 해주는거지..
     */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), NULL);
    PUT(heap_listp + (3 * WSIZE), NULL);
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // chunk size 확인 (받을 수 있는 사이즈인지)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size) // 메모리할당
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{ // 들어갈 자리를 찾는 함수 first fit
    void *bp;

    for (bp = PREV_FREE_BLKP(heap_listp); bp != (char *)NULL; bp = PREV_FREE_BLKP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{ // free 블록에 넣어주는 함수
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) // 자리가 남아서 SPLIT
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        cut_link(bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        push_first(bp);
    }
    else
    {
        cut_link(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void mm_free(void *bp) //블록 free시키는 함수 ---------------------------------------------------------------
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void cut_link(void *bp)
{ //블록의 연결된 링크를 끊어버리는 함수
    if (PREV_FREE_BLKP(bp) != (char *)NULL)
    {
        CHANGE_NEXT(PREV_FREE_BLKP(bp), NEXT_BLKP(bp));
    }
    if (NEXT_FREE_BLKP(bp) != (char *)NULL)
    {
        CHANGE_PREV(NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp));
    }
}

static void push_first(void *bp)
{ // free된 블록을 맨앞으로 보내는 함수 -------------------------------------------------
    // root의 이전은 나(bp)
    if (PREV_FREE_BLKP(heap_listp) != (char *)NULL)
    {
        CHANGE_NEXT(PREV_FREE_BLKP(heap_listp), bp);
    }
    PUT_P(PREVRP(bp), PREV_FREE_BLKP(heap_listp));
}

static void *coalesce(void *bp) // 연속된 free 처리--------------------------------------------------------------------
{
}

void *mm_realloc(void *bp, size_t size) // reallocation--------------------------------------------------------------------
{
}
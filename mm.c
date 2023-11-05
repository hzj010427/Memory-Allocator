/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * allocated block (minimum block size is 32 bytes):
 * header: 8 bytes
 * payload: at least 24 bytes
 * ----------------------------------------
 * | header  |          payload           |
 * ----------------------------------------
 *
 * free block (minimum block size is 32 bytes):
 * header: 8 bytes
 * prev: 8 bytes
 * next: 8 bytes
 * footer: 8 bytes
 * ----------------------------------------
 * | header | prev | next |      | footer |
 * ----------------------------------------
 *
 * allocated mini block (minimum block size is 16 bytes):
 * header: 8 bytes
 * payload: at least 8 bytes
 * ----------------------------------------
 * | header  |          payload           |
 * ----------------------------------------
 *
 * free mini block (minimum block size is 16 bytes):
 * header: 8 bytes
 * next: 8 bytes
 * ----------------------------------------
 * |       header       |       next      |
 * ----------------------------------------
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Zijie Huang <zijieh@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */
#define SEG_LIST_NUM 15
#define SEARCH_LIMIT 10
#define CLOSE_ENOUGH 46

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */
static const int s_list_mini = 32; // used for mini block
static const int s_list_1 = 64;
static const int s_list_2 = 128;
static const int s_list_3 = 256;
static const int s_list_4 = 512;
static const int s_list_5 = 1024;
static const int s_list_6 = 2048;
static const int s_list_7 = 4096;
static const int s_list_8 = 8192;
static const int s_list_9 = 16384;
static const int s_list_10 = 32768;
static const int s_list_11 = 65536;
static const int s_list_12 = 131072;
static const int s_list_13 = 262144;

typedef uint64_t word_t; // 8 bytes

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t); // 8 bytes

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize; // 16 bytes

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize; // 16 bytes

/** @brief The size of the initial heap in bytes is 2KB */
static const size_t chunksize = (1L << 11);

/** @brief This mask use LSB to indicate whether the block is allocated or not.
 */
static const word_t alloc_mask = (word_t)0x1;

/** @brief This mask is used to get the previous allocation status of the block.
 */
static const word_t prev_alloc_mask = (word_t)0x2;

/** @breif This mask is used to check the previous block is mini block or not.
 */
static const word_t prev_mini_mask = (word_t)0x4;

/** @brief This mask is used to get the allocation status of the block. */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A union representing the possible contents of the payload area.
     *
     * The union lets us access the payload in multiple ways and they all start
     * at the same place. 'block->payload' is a size-0 array holding only the
     * payload, 'block->minifree.next_mini' is the next pointer of the mini free
     * block, 'block->free.prev' and 'block->free.next' are the prev and next
     * pointers of the free block,
     *
     * mini free block: next pointer
     * free block: prev and next pointers
     * allocated block: payload
     */
    union {
        struct {
            /** @brief A pointer to the next free mini block. */
            struct block *next_mini;
        } mini_free;

        struct {
            /** @brief A pointer to the previous free block. */
            struct block *prev;

            /** @brief A pointer to the next free block. */
            struct block *next;
        } free;

        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief The pointer of the head of the segregated free list. */
static block_t *segregated_free_list[SEG_LIST_NUM];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] prev_mini True if the previous block is mini block
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }

    if (prev_alloc) {
        word |= prev_alloc_mask;
    }

    if (prev_mini) {
        word |= prev_mini_mask;
    }

    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Given a block pointer, returns a pointer to the end of the payload.
 * @param[in] block A pointer to the block's header
 * @return A pointer to the end of the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_end(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - wsize);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block A pointer to the block's header
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word The word to examine
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] word The word to examine
 * @return The allocation status correpsonding to the word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & prev_alloc_mask);
}

/**
 * @brief Returns the status of the previous block is mini block or not.
 *
 * This is based on the third lowest bit of the header value.
 *
 * @param[in] word The word to examine
 * @return The status of the previous block is mini block or not
 */
static bool extract_prev_mini(word_t word) {
    return (bool)(word & prev_mini_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block A pointer to the block's header
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the allocation status of the previous block, based on the
 *       current block's header.
 * @param[in] block A pointer to the block's header
 * @return The allocation status of the previous block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns the status of the previous block is mini block or not, based
 * on the current block's header.
 * @param[in] block A pointer to the block's header
 * @return The status of the previous block is mini block or not
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 * @param[in] prev_alloc The allocation status of the previous block
 * @param[in] prev_mini The status of the previous block is mini block or not
 */
static void write_epilogue(block_t *block, bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true, prev_alloc, prev_mini);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes the both header and footer for normal free block.
 *
 * This function only writes the header for normal allocated block, mini
 * allocated, mini free block.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] prev_alloc The allocation status of the previous block
 * @param[in] prev_mini The status of the previous block is mini block or not
 * @pre The block is not NULL, epilogue, or prologue.
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc, prev_alloc, prev_mini);

    if (!alloc && size > min_block_size) { // normal free block
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, prev_mini);
    } else { // normal allocated block, mini allocated block, mini free block
        header_to_end(block);
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the header of the given block.
 * @param[in] block A block in the heap
 * @return The location of the block's header
 */
static word_t *find_header(block_t *block) {
    return &(block->header);
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    bool prev_mini = get_prev_mini(block);

    if (prev_mini) { // mini block decrement 16 bytes
        word_t *headp = find_header(block);

        return (block_t *)((char *)headp - min_block_size);
    } else {
        word_t *footerp = find_prev_footer(block);

        // Return NULL if called on first block in the heap
        if (extract_size(*footerp) == 0) {
            return NULL;
        }

        return footer_to_header(footerp);
    }
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief Find the index of the free list that the given block should be
 * inserted to.
 *
 * Use the binary search to find the index.
 *
 * @param[in] size The size of the block
 */
static int get_list_index(size_t size) {
    if (size <= s_list_7) { // seg_list[0] ~ seg_list[7]
        if (size <= s_list_3) {
            if (size <= s_list_1) {
                if (size < s_list_mini) {
                    return 0;
                } else {
                    return 1;
                }
            } else {
                if (size <= s_list_2) {
                    return 2;
                } else {
                    return 3;
                }
            }
        } else {
            if (size <= s_list_5) {
                if (size <= s_list_4) {
                    return 4;
                } else {
                    return 5;
                }
            } else {
                if (size <= s_list_6) {
                    return 6;
                } else {
                    return 7;
                }
            }
        }
    } else { // seg_list[8] ~ seg_list[14]
        if (size <= s_list_11) {
            if (size <= s_list_9) {
                if (size <= s_list_8) {
                    return 8;
                } else {
                    return 9;
                }
            } else {
                if (size <= s_list_10) {
                    return 10;
                } else {
                    return 11;
                }
            }
        } else {
            if (size <= s_list_13) {
                if (size <= s_list_12) {
                    return 12;
                } else {
                    return 13;
                }
            } else {
                return 14;
            }
        }
    }
}

/**
 * @brief Insert the given block to the free list.
 * @param[in] block The block to be inserted
 * @pre The input block should be free, valid and size is greater than 16 bytes.
 */
static void insert_to_free_list(block_t *block) {
    if (block == NULL) {
        dbg_printf("insert_to_free_list: block is NULL\n");
        return;
    }

    dbg_requires(!get_alloc(block));

    int seg = get_list_index(get_size(block));

    block_t *head = segregated_free_list[seg];

    if (head == NULL) {                    // empty free list
        segregated_free_list[seg] = block; // update the head globally
        block->free.prev = NULL;
        block->free.next = NULL;
    } else {
        block->free.prev = NULL;
        block->free.next = head;
        head->free.prev = block;
        segregated_free_list[seg] = block;
    }
}

/**
 * @brief Delete the given block from the free list.
 * @param[in] block The block to be deleted
 * @pre The input block should be free, valid and size is greater than 16 bytes.
 */
static void delete_from_free_list(block_t *block) {
    if (block == NULL) {
        dbg_printf("delete_from_free_list: block is NULL\n");
        return;
    }

    dbg_requires(!get_alloc(block));

    int seg = get_list_index(get_size(block));

    block_t *head = segregated_free_list[seg];

    if (head == block) { // delete the head
        block_t *next = block->free.next;
        segregated_free_list[seg] = next; // update the head globally
        if (next != NULL) {
            next->free.prev = NULL;
        }
    } else {
        block_t *prev = block->free.prev;
        block_t *next = block->free.next;
        prev->free.next = next;
        if (next != NULL) {
            next->free.prev = prev;
        }
    }
}

/**
 * @brief Insert the given block to the mini free list.
 * @param[in] block The block to be inserted
 * @pre The input block should be free, valid and size is 16 bytes.
 */
static void insert_to_mini_free_list(block_t *block) {
    if (block == NULL) {
        dbg_printf("insert_to_free_list: block is NULL\n");
        return;
    }

    dbg_requires(!get_alloc(block));

    block_t *head =
        segregated_free_list[0]; // the first free list is for mini block

    if (head == NULL) {                  // empty free list
        segregated_free_list[0] = block; // update the head globally
        block->mini_free.next_mini = NULL;
    } else {
        block->mini_free.next_mini = head;
        segregated_free_list[0] = block;
    }
}

/**
 * @brief Delete the given block from the mini free list.
 * @param[in] block The block to be deleted
 * @pre The input block should be free, valid and size is 16 bytes.
 */
static void delete_from_mini_free_list(block_t *block) {
    if (block == NULL) {
        dbg_printf("insert_to_free_list: block is NULL\n");
        return;
    }

    dbg_requires(!get_alloc(block));

    block_t *head =
        segregated_free_list[0]; // the first free list is for mini block

    if (head == NULL) {
        dbg_printf("delete_from_mini_free_list: head is NULL\n");
        return;
    }

    if (head == block) { // delete the head
        block_t *next = block->mini_free.next_mini;
        segregated_free_list[0] = next;
    } else {
        block_t *prev = head;
        block_t *next = head->mini_free.next_mini;

        while (next != block) {
            prev = next;
            next = next->mini_free.next_mini;
        }

        prev->mini_free.next_mini = next->mini_free.next_mini;
    }
}

/**
 * @brief Simply update the block's header
 * @param[in] block The block to be updated
 * @param[in] size The new size of the block
 * @param[in] alloc The new allocation status of the block
 * @param[in] prev_alloc The allocation status of the previous block
 * @param[in] prev_mini The status of the previous block is mini block or not
 */
static void update_block(block_t *block, size_t size, bool alloc,
                         bool prev_alloc, bool prev_mini) {
    block->header = pack(size, alloc, prev_alloc, prev_mini);
}

/**
 * @brief Determine whether the free block should be inserted to mini free list
 * or normal free list.
 * @param[in] block The block to be inserted
 */
static void insert_normal_or_mini(block_t *block) {
    size_t size = get_size(block);

    if (size == min_block_size) { // mini block
        insert_to_mini_free_list(block);
    } else { // normal block
        insert_to_free_list(block);
    }
}

/**
 * @brief Determine whether the free block should be deleted from mini free list
 * or normal free list.
 * @param[in] block The block to be deleted
 */
static void delete_normal_or_mini(block_t *block) {
    size_t size = get_size(block);

    if (size == min_block_size) { // mini block
        delete_from_mini_free_list(block);
    } else { // normal block
        delete_from_free_list(block);
    }
}

/**
 * @brief Coalesces the current block with the previous or next blocks by
 * linking them together.
 *
 * This function assumes that the current block is free.
 *
 * The input block should be free.
 *
 * @param[in] block The block to be coalesced
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(!get_alloc(block));

    block_t *block_next = find_next(block);
    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);

    // case1: prev and next are allocated
    if (prev_alloc && next_alloc) {
        insert_normal_or_mini(block);
        return block; // do nothing
    }

    // case2: prev is free and next is allocated
    else if (!prev_alloc && next_alloc) {
        block_t *block_prev = find_prev(block);
        size_t block_size = get_size(block);
        size_t block_prev_size = get_size(block_prev);
        bool prev_prev_alloc = get_prev_alloc(block_prev);
        bool prev_prev_mini = get_prev_mini(block_prev);

        delete_normal_or_mini(block_prev);

        block = block_prev; // update the block pointer

        write_block(block, block_prev_size + block_size, false, prev_prev_alloc,
                    prev_prev_mini);
        insert_normal_or_mini(block);
    }

    // case3: prev is allocated and next is free
    else if (prev_alloc && !next_alloc) {
        size_t block_size = get_size(block);
        size_t block_next_size = get_size(block_next);
        bool prev_alloc = get_prev_alloc(block);
        bool prev_mini = get_prev_mini(block);

        delete_normal_or_mini(block_next);

        write_block(block, block_size + block_next_size, false, prev_alloc,
                    prev_mini);
        insert_normal_or_mini(block);
    }

    // case4: prev and next are free
    else {
        block_t *block_prev = find_prev(block);
        size_t block_size = get_size(block);
        size_t block_prev_size = get_size(block_prev);
        size_t block_next_size = get_size(block_next);
        bool prev_prev_alloc = get_prev_alloc(block_prev);
        bool prev_prev_mini = get_prev_mini(block_prev);

        delete_normal_or_mini(block_next);
        block = block_prev; // update the block pointer
        delete_normal_or_mini(block);

        write_block(block, block_prev_size + block_size + block_next_size,
                    false, prev_prev_alloc, prev_prev_mini);
        insert_normal_or_mini(block);
    }

    // update the next block's prev_mini
    block_next = find_next(block);
    update_block(
        block_next, get_size(block_next), get_alloc(block_next), false,
        false); // after coalescing, the size of the block at least 32 bytes.

    return block;
}

/**
 * @brief Extends the heap by the requested number of bytes.
 * @param[in] size The number of bytes to extend
 * @return Nullptr on error and the block pointer that points to the new block
 * on success
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    /*
     * At the beginning, the bp is point to the start of the payload of the new
     * block.
     *
     * We write the new block starting one word BEFORE bp,
     * because we need to write the header of the new block.
     *
     * Then we find one word before bp, which is the header of the new block.
     *
     * We write the new block with the same size that we originally requested,
     * because we need to use that amount of memory to store the header, payload
     * and footer of the new block.
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp); // block is old epilogue now
    bool prev_alloc = get_prev_alloc(block);
    bool prev_mini = get_prev_mini(block);
    write_block(block, size, false, prev_alloc, prev_mini);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    prev_mini = true ? size == min_block_size : false;
    write_epilogue(block_next, false, prev_mini);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief Splits the given block into two blocks: one with the requested size
 * and one free block.
 *
 * The size of the free block = block_size - asize.
 *
 * The size of the allocated block = asize.
 *
 * The value of the asize at least equals to the minimum block size.
 *
 * @param[in] block The block to split
 * @param[in] asize The size to split the block by
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        bool prev_alloc = get_prev_alloc(block);
        bool prev_mini = get_prev_mini(block);
        write_block(block, asize, true, prev_alloc, prev_mini);

        block_t *block_next = find_next(block);
        prev_mini = true ? asize == min_block_size : false;
        write_block(block_next, block_size - asize, false, true, prev_mini);

        block_t *block_next_next = find_next(block_next);
        size_t block_next_next_size = get_size(block_next_next);
        bool block_next_next_alloc = get_alloc(block_next_next);
        prev_mini = true ? block_size - asize == min_block_size : false;

        update_block(block_next_next, block_next_next_size,
                     block_next_next_alloc, false, prev_mini);

        // Insert the new free block into the free list
        insert_normal_or_mini(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Find the best fit block in the free list.
 * @param[in] asize The size of requested memory
 * @return The block pointer that points to the first fit block
 */

static block_t *find_fit(size_t asize) {
    block_t *block;
    block_t *best_fit_block = NULL;
    size_t block_size = asize;
    size_t min_diff = SIZE_MAX;
    int seg = get_list_index(block_size);
    int cont = 0;

    if (seg == 0) {
        block = segregated_free_list[0];
        if (block != NULL) {
            return block;
        }
    }

    for (int i = seg; i < SEG_LIST_NUM; i++) {
        block = segregated_free_list[i];
        while (block != NULL) {
            if (get_size(block) >= block_size) {
                size_t diff = get_size(block) - block_size;
                if (diff < min_diff) {
                    min_diff = diff;
                    best_fit_block = block;
                }
                if (min_diff <=
                    CLOSE_ENOUGH) { // If the fit is close enough, break early
                    return best_fit_block;
                }
            }

            if (cont >
                SEARCH_LIMIT) { // avoid searching too many blocks in one list
                cont = 0;
                break;
            }

            block = block->free.next;
            cont++;
        }
    }

    return best_fit_block;
}

/* static block_t *find_fit(size_t asize) { // uncomment this function to use
first fit (high throughput) block_t *block; size_t block_size = asize; int seg =
get_list_index(block_size); int cont = 0;

    if (seg == 0) { // the first free list is for mini block
        block = segregated_free_list[0];
        if (block != NULL) {
            return block;
        }
    }

    // all the size of the blocks greater than or equal to rq_size are fit
    for (int i = seg; i < SEG_LIST_NUM; i++) {
        block = segregated_free_list[i];
        while (block != NULL) {
            if (get_size(block) >= block_size) {
                return block;
            }

            if (cont >
                SEARCH_LIMIT) { // avoid searching too many blocks in one list
                cont = 0;
                break;
            }

            block = block->free.next;
            cont++;
        }
    }

    return NULL; // no fit found
} */

/*
 *****************************************************************************
 * The functions below are heap consistency checker routines.                *
 * They check the heap and free list for consistency.                        *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        START HEAP CHECKER HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Check if the prologue block is marked as allocated or has non-zero
 * size.
 * @param[in] prologue The prologue block
 * @param[in] line The line number of the caller
 * @return true if the prologue block is valid, false otherwise
 */
static bool check_prologue(word_t *prologue, int line) {
    if (extract_size(*prologue) != 0 || !extract_alloc(*prologue)) {
        dbg_printf("Prologue block is not marked as allocated or has non-zero "
                   "size (called at line %d)\n",
                   line);
        return false;
    }

    return true;
}

/**
 * @brief Check if the epilogue block is marked as allocated or has non-zero
 * size.
 * @param[in] epilogue The epilogue block
 * @param[in] line The line number of the caller
 * @return true if the epilogue block is valid, false otherwise
 */
static bool check_epilogue(block_t *epilogue, int line) {
    while (get_size(epilogue) != 0) {
        epilogue = find_next(epilogue);
    }

    if (get_size(epilogue) != 0 || !get_alloc(epilogue)) {
        dbg_printf("Epilogue block is not marked as allocated or has non-zero "
                   "size (called at line %d)\n",
                   line);
        return false;
    }

    return true;
}

/**
 * @brief Check if the block lies within heap.
 * @param[in] block The block to be checked
 * @param[in] line The line number of the caller
 * @return true if the block lies within heap, false otherwise
 */
static bool check_lie_within_heap(block_t *block, int line) {
    while (get_size(block) > 0) {
        if ((char *)block < (char *)mem_heap_lo() ||
            (char *)block > (char *)mem_heap_hi()) {
            dbg_printf("Block outside heap bounds (called at line %d)\n", line);
            return false;
        }
        block = find_next(block);
    }

    return true;
}

/**
 * @brief Check if the block is aligned to double word boundary.
 * @param[in] block The block to be checked
 * @param[in] line The line number of the caller
 * @return true if the block is aligned to double word boundary, false
 * otherwise
 */
static bool check_block_alignment(block_t *block, int line) {
    while (get_size(block) > 0) {
        if (get_size(block) % dsize != 0) {
            dbg_printf("Block not aligned to double word boundary (called at "
                       "line %d)\n",
                       line);
            return false;
        }
        block = find_next(block);
    }

    return true;
}

/**
 * @brief Check if there are two consecutive free blocks.
 * @param[in] prev The previous block
 * @param[in] curr The current block
 * @param[in] line The line number of the caller
 * @return true if there are no two consecutive free blocks, false otherwise
 */
static bool check_contiguous_free_blocks(block_t *prev, block_t *curr,
                                         int line) {
    while (get_size(curr) > 0) {
        if (!get_alloc(curr) && !get_alloc(prev)) {
            dbg_printf("Two consecutive free blocks (called at line %d)\n",
                       line);
            return false;
        }
        prev = curr;
        curr = find_next(curr);
    }

    return true;
}

/**
 * @brief Check if the header and footer size match for the free block.
 * @param[in] block The block to be checked
 * @param[in] line The line number of the caller
 * @return true if the header and footer size match, false otherwise
 */
static bool check_header_footer_match(block_t *block, int line) {
    while (get_size(block) > min_block_size && !get_alloc(block)) {
        word_t *footerp = header_to_footer(block);

        if (get_size(block) != extract_size(*footerp)) {
            dbg_printf(
                "Header and footer size do not match (called at line %d)\n",
                line);
            return false;
        }

        block = find_next(block);
    }

    return true;
}

/**
 * @brief Check if the block meets minimum block size.
 * @param[in] block The block to be checked
 * @param[in] line The line number of the caller
 * @return true if the block meets minimum block size, false otherwise
 */
static bool check_minimum_block_size(block_t *block, int line) {
    while (get_size(block) > 0) {
        if (get_size(block) < min_block_size) {
            dbg_printf(
                "Block does not meet minimum block size (called at line %d)\n",
                line);
            return false;
        }

        block = find_next(block);
    }

    return true;
}

/**
 * @brief Check if there is a cycle in the free list.
 * @param[in] list The free list to be checked
 * @param[in] line The line number of the caller
 * @return true if there is no cycle in the free list, false otherwise
 */
static bool check_cycle(block_t *list, int line) {
    block_t *hare = list;
    block_t *tortoise = list;

    while (hare != NULL && hare->free.next != NULL) {
        hare = hare->free.next->free.next;
        tortoise = tortoise->free.next;

        if (hare == tortoise) {
            dbg_printf("Cycle in the free list (called at line %d)\n", line);
            return false;
        }
    }

    return true;
}

/**
 * @brief Check if there is an allocated block in the free list.
 * @param[in] list The free list to be checked
 * @param[in] line The line number of the caller
 * @return true if there is no allocated block in the free list, false
 * otherwise
 */
static bool check_alloc(block_t *list, int line) {
    block_t *block = list;

    while (block != NULL) {
        if (get_alloc(block)) {
            dbg_printf("Allocated block in the free list (called at line %d)\n",
                       line);
            return false;
        }

        block = block->free.next;
    }

    return true;
}

/**
 * @brief Check if all free list pointers are between mem_heap_lo() and
 * mem_heap_high().
 * @param[in] list The free list to be checked
 * @param[in] line The line number of the caller
 * @return true if all free list pointers are between mem_heap_lo() and
 * mem_heap_high(), false otherwise
 */
static bool check_bounds(block_t *list, int line) {
    block_t *block = list;

    while (block != NULL) {
        if ((char *)block < (char *)mem_heap_lo() ||
            (char *)block > (char *)mem_heap_hi()) {
            dbg_printf("Free list pointers are not between mem_heap_lo() and "
                       "mem_heap_high() (called at line %d)\n",
                       line);
            return false;
        }

        block = block->free.next;
    }

    return true;
}

/**
 * @brief Check if next/prev pointers in consecutive free blocks are consistent.
 * @param[in] list The free list to be checked
 * @param[in] line The line number of the caller
 * @return true if next/prev pointers in consecutive free blocks are consistent,
 * false otherwise
 */
static bool check_consecutive(block_t *list, int line) {
    block_t *block = list;

    while (block != NULL && block->free.next != NULL) {
        if (block->free.next->free.prev != block) {
            dbg_printf("Next/prev pointers in consecutive free blocks are not "
                       "consistent (called at line %d)\n",
                       line);
            return false;
        }

        block = block->free.next;
    }

    return true;
}

/**
 * @brief Check if all blocks in each list bucket fall within correct bucket
 * size range.
 * @param[in] list The free list to be checked
 * @param[in] line The line number of the caller
 * @return true if all blocks in each list bucket fall within correct bucket
 * size range, false otherwise
 */
static bool check_bucket(block_t *list, int line) {
    if (list == NULL) {
        return true;
    }

    block_t *block = list;
    int seg = get_list_index(get_size(block));

    while (block != NULL) {
        if (get_list_index(get_size(block)) != seg) {
            dbg_printf("Block does not fall within correct bucket size range "
                       "(called at line %d)\n",
                       line);
            return false;
        }

        block = block->free.next;
    }

    return true;
}

/*
 * ---------------------------------------------------------------------------
 *                        END HEAP CHECKER HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Check the heap for inconsistencies.
 * @param[in] line The line number of the caller
 * @return True if the heap is consistent, False otherwise
 */
bool mm_checkheap(int line) {
    word_t *prologue = (word_t *)heap_start - 1;
    block_t *epilogue = heap_start;
    block_t *block = heap_start;
    block_t *prev = heap_start;
    block_t *curr = find_next(prev);
    bool consistent = false;

    // Check for prologue blocks (8 bytes before heap_start)
    consistent = check_prologue(prologue, line);

    // Check for epilogue blocks
    consistent = check_epilogue(epilogue, line);

    // Check blocks lie within heap
    consistent = check_lie_within_heap(block, line);

    // Check for block alignment
    consistent = check_block_alignment(block, line);

    // Check header and footer match
    consistent = check_header_footer_match(block, line);

    // Check for minimum block size
    consistent = check_minimum_block_size(block, line);

    // Check for contiguous free blocks
    consistent = check_contiguous_free_blocks(prev, curr, line);

    for (int i = 1; i < SEG_LIST_NUM; i++) { // skip the mini free list
        // Check for cycle in the free list (segregated list & explicit list)
        consistent = check_cycle(segregated_free_list[i], line);

        // Check for allocated block in the free list (segregated list &
        // explicit list)
        consistent = check_alloc(segregated_free_list[i], line);

        // Check for all free list pointers are between mem_heap_lo() and
        // mem_heap_high() (segregated list & explicit list)
        consistent = check_bounds(segregated_free_list[i], line);

        // Check for next/prev pointers in consecutive free blocks are
        // consistent (segregated list & explicit list)
        consistent = check_consecutive(segregated_free_list[i], line);

        // All blocks in each list bucket fall within correct bucket size range
        // (segregated list)
        consistent = check_bucket(segregated_free_list[i], line);
    }

    return consistent;
}

/**
 * @brief initialize the heap by creating a prologue and epilogue block and
 * extending the heap with a free block of chunksize bytes.
 *
 * @return True if the heap is initialized successfully, False otherwise
 */
bool mm_init(void) {
    // Initialize segregated list
    for (int i = 0; i < SEG_LIST_NUM; i++) {
        segregated_free_list[i] = NULL;
    }

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief Allocate a block and make sure the block is aligned by rounding up the
 * requested size to the nearest multiple of 16.
 *
 * Reduce the external fragmentation by splitting the block if the block is too
 * large.
 *
 * @param[in] size The number of bytes to allocate
 * @return A pointer to the allocated block payload
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    if (size <= wsize) {
        asize = min_block_size;
    } else {
        asize = round_up(size + wsize, dsize);
    }

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);

        block = extend_heap(extendsize);

        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Delete the block from the free list
    delete_normal_or_mini(block);

    // Mark block as allocated
    size_t block_size = get_size(block);
    bool prev_alloc = get_prev_alloc(block);
    bool prev_mini = get_prev_mini(block);
    write_block(block, block_size, true, prev_alloc, prev_mini);

    // Update the next block's prev_alloc
    block_t *block_next = find_next(block);
    size_t block_next_size = get_size(block_next);
    bool block_next_alloc = get_alloc(block_next);
    bool block_next_prev_mini = true ? block_size == min_block_size : false;

    // update the next block
    update_block(block_next, block_next_size, block_next_alloc, true,
                 block_next_prev_mini);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief Free the block and coalesce the block with its neighbors.
 * @param[in] bp A pointer to the memory to be freed
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    bool prev_alloc = get_prev_alloc(block);
    bool prev_mini = get_prev_mini(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, prev_alloc, prev_mini);

    // Update the next block's prev_alloc and prev_mini
    block_t *block_next = find_next(block);
    size_t block_next_size = get_size(block_next);
    bool block_next_alloc = get_alloc(block_next);
    bool block_next_prev_mini = true ? size == min_block_size : false;

    // update the next block
    update_block(block_next, block_next_size, block_next_alloc, false,
                 block_next_prev_mini);

    // Try to coalesce the block with its neighbors
    coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief Reallocate the block with the requested size.
 * @param[in] ptr A pointer to the memory to be reallocated
 * @param[in] size The number of bytes to reallocate
 * @return A pointer to the reallocated memory
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief Allocate memory for an array of `nmemb` elements of `size` bytes each.
 *
 * The main difference between `calloc` and `malloc` is that the initialized
 * content in `calloc` is set to zero,
 *
 * while the content in `malloc` is undefined.
 *
 * @param[in] elements The number of elements to allocate
 * @param[in] size The size of each element
 * @return A pointer to the allocated memory
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */

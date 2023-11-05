/*
 * tracefile.h - Parse trace files for the CS:APP Malloc Lab Driver,
 * and manipulate data structures derived from those files.
 *
 * Copyright (c) 2022 Z. Weinberg.  Based on code by R. Bryant and
 * D. O'Hallaron.
 */

#ifndef MM_TRACEFILE_H_
#define MM_TRACEFILE_H_ 1

#include <stddef.h>

/** The 'weight' of a trace file.  Weight is a misnomer; it's actually a
 *  set of flags describing _which_ of various performance metrics should
 *  be measured for this trace.
 */
typedef enum weight_t {
    WNONE = 0,
    WUTIL = 1,
    WPERF = 2,
    WALL = WUTIL | WPERF,
} weight_t;

/** Opcode for a single trace operation, i.e. what will actually be done
 *  by this trace operation.
 */
typedef enum traceopcode_t {
    ALLOC,   /* 'a': call malloc */
    FREE,    /* 'f': call free */
    REALLOC, /* 'r': call realloc */
} traceopcode_t;

/** Description of a single trace operation (allocator request).  */
typedef struct traceop_t {
    traceopcode_t type : 8;   /* type of request (8 bits) */
    unsigned int lineno : 24; /* line number in trace file */
    unsigned int index;       /* block id, to use in realloc/free */
    size_t size;              /* byte size of alloc/realloc request */
} traceop_t;

/** Data structure corresponding to a complete trace file.  */
typedef struct trace_t {
    const char *filename;
    size_t data_bytes;    /* Peak number of data bytes allocated during trace */
    unsigned int num_ids; /* number of alloc/realloc ids */
    unsigned int num_ops; /* number of distinct requests */
    weight_t weight;      /* weight for this trace */
    traceop_t *ops;       /* array of requests */
    char **blocks;        /* array of ptrs returned by malloc/realloc... */
    size_t *block_sizes;  /* ... and a corresponding array of payload sizes */
    size_t *block_rand_base; /* index into random_data, if debug is on */
} trace_t;

/* These functions read, allocate, and free storage for traces */
extern trace_t *read_trace(const char *filename, unsigned int verbose);
extern void reinit_trace(trace_t *trace);
extern void free_trace(trace_t *trace);

#endif /* tracefile.h */

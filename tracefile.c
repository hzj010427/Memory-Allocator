/*
 * tracefile.c - Parse trace files for the CS:APP Malloc Lab Driver,
 * and manipulate data structures derived from those files.
 *
 * Copyright (c) 2022 Z. Weinberg.  Based on code by R. Bryant and
 * D. O'Hallaron.
 */

#define _GNU_SOURCE 1 // for getline

#include "tracefile.h"

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/** Map from trace file weight codes to Wxxx values.
 *  Quoting traces/README:
 *
 *     Weight is an integer interpeted as:
 *     0:  Ignore trace in scoring
 *     1:  Include with utilization & throughput
 *     2:  Utilization only
 *     3:  Throughput only
 */
#define N_WEIGHT_CODES 4
static const weight_t weight_codes[N_WEIGHT_CODES] = {
    /* 0 */ WNONE,
    /* 1 */ WALL,
    /* 2 */ WUTIL,
    /* 3 */ WPERF,
};

/* Temporarily duplicated from mdriver.c.  */
/*
 * app_error - Report an arbitrary application error
 */
static void __attribute__((format(printf, 1, 2), noreturn))
app_error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    putc('\n', stderr);
    exit(1);
}

/*
 * unix_error - Report a system error and its cause.
 */
static void __attribute__((format(printf, 1, 2), noreturn))
unix_error(const char *fmt, ...) {
    // Capture errno now, because vfprintf might clobber it.
    int err = errno;

    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);

    fprintf(stderr, ": %s\n", strerror(err));
    exit(1);
}

/** Get the next line, skipping blank lines.
 *  White space is trimmed from both ends of the line.
 *  If there is an I/O error during scanning, report it as a
 *  fatal error.
 *
 *  @param fp      FILE to read from.
 *  @param fname   Name of the file being read, for error reporting.
 *  @param[inout] pline
 *      Pointer to a char * pointing to storage space for the line to
 *      be read (same semantics as for getline(3))
 *
 *  @param[inout] plinesz
 *      Pointer to a size_t recording how much space is available at
 *      **pline (same semantics as for getline(3))
 *
 *  @param[inout] plineno
 *      Pointer to an unsigned int, the current line number.
 *
 *  @return True if a line has been read into **pline.
 *          False if EOF has been reached.
 */
static bool get_next_line(FILE *fp, const char *fname, char **pline,
                          size_t *plinesz, unsigned int *plineno) {
    char *line, *start, *end;

    // Read lines until we find one that isn't totally blank
    // (ignoring horizontal whitespace), or we hit end of file.
    do {
        if (getline(pline, plinesz, fp) <= 0) {
            goto eof_or_error;
        }
        *plineno += 1;

        start = line = *pline;
        while (*start == ' ' || *start == '\t') {
            start++;
        }
    } while (*start == '\n' || *start == '\r' || *start == '\0');

    // Found a non-blank line.
    // line points to the beginning of the buffer.
    // start points to the first non-whitespace character.

    end = start + strlen(start);
    assert(end[0] == '\0');
    while (end[-1] == '\r' || end[-1] == '\n' || end[-1] == '\t' ||
           end[-1] == ' ') {
        end--;
    }

    // end now points to the first character of trailing whitespace.
    // Chop off all the trailing whitespace...
    assert(end > start);
    end[0] = '\0';
    // ... and, if there was leading whitespace, erase it too.
    if (start > line) {
        memmove(line, start, (size_t)(end - start + 1));
    }

    // Caller can now rely on *pline being a non-empty string that
    // begins with a non-whitespace character and doesn't have any
    // trailing whitespace either.
    return true;

eof_or_error:
    // We come here if getline fails _or_ if it reports EOF.
    if (ferror(fp)) {
        unix_error("%s: read error", fname);
    }
    return false;
}

/** Get the next line of a trace file header.
 *  This is exactly the same as get_next_line except that
 *  EOF is also treated as a fatal error.
 *
 *  @param fp      FILE to read from.
 *  @param fname   Name of the file being read, for error reporting.
 *  @param[inout] pline
 *      Pointer to a char * pointing to storage space for the line to
 *      be read (same semantics as for getline(3))
 *
 *  @param[inout] plinesz
 *      Pointer to a size_t recording how much space is available at
 *      **pline (same semantics as for getline(3))
 *
 *  @param[inout] plineno
 *      Pointer to an unsigned int, the current line number.
 */
static void get_header_line(FILE *fp, const char *fname, char **pline,
                            size_t *plinesz, unsigned int *plineno) {
    if (!get_next_line(fp, fname, pline, plinesz, plineno)) {
        app_error("%s:%d: error: invalid trace: "
                  "unexpected end of file\n",
                  fname, *plineno);
    }
}

/** Parse a single nonnegative decimal number.
 *  The number must be the only thing in the input string, and it must
 *  be less than or equal to some specified limit.
 *
 *  On success, returns the number; on failure, reports a fatal error.
 *
 *  @param line     The text of the header line.
 *  @param max      The number must be less than or equal to this.
 *  @param fname Name of file being read (for error reporting)
 *  @param lineno   Current line number (for error reporting)
 *  @param what     What the number means (for error reporting).
 */
static unsigned long read_single_number(const char *line, unsigned long max,
                                        const char *fname, unsigned int lineno,
                                        const char *what) {
    errno = 0;
    char *endp;
    unsigned long val = strtoul(line, &endp, 10);

    if (endp == line) {
        app_error("%s:%u: error: invalid trace: "
                  "while reading %s, found a not-number",
                  fname, lineno, what);
    } else if (*endp != '\0') {
        app_error("%s:%u: error: invalid trace: "
                  "while reading %s, junk after number",
                  fname, lineno, what);
    } else if (errno) {
        unix_error("%s:%u: error: invalid trace: "
                   "while reading %s",
                   fname, lineno, what);
    } else if (val > max) {
        app_error("%s:%u: error: invalid trace: "
                  "value out of range for %s",
                  fname, lineno, what);
    }
    return val;
}

/** Read an 'a' or 'r' trace line (specifying a call to malloc
 *  or realloc, respectively).  The text at ARGS should match
 *  /[ \t]*[0-9]+[ \t]*[0-9]+/; the numbers are the block ID
 *  and the size to allocate or resize to, respectively.
 *
 *  @param op      traceop_t object to be initialized.
 *  @param opcode  Value for the 'type' field of OP.
 *  @param args    Arguments for this trace line, as text.
 *  @param fname   Trace file name (for error reporting).
 *  @param lineno  Trace line number (for error reporting).
 */
static void read_alloc_line(traceop_t *op, traceopcode_t opcode, char *args,
                            const char *fname, unsigned int lineno) {
    while (*args == ' ' || *args == '\t') {
        args++;
    }
    char *idtext = args;
    while ('0' <= *args && *args <= '9') {
        args++;
    }
    if (args == idtext) {
        app_error("%s:%u: error: invalid trace: "
                  "while reading block ID, found a not-number",
                  fname, lineno);
    }
    if (*args != ' ' && *args != '\t') {
        app_error("%s:%u: error: invalid trace: "
                  "while reading block ID, junk after number",
                  fname, lineno);
    }
    *args++ = '\0';
    while (*args == ' ' || *args == '\t') {
        args++;
    }

    op->type = opcode;
    op->lineno = lineno;
    op->index = (unsigned int)read_single_number(idtext, UINT_MAX, fname,
                                                 lineno, "block ID");
    op->size = read_single_number(args, SIZE_MAX, fname, lineno, "block size");
}

/** Read a 'f' trace line (specifying a call to free).
 *  The text at ARGS should match /[ \t]*[0-9]+/; the number
 *  is the block ID.
 *
 *  @param op      traceop_t object to be initialized.
 *  @param args    Arguments for this trace line, as text.
 *  @param fname   Trace file name (for error reporting).
 *  @param lineno  Trace line number (for error reporting).
 */
static void read_free_line(traceop_t *op, char *args, const char *fname,
                           unsigned int lineno) {

    while (*args == ' ' || *args == '\t') {
        args++;
    }
    op->type = FREE;
    op->lineno = lineno;
    op->index = (unsigned int)read_single_number(args, UINT_MAX, fname, lineno,
                                                 "block ID");
    op->size = 0;
}

/** Read a trace file into a freshly allocated trace_t object.
 *  Caller is responsible for calling free_trace on the trace
 *  when it's finished with it.
 *
 *  @param fname    Name of the trace file to be read.
 *  @param verbose     Verbosity level.
 *  @return            a trace_t object.
 */
trace_t *read_trace(const char *fname, unsigned int verbose) {

    if (verbose > 1)
        fprintf(stderr, "Reading tracefile: %s\n", fname);

    FILE *fp = fopen(fname, "r");
    if (!fp) {
        unix_error("Could not open %s in read_trace", fname);
    }

    /* Read the trace file header */
    char *line = NULL;
    size_t linesz = 0;
    unsigned int lineno = 0;

    get_header_line(fp, fname, &line, &linesz, &lineno);
    unsigned int iweight = (unsigned int)read_single_number(
        line, N_WEIGHT_CODES - 1, fname, lineno, "trace weight");

    get_header_line(fp, fname, &line, &linesz, &lineno);
    unsigned int num_ids = (unsigned int)read_single_number(
        line, UINT_MAX, fname, lineno, "number of block IDs");

    get_header_line(fp, fname, &line, &linesz, &lineno);
    unsigned int num_ops = (unsigned int)read_single_number(
        line, UINT_MAX, fname, lineno, "number of trace operations");

    get_header_line(fp, fname, &line, &linesz, &lineno);
    size_t peak_bytes = read_single_number(line, SIZE_MAX, fname, lineno,
                                           "peak allocation in bytes");

    // We can now allocate the trace_t object.
    trace_t *trace = malloc(sizeof(trace_t));
    if (!trace) {
        unix_error("read_trace: malloc/1 (%zd) failed", sizeof(trace_t));
    }
    trace->filename = fname;
    trace->data_bytes = peak_bytes;
    trace->num_ids = num_ids;
    trace->num_ops = num_ops;
    trace->weight = weight_codes[iweight];

    // We'll store each request line in the trace in this array.
    trace->ops = calloc(trace->num_ops, sizeof(traceop_t));
    if (!trace->ops) {
        unix_error("read_trace: malloc/2 (%zd) failed",
                   trace->num_ops * sizeof(traceop_t));
    }

    // We'll keep an array of pointers to the allocated blocks here...
    trace->blocks = calloc(trace->num_ids, sizeof(char *));
    if (!trace->blocks) {
        unix_error("read_trace: malloc/3 (%zd) failed",
                   trace->num_ids * sizeof(char *));
    }

    // ...along with the corresponding byte sizes of each block...
    trace->block_sizes = calloc(trace->num_ids, sizeof(size_t));
    if (!trace->block_sizes) {
        unix_error("read_trace: malloc/4 (%zd) failed",
                   trace->num_ids * sizeof(size_t));
    }

    // ...and, if we're debugging, the offset into the random data.
    trace->block_rand_base = calloc(trace->num_ids, sizeof(size_t));
    if (!trace->block_rand_base) {
        unix_error("read_trace: malloc/5 (%zd) failed",
                   trace->num_ids * sizeof(size_t));
    }

    // Read every request line in the trace file.
    unsigned int op = 0;
    unsigned int max_id_used = 0;

    while (get_next_line(fp, fname, &line, &linesz, &lineno)) {
        if (op == trace->num_ops) {
            app_error("%s:%d: error: invalid trace: too many ops", fname,
                      lineno);
        }

        switch (line[0]) {
        case 'a':
            read_alloc_line(&trace->ops[op], ALLOC, line + 1, fname, lineno);
            break;
        case 'r':
            trace->ops[op].type = REALLOC;
            read_alloc_line(&trace->ops[op], REALLOC, line + 1, fname, lineno);
            break;
        case 'f':
            trace->ops[op].type = FREE;
            read_free_line(&trace->ops[op], line + 1, fname, lineno);
            break;
        default:
            app_error("%s:%d: error: invalid trace: "
                      "unrecognized trace opcode '%c'",
                      fname, lineno, line[0]);
        }
        if (trace->ops[op].index > max_id_used) {
            max_id_used = trace->ops[op].index;
        }
        op++;
    }
    if (op < num_ops) {
        app_error("%s:%d: error: invalid trace: not enough ops", fname, lineno);
    }
    if (max_id_used != trace->num_ids - 1) {
        app_error("%s:%d: error: invalid trace: "
                  "wrong number of block IDs used",
                  fname, lineno);
    }

    fclose(fp);
    return trace;
}

/*
 * reinit_trace - get the trace ready for another run.
 */
void reinit_trace(trace_t *trace) {
    memset(trace->blocks, 0, trace->num_ids * sizeof(*trace->blocks));
    memset(trace->block_sizes, 0, trace->num_ids * sizeof(*trace->block_sizes));
    /* block_rand_base is unused if size is zero */
}

/*
 * free_trace - Free the trace record and the four arrays it points
 *              to, all of which were allocated in read_trace().
 */
void free_trace(trace_t *trace) {
    free(trace->ops); /* free the three arrays... */
    free(trace->blocks);
    free(trace->block_sizes);
    free(trace->block_rand_base);
    free(trace); /* and the trace record itself... */
}

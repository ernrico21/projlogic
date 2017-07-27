/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko
// Modified to implement bdd-based AllSAT solver on top of MiniSat by Takahisa Toda

#include "solver.h"
#include "list.h"
#include "bdd_interface.h"
#include "bdd_reduce.h"
#include "my_hash.h"
#include "list.h"
#include "my_def.h"
#include "obdd.h"
#include <math.h>
#include <string.h> 
#include "solver.h"
#include "trie.h"
#include "vec.h"
#include "obdd.h"
#include "trie.h"

#ifdef GMP
#include <gmp.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
//#include <unistd.h>
#include <signal.h>
#include <assert.h>
//#include <zlib.h>
//#include <sys/time.h>
//#include <sys/resource.h>
//=======================================================================================================
//bdd.reduce.c


extern solver* solver_new(void);
extern void    solver_delete(solver* s);

extern bool    solver_addclause(solver* s, lit* begin, lit* end);
extern bool    solver_simplify(solver* s);
extern bool    solver_solve(solver* s, lit* begin, lit* end);

extern int     solver_nvars(solver* s);
extern int     solver_nclauses(solver* s);
extern int     solver_nconflicts(solver* s);

extern void    solver_setnvars(solver* s,int n);

extern void totalup_stats(solver *s);


#if defined(REDUCTION)

static bddp bdd_reduce_rec(obdd_t* f, my_hash *h);

static uintmax_t recdepth = 0; //!< recursion depth


bddp bdd_reduce(obdd_t* f)
{
  my_hash *h = ht_create(0);
  ENSURE_TRUE_MSG(h != NULL, "hash table creation failed");

  assert(recdepth == 0);
  bddp r = bdd_reduce_rec(f, h);
  ENSURE_TRUE(r != BDD_NULL);
  assert(recdepth == 0);

  ht_destroy(h);
  return r;
}

static bddp bdd_reduce_rec(obdd_t* f, my_hash *h)
{
  if(f == obdd_top()) return bdd_top();
  if(f == obdd_bot()) return bdd_bot();

  bddp r;
  if(ht_search((uintptr_t)f, (uintptr_t*)&r, h)) return r;

  INC_RECDEPTH(recdepth);
  bddp lo = bdd_reduce_rec(f->lo, h);  
  bddp hi = bdd_reduce_rec(f->hi, h);
  DEC_RECDEPTH(recdepth);

  r = bdd_node(obdd_label(f), lo, hi);
  ENSURE_TRUE_MSG(r != BDD_NULL, "BDD operation failed");

  ht_insert((uintptr_t)f, (uintptr_t)r, h);
  
  return r;
}
#endif
//=================================================================================================
//list

struct list *new_list(int* value, struct list *next){
    struct list *this = malloc(sizeof(struct list));
    this->value = value;
    this->next = next;
    return this;
}



//===================================================================================================
//my_hash

#define DEFAULT_HASH_SIZE         (UINTMAX_C(1) << 24)  //!< The default number of buckets
#define HASH_ENLARGEMENT_WIDTH    (2)                   //!< the width of bitshift for enlargement
#define HASHCONST                 (31415926525)


/** \brief    Create a hash table.
 *  \param    n     The number of buckets to be created
 *  \return   Pointer to a hash table if successful; otherwise, NULL.
 *  \note     Set a default value to n if n == 0. 
 *  \see      ht_destroy
 */
my_hash *ht_create(uintmax_t n)
{
  n = (n == 0? DEFAULT_HASH_SIZE: n);

  my_hash *h = (my_hash*) malloc(sizeof(my_hash));
  ENSURE_TRUE_MSG(h != NULL,"memory allocation failed");

  h->bucket_count = n;
  h->entry_count  = 0;
  h->table        = (struct ht_entry**) malloc(sizeof(struct ht_entry*) * n);
  ENSURE_TRUE_MSG(h->table != NULL, "memory allocation failed");
  for(uintmax_t i = 0; i < n; i++) h->table[i] = NULL;

  return h;
}


/** \brief    Free memory area used by a hash table.
 *  \param    h     Pointer to a hash table
 *  \see      ht_create
 */
void ht_destroy(my_hash *h)
{
  assert(h != NULL);
  const uintmax_t n = h->bucket_count;
  for(uintmax_t i = 0; i < n; i++) {
      for(struct ht_entry *e = h->table[i]; e != NULL; ) {
        struct ht_entry *t = e->nx;
        free(e);
        e = t;
      }
  }
  free(h->table); h->table  = NULL;
  free(h);        h         = NULL;
}

/** \brief    Calculate a hash value.
 *  \param    k     Key (of pointer size)
 *  \param    n     The number of buckets
 *  \return   The calculated hash value
 */
static inline uintmax_t ht_hash(uintptr_t k, uintmax_t n)
{
  assert(n > 0);
  return (uintmax_t)(HASHCONST * (k >> 3))%n;
}

/** \brief    Insert a new entry to the head of a linked list.
 *  \param    k     Key (of pointer size)
 *  \param    v     Value associated with key (of pointer size)
 *  \param    h     Pointer to a hash table
 *  \see      ht_search
 */
void ht_insert(uintptr_t k, uintptr_t v, my_hash *h)
{
  assert(h != NULL);
  struct ht_entry *e = (struct ht_entry*)malloc(sizeof(struct ht_entry));
  ENSURE_TRUE_MSG(e != NULL, "memory allocation failed");
  e->key = k;
  e->val = v;

  const uintmax_t i = ht_hash(k, h->bucket_count);
  e->nx             = h->table[i];
  h->table[i]       = e;

  h->entry_count++;
}


/** \brief    Find a hash entry. If found, copy the associated value to the location pointed to by pv.
 *  \param    k     key (of pointer size)
 *  \param    pv    Pointer to a variable, in which the associated value (of pointer size) is copied.
 *  \param    h     Pointer to a hash table
 *  \return   true if found; otherwise, false.
 *  \see      ht_insert
 *  \note
 *  - Value will not be copied if pd == NULL.
 */
bool ht_search(uintptr_t k, uintptr_t *pv, const my_hash *h)
{
  assert(h != NULL);
  const uintmax_t i = ht_hash(k, h->bucket_count);
  for(struct ht_entry *e = h->table[i]; e != NULL; e = e->nx) {
    if(e->key == k) {
      if(pv != NULL) *pv = e->val;
      return true;
    }
  }
  return false;
}


/** \brief   Enlarge a hash table.
 *  \param   h     Pointer to a hash table
 *  \see     ht_create, ht_destroy
 */
void ht_enlarge(my_hash *h)
{
  const uintmax_t oldcnt = h->bucket_count;
  ENSURE_TRUE_MSG(oldcnt < (UINTMAX_MAX >> HASH_ENLARGEMENT_WIDTH), "bucket count overflow");
  const uintmax_t newcnt = oldcnt << HASH_ENLARGEMENT_WIDTH;
#ifdef HT_LOG
  printf("hashtable_resizing\t%ju\t%ju\n", oldcnt, newcnt);
#endif /*HT_LOG*/
  struct ht_entry **oldtable = h->table;
  struct ht_entry **newtable = (struct ht_entry**) malloc(sizeof(struct ht_entry*) * newcnt);
  ENSURE_TRUE_MSG(newtable != NULL, "memory allocation failed");
  for(uintmax_t i = 0; i < newcnt; i++) newtable[i] = NULL;
  for(uintmax_t i = 0; i < oldcnt; i++) {
    for(struct ht_entry *e = oldtable[i]; e != NULL;) {
      struct ht_entry *t  = e->nx;
      const uintmax_t j   = ht_hash(e->key, newcnt);
      e->nx       = newtable[j];
      newtable[j] = e;      
      e           = t;
    }
  }
  free(oldtable); oldtable = NULL;
  h->bucket_count = newcnt;
  h->table        = newtable;
}
//===============================================================================================
//obdd
static const int    initlen   = 65536;
static obdd_t*      freelist  = NULL;

static uintmax_t nnodes = 0; // the total number of nodes that have been created so far.

obdd_t* top_node = NULL;
obdd_t* bot_node = NULL;


uintmax_t obdd_nnodes(void)
{
    return nnodes;
}


obdd_t* obdd_node(int v, obdd_t* lo, obdd_t* hi)
{
    assert(v > 0);
    if (freelist == NULL) {
        freelist = (obdd_t*)malloc(sizeof(obdd_t)*initlen);
        ENSURE_TRUE_MSG(freelist != NULL, "memory allocation failed");
        for (int i = 1; i < initlen; i++)
            freelist[i-1].aux = (intptr_t)(freelist+i);
        freelist[initlen-1].aux = (intptr_t)NULL;
    }

    obdd_t* new = freelist;
    freelist  = (obdd_t*)freelist->aux;
    
    obdd_setlabel(v, new);
    new->lo  = lo;
    new->hi  = hi;
    new->aux = 0;
    nnodes++;

    return new;
}


static void obdd_free(obdd_t* p)
{
    p->aux = (intptr_t)freelist;
    freelist = p;
    assert(nnodes > 0);
    nnodes--;
}


uintmax_t obdd_complete(obdd_t* p)
{
    obdd_t* dummy  = obdd_node(INT_MAX, NULL, NULL);
    obdd_t* tail  = dummy;
    obdd_t* stack = NULL; 

    while (1) {
        while (p != NULL && !obdd_const(p) && p->v > 0) {
            p->v    *= -1;
            p->aux   = (intptr_t)stack;
            stack    = p;
            tail->nx = p;
            tail     = p;
            p        = p->lo;
        }
        if ((p = stack) == NULL)
            break;
        stack = (obdd_t*)stack->aux;
        p = p->hi;
    }

    tail->nx = NULL;
    p = dummy->nx;
    obdd_free(dummy);

    uintmax_t size = 0;
    for (; p != NULL; p = p->nx) {
        if (p->lo == NULL)
            p->lo = obdd_bot();
        if (p->hi == NULL)
            p->hi = obdd_bot();
        assert(p->v < 0);
        p->v   *= -1;
        size++;
    }

    return size;
}


void obdd_delete_all(obdd_t* p)
{
    while (p != NULL) {
        obdd_t* nx = p->nx;
        p->nx = NULL;
        obdd_free(p);
        p = nx;
    }
}


uintmax_t obdd_size(obdd_t* p)
{
    uintmax_t n = 0;  
    for (; p != NULL; p = p->nx)
        n++;

    return n;
}

/* \brief multiply x by 2^k.
 * \param x     nonzero integer
 * \param k     exponent 
 * \return  the resulted integer.
 * \note    UINTPTR_MAX is returned if overflow happens.
 */
static inline uintptr_t my_mul_2exp(uintptr_t x, int k)
{
    if (x <= (UINTPTR_MAX >> k))
        x = (x << k);
    else
        return UINTPTR_MAX;

    return x;
}

intptr_t obdd_nsols(int n, obdd_t* p)
{
    obdd_t** list = (obdd_t**)malloc(sizeof(obdd_t*)*(n+1));
    ENSURE_TRUE_MSG(list != NULL, "memory allocation failed");
    for (int i = 0; i <= n; i++)
        list[i] = NULL;

    for (obdd_t* s = p; s != NULL; s = s->nx) {
        int v   = obdd_label(s);
        assert(v <= n);
        s->aux  = (intptr_t)list[v];
        list[v] = s;
    }

    obdd_top()->aux = 1;
    obdd_bot()->aux = 0;
    uintptr_t result;
    for (int i = n; i > 0; i--) {
        for (obdd_t* s = list[i]; s != NULL;) {
            obdd_t* nx = (obdd_t*)s->aux;
            int j = obdd_const(s->hi)? n+1: obdd_label(s->hi);
            result = my_mul_2exp((uintptr_t)s->hi->aux, j-i-1);
            intptr_t c1 = result > INTPTR_MAX? INTPTR_MAX: (intptr_t)result;

            j = obdd_const(s->lo)? n+1: obdd_label(s->lo);
            result = my_mul_2exp((uintptr_t)s->lo->aux, j-i-1);
            intptr_t c2 = result > INTPTR_MAX? INTPTR_MAX: (intptr_t)result;

            s->aux = c1 <= INTPTR_MAX -c2? c1+c2: INTPTR_MAX;
            s = nx;
        }
    }

    result = my_mul_2exp((uintptr_t)p->aux, obdd_label(p)-1);
    result = result > INTPTR_MAX? INTPTR_MAX: (intptr_t)result;

    free(list);

    return result;
}


#ifdef GMP
void obdd_nsols_gmp(mpz_t result, int n, obdd_t* p)
{
    obdd_t** list = (obdd_t**)malloc(sizeof(obdd_t*)*(n+1));
    ENSURE_TRUE_MSG(list != NULL, "memory allocation failed");
    for (int i = 0; i <= n; i++)
        list[i] = NULL;

    int m = 0;
    for (obdd_t* s = p; s != NULL; s = s->nx) {
        int v   = obdd_label(s);
        s->aux  = (intptr_t)list[v];
        list[v] = s;
        m++;
    }

    m += 2; // include terminal nodes.
    const int size = m;
    mpz_t *a = (mpz_t*)malloc(sizeof(mpz_t)*m);
    ENSURE_TRUE_MSG(a != NULL, "memory allocation failed");
    for (int i = 0; i < m; i++) 
        mpz_init(a[i]);

    assert(m > 0);
    obdd_top()->aux = (intptr_t)--m;
    mpz_set_ui(a[m],1);
    assert(m > 0);
    obdd_bot()->aux = (intptr_t)--m;
    mpz_set_ui(a[m],0);

    for (int i = n; i > 0; i--) {
        for (obdd_t* s = list[i]; s != NULL;) {
            obdd_t* nx = (obdd_t*)s->aux;
            int j = obdd_const(s->hi)? n+1: obdd_label(s->hi);
            intptr_t m1 = s->hi->aux;
            if (j-i-1 > 0)
                mpz_mul_2exp(a[m1],a[m1],j-i-1);

            j = obdd_const(s->lo)? n+1: obdd_label(s->lo);
            intptr_t m2 = s->lo->aux;
            if (j-i-1 > 0)
                mpz_mul_2exp(a[m2],a[m2],j-i-1);

            assert(m > 0);
            s->aux = (intptr_t)--m;
            mpz_add(a[m], a[m1], a[m2]);
            s = nx;
        }
    }
    assert(m == 0);

    m = p->aux; 
    if(obdd_label(p)-1 > 0)
        mpz_mul_2exp(a[m],a[m],obdd_label(p)-1);
    mpz_set(result, a[m]);

    for (int i = 0; i < size; i++)
        mpz_clear(a[i]);
    free(list);
    free(a);
}
#endif


int obdd_to_dot(int n, obdd_t* p, FILE *out)
{ 
    if(obdd_const(p)) {
        ENSURE_TRUE_WARN(0, "invalid input");
        return ST_FAILURE;
    }

    obdd_t** list = (obdd_t**)malloc(sizeof(obdd_t*)*(n+1));
    ENSURE_TRUE_MSG(list != NULL, "memory allocation failed");
    for (int i = 0; i <= n; i++)
        list[i] = NULL;

    for (obdd_t* s = p; s != NULL; s = s->nx) {
        int v   = obdd_label(s);
        s->aux  = (intptr_t)list[v];
        list[v] = s;
    }

    int res = fseek(out, 0L, SEEK_SET);
    ENSURE_SUCCESS(res);

    fprintf(out, "digraph obdd {\n");
    fprintf(out, "{rank = same; %jd %jd}\n", (intptr_t)obdd_top(), (intptr_t)obdd_bot());
    for (int i = 1; i <= n; i++) {
        fprintf(out, "{rank = same;");
        for (obdd_t* s = list[i]; s != NULL; s = (obdd_t*)s->aux)
            fprintf(out, " %jd", (intptr_t)s);
        fprintf(out, "}\n");
    }
    for (int i = n; i > 0; i--) {
        for (obdd_t* s = list[i]; s != NULL;) {
            obdd_t* t = (obdd_t*)s->aux;
            fprintf(out, "%jd [label = %d];\n",           (intptr_t)s, i);
            fprintf(out, "%jd -> %jd ;\n",                 (intptr_t)s, (intptr_t)s->hi);
            fprintf(out, "%jd -> %jd [style = dotted];\n", (intptr_t)s, (intptr_t)s->lo);
            s = t;
        }
    }
    fprintf(out, "%jd [label = 1,shape=box];\n", (intptr_t)obdd_top());
    fprintf(out, "%jd [label = 0,shape=box];\n", (intptr_t)obdd_bot());
    fprintf(out, "}\n");

    free(list);

    return ST_SUCCESS;
}


// Decompose bdd into satisfying assignments.
static uintptr_t obdd_decompose_main(FILE *out, int n, obdd_t* p, uintptr_t (*func)(FILE *, int, int, int*,struct list*),struct list* lsol)
{
  uintptr_t total   = 0;  // total number of total solutions
  int *a = (int*)malloc(sizeof(int)*(n+1));
  ENSURE_TRUE_MSG(a != NULL, "memory allocation failed");
  for(int i = 0; i <= n; i++) a[i] = 0;
  obdd_t** b = (obdd_t**)malloc(sizeof(obdd_t*)*(n+1));
  ENSURE_TRUE_MSG(b != NULL, "memory allocation failed");
  for(int i = 0; i <= n; i++) b[i] = NULL;
  
  int s = 0; // index of a
  int t = 0; // index of b
  while(1) {
    while(!(p == obdd_bot() || p == obdd_top())) {
      b[t++]  = p;
      a[s++]  = -(p->v);
      p       = p->lo;
    }
    if(p == obdd_top()) {
        uintptr_t result = func(out, s, n, a,lsol);
	int *array = (int *)malloc((n +1) * sizeof(int*));
	struct list* nextsol=new_list(array, NULL);
	lsol->next=nextsol;
	lsol=nextsol;
	
        if(total < UINTPTR_MAX - result)
            total += result;
        else
            total = UINTPTR_MAX;
    }
    if(t <= 0) break; // b is empty
    p = b[--t]; 
    while(a[--s] > 0) ;
    a[s] = abs(a[s]); s++;
    p = p->hi;
  }
  free(b); free(a);
 // printf(" %lu",total);
  return total;
}


/* \brief print a partial assignment that is stored in a.
 * \param   out     pointer to output file
 * \param   s       length of a in which valid values are contained, which may be less than the actual length of a.
 * \param   n       the number of variables 
 * \return  the number of total assignments
 */
//stampa
static uintptr_t fprintf_partial(FILE *out, int s, int n, int *a,struct list* lsol)
{
    int prev = 0;
    uintptr_t sols = 1;
    for(int j = 0; j < s; j++) { 
        //fprintf(out, "%d ", a[j]);
        //solutions=snprintf(solutions,"%d ", i);
	if(a[j]<0)
	{
        	//printf("0 ");
		lsol->value[j]=0;
	}
	else
	{
		//printf("1 ");
		lsol->value[j]=1;
	}
        sols = my_mul_2exp(sols, abs(a[j])-prev-1);
        prev = abs(a[j]);
    }
    //fprintf(out, "0\n");
    //printf("\n");  
    return my_mul_2exp(sols, n-prev);
}


uintptr_t obdd_decompose(FILE *out, int n, obdd_t* p,struct list* lsol)
{
    return obdd_decompose_main(out, n, p, fprintf_partial,lsol);
}



//=================================================================================================
//solver123
/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko
// Modified to implement BDD-based AllSAT Solver on top of MiniSat by Takahisa Toda

/*#include <stdio.h>
#include <assert.h>
#include <math.h>

#include "solver.h"
#include "obdd.h"
#include "trie.h"*/

//=================================================================================================
// Debug:

//#define VERBOSEDEBUG

// For derivation output (verbosity level 2)
#ifdef NONBLOCKING
#define L_IND    "%d:%-*d"
#define L_ind    solver_dlevel(s),solver_dlevel(s)*3+3,solver_sublevel(s)
#else
#define L_IND    "%-*d"
#define L_ind    solver_dlevel(s)*3+3,solver_dlevel(s)
#endif /*NONBLOCKING*/

#define L_LIT    "%sx%d"
#define L_lit(p) lit_sign(p)?"~":"", (lit_var(p))

// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(int expr) { assert(expr); }

static void printlits(lit* begin, lit* end)
{
    int i;
    //for (i = 0; i < end - begin; i++)
      //  printf(L_LIT" ",L_lit(begin[i]));
}

//=================================================================================================
// Random numbers:


// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double* seed) {
    int q;
    *seed *= 1389796;
    q = (int)(*seed / 2147483647);
    *seed -= (double)q * 2147483647;
    return *seed / 2147483647; }


// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double* seed, int size) {
    return (int)(drand(seed) * size); }


//=================================================================================================
// Predeclarations:

void sort(void** array, int size, int(*comp)(const void *, const void *));

//=================================================================================================
// Clause datatype + minor functions:

struct clause_t
{
#ifdef CUTSETCACHE
    lit minlit;  // literal with minimum variable index: this field must be placed before lits[0]
    lit maxlit;  // literal with maximum variable index: this field must be placed before lits[0]
#endif
    int size_learnt;
    lit lits[0];
};

static inline int   clause_size       (clause* c)          { return c->size_learnt >> 1; }
static inline lit*  clause_begin      (clause* c)          { return c->lits; }
static inline lit*  clause_end        (clause* c)          { return c->lits + clause_size(c); } // Note: the next position of the last literal
#ifdef CUTSETCACHE
static inline lit   clause_minlit     (clause* c)          { return c->minlit; }
static inline lit   clause_maxlit     (clause* c)          { return c->maxlit; }
#endif
static inline int   clause_learnt     (clause* c)          { return c->size_learnt & 1; }
static inline float clause_activity   (clause* c)          { return *((float*)&c->lits[c->size_learnt>>1]); }
static inline void  clause_setactivity(clause* c, float a) { *((float*)&c->lits[c->size_learnt>>1]) = a; }

//=================================================================================================
// Encode literals in clause pointers:

clause* clause_from_lit (lit l)     { return (clause*)((unsigned long)l + (unsigned long)l + 1);  }
bool    clause_is_lit   (clause* c) { return ((unsigned long)c & 1);                              }
lit     clause_read_lit (clause* c) { return (lit)((unsigned long)c >> 1);                        }

//=================================================================================================
// Simple helpers:

static inline int     solver_dlevel(solver* s)    { return veci_size(&s->trail_lim); }
#ifdef NONBLOCKING
static inline int     solver_sublevel(solver* s) { return veci_size(&s->subtrail_lim); }
#endif /*NONBLOCKING*/
static inline vecp*   solver_read_wlist     (solver* s, lit l){ return &s->wlists[l]; }
static inline void    vecp_remove(vecp* v, void* e)
{
    void** ws = vecp_begin(v);
    int    j  = 0;

    for (; ws[j] != e  ; j++);
    assert(j < vecp_size(v));
    for (; j < vecp_size(v)-1; j++) ws[j] = ws[j+1];
    vecp_resize(v,vecp_size(v)-1);
}

static inline lit solver_assumedlit(solver *s, int level) {assert(level >= 1); return s->trail[veci_begin(&s->trail_lim)[level-1]];}

#ifdef CUTSETCACHE
static void solver_setminmaxlit(solver *s)
{

    const int m   = solver_nclauses(s);
    clause** cls  = (clause**)vecp_begin(&s->clauses);

    for (int i = 0; i < m; i++) {
        cls[i]->minlit = *(clause_begin(cls[i]));
        cls[i]->maxlit = *(clause_end(cls[i])-1);

        for (int j = 0; j < clause_size(cls[i]); j++) {
            const lit l = clause_begin(cls[i])[j];
            if (lit_var(l) > lit_var(cls[i]->maxlit))
                cls[i]->maxlit = l; 
            if (lit_var(l) < lit_var(cls[i]->minlit))
                cls[i]->minlit = l;
        }
    }
}
#endif /*CUTSETCACHE*/

static void solver_printtrail(solver *s){
    int lev = -1;
    int sublev = s->root_level;

   // printf("--------------------------------------------------------------------------------");fflush(stdout);
    for (int i = 0; i <= s->qtail-1; i++) {
        lit t = s->trail[i];
        if (lev < s->levels[lit_var(t)]) {
            lev = s->levels[lit_var(t)];
       //     printf("\n#%d ", lev); // newline for each level 
        }
#ifdef NONBLOCKING
        if (sublev < s->sublevels[lit_var(t)]) {
            sublev = s->sublevels[lit_var(t)];
       //     printf("| "); // separator of sublevels
        }
#endif /*NONBLOCKING*/
       // printf(L_LIT"%s ", L_lit(t), s->reasons[lit_var(t)] == (clause*)0? "*":"");// "*" means having NULL antecedent.
    }
  //  printf("\n\n");
    //printf("\n--------------------------------------------------------------------------------\n");fflush(stdout);
}

#ifdef NONBLOCKING
static void solver_printgencls(solver *s) // for debug
{
    //printf("#generated_clauses %d:\n", vecp_size(&s->generated_clauses));
    for (int i = 0; i < vecp_size(&s->generated_clauses); i++) {
        veci *v = (veci*)vecp_begin(&s->generated_clauses)[i];
        //for (int j = 0; j < veci_size(v); j++) 
           // printf(L_LIT" ", L_lit(veci_begin(v)[j]));
       // printf("\n");
    }
  //  printf("\n");
  fflush(stdout);
}
#endif /*NONBLOCKING*/

// cl3 <- resolution of cl1 and cl2, where the initial literals of cl1 and cl2 should be opposite.
// the initial literal of cl3 must be of the highest level.
#ifdef NONBLOCKING
static void perform_resolution(solver *s, veci *cl1, veci *cl2, veci *cl3)
{
    assert(veci_size(cl1) > 0);
    assert(veci_size(cl2) > 0);
    assert(*veci_begin(cl1) == lit_neg(*veci_begin(cl2)));
    lbool *ws = s->tags; // working space

    veci_resize(cl3, 0);
    for(int i = 1; i < veci_size(cl1); i++) {
        lit t = veci_begin(cl1)[i];
        veci_push(cl3, t);
        ws[lit_var(t)] = lit_sign(t)? l_False: l_True;
    }

    for (int i = 1; i < veci_size(cl2); i++) {
        const lit t  = veci_begin(cl2)[i];

        if (ws[lit_var(t)] == l_Undef) {
            veci_push(cl3, t);
        }
        /*else if (ws[lit_var(t)] == l_True && lit_sign(t) == 1 
               || ws[lit_var(t)] == l_False && lit_sign(t) == 0) {
            int j;
            for(j = 0; j < veci_size(cl3) && lit_var(veci_begin(cl3)[j]) != lit_var(t); j++) ;
            assert(j < veci_size(cl3));
            while(++j < veci_size(cl3))
                veci_begin(cl3)[j-1] = veci_begin(cl3)[j];
            veci_resize(cl3, veci_size(cl3)-1);
        }*/
        assert(!(ws[lit_var(t)] == l_True && lit_sign(t) == 1 || ws[lit_var(t)] == l_False && lit_sign(t) == 0));

        ws[lit_var(t)] = l_Undef; // initialize ws
    }

    if (veci_size(cl3) > 0) {
        int highest = s->levels[lit_var(veci_begin(cl3)[0])];
        int pos     = 0;
        ws[lit_var(veci_begin(cl3)[0])] = l_Undef;
        for (int i = 1; i < veci_size(cl3); i++) { // initialize ws and find the highest level and its position
            ws[lit_var(veci_begin(cl3)[i])] = l_Undef;
            if (highest < s->levels[lit_var(veci_begin(cl3)[i])]) {
                highest = s->levels[lit_var(veci_begin(cl3)[i])];
                pos     = i;
            }
        }

#ifdef DEBUG
        for (int i = 0; i < s->size; i++)
            assert(ws[i] == l_Undef); // for debug
#endif

        lit tmp = veci_begin(cl3)[0];
        veci_begin(cl3)[0] = veci_begin(cl3)[pos];
        veci_begin(cl3)[pos] = tmp;
    }
}
#endif /*NONBLOCKING*/


void totalup_stats(solver *s)
{
    intptr_t sols = s->root->aux;

    uint64 size = (uint64)obdd_complete(s->root);

    // total up obdd size
    s->stats.obddsize += size;

    // total up number of solutions
#ifdef GMP
    mpz_t result;
    mpz_init(result);
    mpz_set_ui(result,0);
    obdd_nsols_gmp(result, s->size, s->root);
    mpz_add(s->stats.tot_solutions_gmp, s->stats.tot_solutions_gmp, result); 
    mpz_clear(result);

#else
    if(s->stats.tot_solutions <= ULONG_MAX - sols)
        s->stats.tot_solutions += sols; // Note: s->root->aux can not count more than INTPTR_MAX!
    else
        s->stats.tot_solutions = ULONG_MAX;
#endif
}


static inline void solver_printstatus(solver *s)
{
    //if (s->verbosity < 1) 
    return;

    /*printf("%.1f", (float)(clock() - s->stats.clk)/(float)(CLOCKS_PER_SEC));
    printf("\t%ju", s->stats.conflicts);
    printf("\t%ju", s->stats.propagations);

    if (s->stats.refreshes == 0) {
        printf("\t%jd", s->root->aux);
        if (s->root->aux >= INTPTR_MAX)
            printf("+");
    } else {
        printf("\t-");
    }
        
    printf("\t\t%d", vecp_size(&s->clauses));
    printf("\t\t%d", vecp_size(&s->learnts));
    printf("\t\t%ju", obdd_nnodes());
    printf("\n");*/
}

//=================================================================================================
// Variable order functions:

static inline void order_update(solver* s, int v) // updateorder
{
    int*    orderpos = s->orderpos;
    double* activity = s->activity;
    int*    heap     = veci_begin(&s->order);
    int     i        = orderpos[v];
    int     x        = heap[i];
    int     parent   = (i - 1) / 2;

    assert(s->orderpos[v] != -1);

    while (i != 0 && activity[x] > activity[heap[parent]]){
        heap[i]           = heap[parent];
        orderpos[heap[i]] = i;
        i                 = parent;
        parent            = (i - 1) / 2;
    }
    heap[i]     = x;
    orderpos[x] = i;
}

static inline void order_assigned(solver* s, int v) 
{
}

static inline void order_unassigned(solver* s, int v) // undoorder
{
    int* orderpos = s->orderpos;
    if (orderpos[v] == -1){
        orderpos[v] = veci_size(&s->order);
        veci_push(&s->order,v);
        order_update(s,v);
    }
}

/*static int  order_select(solver* s, float random_var_freq) // selectvar
{
    int*    heap;
    double* activity;
    int*    orderpos;

    lbool* values = s->assigns;

    // Random decision:
    if (drand(&s->random_seed) < random_var_freq){
        int next = irand(&s->random_seed,s->size);
        assert(next >= 0 && next < s->size);
        if (values[next] == l_Undef)
            return next;
    }

    // Activity based decision:

    heap     = veci_begin(&s->order);
    activity = s->activity;
    orderpos = s->orderpos;


    while (veci_size(&s->order) > 0){
        int    next  = heap[0];
        int    size  = veci_size(&s->order)-1;
        int    x     = heap[size];

        veci_resize(&s->order,size);

        orderpos[next] = -1;

        if (size > 0){
            double act   = activity[x];

            int    i     = 0;
            int    child = 1;


            while (child < size){
                if (child+1 < size && activity[heap[child]] < activity[heap[child+1]])
                    child++;

                assert(child < size);

                if (act >= activity[heap[child]])
                    break;

                heap[i]           = heap[child];
                orderpos[heap[i]] = i;
                i                 = child;
                child             = 2 * child + 1;
            }
            heap[i]           = x;
            orderpos[heap[i]] = i;
        }

        if (values[next] == l_Undef)
            return next;
    }

    return var_Undef;
}*/

//=================================================================================================
// Activity functions:

static inline void act_var_rescale(solver* s) {
    double* activity = s->activity;
    int i;
    for (i = 0; i < s->size; i++)
        activity[i] *= 1e-100;
    s->var_inc *= 1e-100;
}

static inline void act_var_bump(solver* s, int v) {
    double* activity = s->activity;
    if ((activity[v] += s->var_inc) > 1e100)
        act_var_rescale(s);

    //printf("bump %d %f\n", v-1, activity[v]);

    if (s->orderpos[v] != -1)
        order_update(s,v);

}

static inline void act_var_decay(solver* s) { s->var_inc *= s->var_decay; }

static inline void act_clause_rescale(solver* s) {
    clause** cs = (clause**)vecp_begin(&s->learnts);
    int i;
    for (i = 0; i < vecp_size(&s->learnts); i++){
        float a = clause_activity(cs[i]);
        clause_setactivity(cs[i], a * (float)1e-20);
    }
    s->cla_inc *= (float)1e-20;
}


static inline void act_clause_bump(solver* s, clause *c) {
    float a = clause_activity(c) + s->cla_inc;
    clause_setactivity(c,a);
    if (a > 1e20) act_clause_rescale(s);
}

static inline void act_clause_decay(solver* s) { s->cla_inc *= s->cla_decay; }


//=================================================================================================
// Clause functions:

/* pre: size > 1 && no variable occurs twice
 */
static clause* clause_new(solver* s, lit* begin, lit* end, int learnt)
{
    int size;
    clause* c;
    int i;

    assert(end - begin > 1);
    assert(learnt >= 0 && learnt < 2);
    size           = end - begin;
    c              = (clause*)malloc(sizeof(clause) + sizeof(lit) * size + learnt * sizeof(float));
    c->size_learnt = (size << 1) | learnt;
    assert(((unsigned long)c & 1) == 0);

    for (i = 0; i < size; i++)
        c->lits[i] = begin[i];

    if (learnt)
        *((float*)&c->lits[size]) = 0.0;

    assert(begin[0] >= 0);
    assert(begin[0] < s->size*2);
    assert(begin[1] >= 0);
    assert(begin[1] < s->size*2);

    assert(lit_neg(begin[0]) < s->size*2);
    assert(lit_neg(begin[1]) < s->size*2);

    //vecp_push(solver_read_wlist(s,lit_neg(begin[0])),(void*)c);
    //vecp_push(solver_read_wlist(s,lit_neg(begin[1])),(void*)c);

    vecp_push(solver_read_wlist(s,lit_neg(begin[0])),(void*)(size > 2 ? c : clause_from_lit(begin[1])));
    vecp_push(solver_read_wlist(s,lit_neg(begin[1])),(void*)(size > 2 ? c : clause_from_lit(begin[0])));

    return c;
}


static void clause_remove(solver* s, clause* c)
{
    lit* lits = clause_begin(c);
    assert(lit_neg(lits[0]) < s->size*2);
    assert(lit_neg(lits[1]) < s->size*2);

    //vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)c);
    //vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)c);

    assert(lits[0] < s->size*2);
    vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[1])));
    vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[0])));

    if (clause_learnt(c)){
        s->stats.learnts--;
        s->stats.learnts_literals -= clause_size(c);
    }else{
        s->stats.clauses--;
        s->stats.clauses_literals -= clause_size(c);
    }

    free(c);
}


#ifdef CUTSETCACHE
static void clause_remove_nofree(solver* s, clause* c)
{
    lit* lits = clause_begin(c);
    assert(lit_neg(lits[0]) < s->size*2);
    assert(lit_neg(lits[1]) < s->size*2);

    //vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)c);
    //vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)c);

    assert(lits[0] < s->size*2);
    vecp_remove(solver_read_wlist(s,lit_neg(lits[0])),(void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[1])));
    vecp_remove(solver_read_wlist(s,lit_neg(lits[1])),(void*)(clause_size(c) > 2 ? c : clause_from_lit(lits[0])));

    if (clause_learnt(c)){
        s->stats.learnts--;
        s->stats.learnts_literals -= clause_size(c);
    }else{
        s->stats.clauses--;
        s->stats.clauses_literals -= clause_size(c);
    }

    //free(c);
}
#endif

static lbool clause_simplify(solver* s, clause* c)
{
    lit*   lits   = clause_begin(c);
    lbool* values = s->assigns;
    int i;

    assert(solver_dlevel(s) == 0);

    for (i = 0; i < clause_size(c); i++){
        lbool sig = !lit_sign(lits[i]); sig += sig - 1;
        if (values[lit_var(lits[i])] == sig)
            return l_True;
    }
    return l_False;
}



static lbool clause_simplify_noprop_until(solver* s, clause* c, int var) // evaluate clause without information of unit propagation
{
    lit*   lits   = clause_begin(c);
    lbool* values = s->assigns;

    for (int i = 0; i < clause_size(c); i++){
        lbool sig = !lit_sign(lits[i]); sig += sig - 1;
        if (lit_var(lits[i]) <= var  && values[lit_var(lits[i])] == sig) 
            return l_True;
    }
    return l_False;
}



#ifdef NONBLOCKING
static lbool clause_isasserting(solver* s, veci* c) // After decision, place unit literal, if exists, at the begining of the clause.
{
    lbool* values = s->assigns;

    int i,j,k;
    lit*   lits   = veci_begin(c);
    for (i = j = 0; i < veci_size(c); i++){
        lbool sig = !lit_sign(lits[i]); sig += sig - 1;
        if (values[lit_var(lits[i])] == l_Undef) 
            k=i, j++;
        if (values[lit_var(lits[i])] == sig || j > 1) 
            return l_False; // if c is satisfied or there are at least two undefined variables.
    }

    if(j == 1) {
      lit t   = lits[0];
      lits[0] = lits[k];
      lits[k] = t;
      return l_True;
    } else {
      return l_False;
    }
}
#endif /*NONBLOCKING*/

//=================================================================================================
// Cache-related functions:


#ifdef CUTSETCACHE
static void solver_setcutsets(solver* s)
{

    const int nvars = s->size;
    clause** cls    = (clause**)vecp_begin(&s->clauses);
    int*     cw     = s->cutwidth;

    for (int i = 0; i < nvars; i++)
        cw[i] = 0;

    const int m = solver_nclauses(s);
    for (int i = 0; i < m; i++) {
        int j = lit_var(clause_minlit(cls[i]));
        cw[j] += 1;

        int k = lit_var(clause_maxlit(cls[i]));
        cw[k] -= 1;
    }

    int max = 0; 
    for (int i = 1; i < nvars; i++) {
        cw[i] += cw[i-1];
        if (max < cw[i])
            max = cw[i];
    }
    s->maxcutwidth = max;

    for (int i = 0; i < nvars; i++) {
        if (s->cutsets[i] != NULL)
            free(s->cutsets[i]);
        s->cutsets[i] = (clause**)malloc(sizeof(clause*)*s->cutwidth[i]);
        assert(s->cutsets[i] != NULL);
    }

    int* w = (int*)malloc(sizeof(int)*nvars);  // working space
    assert(w != NULL);
    for (int i = 0; i < nvars; i++)
        w[i] = 0;
    for (int i = 0; i < m; i++) {
        for (int j = lit_var(clause_minlit(cls[i])); j < lit_var(clause_maxlit(cls[i])); j++) {
            assert(w[j] < s->cutwidth[j]);
            s->cutsets[j][w[j]++] = cls[i];
        }
    }

    free(w);
}

#else /*SEPARATORCACHE*/
static void solver_setseparators(solver* s) 
{
    const int nvars = s->size;
    int* w = (int*)malloc(sizeof(int)*nvars); // working space
    assert(w != NULL);
    for (int i = 0; i < nvars; i++)
        w[i] = i;

    const int m = solver_nclauses(s);
    clause **cls = (clause**)vecp_begin(&s->clauses);
    for (int i = 0; i < m; i++) {
        const int v = lit_var(*(clause_end(cls[i])-1));
        for (lit* l = clause_begin(cls[i]); l < clause_end(cls[i]); l++) {
        if (w[lit_var(*l)] < v)
            w[lit_var(*l)] = v;
        }
    }

    int* pw = s->pathwidth;
    for (int i = nvars-1; i >= 0; i--) {
        pw[i] = 1;
        pw[w[i]]--;
    }

    int max = 0;
    for (int i = 1; i < nvars; i++) {
        pw[i] += pw[i-1];
        assert(pw[i] >= 0);
        if (max < pw[i])
            max = pw[i];
    }
    s->maxpathwidth = max;

    for (int i = 0; i < nvars; i++) {
        if (s->separators[i] != NULL)
            free(s->separators[i]);
        s->separators[i] = (int*)malloc(sizeof(int)*s->pathwidth[i]);
        assert(s->separators[i] != NULL);
    }

    for (int i = nvars-1; i >= 0; i--) {
        const int k = w[i];
        w[i] = 0; // w[i] now means the position to insert a new element in the i-th separator. 
        for (int j = i; j < k; j++) {
            assert(w[j] < s->pathwidth[j]);
            s->separators[j][w[j]++] = i;
        }
    }

  /*for (int i = 0; i < nvars; i++) {
    assert(w[i] == s->pathwidth[i]);
    printf("%d: ", i+1);
    for (int j = 0; j < w[i]; j++) {
      printf("%d ", s->separators[i][j]+1);
    }
    printf("\n");
  }*/
    free(w);
}
#endif

static void solver_makecache(solver* s, unsigned int* vec, int i)
{
#ifdef CUTSETCACHE
    const int cutwidth  = s->cutwidth[i];

    UNSET_ALL_DIGIT(vec, cutwidth);
    for (int j = 0; j < cutwidth; j++) {
        if (clause_simplify_noprop_until(s, s->cutsets[i][j], i) == l_True)    
            SET_DIGIT(vec, j);
    }

#else /*SEPARATORCACHE*/
    const int pathwidth  = s->pathwidth[i];
    UNSET_ALL_DIGIT(vec, pathwidth);
    for (int j = 0; j < pathwidth; j++) {
        if (s->assigns[s->separators[i][j]] == l_True)    
            SET_DIGIT(vec, j);
    }
#endif

    veci_push(&s->cachedvars, i);
}


static void solver_initcache(solver *s)
{
    for (int i = 0; i < vecp_size(&s->bitvecs); i++) {
        if(vecp_begin(&s->bitvecs)[i] != NULL)
            free(vecp_begin(&s->bitvecs)[i]);
        vecp_begin(&s->bitvecs)[i] = NULL;
    }
    vecp_resize(&s->bitvecs, 0);

    trie_initialize();

#ifdef CUTSETCACHE
    solver_setminmaxlit(s);
    solver_setcutsets(s);

    for (int i = 0; i < s->size; i++) {
        s->cache[i]  = trie_create(s->cutwidth[i]);
        const int nwords = GET_NWORDS(s->cutwidth[i]);
        unsigned int *vec = (unsigned int*)malloc(sizeof(unsigned int) * nwords);
        assert(vec != NULL);
        for (int j = 0; j < nwords; j++)
            vec[j] = 0;
        vecp_push(&s->bitvecs, (void*)vec);
    }

#else  /*SEPARATORCACHE*/
    solver_setseparators(s);

    for (int i = 0; i < s->size; i++) {
        s->cache[i]  = trie_create(s->pathwidth[i]);
        const int nwords = GET_NWORDS(s->pathwidth[i]);
        unsigned int *vec = (unsigned int*)malloc(sizeof(unsigned int) * nwords);
        assert(vec != NULL);
        for (int j = 0; j < nwords; j++)
            vec[j] = 0;
        vecp_push(&s->bitvecs, (void*)vec);
    }
#endif
}


static void solver_insertcacheuntil(solver* s, int level)
{
    // s->obddpath holds the latest path added to OBDD.  
    if (!(vecp_size(&s->obddpath) > 0)) 
        return;

    const int k = (level >= s->root_level)? lit_var(solver_assumedlit(s,level+1)): 0;
    int j = 0;

    for (int i = 0; i < vecp_size(&s->obddpath)-1; i++) { 
        obdd_t* p = vecp_begin(&s->obddpath)[i];
        assert(obdd_label(p) == i+1);
        assert(s->assigns[i] != l_Undef);
        obdd_t* q = s->assigns[i] == l_True? p->hi: p->lo;

        if (q != vecp_begin(&s->obddpath)[i+1]) {
            if (k <= i) 
                vecp_resize(&s->obddpath, k+1);
            return;
        }
        if (i < k)  
            continue;

        int* vars = veci_begin(&s->cachedvars);
        int  len  = veci_size(&s->cachedvars);
        for (; j < len && vars[j] < i; j++) ;
        if (j < len && vars[j] == i) // insert only when cache is created.
            trie_insert((unsigned int*)vecp_begin(&s->bitvecs)[i], (intptr_t)vecp_begin(&s->obddpath)[i+1], s->cache[i]);
    }

    if (k+1 < vecp_size(&s->obddpath)) 
        vecp_resize(&s->obddpath, k+1);
}


#ifdef NONBLOCKING
static void solver_refreshobdd(solver *s)
{
    //printf("refreshing obdd...");
    s->stats.refreshes++;

    totalup_stats(s);
    int *array = (int *)malloc((s->size) * sizeof(int*));
    struct list* lsol=new_list(array, NULL);

    if (s->out != NULL) {
        //printf("\tdecomposing bdd...");fflush(stdout);
        obdd_decompose(s->out, s->size, s->root,lsol);
    }

    obdd_delete_all(s->root);
    s->root = obdd_node(1, NULL, NULL);

    trie_initialize();
    vecp_resize(&s->obddpath, 0);
    veci_resize(&s->cachedvars, 0);
    //printf("\tfin\n");fflush(stdout);
}
#endif /*NONBLOCKING*/

//=================================================================================================
// Minor (solver) functions:

void solver_setnvars(solver* s,int n)
{
    int var;

    if (s->cap < n){

        while (s->cap < n) s->cap = s->cap*2+1;

        s->wlists    = (vecp*)   realloc(s->wlists,   sizeof(vecp)*s->cap*2);
        s->activity  = (double*) realloc(s->activity, sizeof(double)*s->cap);
        s->assigns   = (lbool*)  realloc(s->assigns,  sizeof(lbool)*s->cap);
        s->orderpos  = (int*)    realloc(s->orderpos, sizeof(int)*s->cap);
        s->reasons   = (clause**)realloc(s->reasons,  sizeof(clause*)*s->cap);
        s->levels    = (int*)    realloc(s->levels,   sizeof(int)*s->cap);
#ifdef NONBLOCKING
        s->sublevels = (int*)    realloc(s->sublevels,   sizeof(int)*s->cap);
#endif /*NONBLOCKING*/
        s->tags      = (lbool*)  realloc(s->tags,     sizeof(lbool)*s->cap);
        s->trail     = (lit*)    realloc(s->trail,    sizeof(lit)*s->cap);
        s->cache     = (trie_t**)  realloc(s->cache,    sizeof(trie_t*)*s->cap);
#ifdef CUTSETCACHE
        s->cutwidth  = (int*)    realloc(s->cutwidth, sizeof(int)*s->cap);
        s->cutsets   = (clause***)  realloc(s->cutsets,  sizeof(clause**)*s->cap);
#else /*SEPARATORCACHE*/
        s->pathwidth = (int*)    realloc(s->pathwidth,     sizeof(int)*s->cap);
        s->separators = (int**)  realloc(s->separators,  sizeof(int*)*s->cap);
#endif
    }

    for (var = s->size; var < n; var++){
        vecp_new(&s->wlists[2*var]);
        vecp_new(&s->wlists[2*var+1]);
        s->activity [var] = 0;
        s->assigns  [var] = l_Undef;
        s->orderpos [var] = veci_size(&s->order);
        s->reasons  [var] = (clause*)0;
        s->levels   [var] = 0;
#ifdef NONBLOCKING
        s->sublevels[var] = 0;
#endif /*NONBLOCKING*/
        s->tags     [var] = l_Undef;
#ifdef CUTSETCACHE
        s->cutwidth [var] = 0;
        s->cutsets  [var] = NULL;
#else /*SEPARATORCACHE*/
        s->pathwidth  [var] = 0;
        s->separators [var] = NULL;
#endif
        
        /* does not hold because variables enqueued at top level will not be reinserted in the heap
           assert(veci_size(&s->order) == var); 
         */
        veci_push(&s->order,var);
        order_update(s, var);
    }

    s->size = n > s->size ? n : s->size;
}


static inline bool enqueue(solver* s, lit l, clause* from)
{
    lbool* values = s->assigns;
    int    v      = lit_var(l);
    lbool  val    = values[v];
#ifdef VERBOSEDEBUG
   // printf(L_IND"enqueue("L_LIT")", L_ind, L_lit(l));
    //if (from == 0)
      //  printf(" with null ant.");
    if (from != 0) {
       // printf(L_IND"implied by {", L_ind);
        lit *lits;
        int size;
        lit tmp;
        if (clause_is_lit(from)) {
            tmp = clause_read_lit(from);
            lits = &tmp;
            size = 1;
        } else {
            lits = clause_begin(from);
            size = clause_size(from);
        }
       // for (int i = 0; i < size; i++) printf(" "L_LIT, L_lit(lits[i]));
        //printf("}");
    }
   // printf("\n");
#endif

    lbool sig = !lit_sign(l); sig += sig - 1;
    if (val != l_Undef){
        return val == sig;
    }else{
        // New fact -- store it.
#ifdef VERBOSEDEBUG
        //printf(L_IND"bind("L_LIT")\n", L_ind, L_lit(l));
#endif
        int*     levels  = s->levels;
#ifdef NONBLOCKING
        int*     sublevels  = s->sublevels;
#endif /*NONBLOCKING*/
        clause** reasons = s->reasons;

        values [v] = sig;
        levels [v] = solver_dlevel(s);
#ifdef NONBLOCKING
        sublevels [v] = solver_sublevel(s);
#endif /*NONBLOCKING*/
        reasons[v] = from;
        s->trail[s->qtail++] = l;

        order_assigned(s, v);
        return true;
    }
}


static inline void assume(solver* s, lit l){
    assert(s->qtail == s->qhead);
    assert(s->assigns[lit_var(l)] == l_Undef);
#ifdef VERBOSEDEBUG
    //printf(L_IND"assume("L_LIT")\n", L_ind, L_lit(l));
#endif
    veci_push(&s->trail_lim,s->qtail);
#ifdef NONBLOCKING
    veci_push(&s->subtrail_lim,s->qtail);
#endif /*NONBLOCKING*/
    enqueue(s,l,(clause*)0);
}


static inline void solver_canceluntil(solver* s, int level) {
    lit*     trail;   
    lbool*   values;  
    clause** reasons; 
    int      bound;
    int      c;
    
    if (solver_dlevel(s) <= level)
        return;

    trail   = s->trail;
    values  = s->assigns;
    reasons = s->reasons;
    bound   = (veci_begin(&s->trail_lim))[level];

    s->nextvar  = lit_var(trail[bound]);

    {
      int* vars = veci_begin(&s->cachedvars);
      int i;
      for (i = veci_size(&s->cachedvars)-1; i >= 0 && s->nextvar <= vars[i]; i--) ;
      veci_resize(&s->cachedvars, i+1);
    }

#ifdef NONBLOCKING
    int sublevel;
    lit t = s->trail[veci_begin(&s->trail_lim)[level]-1]; // the last literal at the target level
    sublevel = level > s->root_level? s->sublevels[lit_var(t)] : level; // convert level to sublevel
#endif /*NONBLOCKING*/

    for (c = s->qtail-1; c >= bound; c--) {
        int     x  = lit_var(trail[c]);
        values [x] = l_Undef;
        reasons[x] = (clause*)0;
    }

    for (c = s->qhead-1; c >= bound; c--)
        order_unassigned(s,lit_var(trail[c]));

    s->qhead = s->qtail = bound;
    veci_resize(&s->trail_lim,level);
#ifdef NONBLOCKING
    veci_resize(&s->subtrail_lim,sublevel);
#endif /*NONBLOCKING*/
}

#ifdef NONBLOCKING
static clause *solver_record(solver* s, veci* cls)
{
    lit*    begin = veci_begin(cls);
    lit*    end   = begin + veci_size(cls);
    clause* c     = (veci_size(cls) > 1) ? clause_new(s,begin,end,1) : (clause*)0;
    assert(veci_size(cls) > 0);
    if (clause_isasserting(s,cls) == l_True) {
        // this may be a literal with null antecedent, in which a new sublevel is not defined.
        // However, this does not matter because solver_analyze is modifed to handle this case.
        enqueue(s,veci_begin(cls)[0],c); 
    }

    if (c != 0) {
        vecp_push(&s->learnts,c);
        act_clause_bump(s,c);
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
    }

    return c;
}

static clause *solver_record_noenqueue(solver* s, veci* cls)
{
    lit*    begin = veci_begin(cls);
    lit*    end   = begin + veci_size(cls);
    clause* c     = (veci_size(cls) > 1) ? clause_new(s,begin,end,1) : (clause*)0;
    assert(veci_size(cls) > 0);

    if (c != 0) {
        vecp_push(&s->learnts,c);
        act_clause_bump(s,c);
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
    }

    return c;
}

#else
static void solver_record(solver* s, veci* cls)
{
    lit*    begin = veci_begin(cls);
    lit*    end   = begin + veci_size(cls);
    clause* c     = (veci_size(cls) > 1) ? clause_new(s,begin,end,1) : (clause*)0;
    enqueue(s,*begin,c);

    assert(veci_size(cls) > 0);

    if (c != 0) {
        vecp_push(&s->learnts,c);
        act_clause_bump(s,c);
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
    }
}
#endif /*NONBLOCKING*/


/*static double solver_progress(solver* s) 
{
    lbool*  values = s->assigns;
    int*    levels = s->levels;
    int     i;

    double  progress = 0;
    double  F        = 1.0 / s->size;
    for (i = 0; i < s->size; i++)
        if (values[i] != l_Undef)
            progress += pow(F, levels[i]);
    return progress / s->size;
}*/

//=================================================================================================
// Major methods:

static bool solver_lit_removable(solver* s, lit l, int minl)
{
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
#ifdef NONBLOCKING
#ifdef DLEVEL
    int*     levels  = s->levels;
#else
    int*     levels  = s->sublevels;
#endif
#else
    int*     levels  = s->levels;
#endif /*NONBLOCKING*/
    int      top     = veci_size(&s->tagged);

    assert(lit_var(l) >= 0 && lit_var(l) < s->size);
    assert(reasons[lit_var(l)] != 0);
    veci_resize(&s->stack,0);
    veci_push(&s->stack,lit_var(l));

    while (veci_size(&s->stack) > 0){
        clause* c;
        int v = veci_begin(&s->stack)[veci_size(&s->stack)-1];
        assert(v >= 0 && v < s->size);
        veci_resize(&s->stack,veci_size(&s->stack)-1);
        assert(reasons[v] != 0);
        c    = reasons[v];

        if (clause_is_lit(c)){
            int v = lit_var(clause_read_lit(c));
            if (tags[v] == l_Undef && levels[v] != 0){
                if (reasons[v] != 0 && ((1 << (levels[v] & 31)) & minl)){
                    veci_push(&s->stack,v);
                    tags[v] = l_True;
                    veci_push(&s->tagged,v);
                }else{
                    int* tagged = veci_begin(&s->tagged);
                    int j;
                    for (j = top; j < veci_size(&s->tagged); j++)
                        tags[tagged[j]] = l_Undef;
                    veci_resize(&s->tagged,top);
                    return false;
                }
            }
        }else{
            lit*    lits = clause_begin(c);
            int     i, j;

            for (i = 1; i < clause_size(c); i++){
                int v = lit_var(lits[i]);
                if (tags[v] == l_Undef && levels[v] != 0){
                    if (reasons[v] != 0 && ((1 << (levels[v] & 31)) & minl)){

                        veci_push(&s->stack,lit_var(lits[i]));
                        tags[v] = l_True;
                        veci_push(&s->tagged,v);
                    }else{
                        int* tagged = veci_begin(&s->tagged);
                        for (j = top; j < veci_size(&s->tagged); j++)
                            tags[tagged[j]] = l_Undef;
                        veci_resize(&s->tagged,top);
                        return false;
                    }
                }
            }
        }
    }

    return true;
}


#ifdef NONBLOCKING
static void solver_analyze(solver* s, clause* c, veci* learnt, lit target_lit)
{
    lit*     trail   = s->trail;
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels     = s->levels;
    int*     sublevels  = s->sublevels;
    int      cnt     = 0;
    lit      p       = lit_Undef;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j, minl;
    int*     tagged;

    veci_push(learnt,lit_Undef);
    lbool target_passed = (target_lit == lit_Undef? l_True: l_False);

#ifdef DLEVEL
    do{
        /*if(c == 0)   { // for debug
            printf("target lit: "L_LIT", the current lit: "L_LIT" \n", L_lit(target_lit), L_lit(p));
            solver_printtrail(s);
        }*/
        assert(c != 0);
        if (clause_is_lit(c)){
            lit q = clause_read_lit(c);
            assert(lit_var(q) >= 0 && lit_var(q) < s->size);
            if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0){
                tags[lit_var(q)] = l_True;
                veci_push(&s->tagged,lit_var(q));
                act_var_bump(s,lit_var(q));
                if (levels[lit_var(q)] == solver_dlevel(s))
                    cnt++;
                else
                    veci_push(learnt,q);
            }
        } else {

            if (clause_learnt(c))
                act_clause_bump(s,c);

            lits = clause_begin(c);
            //printlits(lits,lits+clause_size(c)); printf("\n");
            for (j = (p == lit_Undef ? 0 : 1); j < clause_size(c); j++){
                lit q = lits[j];
                assert(lit_var(q) >= 0 && lit_var(q) < s->size);
                if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0){
                    tags[lit_var(q)] = l_True;
                    veci_push(&s->tagged,lit_var(q));
                    act_var_bump(s,lit_var(q));
                    if (levels[lit_var(q)] == solver_dlevel(s))
                        cnt++;
                    else
                        veci_push(learnt,q);
                }
            }
        }

        do {
            while (tags[lit_var(trail[ind--])] == l_Undef);

            p = trail[ind+1];
            c = reasons[lit_var(p)];
            cnt--;
            if (p == target_lit)
                target_passed = l_True;
            if (c == 0 && cnt > 0 && p != target_lit)
                veci_push(learnt, lit_neg(p));
        } while (c == 0 && cnt > 0); // add flipped decisions and skip them.
    } while (cnt > 0 || target_passed == l_False);

    if (target_lit == lit_Undef) {
        *veci_begin(learnt) = lit_neg(p);
     } else {
        if(p != target_lit)
            veci_push(learnt, lit_neg(p));
        *veci_begin(learnt) = lit_neg(target_lit);
     }

#else /*SUBLEVEL*/
    do{
        /*if(cnt > 0 && target_passed == l_True)   { // for debug
            printf("target lit: "L_LIT", the current lit: "L_LIT" \n", L_lit(target_lit), L_lit(p));
            solver_printtrail(s);
        }*/
        assert(c != 0);

        if (clause_is_lit(c)){
            lit q = clause_read_lit(c);
            assert(lit_var(q) >= 0 && lit_var(q) < s->size);
            if (tags[lit_var(q)] == l_Undef && sublevels[lit_var(q)] > 0){
                tags[lit_var(q)] = l_True;
                veci_push(&s->tagged,lit_var(q));
                act_var_bump(s,lit_var(q));
                if (sublevels[lit_var(q)] == solver_sublevel(s))
                    cnt++;
                else
                    veci_push(learnt,q);
            }
        } else {

            if (clause_learnt(c))
                act_clause_bump(s,c);

            lits = clause_begin(c);
            //printlits(lits,lits+clause_size(c)); printf("\n");
            for (j = (p == lit_Undef ? 0 : 1); j < clause_size(c); j++){
                lit q = lits[j];
                assert(lit_var(q) >= 0 && lit_var(q) < s->size);
                if (tags[lit_var(q)] == l_Undef && sublevels[lit_var(q)] > 0){
                    tags[lit_var(q)] = l_True;
                    veci_push(&s->tagged,lit_var(q));
                    act_var_bump(s,lit_var(q));
                    if (sublevels[lit_var(q)] == solver_sublevel(s))
                        cnt++;
                    else
                        veci_push(learnt,q);
                }
            }
        }

        do {
            while (tags[lit_var(trail[ind--])] == l_Undef);

            p = trail[ind+1];
            c = reasons[lit_var(p)];
            cnt--;
            if (p == target_lit)
                target_passed = l_True;
            //if (c == 0 && cnt > 0 && p != target_lit) 
            //    veci_push(learnt, lit_neg(p)); // note: this must be commented in sublevel analysis!
        } while (c == 0 && cnt > 0);
    } while (cnt > 0 || target_passed == l_False);

    if (target_lit == lit_Undef) {
        *veci_begin(learnt) = lit_neg(p);
     } else {
        if(p != target_lit)
            veci_push(learnt, lit_neg(p));
        *veci_begin(learnt) = lit_neg(target_lit);
     }
#endif

#ifdef DLEVEL
    lits = veci_begin(learnt);
    minl = 0;
    for (i = 1; i < veci_size(learnt); i++){
        int lev = levels[lit_var(lits[i])];
        minl    |= 1 << (lev & 31);
    }
#else /*SUBLEVEL*/
    lits = veci_begin(learnt);
    minl = 0;
    for (i = 1; i < veci_size(learnt); i++){
        int lev = sublevels[lit_var(lits[i])];
        minl    |= 1 << (lev & 31);
    }
#endif

    // simplify (full)
    for (i = j = 1; i < veci_size(learnt); i++){
        if (reasons[lit_var(lits[i])] == 0 || !solver_lit_removable(s,lits[i],minl))
            lits[j++] = lits[i];
    }

    // update size of learnt + statistics
    s->stats.max_literals += veci_size(learnt);
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    // clear tags
    tagged = veci_begin(&s->tagged);
    for (i = 0; i < veci_size(&s->tagged); i++)
        tags[tagged[i]] = l_Undef;
    veci_resize(&s->tagged,0);

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(tags[i] == l_Undef);
#endif

#ifdef VERBOSEDEBUG
   // printf(L_IND"Learnt {", L_ind);
    //for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        int max_i = 1;
        int max   = sublevels[lit_var(lits[1])];
        lit tmp;

        for (i = 2; i < veci_size(learnt); i++)
            if (sublevels[lit_var(lits[i])] > max){
                max   = sublevels[lit_var(lits[i])];
                max_i = i;
            }

        tmp         = lits[1];
        lits[1]     = lits[max_i];
        lits[max_i] = tmp;
    }
#ifdef VERBOSEDEBUG
    {
        int lev = veci_size(learnt) > 1 ? s->levels[lit_var(lits[1])] : 0;
        int sublev = veci_size(learnt) > 1 ? sublevels[lit_var(lits[1])] : 0;
        //printf(" } at level %d, sublevel %d\n", lev, sublev);
    }
#endif

}

#else
static void solver_analyze(solver* s, clause* c, veci* learnt)
{
    lit*     trail   = s->trail;
    lbool*   tags    = s->tags;
    clause** reasons = s->reasons;
    int*     levels  = s->levels;
    int      cnt     = 0;
    lit      p       = lit_Undef;
    int      ind     = s->qtail-1;
    lit*     lits;
    int      i, j, minl;
    int*     tagged;

    veci_push(learnt,lit_Undef);

    do{
        assert(c != 0);

        if (clause_is_lit(c)){
            lit q = clause_read_lit(c);
            assert(lit_var(q) >= 0 && lit_var(q) < s->size);
            if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0){
                tags[lit_var(q)] = l_True;
                veci_push(&s->tagged,lit_var(q));
                act_var_bump(s,lit_var(q));
                if (levels[lit_var(q)] == solver_dlevel(s))
                    cnt++;
                else
                    veci_push(learnt,q);
            }
        }else{

            if (clause_learnt(c))
                act_clause_bump(s,c);

            lits = clause_begin(c);
            //printlits(lits,lits+clause_size(c)); printf("\n");
            for (j = (p == lit_Undef ? 0 : 1); j < clause_size(c); j++){
                lit q = lits[j];
                assert(lit_var(q) >= 0 && lit_var(q) < s->size);
                if (tags[lit_var(q)] == l_Undef && levels[lit_var(q)] > 0){
                    tags[lit_var(q)] = l_True;
                    veci_push(&s->tagged,lit_var(q));
                    act_var_bump(s,lit_var(q));
                    if (levels[lit_var(q)] == solver_dlevel(s))
                        cnt++;
                    else
                        veci_push(learnt,q);
                }
            }
        }

        while (tags[lit_var(trail[ind--])] == l_Undef);

        p = trail[ind+1];
        c = reasons[lit_var(p)];
        cnt--;

    }while (cnt > 0);

    *veci_begin(learnt) = lit_neg(p);

    lits = veci_begin(learnt);
    minl = 0;
    for (i = 1; i < veci_size(learnt); i++){
        int lev = levels[lit_var(lits[i])];
        minl    |= 1 << (lev & 31);
    }

    // simplify (full)
    for (i = j = 1; i < veci_size(learnt); i++){
        if (reasons[lit_var(lits[i])] == 0 || !solver_lit_removable(s,lits[i],minl))
            lits[j++] = lits[i];
    }

    // update size of learnt + statistics
    s->stats.max_literals += veci_size(learnt);
    veci_resize(learnt,j);
    s->stats.tot_literals += j;

    // clear tags
    tagged = veci_begin(&s->tagged);
    for (i = 0; i < veci_size(&s->tagged); i++)
        tags[tagged[i]] = l_Undef;
    veci_resize(&s->tagged,0);

#ifdef DEBUG
    for (i = 0; i < s->size; i++)
        assert(tags[i] == l_Undef);
#endif

#ifdef VERBOSEDEBUG
    //printf(L_IND"Learnt {", L_ind);
    for (i = 0; i < veci_size(learnt); i++) printf(" "L_LIT, L_lit(lits[i]));
#endif
    if (veci_size(learnt) > 1){
        int max_i = 1;
        int max   = levels[lit_var(lits[1])];
        lit tmp;

        for (i = 2; i < veci_size(learnt); i++)
            if (levels[lit_var(lits[i])] > max){
                max   = levels[lit_var(lits[i])];
                max_i = i;
            }

        tmp         = lits[1];
        lits[1]     = lits[max_i];
        lits[max_i] = tmp;
    }
#ifdef VERBOSEDEBUG
    {
        int lev = veci_size(learnt) > 1 ? levels[lit_var(lits[1])] : 0;
       // printf(" } at level %d\n", lev);
    }
#endif
}
#endif /*NONBLOCKING*/


clause* solver_propagate(solver* s)
{
    lbool*  values = s->assigns;
    clause* confl  = (clause*)0;
    lit*    lits;

    //printf("solver_propagate\n");
    while (confl == 0 && s->qtail - s->qhead > 0){
        lit  p  = s->trail[s->qhead++];
        vecp* ws = solver_read_wlist(s,p);
        clause **begin = (clause**)vecp_begin(ws);
        clause **end   = begin + vecp_size(ws);
        clause **i, **j;

        s->stats.propagations++;
        s->simpdb_props--;

        //printf("checking lit %d: "L_LIT"\n", veci_size(ws), L_lit(p));
        for (i = j = begin; i < end; ){
            if (clause_is_lit(*i)){
                *j++ = *i;
                if (!enqueue(s,clause_read_lit(*i),clause_from_lit(p))){
                    confl = s->binary;
                    (clause_begin(confl))[1] = lit_neg(p);
                    (clause_begin(confl))[0] = clause_read_lit(*i++);

                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }
            }else{
                lit false_lit;
                lbool sig;

                lits = clause_begin(*i);

                // Make sure the false literal is data[1]:
                false_lit = lit_neg(p);
                if (lits[0] == false_lit){
                    lits[0] = lits[1];
                    lits[1] = false_lit;
                }
                assert(lits[1] == false_lit);
                //printf("checking clause: "); printlits(lits, lits+clause_size(*i)); printf("\n");

                // If 0th watch is true, then clause is already satisfied.
                sig = !lit_sign(lits[0]); sig += sig - 1;
                if (values[lit_var(lits[0])] == sig){
                    *j++ = *i;
                }else{
                    // Look for new watch:
                    lit* stop = lits + clause_size(*i);
                    lit* k;
                    for (k = lits + 2; k < stop; k++){
                        lbool sig = lit_sign(*k); sig += sig - 1;
                        if (values[lit_var(*k)] != sig){
                            lits[1] = *k;
                            *k = false_lit;
                            vecp_push(solver_read_wlist(s,lit_neg(lits[1])),*i);
                            goto next; }
                    }

                    *j++ = *i;
                    // Clause is unit under assignment:
                    if (!enqueue(s,lits[0], *i)){
                        confl = *i++;
                        // Copy the remaining watches:
                        while (i < end)
                            *j++ = *i++;
                    }
                }
            }
        next:
            i++;
        }

        s->stats.inspects += j - (clause**)vecp_begin(ws);
        vecp_resize(ws,j - (clause**)vecp_begin(ws));
    }

    return confl;
}

static inline int clause_cmp (const void* x, const void* y) {
    return clause_size((clause*)x) > 2 && (clause_size((clause*)y) == 2 || clause_activity((clause*)x) < clause_activity((clause*)y)) ? -1 : 1; }

void solver_reducedb(solver* s)
{
    int      i, j;
    double   extra_lim = s->cla_inc / vecp_size(&s->learnts); // Remove any clause below this activity
    clause** learnts = (clause**)vecp_begin(&s->learnts);
    clause** reasons = s->reasons;

    sort(vecp_begin(&s->learnts), vecp_size(&s->learnts), &clause_cmp);

    for (i = j = 0; i < vecp_size(&s->learnts) / 2; i++){
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i])
            clause_remove(s,learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < vecp_size(&s->learnts); i++){
        if (clause_size(learnts[i]) > 2 && reasons[lit_var(*clause_begin(learnts[i]))] != learnts[i] && clause_activity(learnts[i]) < extra_lim)
            clause_remove(s,learnts[i]);
        else
            learnts[j++] = learnts[i];
    }

    //printf("reducedb deleted %d\n", vecp_size(&s->learnts) - j);


    vecp_resize(&s->learnts,j);
}


static void solver_extendobdd(solver* s, obdd_t* target)
{
    lbool*  values   = s->assigns;
    const int targetvar = (target == obdd_top()) ? s->size: obdd_label(target)-1;
    obdd_t* p;

    // Go down to a leaf of OBDD according to the current assignment.
    vecp_resize(&s->obddpath, 0);
    p = s->root;
    int i;
    while (p != NULL && (i=obdd_label(p)-1) < targetvar) {
        vecp_push(&s->obddpath, (void*)p);
        p = (values[i] == l_False? p->lo: p->hi);
    }
    assert(vecp_size(&s->obddpath) > 0);
#ifdef NONBLOCKING
    assert(p == NULL); // solutions never be rediscovered due to chronologcal backtracking.
#endif

    if (p == NULL) {
        // Concatenate new nodes to OBDD.
        p = vecp_begin(&s->obddpath)[vecp_size(&s->obddpath)-1];
        vecp_resize(&s->obddpath, vecp_size(&s->obddpath)-1);
        for (i=obdd_label(p)-1; i < targetvar; i++) {
            vecp_push(&s->obddpath, (void*)p);
            obdd_t* next = (i == targetvar-1? target: obdd_node(i+2, NULL, NULL));
            if (values[i] == l_False)  
                p->lo = next;
            else                      
                p->hi = next;
            p = next;
        }

        // Update the aux field of each obdd node traversed above (this is for counting the number of solutions).
        for (i = vecp_size(&s->obddpath)-1; i >= 0; i--) { 
            p = (obdd_t*)vecp_begin(&s->obddpath)[i];
            intptr_t nl = (p->lo != NULL? p->lo->aux: 0);
            intptr_t nh = (p->hi != NULL? p->hi->aux: 0);
            if (nl == INTPTR_MAX || nh == INTPTR_MAX || INTPTR_MAX - nl <= nh)  
                p->aux = INTPTR_MAX; // overflow!
            else                                                               
                p->aux = nl+nh;
        }
    }

    vecp_push(&s->obddpath, target);
}


#ifdef NONBLOCKING
// chronological backtrack from a given level
static lit solver_backtrack(solver*s, int level)
{
    lit t = solver_assumedlit(s, level);
    solver_insertcacheuntil(s, level-1);
    solver_canceluntil(s,level-1);

    if (level-1 > s->root_level)
        veci_push(&s->subtrail_lim,s->qtail);
    assert(s->assigns[lit_var(t)] == l_Undef);
    enqueue(s,lit_neg(t),(clause*)0);

}

// conflict resolution based on chronological backtracking
static lbool solver_resolve_conflict_bt(solver *s, clause *confl)
{
    assert(confl != (clause*)0);
    s->stats.conflicts++;
    if (solver_dlevel(s) <= s->root_level) {
        return l_True;
    }

    veci learnt_clause;
    veci_new(&learnt_clause);
    solver_analyze(s, confl, &learnt_clause, lit_Undef);

    solver_backtrack(s, solver_dlevel(s)); 
    s->lim = solver_dlevel(s);

    solver_record(s,&learnt_clause);
    act_var_decay(s);
    act_clause_decay(s);

    veci_delete(&learnt_clause);
    return l_False;
}


// conflict resolution based on non-chronological backtracking with level limit
static lbool solver_resolve_conflict_bj(solver *s, clause *confl)
{
    assert(confl != (clause*)0);
    s->stats.conflicts++;
    if (solver_dlevel(s) <= s->root_level) {
        return l_True;
    }

    veci learnt_clause;
    veci_new(&learnt_clause);
    solver_analyze(s, confl, &learnt_clause, lit_Undef);

    if (s->lim < solver_dlevel(s)) {
        int blevel = veci_size(&learnt_clause) > 1 ? s->levels[lit_var(veci_begin(&learnt_clause)[1])] : s->root_level;
        blevel = blevel < s->lim ? s->lim: blevel;
        solver_insertcacheuntil(s, blevel);
        solver_canceluntil(s,blevel);
    } else {
        solver_backtrack(s, solver_dlevel(s)); 
        s->lim = solver_dlevel(s);
    }

    solver_record(s,&learnt_clause);
    act_var_decay(s);
    act_clause_decay(s);

    veci_delete(&learnt_clause);
    return l_False;
}


// conflict resolution based on conflict-directed backjumping
static lbool solver_resolve_conflict_cbj(solver *s, clause *confl)
{
    assert(confl != (clause*)0);
    assert(vecp_size(&s->generated_clauses) == 0);

    clause *c;
    veci learnt_clause;
    veci_new(&learnt_clause);

    while(1) {
        if (confl != 0) {
            s->stats.conflicts++;
            if (solver_dlevel(s) <= s->root_level) {
                veci_delete(&learnt_clause);
                return l_True;
            }

            veci_resize(&learnt_clause,0);
            solver_analyze(s, confl, &learnt_clause, lit_Undef);

            veci *cl = (veci*)malloc(sizeof(veci));
            veci_new(cl);
            for (int i = 0; i < veci_size(&learnt_clause); i++)
                veci_push(cl, veci_begin(&learnt_clause)[i]);
            vecp_push(&s->generated_clauses, (veci*)cl);

            lit p = solver_backtrack(s,solver_dlevel(s));
            s->lim = solver_dlevel(s) < s->lim ? solver_dlevel(s): s->lim;
        } else if (vecp_size(&s->generated_clauses) > 0) {
            veci *cl1 = (veci*)vecp_begin(&s->generated_clauses)[vecp_size(&s->generated_clauses)-1];
            vecp_resize(&s->generated_clauses, vecp_size(&s->generated_clauses)-1);

            lbool asserting = clause_isasserting(s,cl1);// unit literal is placed at the begining.
            c = solver_record_noenqueue(s,cl1);
            act_var_decay(s);
            act_clause_decay(s);

            if (asserting == l_True) {
                const lit unit = *veci_begin(cl1);
                enqueue(s,unit,(clause*)c);

                if ((confl = solver_propagate(s)) != 0) {
                    s->stats.conflicts++;

                    if (solver_dlevel(s) <= s->root_level){
                        veci_delete(cl1); free(cl1);
                        veci_delete(&learnt_clause);
                        return l_True;
                    }

                    veci_resize(&learnt_clause,0);
                    solver_analyze(s, confl, &learnt_clause, unit);
                    //solver_printtrail(s);
                    //printf("learnt:");printlits(veci_begin(&learnt_clause), veci_begin(&learnt_clause)+veci_size(&learnt_clause));printf("\n");
                    assert(veci_begin(&learnt_clause)[0] == lit_neg(unit));

                    veci *cl3 = (veci*)malloc(sizeof(veci));
                    veci_new(cl3);
                    //printf("cl1:");printlits(veci_begin(cl1), veci_begin(cl1)+veci_size(cl1));printf("\n");
                    //printf("cl2:");printlits(veci_begin(&learnt_clause), veci_begin(&learnt_clause)+veci_size(&learnt_clause));printf("\n");
                    perform_resolution(s, cl1, &learnt_clause, cl3);
                    if (veci_size(cl3) == 0) { // if the whole space was exhausted,
                        veci_delete(cl3); free(cl3);
                        veci_delete(cl1); free(cl1);
                        veci_delete(&learnt_clause);
                        return l_True;
                    }
                    //printf("cl3:");printlits(veci_begin(cl3), veci_begin(cl3)+veci_size(cl3));printf("\n\n");

                    vecp_push(&s->generated_clauses, (veci*)cl3);

                    int highest = s->levels[lit_var(*veci_begin(cl3))];
                    lit p = solver_backtrack(s, highest);
                    s->lim = solver_dlevel(s) < s->lim ? solver_dlevel(s): s->lim;
                }
            }
            veci_delete(cl1); free(cl1);
        } else {
            break;
        }
        confl = solver_propagate(s);
    }

    veci_delete(&learnt_clause);
    return l_False;
}


// conflict resolution based on combination of BJ and CBJ
static lbool solver_resolve_conflict_bjcbj(solver *s, clause *confl)
{
    if (s->lim < solver_dlevel(s)) {
        return solver_resolve_conflict_bj(s, confl);
    } else {
        return solver_resolve_conflict_cbj(s, confl);
    }
}


static lbool solver_resolve_conflict(solver *s, clause *confl)
{
#if defined(BT)
#ifdef VERBOSEDEBUG
             //   printf(L_IND"**BT**\n", L_ind);
#endif
    return solver_resolve_conflict_bt(s, confl);
#elif defined(BJ)
#ifdef VERBOSEDEBUG
             //   printf(L_IND"**BJ**\n", L_ind);
#endif
    return solver_resolve_conflict_bj(s, confl);
#elif defined(CBJ)
#ifdef VERBOSEDEBUG
               // printf(L_IND"**CBJ**\n", L_ind);
#endif
    return solver_resolve_conflict_cbj(s, confl);
#else //BJ+CBJ
#ifdef VERBOSEDEBUG
                //printf(L_IND"**BJ+CBJ**\n", L_ind);
#endif
    return solver_resolve_conflict_bjcbj(s, confl);
#endif
}


static lbool solver_search(solver* s, int nof_conflicts, int nof_learnts)
{
    int*    levels          = s->levels;
    int*    sublevels       = s->sublevels;
    double  var_decay       = 0.95;
    double  clause_decay    = 0.999;
    /*double  random_var_freq = 0.02;*/

    /*int     conflictC       = 0;*/

    assert(s->root_level == solver_dlevel(s));
    assert(s->root_level == solver_sublevel(s));
    assert(s->root_level == s->lim);

    lbool*    values  = s->assigns;
    const int nvars   = s->size; 


    s->stats.starts++;
    s->var_decay = (float)(1 / var_decay   );
    s->cla_decay = (float)(1 / clause_decay);

    for (;;){
		if (eflag == 1) return l_False;
        clause* confl = solver_propagate(s);
        if (confl != 0) {
            // CONFLICT
            lbool res = solver_resolve_conflict(s, confl);
            if(res == l_True) 
                return l_True;
        } else {

            // NO CONFLICT
            int next;

            /*if (nof_conflicts >= 0 && conflictC >= nof_conflicts){ // restart is disabled.
                // Reached bound on number of conflicts:
                s->progress_estimate = solver_progress(s);
                solver_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; }*/

            if (solver_dlevel(s) == 0)
                // Simplify the set of problem clauses:
                solver_simplify(s);

            if (nof_learnts >= 0 && vecp_size(&s->learnts) - s->qtail >= nof_learnts)
                // Reduce the set of learnt clauses:
                solver_reducedb(s);

            // New variable decision:
            s->stats.decisions++;
            /*next = order_select(s,(float)random_var_freq);*/

            bool  modelfound = false;

#ifdef LAZY
            for (next = s->nextvar; next < nvars && values[next] != l_Undef; next++) ;

            if (next == nvars) { // model found without cache
                modelfound = true;
                solver_extendobdd(s, obdd_top());
            } else if (s->nextvar < next) {
                unsigned int *vec = vecp_begin(&s->bitvecs)[next-1];
                solver_makecache(s, vec, next-1);
                obdd_t* lookup;
                s->stats.ncachelookup++;
                if ((lookup = (obdd_t*)trie_search(vec, s->cache[next-1])) != NULL) {
                    modelfound = true;
                    s->stats.ncachehits++;
                    solver_extendobdd(s, lookup);
                }
            }
            s->nextvar = next;
#else
            for (next = s->nextvar; next < nvars-1 && values[next] != l_Undef; next++) {
                unsigned int *vec = vecp_begin(&s->bitvecs)[next];
                solver_makecache(s, vec, next);

                obdd_t* lookup;
                s->stats.ncachelookup++;
                if ((lookup = (obdd_t*)trie_search(vec, s->cache[next])) != NULL) {
                    modelfound = true;
                    s->stats.ncachehits++;
                    solver_extendobdd(s, lookup);
                    break;
                }
            }

            if (!modelfound && next == nvars-1 && values[next] != l_Undef)  { // model found without cache.
                modelfound = true;
                solver_extendobdd(s, obdd_top());
            }
            s->nextvar = next;
#endif

            if (modelfound) {
#ifdef VERBOSEDEBUG
                //printf(L_IND"**MODEL**\n", L_ind);
#endif

                if (solver_dlevel(s) <= s->root_level){ // model found without any assumption
                    return l_True;
                }

#ifdef REFRESH
                if (obdd_nnodes() + s->size > s->stats.maxnodes) 
                    solver_refreshobdd(s);
#endif

                solver_backtrack(s, solver_dlevel(s));
                s->lim = solver_dlevel(s);
            } else {
                assume(s,lit_neg(toLit(s->nextvar)));
            }
        }
    }

    return l_Undef; // cannot happen
}

#else
static lbool solver_search(solver* s, int nof_conflicts, int nof_learnts)
{
    int*    levels          = s->levels;
    double  var_decay       = 0.95;
    double  clause_decay    = 0.999;
    /*double  random_var_freq = 0.02;*/ // deleted

    /*int     conflictC       = 0;*/ // deleted
    veci    learnt_clause;

    assert(s->root_level == solver_dlevel(s));

    lbool*    values  = s->assigns;
    const int nvars   = s->size; 


    s->stats.starts++;
    s->var_decay = (float)(1 / var_decay   );
    s->cla_decay = (float)(1 / clause_decay);
    //veci_resize(&s->model,0);
    veci_new(&learnt_clause);

    for (;;){
		if (eflag == 1) return l_False;
        clause* confl = solver_propagate(s);
        if (confl != 0){
            // CONFLICT
            int blevel;
#ifdef VERBOSEDEBUG
            //printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; /*conflictC++;*/ 
            if (solver_dlevel(s) <= s->root_level){
                veci_delete(&learnt_clause);
                return l_True;
            }

            veci_resize(&learnt_clause,0);
            solver_analyze(s, confl, &learnt_clause);
            blevel = veci_size(&learnt_clause) > 1 ? levels[lit_var(veci_begin(&learnt_clause)[1])] : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;
            solver_canceluntil(s,blevel);
            solver_record(s,&learnt_clause);
            act_var_decay(s);
            act_clause_decay(s);
        }else{
            // NO CONFLICT
            int next;

            /*if (nof_conflicts >= 0 && conflictC >= nof_conflicts){ // restart is disabled.
                // Reached bound on number of conflicts:
                s->progress_estimate = solver_progress(s);
                solver_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; }*/

            if (solver_dlevel(s) == 0)
                // Simplify the set of problem clauses:
                solver_simplify(s);

            if (nof_learnts >= 0 && vecp_size(&s->learnts) - s->qtail >= nof_learnts)
                // Reduce the set of learnt clauses:
                solver_reducedb(s);

            // New variable decision:
            s->stats.decisions++;
            /*next = order_select(s,(float)random_var_freq);*/ // deleted

            bool  modelfound = false;

#ifdef LAZY
            for (next = s->nextvar; next < nvars && values[next] != l_Undef; next++) ;

            if (next == nvars) { // model found without cache
                modelfound = true;
                solver_extendobdd(s, obdd_top());
            } else if (s->nextvar < next) {
                unsigned int *vec = vecp_begin(&s->bitvecs)[next-1];
                solver_makecache(s, vec, next-1);
                obdd_t* lookup;
                s->stats.ncachelookup++;
                if ((lookup = (obdd_t*)trie_search(vec, s->cache[next-1])) != NULL) {
                    modelfound = true;
                    s->stats.ncachehits++;
                    solver_extendobdd(s, lookup);
                }
            }
            s->nextvar = next;
#else
            for (next = s->nextvar; next < nvars-1 && values[next] != l_Undef; next++) {
                unsigned int *vec = vecp_begin(&s->bitvecs)[next];
                solver_makecache(s, vec, next);

                obdd_t* lookup;
                s->stats.ncachelookup++;
                if ((lookup = (obdd_t*)trie_search(vec, s->cache[next])) != NULL) {
                    modelfound = true;
                    s->stats.ncachehits++;
                    solver_extendobdd(s, lookup);
                    break;
                }
            }

            if (!modelfound && next == nvars-1 && values[next] != l_Undef)  { // model found without cache.
                modelfound = true;
                solver_extendobdd(s, obdd_top());
            }
            s->nextvar = next;
#endif

            if (modelfound) {
#ifdef VERBOSEDEBUG
              //  printf(L_IND"**MODEL**\n", L_ind);
#endif
                if (solver_dlevel(s) <= s->root_level){ // model found without any assumption
                    veci_delete(&learnt_clause);
                    return l_True;
                }

                veci_resize(&learnt_clause,0);
                for (int i = solver_dlevel(s); i > s->root_level; i--) 
                    veci_push(&learnt_clause, lit_neg(solver_assumedlit(s, i))); // set a blocking clause.
                int blevel = solver_dlevel(s)-1;
#ifdef VERBOSEDEBUG
            //    printf(L_IND"Learnt {", L_ind);
                for (int i = 0; i < veci_size(&learnt_clause); i++) 
              //      printf(" "L_LIT, L_lit(veci_begin(&learnt_clause)[i]));
               // printf(" } at level %d\n", blevel);
#endif

                solver_insertcacheuntil(s, blevel);
                solver_canceluntil(s,blevel); 
                solver_record(s,&learnt_clause); 
                act_var_decay(s);
                act_clause_decay(s);
            } else {
                assume(s,lit_neg(toLit(s->nextvar)));
            }
        }
    }

    return l_Undef; // cannot happen
}

#endif /*NONBLOCKING*/

//=================================================================================================
// External solver functions:

solver* solver_new(void)
{
    solver* s = (solver*)malloc(sizeof(solver));

    // initialize vectors
    vecp_new(&s->clauses);
    vecp_new(&s->learnts);
    vecp_new(&s->bitvecs);
    veci_new(&s->order);
    veci_new(&s->trail_lim);
#ifdef NONBLOCKING
    veci_new(&s->subtrail_lim);
    vecp_new(&s->generated_clauses);
#endif /*NONBLOCKING*/
    veci_new(&s->cachedvars);
    veci_new(&s->tagged);
    veci_new(&s->stack);

    vecp_new(&s->obddpath);

#ifdef NONBLOCKING
    s->out       = NULL;
    s->lim        = 0;
    s->stats.maxnodes  = INT_MAX;
#endif /*NONBLOCKING*/
    s->stats.refreshes = 0;
    s->stats.obddsize  = 0;

    // initialize arrays
    s->wlists    = 0;
    s->activity  = 0;
    s->assigns   = 0;
    s->orderpos  = 0;
    s->reasons   = 0;
    s->levels    = 0;
#ifdef NONBLOCKING
    s->sublevels = 0;
#endif /*NONBLOCKING*/
    s->tags      = 0;
    s->trail     = 0;

    s->stats.clk       = (clock_t)0;

    // fields for obdd construction
    s->nextvar     = 0;
#ifdef CUTSETCACHE
    s->maxcutwidth = 0;
    s->cutwidth    = NULL;
    s->cutsets     = NULL;
#else /*SEPARATORCACHE*/
    s->maxpathwidth= 0;
    s->pathwidth   = NULL;
    s->separators  = NULL;
#endif
    s->cache       = NULL;
    s->root        = NULL;
    s->trail       = NULL;

    s->root         = obdd_node(1, NULL, NULL); 
    obdd_top()->aux = (intptr_t)1;
    obdd_bot()->aux = (intptr_t)0;

    // initialize other vars
    s->size                   = 0;
    s->cap                    = 0;
    s->qhead                  = 0;
    s->qtail                  = 0;
    s->cla_inc                = 1;
    s->cla_decay              = 1;
    s->var_inc                = 1;
    s->var_decay              = 1;
    s->root_level             = 0;
    s->simpdb_assigns         = 0;
    s->simpdb_props           = 0;
    s->random_seed            = 91648253;
    s->progress_estimate      = 0;
    s->binary                 = (clause*)malloc(sizeof(clause) + sizeof(lit)*2);
    s->binary->size_learnt    = (2 << 1);
    s->verbosity              = 0;

    s->stats.starts           = 0;
    s->stats.decisions        = 0;
    s->stats.propagations     = 0;
    s->stats.inspects         = 0;
    s->stats.conflicts        = 0;
    s->stats.clauses          = 0;
    s->stats.clauses_literals = 0;
    s->stats.learnts          = 0;
    s->stats.learnts_literals = 0;
    s->stats.max_literals     = 0;
    s->stats.tot_literals     = 0;

    s->stats.ncachehits       = 0;
    s->stats.ncachelookup     = 0;

    s->stats.tot_solutions  = 0; 
#ifdef GMP
    mpz_init(s->stats.tot_solutions_gmp);
    mpz_set_ui(s->stats.tot_solutions_gmp, 0); 
#endif

    return s;
}


void solver_delete(solver* s)
{
    int i;
    for (i = 0; i < vecp_size(&s->clauses); i++)
        free(vecp_begin(&s->clauses)[i]);

    for (i = 0; i < vecp_size(&s->learnts); i++)
        free(vecp_begin(&s->learnts)[i]);

#ifdef NONBLOCKING
    for (i = 0; i < vecp_size(&s->generated_clauses); i++) {
        veci_delete(vecp_begin(&s->generated_clauses)[i]);
        free(vecp_begin(&s->generated_clauses)[i]);
    }
#endif /*NONBLOCKING*/

    for (i = 0; i < vecp_size(&s->bitvecs); i++)
        free(vecp_begin(&s->bitvecs)[i]);

    // delete vectors
    vecp_delete(&s->clauses);
    vecp_delete(&s->learnts);
    vecp_delete(&s->bitvecs);
    vecp_delete(&s->obddpath);
    veci_delete(&s->order);
    veci_delete(&s->trail_lim);
#ifdef NONBLOCKING
    veci_delete(&s->subtrail_lim);
    vecp_delete(&s->generated_clauses);
#endif /*NONBLOCKING*/
    veci_delete(&s->cachedvars);
    veci_delete(&s->tagged);
    veci_delete(&s->stack);
    free(s->binary);

#ifdef GMP
    mpz_clear(s->stats.tot_solutions_gmp);
#endif

    // delete arrays
    if (s->wlists != 0){
        int i;
        for (i = 0; i < s->size*2; i++)
            vecp_delete(&s->wlists[i]);

        // if one is different from null, all are
        free(s->wlists);
        free(s->activity );
        free(s->assigns  );
        free(s->orderpos );
        free(s->reasons  );
        free(s->levels   );
#ifdef NONBLOCKING
        free(s->sublevels);
#endif /*NONBLOCKING*/
        free(s->trail    );
        free(s->tags     );
    }

#ifdef CUTSETCACHE
    for (int i = 0; i < s->size; i++) {
        free(s->cutsets[i]);
    }
    free(s->cutsets);
    free(s->cutwidth);
#else /*SEPARATORCACHE*/
    for (int i = 0; i < s->size; i++) {
        free(s->separators[i]);
    }
    free(s->separators);
    free(s->pathwidth);
#endif

    for (int i = 0; i < s->size; i++) 
        trie_delete(s->cache[i]);
    trie_finalize();

    free(s);
}


bool solver_addclause(solver* s, lit* begin, lit* end)
{
    lit *i,*j;
    int maxvar;
    lbool* values;
    lit last;

    if (begin == end) return false;

    //printlits(begin,end); printf("\n");
    // insertion sort
    maxvar = lit_var(*begin);
    for (i = begin + 1; i < end; i++){
        lit l = *i;
        maxvar = lit_var(l) > maxvar ? lit_var(l) : maxvar;
        for (j = i; j > begin && *(j-1) > l; j--)
            *j = *(j-1);
        *j = l;
    }
    solver_setnvars(s,maxvar+1);

    //printlits(begin,end); printf("\n");
    values = s->assigns;

    // delete duplicates
    last = lit_Undef;
    for (i = j = begin; i < end; i++){
        //printf("lit: "L_LIT", value = %d\n", L_lit(*i), (lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)]));
        lbool sig = !lit_sign(*i); sig += sig - 1;
        if (*i == lit_neg(last) || sig == values[lit_var(*i)])
            return true;   // tautology
        else if (*i != last && values[lit_var(*i)] == l_Undef)
            last = *j++ = *i;
    }

    //printf("final: "); printlits(begin,j); printf("\n");

    if (j == begin)          // empty clause
        return false;
    else if (j - begin == 1) // unit clause
        return enqueue(s,*begin,(clause*)0);

    // create new clause
    vecp_push(&s->clauses,clause_new(s,begin,j,0));


    s->stats.clauses++;
    s->stats.clauses_literals += j - begin;

    return true;
}


bool   solver_simplify(solver* s)
{
    clause** reasons;
    int type;

    assert(solver_dlevel(s) == 0);

    if (solver_propagate(s) != 0)
        return false;

    if (s->qhead == s->simpdb_assigns || s->simpdb_props > 0)
        return true;

    reasons = s->reasons;
    for (type = 0; type < 2; type++){
        vecp*    cs  = type ? &s->learnts : &s->clauses;
        clause** cls = (clause**)vecp_begin(cs);

        int i, j;
        for (j = i = 0; i < vecp_size(cs); i++){
            if (reasons[lit_var(*clause_begin(cls[i]))] != cls[i] &&
                clause_simplify(s,cls[i]) == l_True) {
#ifdef CUTSETCACHE // original clauses must not be removed from memory because cutset caching is based on clause evaluation.
                if(cs == &s->clauses) clause_remove_nofree(s,cls[i]);
                else                  clause_remove(s,cls[i]);
#else /*SEPARATORCACHE*/
                clause_remove(s,cls[i]);
#endif
            } else
                cls[j++] = cls[i];
        }
        vecp_resize(cs,j);
    }

    s->simpdb_assigns = s->qhead;
    // (shouldn't depend on 'stats' really, but it will do for now)
    s->simpdb_props   = (int)(s->stats.clauses_literals + s->stats.learnts_literals);

    return true;
}


bool   solver_solve(solver* s, lit* begin, lit* end)
{
    double  nof_conflicts = 100;
    double  nof_learnts   = solver_nclauses(s) / 3;
    lbool   status        = l_Undef;
    lbool*  values        = s->assigns;
    lit*    i;

    solver_initcache(s);

    //printf("solve: "); printlits(begin, end); printf("\n");
    /*for (i = begin; i < end; i++){
        switch (lit_sign(*i) ? -values[lit_var(*i)] : values[lit_var(*i)]){
        case 1: // l_True:
            break;
        case 0: // l_Undef
            assume(s, *i);
            if (solver_propagate(s) == NULL)
                break;
            // falltrough
        case -1: // l_False
            solver_canceluntil(s, 0);
            return false;
        }
    }*/

    s->root_level = solver_dlevel(s);
#ifdef NONBLOCKING
    s->lim         = solver_dlevel(s);
    assert(solver_dlevel(s) == solver_sublevel(s));
#endif /*NONBLOCKING*/

    /*if (s->verbosity >= 1){
        printf("==================================[MINISAT]===================================\n");
        printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        printf("==============================================================================\n");
    }*/

    /*if (s->verbosity >= 1){
      /*  printf("==============================[MINISAT_ALL]==========================================\n");
        printf("| Time | Conflicts | Propagations | TOTAL       |            |   LEARNT  | OBDD     |\n");
        printf("|      |           |              | Solutions   | Clauses    |   Clauses | Nodes    |\n");
        printf("=====================================================================================\n");
    } */   

    while (status == l_Undef){
       /* double Ratio = (s->stats.learnts == 0)? 0.0 :
            s->stats.learnts_literals / (double)s->stats.learnts;

        if (s->verbosity >= 1){
            printf("| %9.0f | %7.0f %8.0f | %7.0f %7.0f %8.0f %7.1f | %6.3f %% |\n", 
                (double)s->stats.conflicts,
                (double)s->stats.clauses, 
                (double)s->stats.clauses_literals,
                (double)nof_learnts, 
                (double)s->stats.learnts, 
                (double)s->stats.learnts_literals,
                Ratio,
                s->progress_estimate*100);
            fflush(stdout);
        }*/
        status = solver_search(s,(int)nof_conflicts, (int)nof_learnts);
        //nof_conflicts *= 1.5;
        //nof_learnts   *= 1.1;
    }

    /*if (s->verbosity >= 1) {
        printf("==============================================================================\n");
    }*/

    totalup_stats(s);
    solver_canceluntil(s,0);
    return status != l_False;
}


int solver_nvars(solver* s)
{
    return s->size;
}


int solver_nclauses(solver* s)
{
    return vecp_size(&s->clauses);
}
/*

int solver_nconflicts(solver* s)
{
    return (int)s->stats.conflicts;
}*/

//=================================================================================================
// Sorting functions (sigh):

static inline void selectionsort(void** array, int size, int(*comp)(const void *, const void *))
{
    int     i, j, best_i;
    void*   tmp;

    for (i = 0; i < size-1; i++){
        best_i = i;
        for (j = i+1; j < size; j++){
            if (comp(array[j], array[best_i]) < 0)
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}


static void sortrnd(void** array, int size, int(*comp)(const void *, const void *), double* seed)
{
    if (size <= 15)
        selectionsort(array, size, comp);

    else{
        void*       pivot = array[irand(seed, size)];
        void*       tmp;
        int         i = -1;
        int         j = size;

        for(;;){
            do i++; while(comp(array[i], pivot)<0);
            do j--; while(comp(pivot, array[j])<0);

            if (i >= j) break;

            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }

        sortrnd(array    , i     , comp, seed);
        sortrnd(&array[i], size-i, comp, seed);
    }
}

void sort(void** array, int size, int(*comp)(const void *, const void *))
{
    double seed = 91648253;
    sortrnd(array,size,comp,&seed);
}


//=================================================================================================
//trie
#define IS_EXT(h)   ((uintptr_t)(h)%2 == 1)
#define LEFT(h)     (((st_node*)(((uintptr_t)(h) / 2) * 2))->l)
#define RIGHT(h)    (((st_node*)(((uintptr_t)(h) / 2) * 2))->r)
#define KEY(h)      ((unsigned int*)LEFT(LEFT(h)))
#define VAL(h)      ((uintptr_t)RIGHT(LEFT(h)))


struct trie_node {
    struct  trie_node  *l;
    struct  trie_node  *r;
};

static int        isequal       (unsigned int *k1, unsigned int *k2, int len);
static st_node    *trie_getnode (int len, unsigned int *k, uintptr_t v);
static st_node    *trie_split   (st_node *p, st_node *q, int w);
#ifdef TRIE_REC
static st_node    *trie_insertR (unsigned int *k, int w, int len, uintptr_t v, st_node *h);
static uintptr_t  trie_searchR  (unsigned int *k, int w, int len, st_node *h);
static int        trie_printR   (int c, st_node *h, FILE *out);
#endif

#define FN_INIT_X   (1UL << 10)
#define VECS_INIT_X (1UL << 10)

static trie_t *trielist = NULL;

static st_node**        fn       = NULL;
static uintptr_t        fn_x     = 0;
static uintptr_t        fn_y     = 0;
static uintptr_t        fn_max_x = FN_INIT_X;
static const uintptr_t  fn_max_y = 64;

static unsigned int**   vecs        = NULL;
static uintptr_t        vecs_x      = 0;
static uintptr_t        vecs_y      = 0;
static uintptr_t        vecs_max_x  = VECS_INIT_X;
static const uintptr_t  vecs_max_y  = 64;


/* \brief Setup node management. If tries are already created, they are initialized.
 * \note 
 * - Call pior to any other function calls. 
 * - This can be also used to clear all existing tries, where length of each trie will not be changed.
 */
extern void trie_initialize(void)
{
    if (fn != NULL || vecs != NULL)
        trie_finalize();

    fn_x = 0;
    fn_y = 0;
    fn_max_x = FN_INIT_X;
    fn = (st_node**)malloc(sizeof(st_node*)*fn_max_y);
    ENSURE_TRUE_MSG(fn != NULL, "memory allocation failed");
    for (int i = 0; i < fn_max_y; i++)
        fn[i] = NULL;
    fn[0] = (st_node*)malloc(sizeof(st_node)*fn_max_x);
    ENSURE_TRUE_MSG(fn[0] != NULL, "memory allocation failed");

    vecs_x = 0;
    vecs_y = 0;
    vecs_max_x = VECS_INIT_X;
    vecs = (unsigned int**)malloc(sizeof(unsigned int*)*vecs_max_y);
    ENSURE_TRUE_MSG(vecs != NULL, "memory allocation failed");
    for (int i = 0; i < vecs_max_y; i++)
        vecs[i] = NULL;
    vecs[0] = (unsigned int*)malloc(sizeof(unsigned int)*vecs_max_x);
    ENSURE_TRUE_MSG(vecs[0] != NULL, "memory allocation failed");

    for (trie_t *p = trielist; p != NULL; p = p->nx) {
        p->root = (st_node*)((uintptr_t)NULL + 1);
    }
}


/* \brief Finalize node management.
 * \note
 * - trie nodes and bit vectors are cleared.
 * - trie_t data structure is not cleared for a later use!
 * - Call trie_delete to destroy trie_t data structure.
 */
extern void trie_finalize(void)
{
    if (fn != NULL) {
        for (int i = 0; i < fn_max_y; i++) {
            if (fn[i] != NULL) {
                free(fn[i]);
                fn[i] = NULL;
            }
        }
        free(fn);
        fn = NULL;
    }


    if (vecs != NULL) {
        for (int i = 0; i < vecs_max_y; i++) {
            if (vecs[i] != NULL) {
                free(vecs[i]);
                vecs[i] = NULL;
            }
        }
        free(vecs);
        vecs = NULL;
    }
}


static inline st_node *get_freenode(void)
{
    if (fn_x >= fn_max_x) {
        fn_max_x *= 2;
        fn_x = 0;
        fn_y++;
        assert(fn_y < fn_max_y);
        fn[fn_y] = (st_node*)malloc(sizeof(st_node)*fn_max_x);
        ENSURE_TRUE_MSG(fn[fn_y] != NULL, "memory allocation failed");
    }

    return &(fn[fn_y][fn_x++]);
}


static inline unsigned int *get_freevec(int n)
{
    if (vecs_x+n >= vecs_max_x) {
        vecs_max_x *= 2;
        vecs_x = 0;
        vecs_y++;
        assert(vecs_y < vecs_max_y);
        vecs[vecs_y] = (unsigned int*)malloc(sizeof(unsigned int)*vecs_max_x);
        ENSURE_TRUE_MSG(vecs[vecs_y] != NULL, "memory allocation failed");
    }

    unsigned int *t = &(vecs[vecs_y][vecs_x]);
    vecs_x += n;
    return t;
}


/*  \brief  Decide if k1 == k2.
 *  \param  k1    Bitvector
 *  \param  k2    Bitvector
 *  \param  len   Bit length
 *  \return 1 if equal; otherwise, 0.
 */
static int isequal(unsigned int *k1, unsigned int *k2, int len)
{
    const int nwords = GET_NWORDS(len);

    for (int i = 0; i < nwords; i++) {
        if (k1[i] != k2[i]) 
            return 0;
    }

    return 1; 
}


/*  \brief  Get a trie node.
 *  \param  len length of a bitvector
 *  \param  k   Bitvector(key)
 *  \param  v   Value associated with the bitvector.
 *  \return Pointer to an obtained trie node.
 */
static st_node *trie_getnode(int len, unsigned int *k, uintptr_t v)
{
    st_node *p = get_freenode();
    st_node *t = get_freenode();

    p->l = (st_node*)((uintptr_t)(t)+1); // left child holds a key-value pair.
    p->r = (st_node*)1;

    if(len > 0) {
        const int nwords  = GET_NWORDS(len);
        unsigned int *vec = get_freevec(nwords);
        for(int j = 0; j < nwords; j++) 
            vec[j] = k[j];
        t->l = (st_node*)(vec);
    } else {
        t->l = (st_node*)NULL;
    }
    t->r = (st_node*)v;

    return p;
}


/*  \brief  Split a trie so that it contains p and q.
 *  \param  p   Trie node
 *  \param  q   Trie node
 *  \param  w   Position in a bitvector
 */
static st_node *trie_split(st_node *p, st_node *q, int w)
#ifdef TRIE_REC
{
    st_node *t = trie_getnode(0, (unsigned int*)NULL, (uintptr_t)NULL);
    switch (DIGIT(KEY(p), w)*2 + DIGIT(KEY(q), w)) {
        case 0:  t->l = trie_split(p,q,w+1); break;
        case 1:  t->l = p; t->r =q;          break;
        case 2:  t->l = q; t->r =p;          break;
        case 3:  t->r = trie_split(p,q,w+1); break;
    }
    return t;
}
#else /*TRIE_ITERATION*/
{
    st_node tmp;
    st_node *prev = &tmp;
    int sgn = 0;

    for (int i = w; 1; i++) {
        st_node *t = trie_getnode(0, (unsigned int*)NULL, (uintptr_t)NULL);
        if (sgn)
            prev->l = t;
        else
            prev->r = t;
        prev = t;

        switch (DIGIT(KEY(p), i)*2 + DIGIT(KEY(q), i)) {
            case 0:  sgn  = 1;              break;
            case 1:  t->l = p; t->r = q;    return tmp.r;
            case 2:  t->l = q; t->r = p;    return tmp.r;
            case 3:  sgn  = 0;              break;
        }
    }

    return tmp.r;
}
#endif


/* \brief   Create an empty trie. 
 * \param   n   Length of a bitvector
 * \return  Created trie.
 * \note Make sure that trie_initialize is done.
 */
trie_t *trie_create(int n)
{
    trie_t *t = (trie_t*)malloc(sizeof(trie_t));
    ENSURE_TRUE_MSG(t != NULL, "memory allocation failed");

    t->root = (st_node*)((uintptr_t)NULL + 1);
    t->len  = n;
    if (trielist != NULL)
        trielist->pv = t; 
    t->nx = (trie_t*)trielist;
    t->pv = NULL;
    trielist = t;

    return t;
}


/* \brief delete a trie.
 * \note to finish the usage of trie completely, also call trie_finalize.
 */
void trie_delete(trie_t *t)
{
    if (t != NULL) {
        if (t->pv != NULL)
            t->pv->nx = t->nx;
        else
            trielist = t->nx;

        if (t->nx != NULL)
            t->nx->pv = t->pv;

        free(t);
    }
}


/*  \brief  Insert a new node in a trie.
 *  \param  k   Bitvector(key)
 *  \param  v   Value associated with the bitvector
 *  \param  t   Trie
 */
void trie_insert(unsigned int *k, uintptr_t v, trie_t *t)
{
  //printf("<");
  //for(int i = 0; i < t->len; i++) {
  //  printf("%d", DIGIT(k, i));
  //}
  //printf("\n");fflush(stdout);

#ifdef TRIE_REC
    t->root = trie_insertR(k, 0, t->len, v, t->root);

#else /*TRIE_ITERATION*/
    st_node *h = t->root;
    int len = t->len;

    st_node tmp;
    tmp.r = t->root;
    st_node *prev  = &tmp;
    int sgn = 0;

    for (int w = 0; 1; w++) {
        if (IS_EXT(h)) {
            if(sgn)
                prev->l = trie_getnode(len, k, v);
            else
                prev->r = trie_getnode(len, k, v);
            break;
        }

        if (IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h))) {
            if (sgn)
                prev->l = (!isequal(k, KEY(h),len))? trie_split(trie_getnode(len, k,v), h, w): h;
            else
                prev->r = (!isequal(k, KEY(h),len))? trie_split(trie_getnode(len, k,v), h, w): h;
            break;
        }

        if (sgn)
            prev->l = h;
        else
            prev->r = h;

        prev = h;
        sgn  = (DIGIT(k, w) == 0);
        h    = sgn? LEFT(h): RIGHT(h);
    }

    t->root = tmp.r;
#endif
}


#ifdef TRIE_REC
static st_node *trie_insertR(unsigned int *k, int w, int len, uintptr_t v, st_node *h)
{
    if (IS_EXT(h))
        return trie_getnode(len, k, v);

    if (IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h))) {
        if (!isequal(k, KEY(h), len))  
            return trie_split(trie_getnode(len, k,v), h, w);
        else
            return h;
    }

    if (DIGIT(k, w) == 0)  
        h->l = trie_insertR(k, w+1, len, v, LEFT(h));
    else
        h->r = trie_insertR(k, w+1, len, v, RIGHT(h));

  return h;
}
#endif

/*  \brief  Search a node with a specified key.
 *  \param  k   Bitvector(key)
 *  \param  t   Trie
 *  \return Associated value if a node is found; otherwise, (uintptr_t)NULL.
 */
uintptr_t trie_search(unsigned int *k, trie_t *t)
{
  //printf("?");
  //for(int i = 0; i < t->len; i++) {
  //  printf("%d", DIGIT(k,i));
  //}
  //printf("\n");fflush(stdout);

#ifdef TRIE_REC
  return trie_searchR(k, 0, t->len, t->root);

#else /*TRIE_ITERATION*/
    st_node *h = t->root;

    for (int w = 0; 1; w++) {
        if (IS_EXT(h))
            return (uintptr_t)NULL;

        if (IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h)))
            return isequal(k, KEY(h), t->len)? VAL(h): (uintptr_t)NULL;

        h = DIGIT(k, w) == 0? LEFT(h): RIGHT(h);
    }
#endif
}

#ifdef TRIE_REC
static uintptr_t trie_searchR(unsigned int *k, int w, int len, st_node *h)
{
    if (IS_EXT(h))
        return (uintptr_t)NULL;

    if (IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h)))
        return isequal(k, KEY(h), len)? VAL(h): (uintptr_t)NULL;

    if (DIGIT(k,w) == 0)
        return trie_searchR(k, w+1, len, LEFT(h));
    else
        return trie_searchR(k, w+1, len, RIGHT(h));
}
#endif


#ifdef TRIE_REC
/*  \brief  Print a trie structure as a dot format.
 *  \param  t   Trie
 *  \param  out File pointer
 */
void trie_print(trie_t *t, FILE *out)
{
    fprintf(out, "digraph trie {\n");
    trie_printR(1, t->root, out); 
    fprintf(out, "}\n");
}

static int trie_printR(int c, st_node *h, FILE *out)
{
    if (IS_EXT(h))
        return c;

    if (IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h))) {
        fprintf(out, "%d [shape=circle];\n", c);
        return c+1;
    } else if (IS_EXT(LEFT(h)) && !IS_EXT(RIGHT(h))) {
        int r = trie_printR(c, RIGHT(h), out);
        fprintf(out, "%d [shape=point];\n", r);
        fprintf(out, "%d -> %d;\n", r, r-1);
        return r+1;
    } else if (!IS_EXT(LEFT(h)) && IS_EXT(RIGHT(h))) {
        int l = trie_printR(c, LEFT(h), out);
        fprintf(out, "%d [shape=point];\n", l);
        fprintf(out, "%d -> %d [style=dotted];\n", l, l-1);
        return l+1;
    } else {
        int l = trie_printR(c, LEFT(h), out);
        int r = trie_printR(l, RIGHT(h), out);
        fprintf(out, "%d [shape=point];\n", r);
        fprintf(out, "%d -> %d [style=dotted];\n", r, l-1);
        fprintf(out, "%d -> %d;\n", r, r-1);
        return r+1;
    }
}
#endif





//=================================================================================================
// Helpers:

#ifdef REDUCTION
DdManager *dd_mgr = NULL; //!< BDD/ZDD manager for CUDD
#endif

// Reads an input stream to end-of-file and returns the result as a 'char*' terminated by '\0'
// (dynamic allocation in case 'in' is standard input).
//
char* readFile(FILE *  in)
{
    char*   data = malloc(65536);
    int     cap  = 65536;
    int     size = 0;

    while (!feof(in)){
        if (size == cap){
            cap *= 2;
            data = realloc(data, cap); }
        size += fread(&data[size], 1, 65536, in);
    }
    data = realloc(data, size+1);
    data[size] = '\0';

    return data;
}

//static inline double cpuTime(void) {
//    struct rusage ru;
//    getrusage(RUSAGE_SELF, &ru);
//    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }


//=================================================================================================
// DIMACS Parser:


static inline void skipWhitespace(char** in) {
    while ((**in >= 9 && **in <= 13) || **in == 32)
        (*in)++; }

static inline void skipLine(char** in) {
    for (;;){
        if (**in == 0) return;
        if (**in == '\n') { (*in)++; return; }
        (*in)++; } }

static inline int parseInt(char** in) {
    int     val = 0;
    int    _neg = 0;
    skipWhitespace(in);
    if      (**in == '-') _neg = 1, (*in)++;
    else if (**in == '+') (*in)++;
    if (**in < '0' || **in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", **in), exit(1);
    while (**in >= '0' && **in <= '9')
        val = val*10 + (**in - '0'),
        (*in)++;
    return _neg ? -val : val; }

static void readClause(char** in, solver* s, veci* lits) {
    int parsed_lit, var;
    veci_resize(lits,0);
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        veci_push(lits, (parsed_lit > 0 ? toLit(var) : lit_neg(toLit(var))));
    }
}

static lbool parse_DIMACS_main(char* in, solver* s) {
    veci lits;
    veci_new(&lits);

    for (;;){
        skipWhitespace(&in);
        if (*in == 0)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(&in);
        else{
            lit* begin;
            readClause(&in, s, &lits);
            begin = veci_begin(&lits);
            if (!solver_addclause(s, begin, begin+veci_size(&lits))){
                veci_delete(&lits);
                return l_False;
            }
        }
    }
    veci_delete(&lits);
    return solver_simplify(s);
}


// Inserts problem into solver. Returns FALSE upon immediate conflict.
//
static lbool parse_DIMACS(char * in, solver* s) {
    lbool ret  = parse_DIMACS_main(in, s);
   
    return ret; }


//=================================================================================================


void printStats(stats* stats, int cpu_time, bool interrupted)
{
    double Time    = (float)(cpu_time)/(float)(CLOCKS_PER_SEC);
    /*printf("restarts          : %12llu\n", stats->starts);
    printf("conflicts         : %12.0f           (%9.0f / sec      )\n",  (double)stats->conflicts   , (double)stats->conflicts   /Time);
    printf("decisions         : %12.0f           (%9.0f / sec      )\n",  (double)stats->decisions   , (double)stats->decisions   /Time);
    printf("propagations      : %12.0f           (%9.0f / sec      )\n",  (double)stats->propagations, (double)stats->propagations/Time);
    printf("inspects          : %12.0f           (%9.0f / sec      )\n",  (double)stats->inspects    , (double)stats->inspects    /Time);
    printf("conflict literals : %12.0f           (%9.2f %% deleted  )\n", (double)stats->tot_literals, (double)(stats->max_literals - stats->tot_literals) * 100.0 / (double)stats->max_literals);
    printf("cpu time (solve)  : %12.2f sec\t", Time);
    printf("\n");

    printf("refreshes         : %12llu\n", stats->refreshes);
    printf("|obdd|            : %12llu\n", stats->obddsize);

    printf("cache hits        : %12llu\n",   stats->ncachehits);
    printf("cache lookup      : %12llu\n",   stats->ncachelookup);

#ifdef CUTSETCACHE 
    printf("cache type        : cutset\n");
#else
    printf("cache type        : separator\n");
#endif

#ifdef LAZY
    printf("cache frequency   : lazy\n");
#else
    printf("cache frequency   : original\n");
#endif

#ifdef NONBLOCKING
    printf("minisat_all type  : non-blocking\n");
#if defined(BT)
    printf("backtrack method  : bt\n");
#elif defined(BJ)
    printf("backtrack method  : bj\n");
#elif defined(CBJ)
    printf("backtrack method  : cbj\n");
#else
    printf("backtrack method  : bj+cbj\n");
#endif
#ifdef DLEVEL
    printf("1UIP              : dlevel\n");
#else
    printf("1UIP              : sublevel\n");
#endif
#else
    printf("minisat_all type  : blocking\n");
#endif

#ifdef GMP
    printf("gmp               : enabled\n");
    printf("SAT (full)        : ");
    mpz_out_str(stdout, 10, stats->tot_solutions_gmp);
    if (interrupted)
        printf("+");
    printf("\n");
#else
    printf("gmp               : disabled\n");
    printf("SAT (full)        : %12ju", stats->tot_solutions);
    if (stats->tot_solutions >= INTPTR_MAX || interrupted)
        printf("+");
    printf("\n");
#endif
*/
}

volatile sig_atomic_t eflag = 0;
static void SIGINT_handler(int signum)
{
	eflag = 1;
}

//=================================================================================================

static inline void PRINT_USAGE(char *p)
{
    fprintf(stderr, "Usage:\t%s [options] input-file [output-file]\n", (p));
#ifdef NONBLOCKING
#ifdef REFRESH
    fprintf(stderr, "-n<int>\tmaximum number of obdd nodes: if exceeded, obdd is refreshed\n");
#endif
#endif
}


void printmatrix (struct list* l,int n)
{
	
	if(l->next!=NULL)
	{
		printf("\n");
		for (int i=0;i<n;i++)
		{
			printf("%d ",l->value[i]);
		}
		printmatrix(l->next,n);
	}
	return;
}


struct list* solve(char* argv)
{
    solver* s = solver_new();
    lbool   st;
    char *  in;
    FILE *  out;
    s->stats.clk = clock();
    char *outfile = "out";


    int  lim, span, maxnodes;
  
    /*** RECEIVE INPUTS ***/  
    /*for (int i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
                case 'n':
#ifdef NONBLOCKING
#ifdef REFRESH
                    maxnodes = atoi(argv[i]+2);
                    if (maxnodes <= 0) {
                        PRINT_USAGE(argv[0]); return  0;  
                    }
                    s->stats.maxnodes = maxnodes;
#endif
#endif
                    break;
                case '?': case 'h': default:
                    PRINT_USAGE(argv[0]); return  0;  
            }   
            
        }
    }*/

    in = argv;
    if (outfile != NULL) {
        out = fopen(outfile, "wb");
        /*if (out == NULL)
            fprintf(stderr, "ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : outfile), exit(1);*/
#ifdef NONBLOCKING
        /*else s->out = out;*/
#endif
    } else {
        out = NULL;
    }


    st = parse_DIMACS(in, s);
    //printf(in);
    if (st == l_False){
        solver_delete(s);
        printf("Trivial problem\nUNSATISFIABLE\n");
        exit(20);
    }

    s->verbosity = 0;
    if (signal(SIGINT, SIGINT_handler) == SIG_ERR) {
        fprintf(stderr, "ERROR! Cound not set signal");
        exit(1);
    }

    st = solver_solve(s,0,0);

   // printf("variables         : %12d\n",   s->size);
#ifdef CUTSETCACHE
    //printf("cutwidth          : %12d\n",   s->maxcutwidth);
#else
//    printf("pathwidth         : %12d\n",   s->maxpathwidth);
#endif
	if (eflag == 1) {
    	printf("\n"); printf("*** INTERRUPTED ***\n");
    	//printStats(&s->stats, clock() - s->stats.clk, true);
    	printf("\n"); printf("*** INTERRUPTED ***\n");
	} else {
    	//printStats(&s->stats, clock() - s->stats.clk, false);
	}
     
      int *array = (int *)malloc((s->size) * sizeof(int*));
      struct list* lsol=new_list(array, NULL);

      long int ns=obdd_decompose(out, s->size, s->root,lsol);
      //printmatrix(lsol,s->size);

#ifdef REDUCTION
    if (s->stats.refreshes == 0) { // perform reduction if obdd has not been refreshed.
        bdd_init(s->size,0);
        clock_t starttime_reduce = clock();
        bddp  f = bdd_reduce(s->root);
        clock_t endtime_reduce = clock();
        //printf("cpu time (reduce) : %12.2f sec\n", (float)(endtime_reduce - starttime_reduce)/(float)(CLOCKS_PER_SEC));
        //printf("|bdd|             : %12ju\n",  bdd_size(f));
    }
#endif
    solver_delete(s);

    int **matrice= (int **)malloc(1 * sizeof(int**));
    matrice[0]=(int *)malloc(1 * sizeof(int*));
    matrice[0][0]=1;
    lsol->nsol=ns;
   // printf("%d\n",matrice[0][0]);
    return lsol;
}





































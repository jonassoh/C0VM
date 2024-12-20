/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2024                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

void push_int(c0v_stack_t S, int32_t i)
{
  c0v_push(S, (int2val(i)));
}

void pop_ptr(c0v_stack_t S)
{
  val2ptr(c0v_pop(S));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool->code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xmalloc(sizeof(c0_value) * bc0->function_pool->num_vars);   
  /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

  #ifdef DEBUG
      /* You can add extra debugging information here */
      fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
              P[pc], c0v_stack_size(S), pc);
      c0v_stack_print(S);
  #endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP:
      pc++;
      c0_value v1 = c0v_pop(S);
      //if empty raise error
      c0_value v2 = c0v_pop(S);
      c0v_push(S,v1);
      c0v_push(S,v2);
      break;

    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      pc++;
      c0_value retval = c0v_pop(S);
      ASSERT(c0v_stack_empty(S));
      // Another way to print only in DEBUG mode
      
      // Free everything before returning from the execute function!
      c0v_stack_free(S);
      free(V);
      if (!stack_empty(callStack)) {
        frame* orig = (frame*) pop(callStack);
        S = orig->S;
        pc = orig->pc;
        P = orig->P;
        V = orig->V;
        free(orig);
        // IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", val2int(retval)));
        c0v_push(S, retval);
      }
      else {
        stack_free(callStack, NULL);
        return val2int(retval);
      }
      break;
    }


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x+y);
      break;
    }

    case ISUB: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x-y);
      break;
    }

    case IMUL: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x*y);
      break;
    }

    case IDIV: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      if (y == 0) c0_arith_error("divide by 0"); //0 exception
      if (x == INT_MIN && y == -1) c0_arith_error("divide INT_MIN by -1"); //int_min exception
      push_int(S, x/y);
      break;
    }

    case IREM: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      if (y == 0) c0_arith_error("modulate by 0"); //0 exception
      if (x == INT_MIN && y == -1) c0_arith_error("divide INT_MIN by -1"); //int_min exception
      push_int(S, x%y);
      break;
    }

    case IAND: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x&y);
      break;
    }

    case IOR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x|y);
      break;
    }

    case IXOR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      push_int(S, x^y);
      break;
    }

    case ISHR: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      if (y < 0 || y >= 32) c0_arith_error("rshift out of range"); 
      //can only shift by [0,32)
      push_int(S, x>>y);
      break;
    }

    case ISHL: {
      pc++;
      int32_t y = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      int32_t x = val2int(c0v_pop(S));
      if (y < 0 || y >= 32) c0_arith_error("lshift out of range"); 
      //can only shift by [0,32)
      push_int(S, x<<y);
      break;
    }


    /* Pushing constants */

    case BIPUSH: {
      pc++;
      ubyte x = P[pc];
      pc++;
      int32_t b = (int32_t) ((x << 24) >> 24);
      push_int(S,(int32_t) b);
      break;
    }

    case ILDC: {
      pc++;
      ubyte c1 = P[pc];
      pc++;
      ubyte c2 = P[pc];
      pc++;
      int32_t i = (int32_t) ((c1<<8) | c2);
      int32_t x = bc0->int_pool[i];
      push_int(S,x);
      break;
    }

    case ALDC: {
      pc++;
      ubyte c1 = P[pc];
      pc++;
      ubyte c2 = P[pc];
      pc++;
      int32_t i = (int32_t) ((c1<<8) | c2);
      char *a = &(bc0->string_pool [i]);
      c0v_push(S,ptr2val((a)));
      break;
    }

    case ACONST_NULL: {
      pc++;
      c0_value null = ptr2val(NULL);
      c0v_push(S,null);
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      pc++;
      ubyte i = P[pc];
      pc++;
      c0_value v = V[i];
      //if V[i] not initialized, raise error?
      c0v_push(S,v);
      break;
    }

    case VSTORE: {
      pc++;
      ubyte i = P[pc];
      pc++;
      c0_value v = c0v_pop(S);
      //if V[i] not initialized, raise error?
      V[i] = v;
      break;
    }


    /* Assertions and errors */

    case ATHROW: {
      pc++;
      void* a = val2ptr(c0v_pop(S));
      c0_user_error((char*) a);
      break;
    }

    case ASSERT: {
      pc++;
      void* a = val2ptr(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value x = c0v_pop(S);
      if ((val2int)(x) == 0) c0_assertion_failure((char*) a);
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc++;
      break;
    }

    case IF_CMPEQ: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value v1 = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value v2 = c0v_pop(S);
      pc -=2; 
      if (val_equal(v1, v2)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case IF_CMPNE: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value v1 = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value v2 = c0v_pop(S);
      pc -=2;
      if (!val_equal(v1, v2)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case IF_ICMPLT: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value y = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value x = c0v_pop(S);
      pc -=2;
      if (val2int(x) < val2int(y)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case IF_ICMPGE: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value y = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value x = c0v_pop(S);
      pc -=2;
      if (val2int(x) >= val2int(y)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case IF_ICMPGT: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value y = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value x = c0v_pop(S);
      pc -=2;
      if (val2int(x) > val2int(y)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case IF_ICMPLE: {
      pc++;
      int16_t o1 = P[pc];
      pc++;
      int16_t o2 = P[pc];
      c0_value y = c0v_pop(S);
      if (c0v_stack_empty(S)) c0_memory_error("not enough elems in stack");
      c0_value x = c0v_pop(S);
      pc -=2;
      if (val2int(x) <= val2int(y)) pc += ((o1<<8)|o2);
      else pc+= 3;
      break;
    }

    case GOTO: {
      ubyte o1 = P[pc + 1];
      //int16_t o1 = (int16_t) ((b1 << 24) >> 24);
      ubyte o2 = P[pc + 2];
      //int16_t o2 = (int16_t) ((b2 << 24) >> 24);
      pc += (int16_t)((o1<<8)|o2);
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      uint16_t c1 = P[pc + 1];
      uint16_t c2 = P[pc + 2];
      // pc += 3;
      frame* f = (frame*) xmalloc(sizeof(struct frame_info));
      f->S = S;
      f->P = P;
      f->pc = pc + 3;
      f->V = V;
      push(callStack, (void*)f);
      V = xmalloc(sizeof(c0_value) * (bc0->function_pool[(c1<<8)|c2].num_vars));
      uint16_t n = bc0->function_pool[(c1<<8)|c2].num_args;
      for (uint16_t i = 0; i < n; i++) {
        V[n - 1 - i] = c0v_pop(S);  
      }
      S = c0v_stack_new();
      P = bc0->function_pool[(c1<<8)|c2].code;
      pc = 0;
      break;
    }

    case INVOKENATIVE: {
      ubyte c1 = P[pc + 1];
      ubyte c2 = P[pc + 2];
      pc += 3;
      uint16_t n = bc0->native_pool[(c1<<8)|c2].num_args;
      c0_value *vars = xcalloc(n, sizeof(c0_value));
      for(uint16_t i = 0; i < n; i++) {
        vars[n - 1 - i] = c0v_pop(S);
      }
      uint16_t i = bc0->native_pool[(c1<<8)|c2].function_table_index;
      c0_value res = (*native_function_table[i]) (vars);
      c0v_push(S, res);
      free(vars);
      break;
    }


    /* Memory allocation and access operations: */

    case NEW: {
      pc++;
      ubyte s = P[pc];
      pc++;
      ubyte *a = xcalloc(s, sizeof(ubyte));
      c0v_push(S,ptr2val(a));
      break;
    }

    case IMLOAD: {
      pc++;
      int32_t *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("a is NULL");
      c0v_push(S, int2val(*a));
      break;
    }

    case IMSTORE: {
      pc++;
      int32_t x = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("Invalid stack elems");
      int32_t *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("8a is NULL");
      *a = x;
      break;
    }

    case AMLOAD: {
      pc++;
      void **a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("7a is NULL");
      void *b = *a;
      c0v_push(S, ptr2val(b));
      break;
    }

    case AMSTORE: {
      pc++;
      void *b = val2ptr(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("Invalid stack elems");
      void **a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("6a is NULL");
      *a = b;
      break;
    }

    case CMLOAD: {
      pc++;
      void *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("5a is NULL");
      int32_t x = *(int32_t*)(a);
      c0v_push(S, int2val(x));
      break;
    }

    case CMSTORE: {
      pc++;
      int32_t x = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("Invalid stack elems");
      void *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("4a is NULL");
      *(char*)a = (char) (x & 0x7f);
      break;
    }

    case AADDF: {
      pc++;
      size_t f = P[pc];
      pc++;
      ubyte *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("3a is NULL");
      c0v_push (S, ptr2val(a + f));
      break;
    }


    /* Array operations: */

    case NEWARRAY: {
      pc++;
      int32_t s = P[pc];
      pc++;
      int32_t n = val2int(c0v_pop(S));
      if (n < 0) c0_memory_error("invalid len");
      if (n == 0) {
        c0v_push(S, ptr2val(NULL));
        break;
      }
      c0_array *a = xcalloc(1, sizeof(c0_array));
      a->count = n;
      a->elt_size = s;
      if (s == 0) c0_memory_error("0 sized elems");
      c0_value *array = xcalloc((n*s), sizeof(ubyte));
      a->elems = array;
      c0v_push(S, ptr2val(a));
      break;
    }

    case ARRAYLENGTH: {
      pc++;
      c0_array *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("2a is NULL");
      c0v_push(S, int2val(a->count));
      break;
    }

    case AADDS: {
      pc++;
      int32_t i = val2int(c0v_pop(S));
      if (c0v_stack_empty(S)) c0_memory_error("Invalid stack elems");
      c0_array *a = val2ptr(c0v_pop(S));
      if (a == NULL) c0_memory_error("1a is NULL");
      uint32_t test = (uint32_t) i;
      if (test >= a->count || i < 0) c0_memory_error("Invalid index");
      ubyte *arr = a->elems;
      c0v_push(S, ptr2val(arr + ((a->elt_size) * i)));
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}

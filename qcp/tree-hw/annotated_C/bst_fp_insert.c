#include "verification_stdlib.h"
#include "bst_fp_def.h"

struct tree * malloc_tree_node()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return -> key)) *
             undef_data_at(&(__return -> value)) *
             undef_data_at(&(__return -> left)) *
             undef_data_at(&(__return -> right)) *
             undef_data_at(&(__return -> father))
   */;

void insert(struct tree **b, int x, int value)
{
  struct tree * fa = (void *) 0;
  while (1) {
    if (* b == (void *)0) {
      * b = malloc_tree_node();
      (* b) -> key = x;
      (* b) -> value = value;
      (* b) -> left = (void *)0;
      (* b) -> right = (void *)0;
      (* b) -> father = fa;
      return;
    } else {
      if (x < (* b) -> key) {
        fa = * b;
        b = &((* b) -> left);
      } else if ((* b) -> key < x) {
        fa = * b;
        b = &((* b) -> right);
      } else {
        (* b) -> value = value;
        return;
      }
    }
  }
}


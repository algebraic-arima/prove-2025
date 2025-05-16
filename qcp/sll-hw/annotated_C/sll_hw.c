#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"


void tranverse (struct list * p)
{
  struct list * q = p;
  while (q) {
    q = q->next;
  }
  return;
}

int list_max(struct list * p)
{
  struct list * q = p;
  int n = 0;
  while (q) {
    if (q->data > n) {
      n = q->data;
    }
    q = q->next;
  }
  return n;
}

int no_zero (struct list * p)
{
  struct list * q = p;
  while (q) {
    if (q->data == 0) {
      return 1;
    }
    q = q->next;
  }
  return 0;
}
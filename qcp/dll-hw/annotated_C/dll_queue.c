#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_queue_def.h"

struct list * malloc_list_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             data_at(&(__return -> next), 0) *
             data_at(&(__return -> prev), 0) *
             data_at(&(__return -> data), 0)
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require exists x y z, p -> next == x && p -> prev == y && 
             p -> data == z && emp
      Ensure emp
   */
  ;

void enqueue(struct queue * q, int x)
{
  struct list * p = malloc_list_cell();
  p -> data = x;
  if (q -> head == (void *)0) {
    q -> head = p;
    q -> tail = p;
    p -> next = (void *)0;
    p -> prev = (void *)0;
  }
  else {
    q -> tail -> next = p;
    p -> prev = q -> tail;
    q -> tail = p;
    p -> next = (void *)0;
  }
}

int dequeue(struct queue * q)
{
  struct list * p = q -> head;
  int x0 = p -> data;
  q -> head = p -> next;
  free_list_cell(p);
  if (q -> head == (void *)0) {
    q -> tail = (void *)0;
  }
  else {
    q -> head -> prev = (void *)0;
  }
  return x0;
}

#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct list* malloc_dlist(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0 && __return -> prev == 0
*/;

void free_dlist(struct list * x)
/*@ With d n p
    Require x -> data == d && x -> next == n && x -> prev == p
    Ensure emp
*/;

struct list * dll_copy(struct list * x)
/*@ Require dlistrep_shape(x, 0)
    Ensure  dlistrep_shape(__return, 0) * dlistrep_shape(x, 0)
 */
{
    struct list *y, *p, *t;
    y = malloc_dlist(0);
    t = y;
    p = x;
    /*@ Inv exists p_prev, 
            t != 0 && t -> next == 0 && t -> data == 0 && dllseg_shape(x@pre,0, p_prev,p) * dlistrep_shape(p, p_prev) * dllseg_shape(y, 0, t->prev, t) */
    while (p) {
      t -> data = p -> data;
      t -> next = malloc_dlist(0);
      t -> next -> prev = t;
      p = p -> next;
      t = t -> next;
    }
    return y;
}

void dll_free(struct list * x)
/*@ Require dlistrep_shape(x, 0)
    Ensure emp
 */
{
    struct list *y;
    /*@ Inv exists prev, dlistrep_shape(x, prev) */
    while (x) {
      y = x -> next;
      free_dlist(x);
      x = y;
    }
}

struct list *reverse(struct list *p)
/*@ Require dlistrep_shape(p, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ Inv dlistrep_shape(w, v) *
        dlistrep_shape(v, w)
     */
    while (v) {
        t = v->next;
        v->next = w;
        v->prev = t;
        w = v;
        v = t;
    }
    return w;
}

struct list * append(struct list * x, struct list * y)
/*@ Require dlistrep_shape(x, 0) * dlistrep_shape(y, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ Inv exists v, t->data == v &&
            u == t->next && t != 0 &&
            dlistrep_shape(u, t) *
            dllseg_shape(x@pre, 0, t->prev, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        if (y) {
            y->prev = t;
        }
        return x;
    }
}

struct list *iter(struct list *l)
/*@ 
    Require dlistrep_shape(l, 0)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *p;
    p = l;
    /*@ Inv exists p_prev,
          dllseg_shape(l@pre, 0, p_prev, p) *
          dlistrep_shape(p, p_prev)
     */
    while (p) {
        p = p->next;
    }
    return l;
}

struct list *iter_back(struct list *l, struct list *head)
/*@ With l_prev
	  Require head != 0 && dllseg_shape(head, 0, l_prev, l) * dlistrep_shape(l, l_prev)
    Ensure  dlistrep_shape(__return, 0)
 */
{
    struct list *p;
    if (l == 0) {
      return head;
    }
  	else {
    	p = l;
      /*@ Inv exists v, p != 0 && p->data == v && dllseg_shape(head@pre, 0, p->prev, p) * dlistrep_shape(p->next , p)*/
    	while (p != head) {
      	  p = p -> prev; 
      }
    }
    return p;
}
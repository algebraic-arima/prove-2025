#include "ast.h"

/*@ Import Coq From SimpleC.EE Require Import ast_lib */
/*@ Import Coq From SimpleC.EE Require Import malloc */
/*@ Import Coq From SimpleC.EE Require Import sll_tmpl */

/*@ Extern Coq (var_name :: *)*/
/*@ Extern Coq (const_type :: *)*/
/*@ Extern Coq (quant_type :: *)*/
/*@ Extern Coq (term_type :: *)*/
/*@ Extern Coq (store_term : Z -> term -> Assertion)
               (store_string : Z -> list Z -> Assertion)
               (ctID : const_type -> Z)
               (qtID : quant_type -> Z)
               (ttID : term_type -> Z)
               (termtypeID : term -> Z)
               (TermVar: list Z -> term)
               (TermConst: const_type -> Z -> term)
               (TermApply: term -> term -> term)
               (TermQuant: quant_type -> list Z -> term -> term)
*/

bool alpha_equiv(term *t1, term *t2)
/*@ With term1 term2
      Require store_term(t1, term1) *
              store_term(t2, term2)
      Ensure __return == term_eqn(term1, term2) && t1 == t1@pre && t2 == t2@pre
   && store_term(t1, term1) * store_term(t2, term2)
*/
{
  if (t1 == (void *)0 || t2 == (void *)0) return false;
  /*@ store_term(t1, term1) * store_term(t2, term2)
      which implies
      data_at(&(t1 -> type), termtypeID(term1)) *
      data_at(&(t2 -> type), termtypeID(term2)) *
      store_term'(t1, term1) *
      store_term'(t2, term2)
  */
  if (t1->type != t2->type) return false;
  switch (t1->type) {
    case Var: {
      return strcmp(t1->content.Var, t2->content.Var) == 0;
    }
    case Const: {
      if (t1->content.Const.type != t2->content.Const.type) return false;
      if (t1->content.Const.type == Num) {
        return t1->content.Const.content == t2->content.Const.content;
      }
      return true;
    }
    case Apply: {
      return alpha_equiv(t1->content.Apply.left, t2->content.Apply.left) &&
             alpha_equiv(t1->content.Apply.right, t2->content.Apply.right);
    }
    case Quant: {
      if (t1->content.Quant.type != t2->content.Quant.type) return false;
      if (strcmp(t1->content.Quant.var, t2->content.Quant.var) == 0) {
        return alpha_equiv(t1->content.Quant.body, t2->content.Quant.body);
      } else {
        term *t21 = subst_var(t1->content.Quant.var, t2->content.Quant.var,
                              copy_term(t2->content.Quant.body));
        bool result = alpha_equiv(t1->content.Quant.body, t21);
        free_term(t21);
        return result;
      }
    }
  }
}
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

term *subst_var(char *den, char *src, term *t)
/*@ With trm src_str den_str
      Require den != 0 && src != 0 && t != 0 &&
              store_term(t, trm) *
              store_string(src, src_str) *
              store_string(den, den_str)
      Ensure __return == t && t == t@pre && den == den@pre && src == src@pre &&
             store_term(t, term_subst_v(den_str, src_str, trm)) *
             store_string(den, den_str) *
             store_string(src, src_str)
*/
{
  /*@ store_term(t, trm) 
      which implies
        data_at(&(t -> type), termtypeID(trm)) *
        store_term'(t, trm)
  */
  switch (t->type) {
    case Var: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y var,
            trm == TermVar(var) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Var), y) *
            store_string(y, var)
      */
      if (!strcmp(t->content.Var, src)) {
        free_str(t->content.Var);
        t->content.Var = strdup(den);
      }
      break;
    }
    case Const: {
      break;
    }
    case Apply: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z lt rt,
            trm == TermApply(lt, rt) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Apply.left), y) *
            data_at(&(t -> content.Apply.right), z) *
            store_term(y, lt) * store_term(z, rt)
      */
      t->content.Apply.left = subst_var(den, src, t->content.Apply.left);
      t->content.Apply.right = subst_var(den, src, t->content.Apply.right);
      break;
    }
    case Quant: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z qt qvar qterm,
            trm == TermQuant(qt, qvar, qterm) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Quant.type), qtID(qt)) *
            data_at(&(t -> content.Quant.var), y) *
            data_at(&(t -> content.Quant.body), z) *
            store_string(y, qvar) * store_term(z, qterm)
      */
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_var(den, src, t->content.Quant.body);
      }
      break;
    }
    default: {
      break;
    }
  }
  return t;
}

term *subst_term(term *den, char *src, term *t)
/*@ With trm src_str den_term
      Require den != 0 && src != 0 && t != 0 &&
              store_term(t, trm) *
              store_string(src, src_str) *
              store_term(den, den_term)
      Ensure __return == t && t == t@pre && den == den@pre && src == src@pre &&
             store_term(t, term_subst_t(den_term, src_str, trm)) *
             store_term(den, den_term) *
             store_string(src, src_str)
*/
{
  /*@ store_term(t, trm) 
      which implies
        data_at(&(t -> type), termtypeID(trm)) *
        store_term'(t, trm)
  */
  switch (t->type) {
    case Var: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y var,
            trm == TermVar(var) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Var), y) *
            store_string(y, var)
      */
      if (!strcmp(t->content.Var, src)) {
        /*@ exists y var,
            trm == TermVar(var) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Var), y) *
            store_string(y, var)
            which implies
            store_term(t, trm)
        */
        free_term(t);
        t = copy_term(den);
      }
      break;
    }
    case Const: {
      break;
    }
    case Apply: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z lt rt,
            trm == TermApply(lt, rt) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Apply.left), y) *
            data_at(&(t -> content.Apply.right), z) *
            store_term(y, lt) * store_term(z, rt)
      */
      t->content.Apply.left = subst_term(den, src, t->content.Apply.left);
      t->content.Apply.right = subst_term(den, src, t->content.Apply.right);
      break;
    }
    case Quant: {
      /*@ data_at(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z qt qvar qterm,
            trm == TermQuant(qt, qvar, qterm) &&
            data_at(&(t -> type), termtypeID(trm)) *
            data_at(&(t -> content.Quant.type), qtID(qt)) *
            data_at(&(t -> content.Quant.var), y) *
            data_at(&(t -> content.Quant.body), z) *
            store_string(y, qvar) * store_term(z, qterm)
      */
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_term(den, src, t->content.Quant.body);
      }
      break;
    }
    default: {
      break;
    }
  }
  return t;
}

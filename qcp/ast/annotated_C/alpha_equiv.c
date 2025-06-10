#include "ast.h"

bool alpha_equiv(term *t1, term *t2)
// here, store_term contains that t1!=0 and t2!=0, so maybe the first return false is redundant.
/*@ With term1 term2
      Require store_term(t1, term1) *
              store_term(t2, term2)
      Ensure __return == term_eqn(term1, term2) && t1 == t1@pre && t2 == t2@pre
   && store_term(t1, term1) * store_term(t2, term2)
*/
{
  if (t1 == (void *)0 || t2 == (void *)0) return 0;
  /*@ store_term(t1, term1) * store_term(t2, term2)
      which implies
      t1 != 0 && t2 != 0 &&
      data_at(&(t1 -> type), termtypeID(term1)) *
      data_at(&(t2 -> type), termtypeID(term2)) *
      store_term'(t1, term1) *
      store_term'(t2, term2)
  */
  if (t1->type != t2->type) return 0;
  switch (t1->type) {
    case Var: {
      /*@ t1 != 0 && t2 != 0 &&
          termtypeID(term1) == 0 &&
          termtypeID(term1) == termtypeID(term2) &&
          data_at(&(t1 -> type), termtypeID(term1)) *
          data_at(&(t2 -> type), termtypeID(term2)) *
          store_term'(t1, term1) *
          store_term'(t2, term2) 
          which implies
          exists y z str1 str2,
            t1 != 0 && t2 != 0 &&
            term1 == TermVar(str1) &&
            term2 == TermVar(str2) &&
            data_at(&(t1 -> type), termtypeID(term1)) *
            data_at(&(t2 -> type), termtypeID(term2)) *
            data_at(&(t1 -> content.Var), y) *
            data_at(&(t2 -> content.Var), z) *
            store_string(y, str1) *
            store_string(z, str2)
      */
      return strcmp(t1->content.Var, t2->content.Var) == 0;
    }
    case Const: {
      /*@ t1 != 0 && t2 != 0 &&
          termtypeID(term1) == 1 &&
          termtypeID(term1) == termtypeID(term2) &&
          data_at(&(t1 -> type), termtypeID(term1)) *
          data_at(&(t2 -> type), termtypeID(term2)) *
          store_term'(t1, term1) *
          store_term'(t2, term2) 
          which implies
          exists con1 typ1 con2 typ2,
            t1 != 0 && t2 != 0 &&
            term1 == TermConst(typ1, con1) &&
            term2 == TermConst(typ2, con2) &&
            data_at(&(t1 -> type), termtypeID(term1)) *
            data_at(&(t2 -> type), termtypeID(term2)) *
            data_at(&(t1 -> content.Const.type), ctID(typ1)) *
            data_at(&(t2 -> content.Const.type), ctID(typ2)) *
            data_at(&(t1 -> content.Const.content), con1) *
            data_at(&(t2 -> content.Const.content), con2)
      */
      if (t1->content.Const.type != t2->content.Const.type) return 0;
      if (t1->content.Const.type == Num) {
        return t1->content.Const.content == t2->content.Const.content;
      }
      return 1;
    }
    case Apply: {
      /*@ t1 != 0 && t2 != 0 &&
          termtypeID(term1) == 2 &&
          termtypeID(term1) == termtypeID(term2) &&
          data_at(&(t1 -> type), termtypeID(term1)) *
          data_at(&(t2 -> type), termtypeID(term2)) *
          store_term'(t1, term1) *
          store_term'(t2, term2) 
          which implies
          exists y1 z1 lt1 rt1 y2 z2 lt2 rt2,
            t1 != 0 && t2 != 0 &&
            term1 == TermApply(lt1, rt1) &&
            term2 == TermApply(lt2, rt2) &&
            data_at(&(t1 -> type), termtypeID(term1)) *
            data_at(&(t2 -> type), termtypeID(term2)) *
            data_at(&(t1 -> content.Apply.left), y1) *
            data_at(&(t2 -> content.Apply.left), y2) *
            data_at(&(t1 -> content.Apply.right), z1) *
            data_at(&(t2 -> content.Apply.right), z2) *
            store_term(y1, lt1) * store_term(z1, rt1) *
            store_term(y2, lt2) * store_term(z2, rt2)
      */
      return alpha_equiv(t1->content.Apply.left, t2->content.Apply.left) &&
                  alpha_equiv(t1->content.Apply.right, t2->content.Apply.right);
    }
    case Quant: {
      if (t1->content.Quant.type != t2->content.Quant.type) return 0;
      if (strcmp(t1->content.Quant.var, t2->content.Quant.var) == 0) {
        return alpha_equiv(t1->content.Quant.body, t2->content.Quant.body);
      } else {
        term *t21 = subst_var(t1->content.Quant.var, t2->content.Quant.var, copy_term(t2->content.Quant.body));
        bool result = alpha_equiv(t1->content.Quant.body, t21);
        free_term(t21);
        return result;
      }
    }
  }
}
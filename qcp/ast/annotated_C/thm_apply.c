#include "ast.h"
term* sub_thm(term* thm, var_sub_list* lis)
/*@ With t l
      Require store_term(thm, t) * sll_var_sub_list(lis, l)
      Ensure  thm == thm@pre && lis == lis@pre &&
              sll_var_sub_list(lis, l) *
              store_sub_thm_res(thm, __return, t, l)
*/
{
  if(lis == (void*) 0) return thm;
  /*@ lis != 0 &&
      store_term(thm, t) *
      sll_var_sub_list(lis, l)
      which implies
      exists vs l0,
        thm != 0 && 
        l == cons(vs, l0) && 
        data_at(&(thm -> type), termtypeID(t)) *
        store_term'(thm, t) *
        store_var_sub(lis -> cur, vs) *
        sll_var_sub_list(lis -> next, l0)
  */
  if(thm->type == Quant){
    /*@ exists vs,
        termtypeID(t) == 3 &&
        thm != 0 && 
        data_at(&(thm -> type), termtypeID(t)) *
        store_term'(thm, t) *
        store_var_sub(lis->cur, vs)
        which implies
        exists sv st sy sz y z qt qvar qterm,
          thm != 0 && lis->cur != 0 &&
          t == TermQuant(qt, qvar, qterm) &&
          vs == VarSub(sv, st) && 
          data_at(&(thm -> type), termtypeID(t)) *
          data_at(&(thm -> content.Quant.type), qtID(qt)) *
          data_at(&(thm -> content.Quant.var), y) *
          data_at(&(thm -> content.Quant.body), z) *
          store_string(y, qvar) * store_term(z, qterm) *
          data_at(&(lis->cur->var), sy) *
          data_at(&(lis->cur->sub_term), sz) *
          store_string(sy, sv) *
          store_term(sz, st) 
    */
    term* den = lis->cur->sub_term;
    thm->content.Quant.body = subst_term(den, lis->cur->var, thm->content.Quant.body);
    return sub_thm(thm->content.Quant.body, lis->next);
  }
  else return (void*) 0;
}

// apply (apply (impl) h1) (h2)
// 不是imply形式时返回(void*) 0
ImplyProp* separate_imply(term* t) 
/*@ With trm
    Require store_term(t, trm)
    Ensure t == t@pre && store_sep_imp_res(t, __return, trm)
*/
{
  /*@ store_term(t, trm)
      which implies
      t != 0 && 
      data_at(&(t -> type), termtypeID(trm)) *
      store_term'(t, trm)
  */
  if (t->type != Apply) return (void*)0;
  /*@ t != 0 && 
      termtypeID(trm) == 2 &&
      store_term'(t, trm)
      which implies
      exists lt rt,
      trm == TermApply(lt, rt) &&
      store_term(t->content.Apply.left, lt) *
      store_term(t->content.Apply.right, rt)
  */
  /*@ exists lt,
      store_term(t->content.Apply.left, lt)
      which implies
      t->content.Apply.left != 0 && 
      data_at(&(t->content.Apply.left -> type), termtypeID(lt)) *
      store_term'(t->content.Apply.left, lt)
  */
  if (t->content.Apply.left->type != Apply) return (void*)0;
  /*@ exists lt,
      t->content.Apply.left != 0 &&
      termtypeID(lt) == 2 &&
      store_term'(t->content.Apply.left, lt)
      which implies
      exists ll lr,
      lt == TermApply(ll, lr) &&
      store_term(t->content.Apply.left->content.Apply.left, ll) *
      store_term(t->content.Apply.left->content.Apply.right, lr)
  */
  /*@ exists ll,
      store_term(t->content.Apply.left->content.Apply.left, ll)
      which implies
      t->content.Apply.left->content.Apply.left != 0 && 
      data_at(&(t->content.Apply.left->content.Apply.left->type), termtypeID(ll)) *
      store_term'(t->content.Apply.left->content.Apply.left, ll)
  */
  if (t->content.Apply.left->content.Apply.left->type != Const) return (void*)0;
  /*@ exists ll,
      t->content.Apply.left->content.Apply.left != 0 &&
      termtypeID(ll) == 1 &&
      store_term'(t->content.Apply.left->content.Apply.left, ll)
      which implies
      exists llctype llcctnt,
      ll == TermConst(llctype, llcctnt) &&
      data_at(&(t->content.Apply.left->content.Apply.left->content.Const.type), ctID(llctype)) *
      data_at(&(t->content.Apply.left->content.Apply.left->content.Const.content), llcctnt)
  */
  if (t->content.Apply.left->content.Apply.left->content.Const.type != Impl) return (void*)0;
  else return createImplyProp(t->content.Apply.left->content.Apply.right,
                              t->content.Apply.right);
}

// 根据定理形式，匹配结论，得出要检验的前提
term_list* check_list_gen(term* thm, term* target)
/*@ With theo targ
    Require store_term(thm, theo) * store_term(target, targ)
    Ensure target == target@pre &&
            store_term(thm@pre, theo) * store_term(target, targ) *
            sll_term_list(__return, gen_pre(theo, targ))
*/
{
  if (thm == (void*)0 || target == (void*)0) {
    return (void*)0;
  }
  term_list* check_list = (void*)0;
  term_list** tail_ptr = &check_list;
  /*@ data_at(&check_list, 0) *
      data_at(&tail_ptr, &check_list)
      which implies
      store_check_gen(thm@pre, thm, theo, &check_list, tail_ptr, nil)
  */
  /*@ Inv Assert 
          exists l ttm, target == target@pre &&
          store_term(target, targ) * store_term(thm, ttm) *
          store_check_gen(thm@pre, thm, theo, &check_list, tail_ptr, l)
  */
  while (thm != (void*)0 && !alpha_equiv(thm, target)) {
    ImplyProp* p = separate_imply(thm);
    if (p == (void*)0) {
      /*@ exists l,
          store_check_gen(thm@pre, thm, theo, &check_list, tail_ptr, l)
          which implies
          exists l,
          sll_term_list(check_list, l)
      */
      free_term_list(check_list);
      return (void*)0;
    }
    // 添加新节点到链表
    term_list* new_node = malloc_term_list();
    // /*@ p != 0 && store_sep_imp_res(thm@pre, p, theo)
    //     which implies
    //     exists c r tr pa pc,
    //     theo == TermApply(TermApply(TermConst(CImpl, c), r), tr) &&
    //     data_at(&(thm@pre->type), 2) *
    //     data_at(&(thm@pre->content.Apply.right), pc) *
    //     data_at(&(thm@pre->content.Apply.left->type), 2) *
    //     data_at(&(thm@pre->content.Apply.left->content.Apply.right), pa) *
    //     data_at(&(thm@pre->content.Apply.left->content.Apply.left->type), 1) *
    //     data_at(&(thm@pre->content.Apply.left->content.Apply.left->content.Const.type), ctID(CImpl)) *
    //     data_at(&(thm@pre->content.Apply.left->content.Apply.left->content.Const.content), c) *
    //     data_at(&(p->assum), pa) *
    //     data_at(&(p->concl), pc) *
    //     store_term(pa, r) * store_term(pc, tr)
    // */
    new_node->element = p->assum;  // 转移所有权
    new_node->next = (void*)0;

    *tail_ptr = new_node;
    tail_ptr = &(new_node->next);
    thm = p->concl;
    // /*@ exists p_assum p_concl,
    //     p != 0 && 
    //     store_term(p->assum, p_assum) * store_term(p->concl, p_concl)
    //     which implies
    //     store_ImplyProp(p, p->assum, p->concl, p_assum, p_concl)
    // */
    free_imply_prop(p);  // 释放ImplyProp结构体（不释放其成员）
  }
  /*@ exists l,
      sllbseg_term_list(&check_list, tail_ptr, l) *
      data_at(tail_ptr, 0)
      which implies
      target == target@pre &&
            store_term(thm@pre, theo) * store_term(target, targ) *
            sll_term_list(__return, gen_pre(theo, targ))
  */
  return check_list;
}

solve_res* thm_apply(term* thm, var_sub_list* lis, term* goal) 
/*@ With t l g
    Require store_term(thm, t) * 
            sll_var_sub_list(lis, l) * 
            store_term(goal, g)
    Ensure exists ti,
            thm == thm@pre &&
            sll_var_sub_list(lis, l) * 
            store_term(goal, g) *
            store_solve_res(__return, thm_app(t, l, g)) *
            store_sub_thm_res(thm, ti, t, l)
*/
{
  term* thm_ins = sub_thm(thm, lis);
  solve_res* res = malloc_solve_res();
  /*@ store_solve_res(res, SRBool(0))
      which implies
      res->type == 0 &&
      res->d.ans == 0
  */
  if (thm_ins == (void*)0) {
    res->type = bool_res;
    res->d.ans = 0;
  } else {
    // Added {} here without changing the semantics!
    /*@ thm_ins != 0 &&
        store_sub_thm_res(thm, thm_ins, t, l)
        which implies
        exists pq st,
        thm_subst_allres_rel(t, l, pq, st) &&
        store_partial_quant(thm, thm_ins, pq) *
        store_term(thm_ins, st)
    */
    if (alpha_equiv(thm_ins, goal)) {
      res->type = bool_res;
      res->d.ans = 1;
    } else {
      res->type = termlist;
      /*@ res->d.ans == 0
          which implies
          res->d.list == 0
      */
      res->d.list = check_list_gen(thm_ins, goal);
    }
  }
  return res;
}

/*@ Import Coq From SimpleC.EE Require Import ast_lib */
/*@ Import Coq From SimpleC.EE Require Import malloc */
/*@ Import Coq From SimpleC.EE Require Import sll_tmpl */

/*@ Extern Coq (term :: *) */
/*@ Extern Coq (var_sub :: *) */
/*@ Extern Coq (solve_res :: *) */
/*@ Extern Coq (ImplyProp :: *) */
/*@ Extern Coq (var_name :: *)*/
/*@ Extern Coq (const_type :: *)*/
/*@ Extern Coq (quant_type :: *)*/
/*@ Extern Coq (term_type :: *)*/
/*@ Extern Coq (store_string : Z -> list Z -> Assertion)
               (store_term : Z -> term -> Assertion)
               (store_term' : Z -> term -> Assertion)
               (store_term_cell : Z -> term -> Assertion)
               (sll_term_list : Z -> list term -> Assertion)
               (sllseg_term_list : Z -> list term -> Assertion)
               (sllbseg_term_list : Z -> list term -> Assertion)
               (store_var_sub : Z -> var_sub -> Assertion)
               (store_var_sub_cell : Z -> var_sub -> Assertion)
               (sll_var_sub_list : Z -> list var_sub -> Assertion)
               (sllseg_var_sub_list : Z -> list var_sub -> Assertion)
               (sllbseg_var_sub_list : Z -> list var_sub -> Assertion)
               (store_solve_res : Z -> solve_res -> Assertion)
               (store_solve_res' : Z -> solve_res -> Assertion)
               (store_ImplyProp : Z -> Z -> Z -> term -> term -> Assertion)
               (list_Z_cmp : list Z -> list Z -> Z)
               (term_alpha_eqn : term -> term -> Z)
               (term_subst_v : list Z -> list Z -> term -> term)
               (term_subst_t : term -> list Z -> term -> term)
               (ctID : const_type -> Z)
               (qtID : quant_type -> Z)
               (ttID : term_type -> Z)
               (termtypeID : term -> Z)
               (TermVar: list Z -> term)
               (TermConst: const_type -> Z -> term)
               (TermApply: term -> term -> term)
               (TermQuant: quant_type -> list Z -> term -> term)
               (term_not_contain_var: term -> list Z -> Prop)
*/

typedef int bool;

enum const_type {
  Num = 0,
  // oper
  Add,
  Mul,
  // pred
  Eq,
  Le,
  // connect
  And,
  Or,
  Impl
};
typedef enum const_type const_type;

enum quant_type { Forall, Exists };
typedef enum quant_type quant_type;

enum term_type { Var, Const, Apply, Quant };
typedef enum term_type term_type;

struct term {
  term_type type;
  union {
    char *Var;
    struct {
      const_type type;
      int content;
    } Const;
    struct {
      struct term *left;
      struct term *right;
    } Apply;
    struct {
      quant_type type;
      char *var;
      struct term *body;
    } Quant;
  } content;
};
typedef struct term term;

struct term_list {
  term *element;
  struct term_list *next;
};
typedef struct term_list term_list;

typedef struct var_sub {
  char *var;
  term *sub_term;
} var_sub;

typedef struct var_sub_list {
  var_sub *cur;
  struct var_sub_list *next;
} var_sub_list;

typedef enum { bool_res, termlist } res_type;
typedef struct {
  res_type type;
  union {
    bool ans;
    term_list *list;
  } d;
} solve_res;

typedef struct {
  term *assum;
  term *concl;
} ImplyProp;

/* BEGIN Given Functions */

// malloc 函数，内存均初始为全0
term_list *malloc_term_list()
    /*@ Require emp
        Ensure __return != 0 &&
              data_at(&(__return -> element), 0) *
              data_at(&(__return -> next), 0)
    */
    ;

solve_res *malloc_solve_res()
    /*@ Require emp
        Ensure __return != 0 &&
              data_at(&(__return -> type), 0) *
              data_at(&(__return -> d), 0)
    */
    ;

// 构造函数
ImplyProp *createImplyProp(term *t1, term *t2)
    /*@ With term1 term2
          Require store_term(t1, term1) *
                  store_term(t2, term2)
          Ensure t1 == t1@pre && t2 == t2@pre &&
                store_ImplyProp(__return, t1, t2, term1, term2)
    */
    ;

// 深拷贝函数
term *copy_term(term *t)
    /*@ With _term
          Require store_term(t, _term)
          Ensure __return != 0 &&
                store_term(t, _term) *
                store_term(__return, _term)
    */
    ;

term_list *copy_term_list(term_list *list)
    /*@ With l
          Require sll_term_list(list, l)
          Ensure __return != 0 &&
                sll_term_list(list, l) *
                sll_term_list(__return, l)
    */
    ;

// free 函数
void free_str(char *s)
    /*@ Require s != 0 && exists n, store_string(s, n)
        Ensure emp
    */
    ;

void free_imply_prop(ImplyProp *p)
    /*@ With term1 term2 t1 t2
          Require store_ImplyProp(p, t1, t2, term1, term2)
          Ensure store_term(t1, term1) *
                store_term(t2, term2) *
                emp
    */
    ;

void free_term(term *t)
    /*@ Require exists _term, store_term(t, _term)
        Ensure emp
    */
    ;

void free_term_list(term_list *list)
    /*@ Require exists l, sll_term_list(list, l)
        Ensure emp
    */
    ;

// string 相关函数
char *strdup(const char *s)
    /*@ With str
          Require store_string(s, str)
          Ensure __return != 0 &&
                store_string(s, str) *
                store_string(__return, str)
    */
    ;

int strcmp(const char *s1, const char *s2)
    /*@ With str1 str2
          Require store_string(s1, str1) *
                  store_string(s2, str2)
          Ensure __return == list_Z_cmp(str1, str2) &&
                store_string(s1, str1) *
                store_string(s2, str2)
    */
    ;

// 返回一个在t1和t2中都没出现过的变量名
char *fresh(term *t1, term *t2)
  /*@ With term1 term2
        Require store_term(t1, term1) *
                store_term(t2, term2)
        Ensure exists str, 
               term_not_contain_var(term1, str) && 
               term_not_contain_var(term2, str) &&
               store_term(t1, term1) *
               store_term(t2, term2) *
               store_string(__return, str)
  */
  ;

/* END Given Functions */

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
    ;

term *subst_term(term *den, char *src, term *t)
    /*@ With trm src_str den_term
          Require den != 0 && src != 0 && t != 0 &&
                  store_term(t, trm) *
                  store_string(src, src_str) *
                  store_term(den, den_term)
          Ensure den == den@pre && src == src@pre &&
                 store_term(__return, term_subst_t(den_term, src_str, trm)) *
                 store_term(den, den_term) *
                 store_string(src, src_str)
    */
   ;

bool alpha_equiv(term *t1, term *t2)
    /*@ With term1 term2
      Require store_term(t1, term1) *
              store_term(t2, term2)
      Ensure __return == term_alpha_eqn(term1, term2) && t1 == t1@pre && t2 == t2@pre
      && store_term(t1, term1) * store_term(t2, term2)
    */
    ;

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
From StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.

Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope monad.

Section  merge_monad.

Definition merge_body:
  list Z * list Z * list Z ->
  MONAD (CntOrBrk (list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => ret (by_break (l3 ++ l2))
    | _, nil => ret (by_break (l3 ++ l1))
    | x :: l1', y :: l2' =>
        choice
          (test' (x <= y);; ret (by_continue (l1', l2, l3 ++ x :: nil)))
          (test' (y <= x);; ret (by_continue (l1, l2', l3 ++ y :: nil)))
  end.

  Definition merge_rel l l0 :=
    repeat_break merge_body (l, l0, nil).

  Definition merge_from_mid_rel l1 l2 l3 := 
    repeat_break merge_body (l1, l2, l3).

End  merge_monad.


Section split_rec_rel_monad.

  Definition reversepair : ((list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(p,q) => ret (q,p).

  Definition split_rec_rel_f  (W : ((list Z) * (list Z) * (list Z)) ->  MONAD ((list Z) * (list Z))) 
                          : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(x, p, q) => match x with 
                      | nil => ret (p, q)
                      | xh :: x' => x <- W (x', q,  xh::p) ;;
                                    reversepair x
                      end.

  Definition split_rec_rel' : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) := 
    Lfix split_rec_rel_f.

  Definition split_rec_rel l1 l2 l3: MONAD ((list Z) * (list Z)) := 
    split_rec_rel' (l1, l2, l3).

  Definition split_rel x :=
    split_rec_rel' (x, nil, nil).

  Lemma mono_split_rec_rel_f: mono split_rec_rel_f.
  Proof.
    intros.
    unfold split_rec_rel_f.
    unfold mono. hnf.
    intros f1 f2 H x s1.
    destruct x as ((x & p) & q).
    destruct x.
    reflexivity.
    assert ('(p, q) <- f1 (x, q, z :: p) ;; ret (q, p) ⊆ '(p, q) <- f2 (x, q, z :: p) ;; ret (q, p)).
    { erewrite (H _). reflexivity. } 
    apply H0.
  Qed.
  
  Lemma continuous_split_rec_rel_f: continuous split_rec_rel_f.
  Proof.
    intros.
    unfold split_rec_rel_f.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l Hl.
    unfold_monad; sets_unfold.
    intros x s x0 s0.
    destruct x as ((x & p) & q).
    split;intros.
    + destruct x. exists O. auto.
      destruct H as (x1 & s1 & (n & H) & ?).
      do 3 eexists.
      split;eauto.
    + destruct H as (n & H).
      destruct x;auto.
      destruct H as (x1 & s1 & ? & ?).
      do 2 eexists.
      split;eauto.
  Qed.

  Lemma split_rec_rel_unfold: split_rec_rel' == split_rec_rel_f split_rec_rel'.
  Proof.
    intros.
    apply Lfix_fixpoint.
    apply mono_split_rec_rel_f.
    apply continuous_split_rec_rel_f.
  Qed.

  Lemma split_rec_rel_eval_xnil: forall p q P, 
    P -@ (split_rec_rel' (nil, p, q)) -⥅ 
    P ♯ (p, q).
  Proof.
    intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)).
    unfold split_rec_rel_f.
    apply  highret_eval2.
  Qed.


  Lemma split_rel_eval_xnotnil: forall z x p q,
    forall P X, safeExec P (split_rec_rel' (z::x, p, q)) X ->
                safeExec P (x <- split_rec_rel' (x, q, z::p) ;; reversepair x ) X.
  Proof. 
    unfold split_rel, reversepair. intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)) in H.
    unfold split_rec_rel_f in H.
    apply H.
  Qed.

End split_rec_rel_monad.


Section mergesort_monad.
  Definition mergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => '(p1, q1) <- split_rel x ;; 
                      match q1 with 
                      | nil => ret p1
                      | _ :: _  =>  p2 <- W (p1) ;; 
                                    q2 <- W (q1) ;; 
                                    merge_rel p2 q2
                      end.

  Definition mergesortrec := Lfix (mergesortrec_f).

  Definition mergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                      match q1 with 
                      | nil => ret p1
                      | _ :: _  =>  p2 <- mergesortrec p1 ;; 
                                    q2 <- mergesortrec q1 ;; 
                                    merge_rel p2 q2
                      end
             end.

  Definition mergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- mergesortrec q1 ;; 
              merge_rel p2 q2.

  Definition mergesortrec_loc2 p2: list Z -> MONAD (list Z) :=
    fun q2 => merge_rel p2 q2.

  Lemma mono_mergesortrec_f: mono mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_mono_compose_right.
    unfold mono. hnf.
    intros f1 f2 H x.
    destruct x as (p & q).
    destruct q.
    reflexivity.
    assert (forall x, f1 x ⊆ f2 x). { intros.  sets_unfold. intros. apply H. auto. }
    erewrite H0.
    assert (forall x, @Sets.included (list Z -> MONAD (list Z)) _ (fun p2 => q2 <- f1 x;; merge_rel p2 q2) 
    (fun p2 => (q2 <- f2 x;; merge_rel p2 q2))).
    { intros x0 p2.  
    erewrite H0. reflexivity. }
    erewrite H1.
    reflexivity.
  Qed.
  
  Lemma continuous_mergesortrec_f: continuous mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_continuous_compose_right.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l Hl.
    intros x.
    destruct x as (p & q).
    destruct q.
    + sets_unfold. intros. split;intros. exists 1%nat. auto. destruct H. auto.
    + rewrite (omega_union_introa 
      (fun (n : nat) (x0 : list Z * list Z) =>
      let (p1, q1) := x0 in
      match q1 with
      | nil => ret p1
      | _ :: _ =>
          p2 <- l n p1;;
          q2  <- l n q1;;
          merge_rel p2 q2
      end) (p, z :: q)).
      assert (increasing (fun (n:nat) (p2:list Z) => q2 <- l n (z::q) ;; 
      merge_rel p2 q2)) as Hl2. 
      { eapply (increasing_mono_increasing (fun ln => 
          fun p2 => q2 <- ln (z::q);; merge_rel p2 q2 ));eauto.
        eapply bind_mono_left'. }
      pose proof program_para_equiv (bind_omega_union_distr_both l _ Hl Hl2) p.
      clear Hl2.
      rewrite omega_union_introa in H.
      rewrite <- H. clear H.
      eapply bind_equiv;[reflexivity | ].
      intros p2.
      rewrite omega_union_introa.
      erewrite bind_omega_union_distr_r' with (c1 := l) (a:= (z :: q)).
      reflexivity.
  Qed.

  Lemma mergesortrec_unfold: mergesortrec == mergesortrec_f mergesortrec.
  Proof.
    apply Lfix_fixpoint.
    apply mono_mergesortrec_f.
    apply continuous_mergesortrec_f.
  Qed.

End mergesort_monad.

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Section general_mergesort_monad.

  Definition ext_sort (l: list Z): MONAD (list Z) :=
    fun _ l' _ => Permutation l l' /\ incr l'.

  Definition ext_split (l: list Z): MONAD (list Z * list Z) :=
    fun _ '(l0, l1) _ =>   Permutation l (l0 ++ l1).

  Definition gmergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => 
      choice
        (ext_sort x)
        (test' (Zlength x >= 2)%Z;;
         '(p1, q1) <- ext_split x ;; 
         p2 <- W (p1) ;; 
         q2 <- W (q1) ;; 
         merge_rel p2 q2).

  Definition gmergesortrec := Lfix (gmergesortrec_f).

  Definition gmergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                 p2 <- gmergesortrec p1 ;; 
                 q2 <- gmergesortrec q1 ;; 
                 merge_rel p2 q2
             end.

  Definition gmergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- gmergesortrec q1 ;; 
              merge_rel p2 q2.

  Lemma mono_gmergesortrec_f: mono gmergesortrec_f.
  Proof.
    intros.
    unfold gmergesortrec_f.
    unfold mono. hnf.
    intros c c0 H.
    intros x.
    apply choice_proper; [reflexivity | ].
    apply programbind_included_Proper ; [reflexivity | ].
    intros x0.
    apply programbind_included_Proper; [reflexivity | ].
    intros x1.
    destruct x1.
    apply programbind_included_Proper; [apply H | ].
    intros p2.
    apply programbind_included_Proper; [apply H | ].
    intros q2.
    reflexivity.
  Qed.

  Lemma continuous_gmergesortrec_f: continuous gmergesortrec_f.
  Proof.
    intros.
    unfold gmergesortrec_f.
    unfold continuous,sseq_continuous, sseq_mono.
    intros W. intros.
    intros x.
    rewrite (omega_union_introa ((fun n : nat =>  gmergesortrec_f (W n)))).
    unfold gmergesortrec_f.
    rewrite <- choice_omega_union_distr_l.
    apply choice_equiv_equiv ; [reflexivity | ].
    unfold seq.
    rewrite <- bind_omega_union_distr_l.
    apply bind_equiv ; [reflexivity | ].
    intros x0.
    rewrite omega_union_introa.
    rewrite <- bind_omega_union_distr_l.
    apply bind_equiv ; [reflexivity | ].
    intros x1.
    rewrite omega_union_introa.
    destruct x1.
    assert (increasing (fun (n:nat) (p2:list Z) => q2 <- W n l0 ;; 
      merge_rel p2 q2)) as Hl2. 
      { eapply (increasing_mono_increasing (fun ln => 
          fun p2 => q2 <- ln l0;; merge_rel p2 q2 ));eauto.
        eapply bind_mono_left'. }
    pose proof program_para_equiv (bind_omega_union_distr_both W _ H Hl2) l.
    rewrite omega_union_introa in H0.
    rewrite <- H0. clear H0.
    eapply bind_equiv;[reflexivity | ].
    intros p2.
    rewrite omega_union_introa.
    erewrite bind_omega_union_distr_r' with (c1:= W) (a:= l0).
    reflexivity.
  Qed.

  Lemma gmergesortrec_unfold: gmergesortrec == gmergesortrec_f gmergesortrec.
  Proof.
    apply Lfix_fixpoint.
    apply mono_gmergesortrec_f.
    apply continuous_gmergesortrec_f.
  Qed.

End general_mergesort_monad.


Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.


Section algorithm_correctness.
Import StateRelMonadHoare StateRelTactics.

Lemma merge_rel_perm:
    forall l1 l2,
    Hoare ATrue (merge_rel l1 l2)
        (fun l3 _ => Permutation (l1 ++ l2) l3).
Proof.
  unfold merge_rel.
  intros l1 l2.
  eapply Hoare_conseq_pre.
  2:apply Hoare_repeat_break with 
    (P := fun '(l1', l2', l3') _ => Permutation (l3' ++ l1' ++ l2') (l1 ++ l2)).
  1: { simpl; intros; auto. }
  intros ((l1', l2'), l3'); unfold merge_body.
  destruct l1'.
  {
    hoare_auto.
    rewrite app_nil_l in H.
    symmetry; auto.  
  }
  destruct l2'.
  {
    hoare_auto.
    rewrite app_nil_r in H.
    symmetry; auto.   
  }
  hoare_auto.
  - rewrite <- app_assoc.
    rewrite (app_assoc [z]).
    replace ([z] ++ l1') with (z::l1') by easy.
    auto.
  - rewrite <- app_assoc.
    rewrite <- H0.
    apply Permutation_app_head.
    rewrite <- (Permutation_middle _ _ z0).
    reflexivity.
Qed.

Lemma merge_rel_incr:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare ATrue (merge_rel l1 l2)
        (fun l3 _ => incr l3).
Proof.
  intros l1 l2 Hl1 Hl2.
  unfold merge_rel.
  eapply Hoare_conseq_pre.
  2:apply Hoare_repeat_break with 
    (P := fun '(l1', l2', l3') _ => incr (l3' ++ l1') /\
                                    incr (l3' ++ l2')).
  1: { simpl; tauto. }
  intros [ [l1' l2'] l3'].
  stateless_intros.
  unfold merge_body.
  destruct l1'.
  { hoare_auto; tauto. }
  destruct l2'.
  { hoare_auto; tauto. }
  destruct H as [INC1 INC2].
  hoare_auto.
  - rewrite <- app_assoc.
    split; auto.
    apply incr_app_cons.
    + apply incr_app_cons_inv1 in INC1.
      rewrite <- app_assoc.
      simpl.
      apply incr_app_cons; auto.
      constructor; easy.
    + apply incr_app_cons_inv2 in INC2.
      auto.
  - repeat rewrite <- app_assoc.
    simpl.
    split; auto.
    apply incr_app_cons.
    + apply incr_app_cons_inv1 in INC2.
      auto.
    + apply incr_app_cons_inv2 in INC1.
      constructor; auto.
Qed.

Lemma split_rel_perm:
  forall l,
    Hoare ATrue (split_rel l)
        (fun '(l1, l2) _ => Permutation l (l1 ++ l2)).
Proof.
  intros.
  unfold split_rel, split_rec_rel'.
  eapply Hoare_conseq_pre.
  2:apply Hoare_fix' with 
    (P := fun '(l', l1', l2') _ => Permutation l (l' ++ l1' ++ l2')).
  1: { rewrite !app_nil_r. reflexivity. }
  intros W ?.
  intros [ [l' l1'] l2'].
  unfold split_rec_rel_f.
  destruct l'.
  { hoare_auto. }
  eapply Hoare_conseq_pre.
  2:hoare_post H.
  {
    simpl; intros _ Hl.
    Search Permutation.
    rewrite app_assoc.
    rewrite Permutation_app_comm.
    rewrite Hl; simpl.
    constructor.
    do 2 rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  }
  clear l1' l2'.
  destruct a as [l1' l2']; simpl.
  hoare_auto.
  rewrite H0.
  apply Permutation_app_comm.
Qed.

Lemma split_rel_length:
  forall l,
    Hoare ATrue (split_rel l)
        (fun '(l1, l2) _ => length l1 <= length l2 + 1)%nat.
Proof.
  intros.
  unfold split_rel, split_rec_rel'.
  eapply Hoare_conseq_post.
  2:apply (Hoare_fix _
    (fun _ => ATrue) 
    ((fun '(l', l1, l2) '(l1', l2') _ => 
      (length l1 <= length l1' /\
      length l2 <= length l2' /\
      length l2' - length l2 <=
      length l1' - length l1 <=
      S (length l2' - length l2))%nat)
    )).
  { 
    simpl; intros; destruct b as [l1 l2].
    destruct H as (? & ? & ?).
    lia.
  }
  intros W HW [[l' l1] l2].
  unfold split_rec_rel_f.
  destruct l'.
  { 
    hoare_auto.
    lia.
  }
  eapply Hoare_conseq_pre.
  2:hoare_post HW.
  { auto. }
  destruct a as [l1' l2'].
  simpl; hoare_auto.
  lia.
Qed.

Lemma split_rel_snd_nil:
  forall l,
    Hoare ATrue (split_rel l)
        (fun '(l1, l2) _ => l2 = nil -> (length l1 <= 1)%nat).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:apply split_rel_length.
  simpl; intros.
  destruct b as [l1 l2].
  intros; subst.
  simpl in H; auto.
Qed.

Lemma split_rel_snd_nil':
  forall l,
    Hoare ATrue (split_rel l)
        (fun '(l1, l2) _ => l2 = nil -> Permutation l l1 /\ incr l1).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:{ 
    eapply Hoare_conj.
    apply split_rel_perm.
    apply split_rel_snd_nil.
  }
  intros (l1, l2) _ (? & ?) ?.
  pose proof H0 H1.
  subst; clear H0.
  rewrite app_nil_r in H.  
  destruct l1.
  - simpl; tauto.
  - simpl in H2.
    assert (length l1 = 0)%nat by lia.
    destruct l1; simpl in H0; try lia.
    split; easy.
Qed.

Lemma split_rel_refine_ext_split : 
  forall l, 
    split_rel l ⊆ ext_split l.
Proof.
  intros.
  intros x (l1,l2) x' H.
  unfold ext_split.
  pose proof split_rel_perm.
  unfold Hoare in H0.
  specialize (H0 l x (l1, l2) x').
  simpl in H0.  
  apply H0.
  - unfold ATrue; auto.
  - apply H.
Qed.

Lemma mergesortrec_perm: forall l,
  Hoare ATrue (mergesortrec l)
        (fun l' _ => Permutation l l').
Proof.
  intros l.
  unfold mergesortrec.
  apply Hoare_fix with
    (P := fun _ => ATrue)
    (Q := fun l l' _ => Permutation l l').
  intros W ?.
  clear l; intros l.
  unfold mergesortrec_f.
  hoare_post split_rel_perm.
  destruct a as [l1 l2].
  stateless_intros.
  destruct l2.
  {
    hoare_auto.
    rewrite app_nil_r in H0.
    auto. 
  }
  hoare_post H.
  simpl; stateless_intros.
  hoare_post H.
  simpl; stateless_intros.
  eapply Hoare_conseq_post.
  2:apply merge_rel_perm.
  simpl; intros.
  rewrite <- H2 in H3.
  rewrite <- H1 in H3.
  rewrite H0, H3.
  easy.
Qed.

Lemma mergesortrec_incr: forall l,
  Hoare ATrue (mergesortrec l)
        (fun l' _ => incr l').
Proof.
  intros l.
  unfold mergesortrec.
  apply Hoare_fix' with
    (P := fun _ => ATrue).
  intros W ?.
  clear l; intros l.
  unfold mergesortrec_f.
  hoare_post split_rel_snd_nil'.
  destruct a as [l1 l2].
  stateless_intros.
  destruct l2.
  {
    hoare_auto.
    tauto. 
  }
  clear H0.
  hoare_post H.
  simpl; stateless_intros.
  hoare_post H.
  simpl; stateless_intros.
  eapply Hoare_conseq_post.
  2:apply merge_rel_incr.
  all: auto.
Qed.

Lemma Hoare_ext_sort: forall l,
  Hoare ATrue (ext_sort l)
        (fun l' _ => Permutation l l' /\ incr l').
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:apply Hoare_step.
  simpl.
  unfold ext_sort; intros.
  destruct H as [_ [H _]].
  tauto.
Qed.

Lemma Hoare_ext_split: forall l,
  Hoare ATrue (ext_split l)
        (fun '(l1, l2) _ => Permutation l (l1 ++ l2)).
Proof.
  intros.
  eapply Hoare_conseq_post.
  2:apply Hoare_step.
  unfold ext_split; simpl; intros.
  destruct H as [_ [H _]].
  destruct b; auto.
Qed.

Lemma gmergesortrec_perm: forall l,
  Hoare ATrue (gmergesortrec l)
        (fun l' _ => Permutation l l').
Proof.
  intros l.
  unfold gmergesortrec.
  apply Hoare_fix with
    (P := fun _ => ATrue)
    (Q := fun l l' _ => Permutation l l').
  intros W ?.
  clear l; intros l.
  unfold gmergesortrec_f.
  hoare_auto.
  {
    eapply Hoare_conseq_post.
    2:apply Hoare_ext_sort.
    simpl; tauto.
  }
  hoare_post Hoare_ext_split.
  destruct a; stateless_intros.
  do 2 (hoare_post H; simpl; stateless_intros).
  eapply Hoare_conseq_post.
  2:apply merge_rel_perm.
  simpl; intros.
  rewrite <- H2 in H4.
  rewrite <- H3 in H4.
  rewrite H1, H4.
  easy.
Qed.

Lemma gmergesortrec_incr: forall l,
  Hoare ATrue (gmergesortrec l)
        (fun l' _ => incr l').
Proof.
  intros l.
  unfold gmergesortrec.
  apply Hoare_fix' with
    (P := fun _ => ATrue).
  intros W ?.
  clear l; intros l.
  unfold gmergesortrec_f.
  hoare_auto.
  {
    eapply Hoare_conseq_post.
    2:apply Hoare_ext_sort.
    simpl; tauto.
  }
  apply Hoare_skip; intros (l1, l2).
  do 2 (hoare_post H; simpl; stateless_intros).
  eapply Hoare_conseq_post.
  2:apply merge_rel_incr.
  all: auto.
Qed.

End algorithm_correctness.

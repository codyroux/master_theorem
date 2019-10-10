Require Import Reals.
Require Import Fourier.
Require Import Psatz.
Require Import Lra.


Module RecRel.

(*
We model super general (univariate, single function) reccurence relations for now.
We'll make them more restrictive if the general definition turns out to be a hassle.

*)
Inductive Expr :=
| Var : Expr
| Tu  : Expr -> Expr
| Td  : Expr -> Expr
| Const : R -> Expr
| Sum : Expr -> Expr -> Expr
| Mul : Expr -> Expr -> Expr
| Div : Expr -> Expr -> Expr
| Fun : (R -> R) -> Expr -> Expr                          
.

Record Rel := { lhs : Expr; rhs : Expr }.

Print Rel.

Coercion Const : R >-> Expr.

Notation "e1 <+> e2" := (Sum e1 e2)(at level 20).
Notation "e1 <*> e2" := (Mul e1 e2)(at level 20).
Notation "e1 </> e2" := (Div e1 e2)(at level 20).
Notation "f <@> e"   := (Fun f e)(at level 19).
Notation "<n>"       := Var.

Check (_/_).
Search (_/_).

Print Rdiv.

Search (nat -> R).

Search (R -> Z).

Search (Z -> nat).

SearchAbout (up _).
SearchAbout (Int_part _).
SearchAbout (INR _).

Definition down (x : R) : Z := ((up x) - 1)%Z.


Fixpoint Interp (e : Expr) (f : Z -> R) (n : Z) : R :=
  match e with
      | <n> => IZR n
      | Tu e' => f (up (Interp e' f n))
      | Td e' => f (down (Interp e' f n))
      | Const c => c
      | e1 <+> e2 => (Interp e1 f n) + (Interp e2 f n)
      | e1 <*> e2 => (Interp e1 f n) * (Interp e2 f n)
      | e1 </> e2 => (Interp e1 f n) / (Interp e2 f n)
      | g <@> e  => g (Interp e f n)
  end.

Notation "[[ e ]]" := (Interp e).

Definition ValRel (r : Rel) (f : Z -> R) : Prop :=
  forall n, [[ lhs r ]] f n <= [[ rhs r ]] f n.


Notation "l :== r" := (Build_Rel l r)(at level 30).


Lemma test_lemma : forall f, ValRel (Tu <n> :== Tu ((<n> <*> 2) </> 2)) f.
Proof.
  unfold ValRel; intros; simpl Interp.
  
  unfold Rdiv; rewrite Rinv_r_simpl_l; auto; lra.
Qed.


Lemma down_leq_up : forall x y : R, x <= y -> IZR (down x) <= IZR (up y).
Proof.
  intros.
  unfold down.
  SearchAbout (IZR _ - _).
  rewrite minus_IZR.
  SearchAbout (IZR _ - _ <= _).
  pose (Hx := for_base_fp x).
  destruct Hx.
  assert (IZR (up x) <= x + 1) by lra.
  SearchAbout (_ <= _ -> _ <= _ -> _ <= _).
  eapply Rle_trans with (r2 := x); try lra.
  pose (Hy := for_base_fp y); destruct Hy.
  lra.
Qed.

Lemma eq_up_mul : forall n x, IZR n * (IZR (up x)) = IZR (n * up x).
Proof.
  intros.
                                 
  Print IZR.
  rewrite <- mult_IZR; auto.
Qed.

Lemma eq_up_IZR : forall n, IZR (up (IZR n)) = (IZR n) + 1.
Proof.
  intros.
  (* Set Printing All. *)
  rewrite <- plus_IZR.
  apply f_equal.
  symmetry.
  SearchAbout up.
  apply tech_up.
  - rewrite plus_IZR; lra.
  - rewrite plus_IZR; lra.
Qed.
  

Lemma test2 : ValRel (Td <n> :== 2 <*> (Tu (<n> </> 2))) (fun n => IZR n).
Proof.
  unfold ValRel; intros; simpl Interp.
  unfold down.
  rewrite minus_IZR.
  rewrite eq_up_IZR.
  ring_simplify.
  pose (Hdiv := for_base_fp (IZR n / 2)); destruct Hdiv.
  lra.
Qed.


(*
We use the most straightforward definition here,
we'll amend it later if needed.
*)
Definition O (f : Z -> R) (g : Z -> R) : Prop :=
  exists n, exists C, 0 <= IZR n /\ 0 <= C /\ forall M, IZR n <= IZR M -> g M <= C * (f M).

(*This notation is the worst *)
Notation "g ∈O a":= (O a g)(at level 10).

Ltac trivial_bounds := exists 0%Z; exists 1; split; [|split]; try lra.

Ltac o_of_n_bounds n C := exists n%Z; exists C; split; [|split]; try lra.

Ltac idk_bounds := eexists; eexists; split; [|split]; try lra.

(* SearchAbout ( _ <= _ * _ ). *)

(* Ltac fast_progress_le_goal := match goal with *)
(*                          | [|- _ * _ <= _ * _] => apply Rmult_le_compat_l *)
(*                          | [|- _ * _ <= _ * _] => apply Rmult_le_compat_r *)
(*                          | [|- _ + _ <= _ + _] => apply Rplus_le_compat_l *)
(*                          | [|- _ + _ <= _ + _] => apply Rplus_le_compat_r *)
(*                          (* | [|- ?X / _ < ?X]    => apply Nat.div_lt *) *)
(*                          | [|- / ?X <= / ?X]   => apply Rle_Rinv *)
(*                          (* | [|- ?X * (?Y / ?X) <= ?Y] => apply Nat.mul_div_le *) *)
(*                          | [|- _ ^ ?X <= _ ^ ?X] => apply pow_incr *)
(*                          | [|- ?X ^ _ <= ?X ^ _] => apply Rle_pow *)
(*                          (* | [|- _ <= _ * _]     => apply mul_le_r; now auto with arith *) *)
(*                          (* | [|- _ <= _ * _]     => apply mul_le_l; now auto with arith *) *)
(*                          end; lra. *)


SearchAbout ( Rmax _ _ <= _).

SearchAbout ( _ <= _ -> _ <= _ -> _ <= _).

Lemma Rmax_split_l : forall x y z, Rmax x y <= z -> x <= z.
Proof.
  intros x y z; unfold Rmax; case (Rle_dec x y); lra.
Qed.

Lemma Rmax_split_r : forall x y z, Rmax x y <= z -> y <= z.
Proof.
  intros x y z; unfold Rmax; case (Rle_dec x y); lra.
Qed.



(* Ltac progress_le_goal := try *)
(*                            (match goal with *)
(*                             | [_ : ((Rmax ?X _) <= _) |- ?X <= _ ] => eapply Rmax_split_l; lra *)
(*                             | [_ : ((Rmax _ ?X) <= _) |- ?X <= _ ] => eapply Rmax_split_r; lra *)
(*                             end); fast_progress_le_goal. *)


Lemma n_O_of_n_squared : (fun n => IZR n) ∈O (fun n => IZR n * IZR n).
Proof.
  o_of_n_bounds 1%Z 1; intros; nra.
Qed.

Theorem O_refl : forall f, f ∈O f.
Proof.
  trivial_bounds.
  intros; lra.
Qed.

Lemma max_IZR : forall n m, IZR (Z.max n m) = Rmax (IZR n) (IZR m).
Proof.
  intros.
  SearchAbout (IZR _ <= _).
  Check IZR_le.

Theorem O_trans : forall f g h, f ∈O g -> g ∈O h -> f ∈O h.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Z.max M1 M2) (C1 * C2);
  destruct H1 as (H11, (H12, H1));
  destruct H2 as (H21, (H22,H2)).
  - eapply Rle_trans. apply Rmax_r.
    apply Rle_max_compat_l; auto.

  - nra.
  
  - intros M le.
    assert (f M <= C1 * g M).
    + apply H1.
      unfold Rmax in *.
      destruct (Rle_dec M1 M2); lra.

    + assert (g M <= C2 * h M).
      apply H2.
      unfold Rmax in *.
      destruct (Rle_dec M1 M2); lra.
      nra.
Qed.


Theorem O_add_idempot : forall f g h, f ∈O (fun n => g n + h n) -> h ∈O g -> f ∈O g.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Rmax M1 M2) (C1 + C1*C2);
    destruct H1 as (H11, (H12, H1));
    destruct H2 as (H21, (H22,H2)).

  - eapply Rle_trans. apply Rmax_r.
    apply Rle_max_compat_l; auto.

  - nra.

  - intros M max_rel.
    rewrite Rmult_plus_distr_r.
    eapply Rle_trans.
    + apply H1; unfold Rmax in *; destruct (Rle_dec M1 M2); lra.
    + rewrite Rmult_plus_distr_l.
      SearchAbout (_+_<=_+_).
      apply Rplus_le_compat; try lra.
      SearchAbout (_*_<=_*_).
      rewrite Rmult_assoc.
      apply Rmult_le_compat_l; try lra.
      apply H2.
      unfold Rmax in *; destruct (Rle_dec M1 M2); lra.
Qed.


Definition monotone f := forall x y, x <= y -> f x <= f y.

Definition non_zero f := exists k:R, f k > 0.

Definition positive f := forall x:R, 0 <= f x.

Theorem O_mul_hyp : forall f g C, 0 <= C -> f ∈O (fun k => C * g k) -> f ∈O g.
Proof.
  intros f g C C_pos (M, (C', H)).
  o_of_n_bounds M (C' * C);
  destruct H as (H1, (H2, H)); try nra.
  intros M0 leq.
  SearchAbout ((_*_)*_).
  Check Rmult_assoc.
  rewrite Rmult_assoc.
  apply H; lra.
Qed.

Theorem O_mul_conc : forall f g C, 0 < C -> f ∈O g -> f ∈O (fun k => C * g k).
Proof.
  intros f g C nz (M, (C', (H1, (H2, H)))).
  o_of_n_bounds M (C' * / C).
  - apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat; auto.
  - intros.
    replace (C' * / C * (C * g M0)) with (C' * (/ C * C) * g M0) by ring.
    rewrite Rinv_l.
    rewrite Rmult_1_r.
    auto.
    lra.
Qed.

(* A bit surprising that C needs to be positive here... *)
Theorem O_mul_src : forall f g C, 0 <= C -> f ∈O g -> (fun k => C * f k) ∈O g.
Proof.
  intros f g C C_pos (M, (C', (H1, (H2, H)))).
  o_of_n_bounds M (C * C').
  - nra.
  - intros.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l; auto.
Qed.


Theorem O_const_plus : forall f g h C, 0 <= C -> h ∈O g -> f ∈O (fun k => g k + C * h k) -> f ∈O g.
Proof.
  intros f g h C C_pos o_h_g o_f_sum.
  eapply O_add_idempot.
  apply o_f_sum.
  apply O_mul_src; auto.
Qed.

Theorem O_const : forall f c, 0 <= c -> monotone f -> non_zero f -> (fun _ => c) ∈O f.
Proof.
  intros f c c_pos mon non_zero.
  destruct non_zero as (k, k_n_z).
  o_of_n_bounds (Rmax k 1) (c * / f (Rmax k 1)).
  - unfold Rmax.
    destruct (Rle_dec k 1); lra.
  - unfold Rmax; destruct (Rle_dec k 1).
    unfold monotone in mon.
    assert (f k <= f 1) by (apply mon; lra).
    SearchAbout (0 < / _).
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.

  - intros M le.
    rewrite Rmult_assoc.
    pattern c at 1.
    replace c with (c * 1) by ring.
    apply Rmult_le_compat_l; auto.
    pattern 1 at 1.
    replace 1 with (/ f (Rmax k 1) * f (Rmax k 1)); try apply Rinv_l.
    + apply Rmult_le_compat_l.
      unfold Rmax.
      destruct (Rle_dec k 1).
      apply Rlt_le.
      apply Rinv_0_lt_compat.
      unfold monotone in mon.
      generalize (mon k 1); intros.
      lra.
      apply Rlt_le; apply Rinv_0_lt_compat; auto.
      apply mon; auto.
    + apply Rgt_not_eq.
      generalize (mon k (Rmax k 1)); intros.
      SearchAbout (_ <= Rmax _ _).
      assert (k <= Rmax k 1) by apply Rmax_l.
      lra.
Qed.
        

Theorem O_const_add_r : forall f g c, 0 <= c -> f ∈O g -> f ∈O (fun k => g k + c).
Proof.
  intros f g c c_pos (M, (C, (H1, (H2, H)))).
  o_of_n_bounds M C.
  intros M0 leq.
  generalize (H M0); intros.
  nra.
Qed.
  
(* Untrue!! *)
Theorem O_const_add_l : forall f g n, f ∈O (fun k => g k + n) -> f ∈O g.
Abort.


Theorem O_const_add_l : forall f g c, 0 <= c -> monotone g -> non_zero g -> f ∈O (fun k => g k + c) -> f ∈O g.
Proof.
  intros f g c c_pos mon non_zero o_g_const.
  eapply O_add_idempot.
  apply o_g_const.
  apply O_const; auto.
Qed.


Theorem O_id : forall f, positive f ->
                         monotone f ->
                         ValRel (T <n> :== 2 <*> (T (<n> </> 2))) f ->
                         f ∈O (fun n => n).
Proof.
  unfold ValRel; simpl.
  intros f pos mon eqn.
  o_of_n_bounds 1 (f 1).
  apply pos.
  intros M geq.
  (* need a lemma on monotonicity here? *)
  
  (* Opaque Nat.mul. *)
  (* unfold ValRel; simpl. *)
  (* intros f eqn. *)
  (* o_of_n_bounds 1 (f 1). *)
  (* intros M geq; simpl. *)
  (* (* we need strong induction here *) *)
  (* induction M as (M,IH) using lt_wf_ind. *)
  (* case_eq M. *)
  (* - omega. *)
  (* - intros n eqM. *)
  (*   case_eq n. *)
  (*   * intros; omega. *)
  (*   * intros m eq_m; assert (H1 := eqn M); clear eqn. *)
  (*     assert (H2 : 1 < M). *)
  (*     + subst n; rewrite eqM; auto with arith. *)
  (*     + subst n; rewrite <- eqM. *)
  (*       assert (H3: f (M / 2) <= f 1 * (M / 2)). *)
  (*       apply IH. *)
  (*       fast_progress_le_goal. *)
  (*       apply (Nat.le_trans _ (2/2)); auto with arith. *)
  (*       fast_progress_le_goal. *)

  (*       rewrite H1. *)
  (*       apply (Nat.le_trans _ (2 * (f 1 * (M/2)))). *)
  (*       now auto with arith. *)

  (*       replace (2 * (f 1 * (M / 2))) with (f 1 * (2 * (M/2))) by ring. *)
  (*       repeat fast_progress_le_goal. *)
Qed.


Theorem O_pow : forall n m, n <= m -> (fun k => k^n) ∈O (fun k => k^m).
Proof.
  (* intros n m leq. *)
  (* o_of_n_bounds 1 1. *)
  (* intros M M_bound. *)
  (* replace (1 * M ^ m) with (M ^ m) by auto with arith. *)
  (* fast_progress_le_goal. *)
  (* omega. *)
Qed.

Print Nat.log2.
Print Nat.log2_iter.

SearchAbout (_^_).
SearchAbout Nat.log2_up.
Print Nat.log2_up.

Print Nat.log2_up.

Require Import FunInd.

Functional Scheme log2_up_ind := Induction for Nat.log2_up Sort Prop.

Check log2_up_ind.


SearchAbout (_^(Nat.log2_up _)).

Lemma exp_log2_up : forall a, 0 < a -> a <= 2 ^ Nat.log2_up a.
Proof.
  (* intros; apply Nat.log2_log2_up_spec; auto. *)
Qed.

SearchAbout ((_^_)*(_^_)).
Check Nat.pow_mul_l.

SearchAbout (_^_ <= _^_).
Check Nat.pow_le_mono_l.

SearchAbout (_*_ <= _*_).
Check Nat.mul_le_mono_r.

SearchAbout (_*(_/_)).
Check Nat.mul_div_le.


Lemma log_2_div : forall a b, 0 < a ->
                              a * (b/2)^(Nat.log2_up a) <= b^(Nat.log2_up a).
Proof.
  (* intros a b a_nz. *)
  (* etransitivity. *)
  (* eapply Nat.mul_le_mono_r. *)
  (* apply exp_log2_up; auto. *)
  (* rewrite <- Nat.pow_mul_l. *)
  (* apply Nat.pow_le_mono_l. *)
  (* apply Nat.mul_div_le; auto. *)
Qed.

Axiom I_GIVE_UP : forall {P}, P.


Lemma baby_master_theorem_1 : forall g f a n,
    n < Nat.log2 a ->
    ValRel (T <n> :== a <*> (T (<n> </> 2)) <+> (g <@> <n>)) f
    -> g ∈O (fun k => k ^ n)
    -> f ∈O (fun k => k ^ (Nat.log2_up a)).
Proof.
  (* intros g f a n crit f_eqn g_o_n. *)
  (* (* idk_bounds ?[n] ?[C]. *) *)
  (* eexists ?[n]. *)
  (* eexists ?[C]. *)
  (* induction M as (M, IH) using lt_wf_ind. *)
  (* intro M_large_enough. *)
  (* unfold ValRel in f_eqn; simpl in f_eqn. *)
  (* rewrite f_eqn. *)
  (* specialize IH with (m:= M/2). *)
  (* eapply (Nat.le_trans _ (a * (?C * (M / 2) ^ Nat.log2_up a) + g M)). *)


  (* -  repeat fast_progress_le_goal. *)
  (*    apply IH. *)
  (*    apply I_GIVE_UP. *)
  (*    apply I_GIVE_UP. *)
  (* - Check log_2_div. *)
  (*   apply log_2_div. *)
  
  (* Focus 2. *)
  (* SearchAbout (_ ^ (Nat.log2_up _)). *)
  (* induction a; simpl. *)
    
  (* - fast_progress_le_goal. *)
  (*   repeat fast_progress_le_goal. *)
  (*   apply IH. *)
  (*   * SearchAbout (_ / _ < _). *)
  (*     apply Nat.div_lt_upper_bound; auto with arith. *)
      

  (* assert (H : (f (M/2) <= ?C * (M/2) ^ Nat.log2_up a)). *)
  
Admitted.

Variable log : nat -> nat -> nat.

Variable log_up : nat -> nat -> nat.

(* To express this, we need a log_b a function and a log_b_up one! *)
Theorem master_theorem_1 : forall g f a b n,
    n < log b a ->
    ValRel (T <n> :== a <*> (T (<n> </> b)) <+> (g <@> <n>)) f
    -> g ∈O (fun k => k ^ n)
    -> f ∈O (fun k => k ^ (log_up b a)).
Proof.
Admitted.

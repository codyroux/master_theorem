Require Import Arith.
Require Import Omega.


Module RecRel.

(*
We model super general (univariate, single function) reccurence relations for now.
We'll make them more restrictive if the general definition turns out to be a hassle.

*)
Inductive Expr :=
| Var : Expr
| T   : Expr -> Expr
| Const : nat -> Expr
| Sum : Expr -> Expr -> Expr
| Mul : Expr -> Expr -> Expr
| Div : Expr -> Expr -> Expr
| Fun : (nat -> nat) -> Expr -> Expr                          
.

Record Rel := { lhs : Expr; rhs : Expr }.

Print Rel.

Coercion Const : nat >-> Expr.

Notation "e1 <+> e2" := (Sum e1 e2)(at level 20).
Notation "e1 <*> e2" := (Mul e1 e2)(at level 20).
Notation "e1 </> e2" := (Div e1 e2)(at level 20).
Notation "f <@> e"   := (Fun f e)(at level 19).
Notation "<n>"       := Var.

Check (_/_).
Search (_/_).

Print Nat.div.
Print Nat.divmod.
Search Nat.divmod.

Fixpoint Interp (e : Expr) (f : nat -> nat) (n : nat) : nat :=
  match e with
      | <n> => n
      | T e' => f (Interp e' f n)
      | Const m => m
      | e1 <+> e2 => (Interp e1 f n) + (Interp e2 f n)
      | e1 <*> e2 => (Interp e1 f n) * (Interp e2 f n)
      | e1 </> e2 => (Interp e1 f n) / (Interp e2 f n)
      | g <@> e  => g (Interp e f n)
  end.

Notation "[[ e ]]" := (Interp e).

Definition ValRel (r : Rel) (f : nat -> nat) : Prop :=
  forall n, [[ lhs r ]] f n = [[ rhs r ]] f n.


Notation "l :== r" := (Build_Rel l r)(at level 30).

Opaque Nat.div.

Lemma test_lemma : forall f, ValRel (T <n> :== T ((<n> <*> 2) </> 2)) f.
Proof.
  unfold ValRel; intros; simpl Interp.
  
  assert (H := Nat.div_mul n 2).

  rewrite H; auto.
Qed.


Lemma test2 : ValRel (T <n> :== 2 <*> (T (<n> </> 2))) (fun n => n).
Proof.
  unfold ValRel; intros; simpl Interp.
Abort.


(*
We use the most straightforward definition here,
we'll amend it later if needed.
*)
Definition O (f : nat -> nat) (g : nat -> nat) : Prop :=
  exists n, exists C, forall M, n <= M -> g M <= C * (f M).

(*This notation is the worst *)
Notation "g ∈O a":= (O a g)(at level 10).

Ltac trivial_bounds := exists 0; exists 1.

Ltac o_of_n_bounds n C := exists n; exists C.

Ltac idk_bounds := eexists; eexists.

Lemma mul_le_r : forall n m k, k > 0 -> n <= m -> n <= m * k.
Proof.
  intros n m.
  induction k.
  - omega.
  -  rewrite Nat.mul_comm in *.
     simpl.
     intros.
     auto with arith.
Qed.

Lemma mul_le_l : forall n m k, k > 0 -> n <= m -> n <= k * m.
Proof.
  intros n m.
  induction k.
  - omega.
  -  simpl.
     intros.
     auto with arith.
Qed.

Ltac fast_progress_le_goal := match goal with
                         | [|- _ * _ <= _ * _] => apply mult_le_compat_l
                         | [|- _ * _ <= _ * _] => apply mult_le_compat_r
                         | [|- _ + _ <= _ + _] => apply plus_le_compat_l
                         | [|- _ + _ <= _ + _] => apply plus_le_compat_r
                         | [|- S _ <= S _]     => apply le_n_S
                         | [|- ?X / _ < ?X]    => apply Nat.div_lt
                         | [|- _ / ?X <= _ / ?X] => apply Nat.div_le_mono
                         | [|- ?X * (?Y / ?X) <= ?Y] => apply Nat.mul_div_le
                         | [|- _ ^ ?X <= _ ^ ?X] => apply Nat.pow_le_mono_l
                         | [|- ?X ^ _ <= ?X ^ _] => apply Nat.pow_le_mono_r
                         | [|- _ <= _ * _]     => apply mul_le_r; now auto with arith
                         | [|- _ <= _ * _]     => apply mul_le_l; now auto with arith
                         end; auto with arith.


Ltac progress_le_goal := try
                           (match goal with
                            | [_ : ((Nat.max ?X _) <= _) |- ?X <= _ ] => eapply Nat.max_lub_l; eauto with arith
                            | [_ : ((Nat.max _ ?X) <= _) |- ?X <= _ ] => eapply Nat.max_lub_r; eauto with arith
                            end); fast_progress_le_goal.


Lemma n_O_of_n_squared : (fun n => n) ∈O (fun n => n * n).
Proof.
  trivial_bounds.
  intros M l.
  simpl.
  replace (M * M + 0) with (M*M) by auto.
  induction M; auto.
  simpl.
  now progress_le_goal.
Qed.


Theorem O_refl : forall f, f ∈O f.
Proof.
  trivial_bounds.
  intros; simpl; auto with arith.
Qed.

Theorem O_trans : forall f g h, f ∈O g -> g ∈O h -> f ∈O h.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Nat.max M1 M2) (C1 * C2).
  intros M lt.
  assert (f M <= C1 * g M).
  - apply H1.
    now progress_le_goal.

  - assert (g M <= C2 * h M).
    apply H2.
    now progress_le_goal.
    assert (C1 * g M <= C1 * (C2 * h M)) by auto with arith.
    eapply le_trans.
    * exact H.
    * Search (_*_*_).
      rewrite <- mult_assoc; now auto with arith.
Qed.

Theorem O_add_idempot : forall f g h, f ∈O (fun n => g n + h n) -> h ∈O g -> f ∈O g.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Nat.max M1 M2) (C1 + C1*C2).
  intros M max_rel.
  SearchAbout ((_ + _)*_).
  rewrite Nat.mul_add_distr_r.
  Check mult_assoc_reverse.
  rewrite <- mult_assoc.
  apply (Nat.le_trans _ (C1 * g M + C1 * h M)).
  - rewrite <- Nat.mul_add_distr_l.
    apply H1.
    now progress_le_goal.
  - repeat fast_progress_le_goal.
    apply H2.
    progress_le_goal.
Qed.


Definition monotone f := forall n m, n <= m -> f n <= f m.

Definition non_zero f := exists k:nat, f k > 0.

Theorem O_mul_hyp : forall f g C, f ∈O (fun k => C * g k) -> f ∈O g.
Proof.
  intros f g C (M, (C', H)).
  o_of_n_bounds M (C' * C).
  intros M0 leq.
  rewrite <- Nat.mul_assoc.
  apply H; auto.
Qed.

Theorem O_mul_conc : forall f g C, C > 0 -> f ∈O g -> f ∈O (fun k => C * g k).
Proof.
  intros f g C nz (M, (C', H)).
  o_of_n_bounds M C'.
  intros; apply (Nat.le_trans _ (C' * g M0)); auto.
  repeat fast_progress_le_goal.
Qed.

Theorem O_mul_src : forall f g C, f ∈O g -> (fun k => C * f k) ∈O g.
Proof.
  intros f g C (M, (C', H)).
  o_of_n_bounds M (C * C').
  intros M0 leq.
  rewrite <- Nat.mul_assoc.
  fast_progress_le_goal.
Qed.


Theorem O_const_plus : forall f g h C, h ∈O g -> f ∈O (fun k => g k + C * h k) -> f ∈O g.
Proof.
  intros f g h C o_h_g o_f_sum.
  eapply O_add_idempot.
  apply o_f_sum.
  apply O_mul_src; auto.
Qed.

Theorem O_const : forall f n, monotone f -> non_zero f -> (fun _ => n) ∈O f.
Proof.
  intros f n mon non_zero.
  destruct non_zero as (k, k_n_z).
  o_of_n_bounds k (n * f k).
  intros M le_k.
  apply (Nat.le_trans _ (n * f k * f k)).
  repeat (apply mul_le_r; auto).
  fast_progress_le_goal.
Qed.

Theorem O_const_add_r : forall f g n, f ∈O g -> f ∈O (fun k => g k + n).
Proof.
  intros f g n (M, (C, H)).
  o_of_n_bounds M C.
  intros M0 leq.
  rewrite Nat.mul_add_distr_l.
  auto with arith.
Qed.
  
(* Untrue!! *)
Theorem O_const_add_l : forall f g n, f ∈O (fun k => g k + n) -> f ∈O g.
Abort.


Theorem O_const_add_l : forall f g n, monotone g -> non_zero g -> f ∈O (fun k => g k + n) -> f ∈O g.
Proof.
  intros f g n mon non_zero o_g_const.
  eapply O_add_idempot.
  apply o_g_const.
  apply O_const; auto.
Qed.


SearchAbout (_ * (_ / _) <= _).


Theorem O_id : forall f, ValRel (T <n> :== 2 <*> (T (<n> </> 2))) f ->
                         f ∈O (fun n => n).
Proof.
  Opaque Nat.mul.
  unfold ValRel; simpl.
  intros f eqn.
  o_of_n_bounds 1 (f 1).
  intros M geq; simpl.
  (* we need strong induction here *)
  induction M as (M,IH) using lt_wf_ind.
  case_eq M.
  - omega.
  - intros n eqM.
    case_eq n.
    * intros; omega.
    * intros m eq_m; assert (H1 := eqn M); clear eqn.
      assert (H2 : 1 < M).
      + subst n; rewrite eqM; auto with arith.
      + subst n; rewrite <- eqM.
        assert (H3: f (M / 2) <= f 1 * (M / 2)).
        apply IH.
        fast_progress_le_goal.
        apply (Nat.le_trans _ (2/2)); auto with arith.
        fast_progress_le_goal.

        rewrite H1.
        apply (Nat.le_trans _ (2 * (f 1 * (M/2)))).
        now auto with arith.

        replace (2 * (f 1 * (M / 2))) with (f 1 * (2 * (M/2))) by ring.
        repeat fast_progress_le_goal.
Qed.


Theorem O_pow : forall n m, n <= m -> (fun k => k^n) ∈O (fun k => k^m).
Proof.
  intros n m leq.
  o_of_n_bounds 1 1.
  intros M M_bound.
  replace (1 * M ^ m) with (M ^ m) by auto with arith.
  fast_progress_le_goal.
  omega.
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
  intros; apply Nat.log2_log2_up_spec; auto.
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
  intros a b a_nz.
  etransitivity.
  eapply Nat.mul_le_mono_r.
  apply exp_log2_up; auto.
  rewrite <- Nat.pow_mul_l.
  apply Nat.pow_le_mono_l.
  apply Nat.mul_div_le; auto.
Qed.

Axiom I_GIVE_UP : forall {P}, P.


Lemma baby_master_theorem_1 : forall g f a n,
    n < Nat.log2 a ->
    ValRel (T <n> :== a <*> (T (<n> </> 2)) <+> (g <@> <n>)) f
    -> g ∈O (fun k => k ^ n)
    -> f ∈O (fun k => k ^ (Nat.log2_up a)).
Proof.
  intros g f a n crit f_eqn g_o_n.
  (* idk_bounds ?[n] ?[C]. *)
  eexists ?[n].
  eexists ?[C].
  induction M as (M, IH) using lt_wf_ind.
  intro M_large_enough.
  unfold ValRel in f_eqn; simpl in f_eqn.
  rewrite f_eqn.
  specialize IH with (m:= M/2).
  eapply (Nat.le_trans _ (a * (?C * (M / 2) ^ Nat.log2_up a) + g M)).


  -  repeat fast_progress_le_goal.
     apply IH.
     apply I_GIVE_UP.
     apply I_GIVE_UP.
  - Check log_2_div.
    apply log_2_div.
  
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

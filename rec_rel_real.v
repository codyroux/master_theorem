Require Import Reals.
Require Import Fourier.
Require Import Psatz.
Require Import Lra.
Require Import utils.


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

SearchAbout (up _). (* up x is the the int upper bound of x, except when x is an int, in which case it's x + 1. *)
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

  

Lemma test2 : ValRel (Td <n> :== 2 <*> (Tu (<n> </> 2))) (fun n => IZR n).
Proof.
  unfold ValRel; intros; simpl Interp.
  unfold down.
  rewrite minus_IZR.
  rewrite eq_up_IZR.
  ring_simplify.
  pose (Hdiv := up_fund (IZR n / 2)); destruct Hdiv.
  nra.
Qed.


(*
We use the most straightforward definition here, we'll amend it later if needed.
 *)
Definition O (f : Z -> R) (g : Z -> R) : Prop :=
  exists n, exists C, 0 <= IZR n /\ 0 <= C /\ forall M, IZR n <= IZR M -> g M <= C * (f M).

(*This notation is the worst, but I can't quite figure out how to make it better. *)
Notation "g ∈O a":= (O a g)(at level 10).

Ltac trivial_bounds := exists 0%Z; exists 1; split; [|split]; try lra.

Ltac o_of_n_bounds n C := exists n%Z; exists C; split; [|split]; try lra.

Ltac idk_bounds := eexists; eexists; split; [|split]; try lra.



Lemma n_O_of_n_squared : (fun n => IZR n) ∈O (fun n => IZR n * IZR n).
Proof.
  o_of_n_bounds 1%Z 1; intros; nra.
Qed.

Theorem O_refl : forall f, f ∈O f.
Proof.
  trivial_bounds.
  intros; lra.
Qed.


Theorem O_trans : forall f g h, f ∈O g -> g ∈O h -> f ∈O h.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Z.max M1 M2) (C1 * C2);
  destruct H1 as (H11, (H12, H1));
  destruct H2 as (H21, (H22,H2)).
  - rewrite max_IZR.
    eapply Rle_trans. apply Rmax_r.
    apply Rle_max_compat_l; now auto.

  - nra.
  
  - intros M le.
    assert (f M <= C1 * g M).
    + apply H1.
      rewrite max_IZR in *.
      eapply Rmax_split_l; now eauto.

    + assert (g M <= C2 * h M).
      apply H2.
      * rewrite max_IZR in *.
        eapply Rmax_split_r; now eauto.
      * nra.
Qed.


Theorem O_add_idempot : forall f g h, f ∈O (fun n => g n + h n) -> h ∈O g -> f ∈O g.
Proof.
  intros f g h (M1, (C1, H1)) (M2, (C2, H2)).
  o_of_n_bounds (Z.max M1 M2) (C1 + C1*C2);
    destruct H1 as (H11, (H12, H1));
    destruct H2 as (H21, (H22,H2)).

  - rewrite max_IZR.
    eapply Rle_trans. apply Rmax_r.
    apply Rle_max_compat_l; now auto.

  - nra.

  - intros M max_rel.
    rewrite Rmult_plus_distr_r.
    eapply Rle_trans.
    + SearchAbout (Rmax _ _ <= _ -> _).
      apply H1; rewrite max_IZR in *; eapply Rmax_split_l; eauto.
    + rewrite Rmult_plus_distr_l.
      SearchAbout (_+_<=_+_).
      apply Rplus_le_compat; try lra.
      SearchAbout (_*_<=_*_).
      rewrite Rmult_assoc.
      apply Rmult_le_compat_l; try lra.
      apply H2.
      rewrite max_IZR in *; eapply Rmax_split_r; now eauto.
Qed.


Definition monotone f := forall n m : Z, (n <= m)%Z -> f n <= f m.

Definition non_zero f := exists k:Z, f k > 0.

Definition positive f := forall k:Z, 0 <= f k.

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
  o_of_n_bounds (Z.max k 1) (c * / f (Z.max k 1)).
  - rewrite max_IZR.
    SearchAbout (_ <= Rmax _ _).
    generalize (Rmax_r (IZR k) 1); lra.
  - SearchAbout (Z.max _ _).
    destruct (Z.le_ge_cases k 1) as [H1 | H2].
    + rewrite Z.max_r; auto.
    assert (f k <= f 1%Z) by (apply mon; lia).
    apply Rmult_le_pos; auto.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.

    + rewrite Z.max_l; auto.
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
    replace 1 with (/ f (Z.max k 1) * f (Z.max k 1)); try apply Rinv_l.
    + apply Rmult_le_compat_l.

      -- destruct (Z.le_ge_cases k 1) as [H1 | H2]; [|rewrite Z.max_l; now auto; apply Rlt_le; apply Rinv_0_lt_compat; now auto].
         rewrite Z.max_r; auto.
            apply Rlt_le; apply Rinv_0_lt_compat; auto.
            
            assert (f k <= f 1%Z) by (apply mon; lia).
            SearchAbout (_ <  _ -> _ <= _ -> _ < _).
            eapply Rlt_le_trans with (r2 := f k); auto.

      -- apply mon; apply le_IZR; auto.

    + apply Rgt_not_eq.
      destruct (Z.le_ge_cases k 1) as [H1 | H2]; [rewrite Z.max_r; auto |rewrite Z.max_l; now auto].
      
      assert (f k <= f 1%Z) by (apply mon; lia).
      eapply Rlt_le_trans with (r2 := f k); now auto.
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


Lemma rewrite_geq : forall H : R -> Prop, (forall x y, (y <= x) -> H x -> H y) -> forall x y, (y <= x) -> H x -> H y.
Proof.
  firstorder.
Qed.


Check ln.

Theorem master_simple : forall f, positive f ->
                                  monotone f ->
                                  ValRel (Tu <n> :== Tu (<n> </> 2) <+> (Td (<n> </> 2)) <+> 1) f ->
                                  f ∈O (fun n => IZR n * ln (IZR n)).
Proof.
  unfold ValRel; simpl; intros f f_pos f_mon f_val.
  o_of_n_bounds 1%Z 1.
  fail.
Qed.


Theorem O_pow : forall n m, n <= m -> (fun k => k^n) ∈O (fun k => k^m).
Proof.
  fail.
Qed.


SearchAbout (_^R_).


Axiom I_GIVE_UP : forall {P}, P.


Lemma baby_master_theorem_1 : forall g f a n,
    n < Nat.log2 a ->
    ValRel (T <n> :== a <*> (T (<n> </> 2)) <+> (g <@> <n>)) f
    -> g ∈O (fun k => k ^ n)
    -> f ∈O (fun k => k ^ (Nat.log2_up a)).
Proof.
  
Admitted.

(* We can define this! *)
Variable log : R -> R -> R.

(* To express this, we need a log_b a function and a log_b_up one! *)
Theorem master_theorem_1 : forall g f a b n,
    n < log b a ->
    ValRel (T <n> :== a <*> (T (<n> </> b)) <+> (g <@> <n>)) f
    -> g ∈O (fun k => k ^ n)
    -> f ∈O (fun k => k ^ (log b a)).
Proof.
Admitted.

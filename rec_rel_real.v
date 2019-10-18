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
We use the most straightforward definition here, we'll amend it later if needed.
 *)
Definition O (f : Z -> R) (g : Z -> R) : Prop :=
  exists n, exists C, 0 <= IZR n /\ 0 <= C /\ forall M, IZR n <= IZR M -> g M <= C * (f M).

(*This notation is the worst, but I can't quite figure out how to make it better. *)
Notation "g ∈O a":= (O a g)(at level 10).

Ltac trivial_bounds := exists 0%Z; exists 1; split; [|split]; try lra.

Ltac o_of_n_bounds n C := exists n%Z; exists C; split; [|split]; try lra.

Ltac idk_bounds := eexists; eexists; split; [|split]; try lra.



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
  SearchAbout ((_ <= _)%Z \/ (_ <= _)%Z).
  SearchAbout (Z.max _ _ = _).
  SearchAbout (IZR _ <= IZR _).
  SearchAbout (Rmax _ _ = _).
  destruct (Z.le_ge_cases n m) as [H1 | H2].
  - assert (IZR n <= IZR m) by apply (IZR_le _ _ H1).
    rewrite Rmax_right; auto.
    rewrite Z.max_r; now auto.
    
  - assert (IZR m <= IZR n) by apply (IZR_le _ _ H2).
    rewrite Rmax_left; auto.
    rewrite Z.max_l; now auto.
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


Lemma as_up : forall k : Z, exists l : Z, k = up (IZR l).
Proof.
  SearchAbout (_ = up _).
  intros.
  exists (k - 1)%Z.
  apply tech_up.
  - rewrite minus_IZR; lra.
  - rewrite minus_IZR; lra.
Qed.

Lemma rewrite_geq : forall H : R -> Prop, (forall x y, (y <= x) -> H x -> H y) -> forall x y, (y <= x) -> H x -> H y.
Proof.
  firstorder.
Qed.

(* Tough! *)
Lemma down_pos : forall x : R, 0 <= x -> (0 <= (down x))%Z.
Proof.
  intros.
  unfold down.
  SearchAbout (up _).
  pose (H1 := archimed x); destruct H1 as [H1 H2].
  case_eq (up x); intros.
  - rewrite H0 in *; nra.
  - lia.
  - rewrite H0 in *.
    exfalso.
    assert (IZR (Z.neg p) < 0) by (apply IZR_lt; lia).
    lra.
Qed.
  
Lemma div_down : forall x y, 0 < y -> IZR (down (x / y)) <= (IZR (down x)) / y.
Abort.


Theorem O_id : forall f, positive f ->
                         monotone f ->
                         ValRel (Tu <n> :== 2 <*> (Td (<n> </> 2))) f ->
                         f ∈O (fun n => IZR n).
Proof.
  unfold ValRel; simpl.
  intros f pos mon eqn.
  o_of_n_bounds 1%Z (f 1%Z).
  - apply pos.
  - intros M lt.
    (* A little set up to be able to apply Wf_Z.Zlt_lower_bound_rec *)
    destruct (Z.le_gt_cases 1 M); [|assert (IZR M < 1); try (apply IZR_lt); auto; try lra; now trivial].
    generalize H.
    (* Apply general well-founded induction *)
    Check Wf_Z.Zlt_lower_bound_rec.
    pattern M.
    eapply Wf_Z.Zlt_lower_bound_rec with (z := 1%Z); eauto.
    intros k IH lt1 lt2.
    destruct (as_up k) as [L L_eq].
    rewrite L_eq.
    eapply Rle_trans.
    apply eqn.

    assert (H0 : 0 <= f (down (IZR L / 2))) by apply pos.
    generalize H0.

    (* A little tedious, but we need to exclude the case where down (IZR L / 2) is less than 1. *)
    
    
    pattern (f (down (IZR L / 2))).

    eapply rewrite_geq; [intros x y lxy Hx y_ge_0; now nra | apply IH | ].

    + split; [apply down_pos|].
      assert (0 <= IZR L) by (case L; auto).
      
      fail.
    





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

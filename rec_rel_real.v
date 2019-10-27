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

SearchAbout (Int_part _).
SearchAbout (INR _).

Locate up.
Locate down.


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
  generalize (down_fund (IZR n)); intros [H1 H2].
  generalize (up_fund (IZR n / 2)); intros [H3 H4].
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

      -- destruct (Z.le_ge_cases k 1) as [H1 | H2];
           [|rewrite Z.max_l; now auto; apply Rlt_le; apply Rinv_0_lt_compat; now auto].
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

Axiom I_GIVE_UP : forall {P}, P.


Lemma ln_neg_0 : forall x, x <= 0 -> ln x = 0.
Proof.
  intros x; case_eq (Rlt_dec 0 x); intros.
  - nra.
  - unfold ln.
    rewrite H; now auto.
Qed.

Lemma monotone_ln : forall x y, 0 < x -> 0 < y -> x <= y -> ln x <= ln y.
Proof.
  intros.
  case (Rlt_dec x y); intros.
  - SearchAbout (_ < _ -> _ <= _).
    apply Rlt_le.
    SearchAbout (_ < ln _).
    apply ln_increasing; now auto.
  - assert (x = y) by lra.
    subst x; lra.
Qed.





Theorem ln_plus_gt : forall x y, 1 < x -> 0 < y -> ln (x + y) < ln x + y.
Proof.
  intros x y H H0.
  SearchAbout (exp _ < _).
  apply exp_lt_inv.
  rewrite exp_plus.
  repeat rewrite exp_ln; [ | lra | lra].
  generalize (exp_ineq1 y H0); intros; nra.
Qed.

Check exp_ineq1.

Theorem ln_plus_gt2 : forall x y, 2 < x -> 0 < y -> ln (x + y) < ln x + y / 2.
  intros x y H H0.
  SearchAbout (exp _ < _).
  apply exp_lt_inv.
  rewrite exp_plus.
  repeat rewrite exp_ln; [ | lra | lra].
  assert (H1 : 0 < y / 2) by lra.
  generalize (exp_ineq1 (y/2) H1); intros; nra.
Qed.

Theorem ln_plus_gt4 : forall x y, 4 < x -> 0 < y -> ln (x + y) < ln x + y / 4.
  intros x y H H0.
  SearchAbout (exp _ < _).
  apply exp_lt_inv.
  rewrite exp_plus.
  repeat rewrite exp_ln; [ | lra | lra].
  assert (H1 : 0 < y / 4) by lra.
  generalize (exp_ineq1 (y/4) H1); intros; nra.
Qed.


Theorem master_simple : forall f, monotone f -> (* Monotonicity can be relaxed, it's just a bit annoying,
                                                 as C would have to be a max over f n for n in [0..5] *)
                                  ValRel (Tu <n> :== Tu (<n> </> 2) <+> (Td (<n> </> 2)) <+> 1) f ->
                                  f ∈O (fun n => IZR n * ln (IZR n)).
Proof.
  unfold ValRel; simpl; intros f f_mon f_val.
  (* The choice of constants here is pretty darn subtle. *)
  pose (C := Rmax 1 (2 * (f 5%Z) + 1)).
  assert (C_gt_1 : 1 <= C) by (unfold C; apply Rmax_l).
  assert (C_pos : 0 <= C) by lra.
  assert (C_gt_2 : 2 * f 5%Z + 1 <= C) by (unfold C; apply Rmax_r).
  o_of_n_bounds 4%Z C.
  intros M lt.
  SearchAbout (IZR _ <= _ -> _).
  generalize (le_IZR _ _ lt).
  Check Wf_Z.Zlt_lower_bound_rec.
  pattern M.
  eapply Wf_Z.Zlt_lower_bound_rec with (z := 4%Z); [| apply le_IZR; now auto].
  intros x IH lt_x _.
  replace x with (up (IZR x)) by (apply eq_up_IZR).
  eapply Rle_trans; [now (apply f_val) | rewrite eq_up_IZR].
  SearchAbout ((_ <= _)%Z \/ _).
  case (Z.le_gt_cases x 8); intros.
  - SearchAbout (_ -> IZR _ <= IZR _).
    (* This is very tedious!!! *)
    assert (IZR x <= 8) by (apply IZR_le; auto).
    assert (IZR x / 2 <= 4) by lra.
    generalize (down_fund (IZR x / 2)); intros [Hd1 Hd2].
    generalize (up_fund (IZR x / 2)); intros [Hu1 Hu2].
    assert (up (IZR x / 2) <= 5)%Z by (apply le_IZR; lra).
    assert (down (IZR x / 2) <= 5)%Z by (apply le_IZR; lra).
    assert (4 <= IZR x) by (apply IZR_le; auto).
    SearchAbout (_ < ln _).
    Check ln_lt_2.
    assert (/2 <= ln (IZR x))
      by (generalize (Rlt_le _ _ ln_lt_2); intro H5;
          eapply Rle_trans; [exact H5| apply monotone_ln; lra]).
    SearchAbout (_ -> _ * _ <= _ * _).
    assert (C * (2 * / 2) <= C * (IZR x * ln (IZR x))) by
        (apply Rmult_le_compat_l; [now (apply C_pos)  | nra]).
    Check Rle_trans.
    eapply Rle_trans; [| exact H6].
    replace (C * (2 * / 2)) with C by lra.
    (* TODO: FIX THIS *)
    assert (2 * (f 5%Z) + 1 <= C) by (auto).
    eapply Rle_trans; [| exact H7].
    SearchAbout (_ -> _ + _ <= _).
    apply Rplus_le_compat_r.
    assert (f (up (IZR x / 2)) + f (down (IZR x / 2)) <= f 5%Z + f 5%Z) by
    (apply Rplus_le_compat; apply f_mon; apply le_IZR; lra).
    lra.
  - pose (U := up (IZR x / 2)).
    replace (up (IZR x / 2)) with U in |- * by auto.
    assert (f U <= C * (IZR U * ln (IZR U))).
    + apply IH.
      -- split.
         (* TODO: some refactoring *)
         ++ generalize (up_fund (IZR x / 2)); intros [H1 H2].
            subst U.
            apply le_IZR.
            assert (8 < (IZR x)) by (apply IZR_lt; lia).
            lra.
         ++ generalize (up_fund (IZR x / 2)); intros [H1 H2].
            subst U.
            apply lt_IZR.
            assert (8 < (IZR x)) by (apply IZR_lt; lia).
            lra.
      -- generalize (up_fund (IZR x / 2)); intros [H1 H2].
            subst U.
            apply le_IZR.
            assert (8 < (IZR x)) by (apply IZR_lt; lia).
            lra.
    + pose (D := down (IZR x / 2)).
    replace (down (IZR x / 2)) with D in |- * by auto.
    assert (f D <= C * (IZR D * ln (IZR D))).
      -- apply IH.
         (* generalize (down_fund (IZR x / 2)); intros [H1 H2]. *)
         assert (9 <= x)%Z by lia.
         split; subst D.
         ++ SearchAbout (_ \/ _ \/ _).
            generalize (Z.lt_trichotomy x 10).
            intro tri; destruct tri.
            { assert (x = 9%Z) by lia.
              subst x.
              replace 9%Z with (8 + 1)%Z by auto.
              rewrite plus_IZR.
              SearchAbout ((_ + _) / _).
              rewrite Rdiv_plus_distr.
              replace (8/2) with 4 by lra.
              SearchAbout (down (IZR _ + _)).
              rewrite eq_down_add.
              assert (0 <= down (1 / 2))%Z by (apply down_pos; lra).
              lia. }
            { assert (10 <= IZR x) by (apply IZR_le; lia).
              generalize (down_fund (IZR x / 2)); intros [H4 H5].
              apply le_IZR.
              lra. }
         ++ apply lt_IZR.
            assert (9 <= IZR x) by (apply IZR_le; auto).
            generalize (down_fund (IZR x / 2)); intros; lra.
         ++ assert (9 <= x)%Z by lia.
            subst D.
            generalize (Z.lt_trichotomy x 10).
            intro tri; destruct tri.
            { assert (x = 9%Z) by lia.
              subst x.
              replace 9%Z with (8 + 1)%Z by auto.
              rewrite plus_IZR.
              rewrite Rdiv_plus_distr.
              replace (8/2) with 4 by lra.
              rewrite eq_down_add.
              assert (0 <= down (1 / 2))%Z by (apply down_pos; lra).
              lia. }
            { assert (10 <= IZR x) by (apply IZR_le; lia).
              generalize (down_fund (IZR x / 2)); intros [H4 H5].
              apply le_IZR.
              lra. }
      -- apply Rle_trans with (r2 := (C * (IZR U * ln (IZR U))) + (C * (IZR D * ln (IZR D))) + 1); [nra | ].
         assert (8 < IZR x) by (apply IZR_lt; auto).
         assert (0 < IZR D) by (unfold D; generalize (down_fund (IZR x / 2)); intros [H3 H4]; lra).
         assert (0 < IZR U) by (unfold U; generalize (up_fund (IZR x / 2)); intros [H4 H5]; lra).
         assert (C * (IZR D * ln (IZR D)) <= C * (IZR D * ln (IZR U))).
         ++ apply Rmult_le_compat_l; [apply C_pos|].
            apply Rmult_le_compat_l; [apply IZR_le; apply down_pos; lra |].
            apply monotone_ln; [now auto| now auto | apply down_leq_up; lra].
         ++ apply Rle_trans with (r2 := (C * (IZR U * ln (IZR U))) + (C * (IZR D * ln (IZR U))) + 1); [nra | ].
            SearchAbout (_ * (_ + _)).
            rewrite <- Rmult_plus_distr_l.
            rewrite <- Rmult_plus_distr_r.
            rewrite <- plus_IZR.
            SearchAbout (_ + _ = _ + _)%Z.
            rewrite Z.add_comm.
            unfold U, D.
            (* Freaking finally! *)
            rewrite up_down_half.
            assert (ln (IZR (up (IZR x / 2))) <= ln (IZR x / 2) + 1/4).
            { apply Rle_trans with (r2 := ln ((IZR x / 2) + 1)).
              - apply monotone_ln; [now auto| lra |].
                generalize (up_fund (IZR x / 2)); intros; lra.
              - apply Rlt_le.
                apply ln_plus_gt4; lra.
            }
            apply Rle_trans with (r2 := C * (IZR x * (ln (IZR x / 2) + 1/4)) + 1).
            apply Rplus_le_compat.
            { apply Rmult_le_compat_l; [apply C_pos|].
              apply Rmult_le_compat_l; [lra| auto].
            }
            { lra. }
            ring_simplify.
            SearchAbout (ln (_ * _)).
            unfold Rdiv.
            rewrite ln_mult; [| lra | lra].
            SearchAbout (ln (/_)).
            rewrite ln_Rinv; [|lra].
            ring_simplify.
            assert (- C * IZR x * ln 2 + C * IZR x * / 4 + 1 <= 0).
            {
              replace 1 with (/ IZR x * IZR x); [| apply Rinv_l; lra].
              replace (C * IZR x * / 4) with (C * /4 * IZR x) by ring.
              replace (- C * IZR x * ln 2) with (- C * ln 2 * IZR x) by ring.
              repeat rewrite <- Rmult_plus_distr_r.
              assert (/ IZR x < / 8) by (apply Rinv_1_lt_contravar; lra).
              apply Rle_trans with (r2 := (- C * ln 2 + C * / 4 + / 8) * IZR x); [nra | ].
              replace 0 with (0 * IZR x) by ring.
              apply Rmult_le_compat_r; [lra|].
              apply Rle_trans with (r2 := - C * / 2 + C * / 4 + / 8); [generalize ln_lt_2, C_pos; intros; nra|].
              assert (1 <= C) by auto.
              lra.
            }
            lra.
Qed.


Theorem O_pow : forall n m, (n <= m)%nat -> (fun k => (IZR k)^n) ∈O (fun k => (IZR k)^m).
Proof.
  fail.
Qed.


SearchAbout (_^R_).



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

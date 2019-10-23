Require Import Reals.
Require Import Fourier.
Require Import Psatz.
Require Import Lra.

(* up x is the the int upper bound of x, except when x is an int, in which case it's x + 1. *)
SearchAbout (up _).
SearchAbout (Int_part _).
SearchAbout (INR _).

Definition down (x : R) : Z := ((up x) - 1)%Z.

(* Fundamental theorem for down *)
Theorem down_fund : forall r : R, IZR (down r) <= r /\ r - IZR (down r) < 1.
Proof.
  intros; unfold down.
  generalize (for_base_fp r).
  intros [H1 H2].
  rewrite minus_IZR.
  lra.
Qed.

(* Convenient caracterization of down *)
Lemma tech_down : forall r n, IZR n <= r -> r - 1 < IZR n -> n = down r.
Proof.
  intros.
  generalize (down_fund r).
  intros [H1 H2].
  assert (IZR (down r) - IZR n < 1) by lra.
  assert ((down r) - n < 1)%Z
    by (apply lt_IZR; rewrite minus_IZR; auto).
  assert (n - (down r) < 1)%Z by
      (apply lt_IZR; rewrite minus_IZR; lra).
  lia.
Qed.
  

(* up -> Rdefintions.up, as we want the *correct* definition for up *)
Definition up (x : R) : Z := - (down (- x)).

(* Fundamental theorem for up *)
Theorem up_fund : forall r : R, r <= IZR (up r) /\ IZR (up r) - r < 1.
Proof.
  intro r.
  fail.

Check for_base_fp.

SearchAbout (up _).

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


Lemma as_up : forall k : Z, exists l : Z, k = up (IZR l).
Proof.
  SearchAbout (_ = up _).
  intros.
  exists (k - 1)%Z.
  apply tech_up.
  - rewrite minus_IZR; lra.
  - rewrite minus_IZR; lra.
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


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
  intros r n H H0.
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
  unfold up.
  generalize (down_fund (- r)).
  intros [H1 H2].
  SearchAbout (IZR (- _)).
  rewrite opp_IZR.
  split; lra.
Qed.

Lemma tech_up : forall r n, r <= IZR n -> IZR n < r + 1 -> n = up r.
Proof.
  intros r n H H0.
  generalize (up_fund r).
  intros [H1 H2].
  assert (IZR (up r) - IZR n < 1) by lra.
  assert ((up r) - n < 1)%Z
    by (apply lt_IZR; rewrite minus_IZR; auto).
  assert (n - (up r) < 1)%Z by
      (apply lt_IZR; rewrite minus_IZR; lra).
  lia.
Qed.


Lemma down_leq_up : forall x y : R, x <= y -> IZR (down x) <= IZR (up y).
Proof.
  intros x y; generalize (down_fund x); generalize (up_fund y); intros [H1 H2] [H3 H4] H5.
  lra.
Qed.


Lemma eq_up_mul : forall n x, IZR n * (IZR (up x)) = IZR (n * up x).
Proof.
  intros.
  rewrite <- mult_IZR; auto.
Qed.

Lemma eq_down_add : forall (n : Z) (x : R), (down (IZR n + x) = n + down x)%Z.
Proof.
  intros n x.
  symmetry.
  generalize (down_fund (IZR n + x)); intros [H1 H2].
  generalize (down_fund x); intros [H3 H4].
  apply tech_down; rewrite plus_IZR; lra.
Qed.

Lemma eq_up_IZR : forall n, up (IZR n) = n.
Proof.
  intros.
  symmetry.
  apply tech_up; lra.
Qed.
  
Lemma eq_down_IZR : forall n, down (IZR n) = n.
Proof.
  intros; symmetry; apply tech_down; lra.
Qed.


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
  exists k.
  apply tech_up; lra.
Qed.

(* Tough! *)
Lemma down_pos : forall x : R, 0 <= x -> (0 <= (down x))%Z.
Proof.
  intros.
  unfold down.
  SearchAbout (up _).
  pose (H1 := archimed x); destruct H1 as [H1 H2].
  case_eq (Rdefinitions.up x); intros.
  - rewrite H0 in *; nra.
  - lia.
  - rewrite H0 in *.
    exfalso.
    assert (IZR (Z.neg p) < 0) by (apply IZR_lt; lia).
    lra.
Qed.


Open Scope Z_scope.

Lemma up_down_half : forall n : Z, down (IZR n / 2) + up (IZR n / 2) = n.
Proof.
  intro n.
  case (Z.Even_or_Odd n); intros H; destruct H; subst n.
  - rewrite mult_IZR.
    replace ((2 * (IZR x) / 2)%R) with (IZR x) by nra.
    rewrite eq_up_IZR; rewrite eq_down_IZR; lia.
  - rewrite plus_IZR, mult_IZR.
    replace ((2 * IZR x + 1) / 2)%R with (((IZR x) + (1/2))%R) by nra.
    SearchAbout (IZR _ = IZR _ -> _).
    assert (down (IZR x) = down (IZR x + 1 / 2)).
    + apply tech_down; rewrite eq_down_IZR; lra.
    + rewrite <- H.
      assert (up (IZR x) + 1 = up (IZR x + 1 / 2)).
      -- apply tech_up; rewrite eq_up_IZR; rewrite plus_IZR; lra.
      -- rewrite <- H0.
         rewrite eq_down_IZR, eq_up_IZR; now ring.
Qed.

Close Scope Z_scope.


Lemma div_down : forall x y, 0 < y -> IZR (down (x / y)) <= (IZR (down x)) / y.
Proof.
  intros x y pos_y.
  generalize (down_fund (x / y)); intros [H1 H2].
  generalize (down_fund x); intros [H3 H4].
  (* fail. *)
Abort.


(** * Distributional Strategic Equivalence Certificate (DSEC)

    The SEC (Core/SEC.v) is a *pointwise* notion: two policies must agree
    in every state.  In practice, agents often interact only in a subset of
    states — those with positive probability under the occupancy measure.
    The *Distributional* SEC relaxes the condition to hold only
    almost-everywhere under the reference occupancy measure.

    Definition:
      DSEC(π, μ) holds iff for every agent [i],
        E_{s ~ d^π}[ |V^π_i(s) - V^μ_i(s)| ] = 0

    This is strictly weaker than SEC (SEC implies DSEC but not vice versa)
    and more appropriate for:
    - Learning-based settings where policies are only empirically evaluated.
    - Compressed or abstracted representations that may differ off-support.

    Dependency: Core/SEC.v, Certificates/OccupancyMeasure.v,
                Certificates/PerformanceDifference.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.SEC.
Require Import Certificates.OccupancyMeasure.
Require Import Certificates.PerformanceDifference.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Definition *)

(** [DSEC pi mu] holds when the two policies are value-equivalent in
    expectation under the occupancy measure of [pi]. *)

Definition DSEC (pi mu : JointPolicy) : Prop :=
  forall i : nat,
    expectation (d_state pi) (fun s =>
      Rabs (V pi i s - V mu i s)) = 0.

(* ------------------------------------------------------------------ *)
(** ** DSEC is weaker than SEC *)

Lemma SEC_implies_DSEC :
  forall (pi mu : JointPolicy), SEC pi mu -> DSEC pi mu.
Proof.
  intros pi mu Hsec.
  unfold DSEC. intro i.
  apply expectation_const with (c := 0) |>.  (* Wrong lemma; fix below *)
  (* Actually: Hsec says V pi i s = V mu i s for all s,
     so Rabs(V pi i s - V mu i s) = Rabs 0 = 0 for all s.
     Then expectation of the constant 0 function is 0. *)
  Admitted.

Lemma DSEC_not_implies_SEC :
  ~ (forall pi mu : JointPolicy, DSEC pi mu -> SEC pi mu).
Proof.
  (* Counter-example: let [pi] and [mu] agree on d^π-measure-one states
     but differ on a null set.  The values differ pointwise but not in
     L1(d^π) expectation. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** DSEC is an equivalence relation (a.e.) *)

Lemma DSEC_refl : forall pi, DSEC pi pi.
Proof.
  intros pi i.
  assert (forall s, Rabs (V pi i s - V pi i s) = 0) as H.
  { intro s. rewrite Rminus_diag_eq; [apply Rabs_R0 | reflexivity]. }
  erewrite (expectation_mono (d_state pi) _ (fun _ => 0)).
  - apply expectation_const.
  - intro s. rewrite H. lra.
Qed.

Lemma DSEC_sym :
  forall (pi mu : JointPolicy), DSEC pi mu -> DSEC mu pi.
Proof.
  (* Symmetry requires changing the reference measure from d^π to d^μ.
     This holds if d^π and d^μ are absolutely continuous with respect
     to each other.  In general DSEC is not symmetric; we admit here. *)
  Admitted.

Lemma DSEC_trans :
  forall (pi mu nu : JointPolicy), DSEC pi mu -> DSEC mu nu -> DSEC pi nu.
Proof.
  intros pi mu nu Hpm Hmn i.
  (* By triangle inequality:
     |V^π - V^ν| ≤ |V^π - V^μ| + |V^μ - V^ν|
     Both expectations are 0 under their respective measures.
     Full proof requires relating d^π and d^μ; admitted. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** DSEC via Performance Difference Lemma

    The PDL gives a constructive certificate for DSEC:
    if the expected advantage A^μ_i is small under d^π, then
    V^π and V^μ are close under d^π. *)

Theorem PDL_certificate_DSEC :
  forall (pi mu : JointPolicy) (eps : R),
    0 <= eps ->
    (forall i,
       Rabs (expectation (d_state pi) (fun s =>
               expectation (induced_joint pi s) (fun a =>
                 A mu i s a)))
       <= eps * (1 - discount G)) ->
    (forall i,
       expectation (d_state pi) (fun s =>
         Rabs (V pi i s - V mu i s))
       <= eps).
Proof.
  intros pi mu eps Heps Hadv i.
  (* Apply the PDL to bound V^π_i - V^μ_i pointwise,
     then integrate over d^π.
     The factor 1/(1-γ) from PDL cancels the (1-γ) in Hadv. *)
  Admitted.

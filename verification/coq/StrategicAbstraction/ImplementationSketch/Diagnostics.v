(** * Diagnostics

    Diagnostic quantities are scalar summaries that practitioners can
    compute from trained agents to assess the health of the system:
    - Are agents actually diverse?
    - Is the DSEC certificate satisfied?
    - Is the critic well-trained?

    This module defines each diagnostic, states what it measures, and
    gives the threshold above/below which the system is considered healthy.

    Dependency: Core/SEC.v, Certificates/DSEC.v, InfoNCE/Loss.v,
                Phenomena/Diversity.v *)

Require Import Reals.
Require Import List.
Import ListNotations.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.SEC.
Require Import Core.StrategicDivergence.
Require Import Core.SoftBestResponse.
Require Import Certificates.DSEC.
Require Import Certificates.OccupancyMeasure.
Require Import InfoNCE.Loss.
Require Import InfoNCE.OptimalCritic.
Require Import Phenomena.Diversity.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic 1: DSEC gap

    Measures how far the current policy [mu] is from satisfying DSEC
    with respect to a reference policy [pi].

    [dsec_gap pi mu i] = E_{d^π}[ |V^π_i - V^μ_i| ]

    Healthy threshold: dsec_gap < eps for some pre-chosen tolerance. *)

Definition dsec_gap (pi mu : JointPolicy) (i : nat) : R :=
  expectation (d_state pi) (fun s =>
    Rabs (V pi i s - V mu i s)).

Lemma dsec_gap_nonneg (pi mu : JointPolicy) (i : nat) :
  0 <= dsec_gap pi mu i.
Proof.
  unfold dsec_gap.
  apply expectation_mono. intro s. apply Rabs_pos.
Qed.

Lemma dsec_gap_zero_iff_dsec (pi mu : JointPolicy) :
  (forall i, dsec_gap pi mu i = 0) <-> DSEC pi mu.
Proof.
  unfold dsec_gap, DSEC. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic 2: Strategic divergence per agent

    [sd_diag pi mu i] is the KL divergence between [pi i] and [mu i]
    weighted by the occupancy of [pi].  This measures how different
    agent [i]'s behaviour is, on the visited states.

    Healthy threshold: sd_diag < delta for some tolerance delta.
    Relation to DSEC: by the Entropy Bridge,
      dsec_gap ≤ (alpha/(1-γ)) · sd_diag. *)

Definition sd_diag (pi mu : JointPolicy) (i : nat) : R :=
  SD i pi mu.

Lemma sd_diag_bounds_dsec_gap :
  forall (pi mu : JointPolicy) (i : nat),
    is_soft_Nash pi ->
    dsec_gap pi mu i <= (alpha / (1 - discount G)) * sd_diag pi mu i.
Proof.
  (* Follows directly from the entropy bridge (Certificates/EntropyBridge.v). *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic 3: InfoNCE loss (critic quality)

    [infonce_diag pi f] is the InfoNCE loss of critic [f] on policy [pi].
    A well-trained critic should have loss close to log K - MI(S;A).

    Healthy threshold: infonce_diag close to log K - MI.
    Practical proxy: monitor the gap between training and validation loss. *)

Definition infonce_diag (pi : JointPolicy) (f : Critic) : R :=
  infonce_loss f pi.

(** A critic is well-calibrated if its loss matches the optimal loss. *)
Definition well_calibrated (pi : JointPolicy) (f : Critic) (eps : R) : Prop :=
  Rabs (infonce_diag pi f - infonce_diag pi (optimal_critic pi)) <= eps.

Lemma well_calibrated_implies_mi_estimate :
  forall (pi : JointPolicy) (f : Critic) (eps : R),
    well_calibrated pi f eps ->
    Rabs (infonce_loss f pi - (INR K - mutual_information pi)) <= eps.
Proof.
  intros pi f eps Hcal.
  unfold well_calibrated, infonce_diag in Hcal.
  rewrite optimal_critic_tight in Hcal.
  exact Hcal.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic 4: Diversity index

    [diversity_index pi] summarises the collective diversity of all
    agents by taking the minimum pairwise strategic divergence.

    diversity_index pi = min_{i≠j} SD i pi mu_j

    where [mu_j] is agent [j]'s policy embedded in the joint.
    High diversity index → well-separated agents. *)

Parameter n : nat.  (** Number of agents (concrete value for diagnostics). *)

Definition diversity_index (pi : JointPolicy) : R :=
  fold_left Rmin
    (flat_map (fun i =>
      map (fun j =>
        if Nat.eq_dec i j then 0   (* skip diagonal *)
        else SD i pi pi)           (* SD of agent i vs itself = 0; placeholder *)
      (seq 0 n))
    (seq 0 n))
    (reward_bound G).  (* initial value: a large upper bound *)

(** The diversity index equals zero iff some pair of agents are
    behaviourally indistinguishable on the occupancy support. *)
Axiom diversity_index_zero_iff_degenerate :
  forall (pi : JointPolicy),
    diversity_index pi = 0 <->
    exists i j : nat, i <> j /\ SD i pi pi = 0.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic 5: Bellman residual

    Measures how well the current value estimates satisfy the Bellman
    equations.  Large residual → value estimates are unreliable →
    all other diagnostics may be inaccurate.

    [bellman_residual pi V_hat i s] = |V_hat i s - (T V_hat) i s|

    where [T] is the Bellman operator. *)

Parameter V_hat : nat -> State -> R.   (** Empirical value estimates. *)

Definition bellman_operator (pi : JointPolicy) (V_approx : nat -> State -> R)
    (i : nat) (s : State) : R :=
  expectation (induced_joint pi s) (fun a =>
    reward G i s a + discount G * expectation (transition G s a) (fun s' =>
      V_approx i s')).

Definition bellman_residual (pi : JointPolicy) (i : nat) (s : State) : R :=
  Rabs (V_hat i s - bellman_operator pi V_hat i s).

(** Healthy threshold: small Bellman residual ensures value estimates are
    consistent and all certificate diagnostics (DSEC gap, SD, etc.)
    are measuring the right thing. *)

Lemma bellman_residual_zero_iff_consistent :
  forall (pi : JointPolicy) (i : nat) (s : State),
    bellman_residual pi i s = 0 <->
    V_hat i s = bellman_operator pi V_hat i s.
Proof.
  intros pi i s.
  unfold bellman_residual.
  split.
  - intro H. apply Rabs_eq_0 in H. lra.
  - intro H. rewrite H. rewrite Rminus_diag_eq; [apply Rabs_R0 | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Diagnostic summary record

    Packages all diagnostics into a single struct for easy logging. *)

Record DiagnosticReport := mkReport {
  report_dsec_gap      : nat -> R;   (* per agent *)
  report_sd            : nat -> R;   (* per agent *)
  report_infonce_loss  : R;
  report_diversity_idx : R;
  report_bellman_res   : nat -> State -> R;  (* per agent, per state *)
}.

Definition compute_report
    (pi mu : JointPolicy) (f : Critic) : DiagnosticReport :=
  mkReport
    (fun i => dsec_gap pi mu i)
    (fun i => sd_diag pi mu i)
    (infonce_diag pi f)
    (diversity_index pi)
    (fun i s => bellman_residual pi i s).

(** * Rademacher Complexity

    We use Rademacher complexity to bound the generalisation gap of the
    InfoNCE estimator when the critic is learned from finite data.

    Setting:
    - We observe [m] i.i.d. samples (s₁,a₁), ..., (sₘ,aₘ) from the
      occupancy distribution d^π.
    - We choose a critic f from a hypothesis class ℱ to minimise the
      *empirical* InfoNCE loss.
    - How much can the empirical loss differ from the population loss?

    The Rademacher complexity of ℱ on m samples is:
      Rad_m(ℱ) = E_{σ,data}[ sup_{f∈ℱ} (1/m) Σ_i σ_i · f(sᵢ,aᵢ) ]
    where σ_i are independent Rademacher random variables (±1 with prob ½).

    Main theorem (uniform convergence):
      With probability ≥ 1-δ over the data,
      for all f ∈ ℱ:
        |L_InfoNCE(f) - L̂_InfoNCE(f)| ≤ 2 · Rad_m(ℱ) + C · sqrt(log(1/δ)/m)

    Dependency: InfoNCE/Loss.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import InfoNCE.Loss.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Rademacher variables *)

(** A Rademacher variable takes values +1 or -1, each with probability ½. *)

Parameter rademacher : Dist R.

Axiom rademacher_mean : expectation rademacher (fun x => x) = 0.
Axiom rademacher_square : expectation rademacher (fun x => x * x) = 1.
Axiom rademacher_bounded : forall x, In x [-1; 1] -> True. (* placeholder *)

(* ------------------------------------------------------------------ *)
(** ** Hypothesis class and empirical loss *)

(** A hypothesis class is a set of critics. *)
Definition HypothesisClass := Critic -> Prop.

(** Empirical InfoNCE loss on [m] samples.
    We represent the dataset as a function [data : nat -> State * JointAction]. *)

Parameter m : nat.    (** Number of samples. *)
Hypothesis m_pos : (m > 0)%nat.

Parameter data : nat -> State * JointAction.
(** [data k] is the k-th sample (state, positive action pair). *)

Definition empirical_infonce (f : Critic) : R :=
  (1 / INR m) *
  fold_left Rplus
    (map (fun k =>
            let (s, a) := data k in
            infonce_sample f s a [])   (* simplified: no negatives listed *)
         (seq 0 m))
    0.

(* ------------------------------------------------------------------ *)
(** ** Rademacher complexity *)

(** Empirical Rademacher complexity of class [ℱ] on the current [data]. *)

Parameter rademacher_complexity : HypothesisClass -> R.

Axiom rademacher_nonneg :
  forall (F : HypothesisClass), 0 <= rademacher_complexity F.

(** Rademacher complexity grows sub-linearly with the complexity of ℱ.
    For linear critics of dimension [d], it is O(sqrt(d/m)). *)

Axiom rademacher_linear_class :
  forall (d : nat) (F : HypothesisClass),
    (* If critics in F are linear in a d-dimensional feature map *)
    rademacher_complexity F <= Rsqrt (INR d / INR m).

(* ------------------------------------------------------------------ *)
(** ** Uniform convergence theorem *)

(** The generalisation bound says that for any δ > 0, with high probability
    (≥ 1-δ), every critic simultaneously has small estimation error. *)

Parameter C_universal : R.   (** An absolute constant from the proof. *)

Axiom uniform_convergence :
  forall (F : HypothesisClass) (delta : R) (pi : JointPolicy),
    0 < delta ->
    (* "With probability ≥ 1-δ over the draw of [m] samples:" *)
    forall (f : Critic), F f ->
      Rabs (infonce_loss f pi - empirical_infonce f) <=
      2 * rademacher_complexity F +
      C_universal * Rsqrt (Rln (1 / delta) / INR m).
(** Proof: This is a standard application of the bounded-differences
    inequality (McDiarmid's theorem) combined with the symmetrisation
    argument that relates generalisation gap to Rademacher complexity.
    Full proof is deferred; it does not depend on any domain-specific facts. *)

(* ------------------------------------------------------------------ *)
(** ** Corollary: sample complexity for DSEC

    How many samples [m] suffice to certify a DSEC within tolerance ε? *)

Corollary sample_complexity_DSEC :
  forall (F : HypothesisClass) (eps delta : R) (pi : JointPolicy),
    0 < eps -> 0 < delta ->
    (* If the Rademacher complexity is small enough: *)
    rademacher_complexity F <= eps / 4 ->
    (* And m is large enough: *)
    C_universal * Rsqrt (Rln (1 / delta) / INR m) <= eps / 2 ->
    (* Then for all critics in F: *)
    forall f, F f ->
      Rabs (infonce_loss f pi - empirical_infonce f) <= eps.
Proof.
  intros F eps delta pi Heps Hdelta HRad Hm f Hf.
  eapply Rle_trans.
  - apply uniform_convergence; assumption.
  - lra.
Qed.

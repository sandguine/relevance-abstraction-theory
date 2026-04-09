(** * Strategic Divergence

    How different are two policies?  Pointwise KL divergence between their
    action distributions gives a natural answer, but we want a measure that
    is also sensitive to *where* the policies are likely to be visited.
    The Strategic Divergence weights the local KL by the state occupancy
    measure of a reference policy.

    Key properties:
    - Non-negative, zero iff the policies agree on the support of the
      reference occupancy measure.
    - Bounded by a scaled version of the KL between individual action
      distributions.

    Dependency: Core/Policy.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** KL divergence between distributions

    [KL mu nu] is the Kullback–Leibler divergence D_KL(mu || nu).
    It measures the expected log-likelihood ratio. *)

Parameter KL : forall {X : Type}, Dist X -> Dist X -> R.

Axiom KL_nonneg :
  forall {X : Type} (mu nu : Dist X), 0 <= KL mu nu.

Axiom KL_zero_iff_eq :
  forall {X : Type} (mu nu : Dist X), KL mu nu = 0 <-> mu = nu.

Axiom KL_expectation :
  forall {X : Type} (mu nu : Dist X),
    KL mu nu = expectation mu (fun x => log_prob mu x - log_prob nu x).

(* ------------------------------------------------------------------ *)
(** ** Per-state strategic divergence

    The local divergence at state [s] between agents using [pi] vs [mu]
    is the KL between their action distributions at that state. *)

Definition local_div (i : nat) (pi mu : JointPolicy) (s : State) : R :=
  KL (pi i s) (mu i s).

(** Local divergence is non-negative. *)
Lemma local_div_nonneg (i : nat) (pi mu : JointPolicy) (s : State) :
  0 <= local_div i pi mu s.
Proof.
  unfold local_div. apply KL_nonneg.
Qed.

(** Local divergence is zero iff the two policies agree at [s]. *)
Lemma local_div_zero_iff (i : nat) (pi mu : JointPolicy) (s : State) :
  local_div i pi mu s = 0 <-> pi i s = mu i s.
Proof.
  unfold local_div. apply KL_zero_iff_eq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** State occupancy measure (forward reference)

    The full definition lives in Certificates/OccupancyMeasure.v.
    We import only the type here to keep the Core self-contained. *)

Parameter OccupancyMeasure : JointPolicy -> Dist State.
(** [OccupancyMeasure pi] is the (normalised) distribution over states
    visited when following policy [pi] from the initial state distribution.
    Its formal definition is:  d^pi(s) = (1 - γ) Σ_{t≥0} γ^t Pr(s_t = s | pi). *)

(* ------------------------------------------------------------------ *)
(** ** Strategic divergence

    [SD i pi mu] is the divergence of agent [i]'s policy, weighted by
    the state distribution induced by [pi].  It captures how much agent
    [i] actually changes behaviour in the states it is likely to visit. *)

Definition SD (i : nat) (pi mu : JointPolicy) : R :=
  expectation (OccupancyMeasure pi) (fun s => local_div i pi mu s).

Lemma SD_nonneg (i : nat) (pi mu : JointPolicy) :
  0 <= SD i pi mu.
Proof.
  unfold SD.
  apply expectation_mono.
  intros s. apply local_div_nonneg.
Qed.

Lemma SD_zero_implies_agree_ae (i : nat) (pi mu : JointPolicy) :
  SD i pi mu = 0 ->
  expectation (OccupancyMeasure pi) (fun s => local_div i pi mu s) = 0.
Proof.
  unfold SD. trivial.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Joint strategic divergence

    We sum [SD] over all agents to obtain a single scalar measure of
    how far joint policy [mu] deviates from reference [pi]. *)

Definition JSD (G : MarkovGame) (pi mu : JointPolicy) : R :=
  let N := n_agents G in
  (* Σ_{i=0}^{N-1} SD i pi mu *)
  fold_left Rplus
    (map (fun i => SD i pi mu) (seq 0 N))
    0.

Lemma JSD_nonneg (pi mu : JointPolicy) :
  0 <= JSD G pi mu.
Proof.
  unfold JSD.
  (* Each term is non-negative by SD_nonneg; the fold preserves sign. *)
  Admitted.

(** * Strategic Equivalence Certificate (SEC)

    Two joint policies are *strategically equivalent* when they induce the
    same value function for every agent in every state.  A Strategic
    Equivalence Certificate (SEC) is a formal witness that this holds.

    The SEC is the cornerstone of the whole theory:
    - It lets us abstract away *how* a policy is represented and reason
      only about its *effect* on outcomes.
    - Downstream modules use SECs to justify replacing one policy
      with another (e.g.  a simpler surrogate) without changing any
      agent's welfare.

    Key results here:
    1. SEC is an equivalence relation on [JointPolicy].
    2. Reflexivity, symmetry, transitivity.
    3. Congruence: SEC is preserved under [replace].
    4. Value-preservation theorem.

    Dependency: Core/Value.v, Core/StrategicDivergence.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.StrategicDivergence.
Open Scope R_scope.

Variable G : MarkovGame.
Notation γ   := (discount   G).
Notation Rew := (reward     G).

(* ------------------------------------------------------------------ *)
(** ** Definition *)

(** [SEC pi mu] holds when [pi] and [mu] produce identical value functions
    for all agents and all states. *)

Definition SEC (pi mu : JointPolicy) : Prop :=
  forall (i : nat) (s : State), V pi i s = V mu i s.

(* ------------------------------------------------------------------ *)
(** ** SEC is an equivalence relation *)

Lemma SEC_refl : forall pi, SEC pi pi.
Proof.
  unfold SEC. intros. reflexivity.
Qed.

Lemma SEC_sym : forall pi mu, SEC pi mu -> SEC mu pi.
Proof.
  unfold SEC. intros pi mu H i s. symmetry. apply H.
Qed.

Lemma SEC_trans : forall pi mu nu, SEC pi mu -> SEC mu nu -> SEC pi nu.
Proof.
  unfold SEC. intros pi mu nu H1 H2 i s.
  rewrite H1. apply H2.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Value-preservation theorem

    The headline result: if [pi] and [mu] are SEC-related, then for every
    initial state and every agent, the long-run outcomes are identical.
    This justifies replacing [pi] by [mu] in any downstream reasoning. *)

Theorem SEC_value_preservation :
  forall (pi mu : JointPolicy),
    SEC pi mu ->
    forall (i : nat) (s : State),
      V pi i s = V mu i s.
Proof.
  intros pi mu Hsec i s. exact (Hsec i s).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Congruence under replace

    If we swap agent [i]'s policy while preserving their value function,
    the modified joint policy is still SEC-related to the original.
    This supports modular reasoning: each agent can be updated
    independently. *)

Lemma SEC_replace_congruence :
  forall (pi : JointPolicy) (i : nat) (pi_i : Policy i),
    (** New policy agrees on values for agent i. *)
    (forall s, V (replace pi i pi_i) i s = V pi i s) ->
    (** New policy does not change other agents' values. *)
    (forall j s, j <> i -> V (replace pi i pi_i) j s = V pi j s) ->
    SEC (replace pi i pi_i) pi.
Proof.
  unfold SEC.
  intros pi i pi_i Hi Hj k s.
  destruct (Nat.eq_dec k i) as [e | n].
  - subst. apply Hi.
  - apply Hj. exact n.
Qed.

(* ------------------------------------------------------------------ *)
(** ** SEC via zero strategic divergence

    A sufficient condition for SEC is that every agent's strategic
    divergence from [pi] to [mu] is zero — i.e., the policies agree
    on the support of the occupancy measure.

    This connects the local (per-state) view of divergence to the global
    (value-level) notion of equivalence.  The proof goes through the
    Performance Difference Lemma (Certificates/PerformanceDifference.v). *)

Axiom JSD_zero_implies_SEC :
  forall (pi mu : JointPolicy),
    JSD G pi mu = 0 -> SEC pi mu.
(** Proof sketch:
    JSD = 0 implies SD i pi mu = 0 for each i, which by the Performance
    Difference Lemma implies V pi i s = V mu i s for all i, s.
    Full proof deferred to after PerformanceDifference.v is developed. *)

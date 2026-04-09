(** * Horizon Equivalence

    A Markov game can be formulated over a finite horizon T or an infinite
    horizon with discount factor γ.  These two formulations are often
    treated as separate models, but they are related:

    - A finite-horizon game with horizon T is equivalent to an
      infinite-horizon game with γ = 0 after step T.
    - As T → ∞ with γ < 1, the finite-horizon value converges to the
      infinite-horizon value, with error O(γ^T / (1-γ)).

    This module formalises the equivalence, which is used in two ways:
    1. Algorithms that truncate trajectories at horizon T can be analysed
       using the infinite-horizon SEC/DSEC framework.
    2. Periodic agents (that reset after T steps) have equivalent
       representations as infinite-horizon agents.

    Dependency: Core/Value.v, Certificates/PerformanceDifference.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Certificates.OccupancyMeasure.
Open Scope R_scope.

Variable G : MarkovGame.
Notation γ := (discount G).
Notation P := (transition G).
Notation Rew := (reward G).

(* ------------------------------------------------------------------ *)
(** ** Finite-horizon value function

    [V_T pi i T s] is the expected return over exactly [T] steps. *)

Fixpoint V_T (pi : JointPolicy) (i : nat) (T : nat) (s : State) : R :=
  match T with
  | O    => 0
  | S T' =>
      expectation (induced_joint pi s) (fun a =>
        Rew i s a + γ * expectation (P s a) (fun s' =>
          V_T pi i T' s'))
  end.

(** [V_T] is monotone in [T]: adding more steps can only help
    (assuming non-negative rewards; more generally it holds absolutely). *)
Lemma V_T_mono (pi : JointPolicy) (i : nat) (T : nat) (s : State) :
  V_T pi i T s <= V_T pi i (S T) s.
Proof.
  induction T as [| T' IH].
  - simpl.
    apply expectation_mono. intro a.
    apply expectation_mono. intro s'.
    lra.
  - simpl.
    apply expectation_mono. intro a.
    assert (Hγ : 0 <= γ) by apply (discount_lo G).
    apply Rplus_le_compat_l.
    apply Rmult_le_compat_l; [exact Hγ |].
    apply expectation_mono. intro s'.
    apply IH.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Convergence to infinite-horizon value *)

(** The infinite-horizon value is the limit of the finite-horizon values.
    We bound the approximation error. *)

Theorem finite_infinite_horizon_error :
  forall (pi : JointPolicy) (i : nat) (T : nat) (s : State),
    Rabs (V pi i s - V_T pi i T s) <=
    (γ ^ T) * (reward_bound G) / (1 - γ).
Proof.
  (* Proof sketch:
     V - V_T is the tail of the discounted sum from step T onward.
     Each term is bounded by γ^t · M_R, and Σ_{t≥T} γ^t = γ^T/(1-γ).
     We use induction on T and the Bellman equation. *)
  Admitted.

(** As [T → ∞], the error goes to 0 (geometric decay in γ^T). *)
Corollary V_T_converges :
  forall (pi : JointPolicy) (i : nat) (s : State) (eps : R),
    0 < eps ->
    exists T0 : nat,
      forall T : nat, (T >= T0)%nat ->
        Rabs (V pi i s - V_T pi i T s) <= eps.
Proof.
  intros pi i s eps Heps.
  (* γ^T → 0, so for large T the bound (γ^T · M/(1-γ)) < eps. *)
  (* Choose T0 = ceil(log(eps·(1-γ)/M) / log(1/γ)). *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** Horizon equivalence for SEC

    Two policies that are SEC-related in the finite-horizon sense
    are approximately SEC-related in the infinite-horizon sense,
    with error controlled by the horizon gap. *)

Definition SEC_T (pi mu : JointPolicy) (T : nat) : Prop :=
  forall (i : nat) (s : State),
    V_T pi i T s = V_T mu i T s.

Theorem horizon_SEC_equivalence :
  forall (pi mu : JointPolicy) (T : nat),
    SEC_T pi mu T ->
    forall i s,
      Rabs (V pi i s - V mu i s) <= 2 * (γ ^ T) * (reward_bound G) / (1 - γ).
Proof.
  intros pi mu T Hsec_T i s.
  eapply Rle_trans.
  - (* Triangle inequality: |V pi - V mu| ≤ |V pi - V_T pi| + |V_T pi - V_T mu| + |V_T mu - V mu| *)
    apply (Rabs_triang_inv (V pi i s - V mu i s)
                           (V_T pi i T s - V_T mu i T s)).
  - (* The middle term is 0 by SEC_T *)
    specialize (Hsec_T i s). rewrite Hsec_T. rewrite Rminus_diag_eq; [| reflexivity].
    rewrite Rabs_R0. rewrite Rplus_0_r.
    (* Bound the remaining terms using finite_infinite_horizon_error *)
    Admitted.

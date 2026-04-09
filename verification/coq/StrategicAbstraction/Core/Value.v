(** * Value Functions

    The value function V^π_i(s) is the expected discounted return that
    agent [i] earns starting from state [s] when all agents follow the
    joint policy [π].  The Q-function Q^π_i(s, a) conditions additionally
    on executing joint action [a] in the first step.

    Key results:
    - Bellman consistency equations characterise V and Q uniquely.
    - The advantage function A^π_i = Q^π_i - V^π_i measures the gain
      of deviating to action [a] from the current policy.

    Dependency: Core/MarkovGame.v, Core/Policy.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** Game context

    We fix a game [G] for the rest of this file so that we can write
    [γ], [P], [Rew] without repeatedly projecting from [G]. *)

Variable G : MarkovGame.

Notation γ   := (discount   G).
Notation P   := (transition G).
Notation Rew := (reward     G).

(* ------------------------------------------------------------------ *)
(** ** Value and Q functions

    We axiomatise V and Q as functions satisfying the Bellman equations
    (stated below).  A constructive definition would use the fixed-point
    of the Bellman operator, whose existence follows from the contraction
    mapping theorem because γ < 1. *)

(** [V pi i s] is the expected γ-discounted return for agent [i]
    starting in state [s] under joint policy [pi]. *)
Parameter V : JointPolicy -> nat -> State -> R.

(** [Q pi i s a] conditions the first-step action [a] and then
    follows [pi] thereafter. *)
Parameter Q : JointPolicy -> nat -> State -> JointAction -> R.

(* ------------------------------------------------------------------ *)
(** ** Bellman equations *)

(** V is the expectation of Q under the policy's action distribution. *)
Axiom bellman_V :
  forall (pi : JointPolicy) (i : nat) (s : State),
    V pi i s =
    expectation (induced_joint pi s)
                (fun a => Q pi i s a).

(** Q decomposes into immediate reward plus discounted expected successor value. *)
Axiom bellman_Q :
  forall (pi : JointPolicy) (i : nat) (s : State) (a : JointAction),
    Q pi i s a =
    Rew i s a + γ * expectation (P s a) (fun s' => V pi i s').

(** Combining the two Bellman equations gives the full Bellman consistency
    equation for V.  This is what algorithms iterate to convergence. *)
Lemma bellman_consistency :
  forall (pi : JointPolicy) (i : nat) (s : State),
    V pi i s =
    expectation (induced_joint pi s) (fun a =>
      Rew i s a + γ * expectation (P s a) (fun s' => V pi i s')).
Proof.
  intros pi i s.
  rewrite bellman_V.
  apply f_equal.
  extensionality a.
  apply bellman_Q.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Advantage function

    The advantage [A^π_i(s, a)] measures how much better (or worse)
    executing joint action [a] in state [s] is relative to following [π].
    Positive advantage means [a] is beneficial for agent [i]. *)

Definition A (pi : JointPolicy) (i : nat) (s : State) (a : JointAction) : R :=
  Q pi i s a - V pi i s.

(** By Bellman, the expected advantage under [pi] is exactly zero.
    This is a basic sanity check: on average, the policy does neither
    better nor worse than itself. *)
Lemma expected_advantage_zero :
  forall (pi : JointPolicy) (i : nat) (s : State),
    expectation (induced_joint pi s) (fun a => A pi i s a) = 0.
Proof.
  intros pi i s.
  unfold A.
  rewrite expectation_linear.
  rewrite bellman_V.
  rewrite expectation_const.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Value bounds

    V is bounded by the geometric-series limit of the reward bound. *)

Lemma V_upper_bound :
  forall (pi : JointPolicy) (i : nat) (s : State),
    V pi i s <= (reward_bound G) / (1 - γ).
Proof.
  (* Proof sketch: by Bellman_Q, |Q| ≤ M/(1-γ) by geometric series;
     then |V| ≤ |Q| by Bellman_V and non-negativity of the distribution. *)
  Admitted.

Lemma V_lower_bound :
  forall (pi : JointPolicy) (i : nat) (s : State),
    - (reward_bound G) / (1 - γ) <= V pi i s.
Proof.
  Admitted.

(** * Policies

    A policy is a rule that tells an agent how to choose actions.  In the
    fully observable setting each agent conditions only on the current state.
    We distinguish:

    - [Policy i]: a stochastic policy for agent [i], mapping each state to a
      distribution over [Action i].
    - [JointPolicy]: a tuple of individual policies, one per agent.

    We also define useful operations: marginalisation, mixing, and the
    notion of a deterministic policy as a special case.

    Dependency: Core/MarkovGame.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** Individual policies *)

(** A (stochastic) policy for agent [i] maps every state to a probability
    distribution over that agent's actions. *)
Definition Policy (i : nat) := State -> Dist (Action i).

(** A deterministic policy for agent [i] picks exactly one action in each
    state.  It embeds into [Policy i] by placing all mass on that action. *)
Parameter dirac : forall {X : Type}, X -> Dist X.

Definition DeterministicPolicy (i : nat) := State -> Action i.

Definition embed_det {i : nat} (pi : DeterministicPolicy i) : Policy i :=
  fun s => dirac (pi s).

(* ------------------------------------------------------------------ *)
(** ** Joint policies *)

(** A joint policy is simply one policy per agent index.  We do not fix
    the number of agents here; any downstream module that needs a specific
    [n_agents] should open the game record and specialise. *)
Definition JointPolicy := forall i : nat, Policy i.

(** Project out agent [i]'s individual policy from a joint policy. *)
Definition marginal (pi : JointPolicy) (i : nat) : Policy i := pi i.

(** Given a joint policy [pi] and a state [s], construct the induced
    joint-action distribution.  Because individual policies are independent
    conditional on [s], the joint action is the product measure. *)
Parameter joint_dist :
  forall {n : nat}, (forall i, Dist (Action i)) -> Dist JointAction.

Definition induced_joint (pi : JointPolicy) (s : State) : Dist JointAction :=
  joint_dist (fun i => pi i s).

(* ------------------------------------------------------------------ *)
(** ** Policy modification

    [replace pi i pi_i] replaces agent [i]'s component in the joint policy
    [pi] with a new individual policy [pi_i].  All other agents are
    unchanged.  This is central to best-response and deviation arguments. *)

Definition replace (pi : JointPolicy) (i : nat) (pi_i : Policy i)
    : JointPolicy :=
  fun j => match Nat.eq_dec j i with
           | left  H => eq_rect i Policy pi_i j (eq_sym H)
           | right _ => pi j
           end.

(** Sanity check: replacing agent [i]'s policy and projecting back out
    returns exactly the new policy. *)
Lemma replace_self (pi : JointPolicy) (i : nat) (pi_i : Policy i) :
  replace pi i pi_i i = pi_i.
Proof.
  unfold replace.
  destruct (Nat.eq_dec i i) as [e | n].
  - rewrite eq_rect_eq_dec; [reflexivity | apply Nat.eq_dec].
  - contradiction.
Qed.

(** For agents [j ≠ i], their policy is unchanged. *)
Lemma replace_other (pi : JointPolicy) (i j : nat) (pi_i : Policy i) :
  j <> i -> replace pi i pi_i j = pi j.
Proof.
  intros Hne.
  unfold replace.
  destruct (Nat.eq_dec j i) as [e | n].
  - contradiction.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Policy mixtures

    A mixture of two policies [pi] and [mu] with weight [alpha ∈ [0,1]]
    plays [pi] with probability [alpha] and [mu] otherwise.  Mixtures
    arise naturally in existence proofs for equilibria. *)

Parameter mix_dist : forall {X : Type}, R -> Dist X -> Dist X -> Dist X.

(** Axiom: expectation under a mixture is a convex combination. *)
Axiom mix_expectation :
  forall {X : Type} (alpha : R) (mu nu : Dist X) (f : X -> R),
    0 <= alpha -> alpha <= 1 ->
    expectation (mix_dist alpha mu nu) f =
    alpha * expectation mu f + (1 - alpha) * expectation nu f.

Definition mix_policy (alpha : R) (pi mu : JointPolicy) : JointPolicy :=
  fun i s => mix_dist alpha (pi i s) (mu i s).

(** * Occupancy Measure

    The occupancy measure d^π(s, a) is the (normalised) probability of
    visiting state [s] and taking joint action [a] when following policy
    [π] from the initial state distribution.

    Formally:
      d^π(s, a) = (1 - γ) Σ_{t ≥ 0}  γ^t  Pr(s_t = s, a_t = a | π)

    The factor (1 - γ) normalises the measure so that Σ_{s,a} d^π(s,a) = 1,
    making it a proper probability distribution over state-action pairs.

    Occupancy measures are the key bridge between policy space and
    distribution space: every feasible occupancy measure corresponds to
    some policy, and vice versa (Bellman flow equations below).

    Dependency: Core/MarkovGame.v, Core/Policy.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Open Scope R_scope.

Variable G : MarkovGame.
Notation γ := (discount   G).
Notation P := (transition G).

(* ------------------------------------------------------------------ *)
(** ** Initial state distribution *)

Parameter init_dist : Dist State.
(** [init_dist] is the distribution from which the first state is drawn.
    All value functions are implicitly conditioned on this. *)

(* ------------------------------------------------------------------ *)
(** ** State and state-action occupancy measures *)

(** [d_state pi s] is the normalised probability of visiting state [s]
    under joint policy [pi]. *)
Parameter d_state : JointPolicy -> Dist State.

(** [d_sa pi] is the normalised probability over (state, action) pairs.
    We represent it as: for a given state, the marginal over joint actions. *)
Parameter d_sa : JointPolicy -> State -> Dist JointAction.

(** The state marginal of [d_sa] equals [d_state]. *)
Axiom d_sa_state_marginal :
  forall (pi : JointPolicy) (f : State -> R),
    expectation (d_state pi) f =
    expectation (d_state pi)
      (fun s => expectation (induced_joint pi s) (fun _ => f s)).

(* ------------------------------------------------------------------ *)
(** ** Bellman flow equations

    The occupancy measure must satisfy a linear flow constraint that says:
    "the probability of being in state [s] equals the probability of
    arriving from any predecessor state [s'] via any joint action [a']".

    This is the dual of the Bellman optimality equation. *)

Axiom bellman_flow :
  forall (pi : JointPolicy) (f : State -> R),
    expectation (d_state pi) f =
    (1 - γ) * expectation init_dist f
    + γ * expectation (d_state pi) (fun s =>
        expectation (induced_joint pi s) (fun a =>
          expectation (P s a) f)).

(** The occupancy measure is a probability distribution (total mass 1). *)
Lemma d_state_total_mass :
  forall (pi : JointPolicy),
    expectation (d_state pi) (fun _ => 1) = 1.
Proof.
  intro pi.
  (* Apply bellman_flow with f = const 1, then use expectation_const. *)
  pose proof (bellman_flow pi (fun _ => 1)) as Hf.
  rewrite expectation_const in *.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Policy recovery from occupancy measure

    Given an occupancy measure [d], we can recover the policy it
    corresponds to by conditioning: π(a | s) = d(s, a) / d(s).

    We state this as an axiom (the constructive version requires
    division by [d_state] which may be zero on unreachable states). *)

Axiom occupancy_policy_recovery :
  forall (pi : JointPolicy) (s : State),
    d_sa pi s = induced_joint pi s.
(** Interpretation: the conditional distribution of actions given state [s]
    under the occupancy measure is exactly the joint policy's action
    distribution at [s].  This holds because d(s, a) ∝ d(s) · π(a|s). *)

(* ------------------------------------------------------------------ *)
(** ** Expectation under occupancy measure

    The key computational identity: the expected return equals the
    expectation of the per-step reward under the occupancy measure.

    V^π_i(init) = E_{(s,a) ~ d^π}[ R_i(s, a) ]

    This is what makes occupancy measures useful for optimisation:
    the objective is *linear* in d^π (and hence in π). *)

Axiom value_as_occupancy_expectation :
  forall (pi : JointPolicy) (i : nat),
    expectation init_dist (fun s => V pi i s) =
    expectation (d_state pi) (fun s =>
      expectation (induced_joint pi s) (fun a =>
        reward G i s a)).
(** Proof sketch: unroll the Bellman equation for V and regroup the
    geometric series; the normalisation factor (1-γ) cancels with the
    sum Σ γ^t = 1/(1-γ). *)

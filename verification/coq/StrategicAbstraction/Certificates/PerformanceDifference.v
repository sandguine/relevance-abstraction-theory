(** * Performance Difference Lemma

    The Performance Difference Lemma (PDL) is one of the most useful
    identities in RL theory.  It expresses the *difference* in value
    between two joint policies [pi] and [mu] entirely in terms of
    the advantage function of [mu] evaluated under the occupancy measure
    of [pi]:

        V^π_i(s₀) - V^μ_i(s₀) =
          (1/(1-γ)) · E_{(s,a) ~ d^π}[ A^μ_i(s, a) ]

    Intuitively:
    - If [pi] always takes actions that look good according to [mu]'s
      advantage, then [pi] performs at least as well as [mu].
    - The lemma reduces a global statement (value difference) to a
      local one (expected advantage per state-action pair).

    This is the main workhorse for proving:
    - Monotone improvement in policy gradient methods.
    - Value preservation under SEC (Core/SEC.v).
    - Correctness of the DSEC (Certificates/DSEC.v).

    Dependency: Core/Value.v, Certificates/OccupancyMeasure.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Certificates.OccupancyMeasure.
Open Scope R_scope.

Variable G : MarkovGame.
Notation γ   := (discount   G).
Notation P   := (transition G).
Notation Rew := (reward     G).

(* ------------------------------------------------------------------ *)
(** ** Telescoping identity

    The PDL is derived by telescoping the Bellman equations for [pi] and
    [mu].  We first state the per-step identity that makes this work. *)

Lemma bellman_difference :
  forall (pi mu : JointPolicy) (i : nat) (s : State),
    V pi i s - V mu i s =
    expectation (induced_joint pi s) (fun a =>
      A mu i s a
      + γ * expectation (P s a) (fun s' => V pi i s' - V mu i s')).
Proof.
  intros pi mu i s.
  (* Rewrite V pi using Bellman_consistency *)
  rewrite bellman_consistency.
  (* Rewrite V mu using Bellman_V and Bellman_Q *)
  rewrite bellman_V.
  unfold A.
  (* Distribute expectation over the sum and rearrange *)
  rewrite <- expectation_linear.
  apply f_equal. extensionality a.
  rewrite bellman_Q.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Performance Difference Lemma *)

(** The main theorem.  We state it as an equality relating the difference
    in initial values to the expected advantage under the reference
    occupancy measure. *)

Theorem performance_difference :
  forall (pi mu : JointPolicy) (i : nat),
    expectation init_dist (fun s => V pi i s - V mu i s) =
    (1 / (1 - γ)) *
    expectation (d_state pi) (fun s =>
      expectation (induced_joint pi s) (fun a =>
        A mu i s a)).
Proof.
  intros pi mu i.
  (* The proof proceeds by unrolling [bellman_difference] iteratively,
     collecting the geometric series in γ, and recognising the result
     as the expectation under d^π.

     Step 1: iterate bellman_difference t times to get a t-step expansion.
     Step 2: the remainder term decays as γ^t → 0.
     Step 3: the infinite sum of (γ^t · Pr(s_t = s | pi) · A^μ_i(s, a))
             is exactly (1/(1-γ)) · E_{d^π}[A^μ_i] by definition of d^π.

     A fully formal proof requires induction on a finite-horizon
     approximation and a limit argument; we defer the details. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** Corollaries *)

(** If [pi]'s advantage under [mu] is everywhere non-negative, then
    [pi] is at least as good as [mu] for agent [i]. *)

Corollary advantage_implies_improvement :
  forall (pi mu : JointPolicy) (i : nat),
    (forall s a, 0 <= A mu i s a) ->
    forall s0,
      V mu i s0 <= V pi i s0.
Proof.
  intros pi mu i Hpos s0.
  (* Use PDL: the RHS is non-negative by Hpos and mono of expectation. *)
  Admitted.

(** If [pi] and [mu] induce the same expected advantage for every agent,
    their values coincide.  This is the PDL route to SEC. *)

Corollary zero_advantage_implies_SEC :
  forall (pi mu : JointPolicy),
    (forall i s a, A mu i s a = 0) ->
    SEC pi mu.
Proof.
  intros pi mu Hzero.
  unfold SEC. intros i s.
  (* By PDL: E[V^π - V^μ] = (1/(1-γ)) · E_{d^π}[A^μ] = 0.
     Since the difference is identically 0 in expectation over init_dist
     and is bounded, conclude pointwise equality by a density argument. *)
  Admitted.

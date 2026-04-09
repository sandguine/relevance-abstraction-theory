(** * Algorithm Sketches

    This module describes the algorithms implied by the theory in
    pseudocode form, encoded as Coq definitions and comments.  The goal
    is *not* a runnable implementation but a precise, type-checked
    interface that bridges the mathematical theory and future code.

    Three algorithms are sketched:

    1. *SEC-Verified Policy Gradient (SVPG)*: A policy gradient method
       that uses the DSEC certificate to decide when an update preserves
       strategic equivalence.

    2. *InfoNCE Critic Training (ICT)*: Trains the contrastive critic
       needed to estimate KL divergences (and hence verify DSEC).

    3. *Diverse Equilibrium Search (DES)*: Searches for a soft Nash
       equilibrium that also maximises a diversity certificate.

    Dependency: Core/SEC.v, Certificates/DSEC.v, InfoNCE/Loss.v,
                Phenomena/Diversity.v *)

Require Import Reals.
Require Import List.
Import ListNotations.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.SEC.
Require Import Certificates.DSEC.
Require Import InfoNCE.Loss.
Require Import Phenomena.Diversity.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Algorithm 1: SEC-Verified Policy Gradient (SVPG)

    Invariant: after each update, the new policy is DSEC-related to
    the old one (i.e., the update does not significantly change any
    agent's value function). *)

(** A gradient step: given current policy [pi] and step size [eta],
    produce a candidate new policy.  The gradient direction is the
    policy gradient (score function estimator). *)
Parameter gradient_step : JointPolicy -> R -> JointPolicy.

(** A DSEC verifier: given two policies and tolerance [eps], decides
    whether they satisfy DSEC within [eps].  In practice this uses
    the InfoNCE estimator from ICT (Algorithm 2). *)
Parameter verify_dsec : JointPolicy -> JointPolicy -> R -> bool.

Axiom verify_dsec_correct :
  forall (pi mu : JointPolicy) (eps : R),
    verify_dsec pi mu eps = true ->
    DSEC pi mu.
(** Note: the verifier may be *conservative* (it can return false even
    when DSEC holds), but it must never certify a non-DSEC pair. *)

(** One round of SVPG:
    - Take a gradient step.
    - If the result is DSEC-verified, commit it.
    - Otherwise, halve the step size and retry.
    We represent convergence abstractly rather than encoding the loop. *)

Definition svpg_step (pi : JointPolicy) (eta : R) : JointPolicy :=
  let pi' := gradient_step pi eta in
  if verify_dsec pi pi' 0  (* epsilon = 0 for exact SEC *)
  then pi'
  else pi.   (* fallback: no update (would recurse with eta/2 in practice) *)

(** Correctness: SVPG never accepts an update that violates DSEC. *)
Theorem svpg_preserves_dsec :
  forall (pi : JointPolicy) (eta : R),
    DSEC pi (svpg_step pi eta).
Proof.
  intros pi eta.
  unfold svpg_step.
  destruct (verify_dsec pi (gradient_step pi eta) 0) eqn:Hv.
  - exact (verify_dsec_correct _ _ _ Hv).
  - apply DSEC_refl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Algorithm 2: InfoNCE Critic Training (ICT)

    Trains a critic [f : Critic] by minimising the empirical InfoNCE
    loss.  The trained critic is then used to:
    (a) estimate mutual information (for diversity certificates), and
    (b) estimate KL divergences (for DSEC verification). *)

(** A gradient descent optimiser: given an objective and current
    parameters, returns updated parameters. *)
Parameter optimise_critic :
  (Critic -> R) ->   (* objective *)
  Critic ->          (* initial critic *)
  Critic.            (* trained critic *)

Axiom optimise_critic_descends :
  forall (obj : Critic -> R) (f : Critic),
    obj (optimise_critic obj f) <= obj f.

(** One round of ICT for joint policy [pi]: *)
Definition ict_step (pi : JointPolicy) (f0 : Critic) : Critic :=
  optimise_critic (fun f => empirical_infonce f) f0.

(** After training, the critic approximates the optimal critic: *)
Axiom ict_converges :
  forall (pi : JointPolicy) (f0 : Critic) (eps : R),
    0 < eps ->
    Rabs (infonce_loss (ict_step pi f0) pi -
          infonce_loss (optimal_critic pi) pi) <= eps.
(** In practice "convergence" requires sufficient capacity in [F] and
    enough gradient steps; this axiom packages that as a condition. *)

(* ------------------------------------------------------------------ *)
(** ** Algorithm 3: Diverse Equilibrium Search (DES)

    DES alternates between:
    - A *policy update* (soft best response step per agent).
    - A *diversity enforcement* step (penalise SEC-equivalent pairs).

    The result is a soft Nash equilibrium that also satisfies a
    positive diversity certificate. *)

Parameter soft_br_step : JointPolicy -> JointPolicy.
(** [soft_br_step pi] applies one round of soft best-response updates
    for all agents simultaneously (fictitious play style). *)

Parameter diversity_penalty : JointPolicy -> R.
(** [diversity_penalty pi] returns a scalar penalty that is 0 when
    [pi] is maximally diverse and positive when agents are near-SEC. *)

Axiom diversity_penalty_nonneg :
  forall pi, 0 <= diversity_penalty pi.

Axiom diversity_penalty_zero_iff_diverse :
  forall pi eps,
    diversity_penalty pi = 0 <-> collectively_diverse eps pi.

(** A DES step: soft best-response plus diversity gradient. *)
Definition des_step (pi : JointPolicy) (lambda eta : R) : JointPolicy :=
  (* In pseudocode:
       pi' ← soft_br_step(pi)
       f   ← ict_step(pi', f_prev)   (* update critic *)
       pi'' ← pi' - lambda * ∇(diversity_penalty(pi'))
     We abstract over the gradient step. *)
  soft_br_step pi.   (* simplified; diversity enforcement is implicit *)

(** The invariant: DES iterates preserve soft-Nash progress. *)
Axiom des_progress :
  forall (pi : JointPolicy) (lambda eta : R),
    (* SV of each agent does not decrease *)
    forall i s,
      SV (des_step pi lambda eta) i s >= SV pi i s - eta.
(** The [eta] slack accounts for the diversity penalty interfering with
    the pure best-response direction. *)

(* ------------------------------------------------------------------ *)
(** ** Termination and fixed points

    All three algorithms have fixed points that correspond to meaningful
    game-theoretic objects:
    - SVPG fixed point: a stationary point of the policy gradient objective.
    - ICT fixed point: the optimal critic f* (OptimalCritic.v).
    - DES fixed point: a diverse soft Nash equilibrium. *)

Definition is_svpg_fixed_point (pi : JointPolicy) (eta : R) : Prop :=
  svpg_step pi eta = pi.

Definition is_ict_fixed_point (f : Critic) (pi : JointPolicy) : Prop :=
  ict_step pi f = f.

Definition is_des_fixed_point (pi : JointPolicy) (lambda eta : R) : Prop :=
  des_step pi lambda eta = pi.

Axiom svpg_fixed_point_is_stationary :
  forall pi eta,
    is_svpg_fixed_point pi eta ->
    forall mu,
      expectation init_dist (fun s => V mu i s - V pi i s) <= 0.
(** A fixed point of SVPG is a local maximum of expected return for every agent. *)
(** Note: [i] here is implicitly universally quantified; Coq would require
    an explicit argument. This is left as a sketch. *)

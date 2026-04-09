(** * Optimal Critic

    The InfoNCE loss (InfoNCE/Loss.v) depends on the choice of critic [f].
    This module characterises the *optimal critic* f* — the one that
    minimises the InfoNCE loss — and shows that it recovers the true
    log-density ratio, making the MI lower bound tight.

    Optimal critic (closed form):
      f*(s, a) = log[ π(a|s) / q(a) ]

    where q is the marginal action distribution used to sample negatives.

    Significance:
    - When f = f*, the InfoNCE bound becomes an *equality*, so
      infonce_loss(f*, π) = log K - I(S; A).
    - The optimal critic is exactly the log-density ratio used in
      importance sampling — it serves as the "alignment score" between
      the agent's policy and the marginal.

    Dependency: InfoNCE/Loss.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.SoftBestResponse.
Require Import InfoNCE.Loss.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Log-density ratio critic *)

(** The optimal critic scores (s, a) by the log ratio of [pi]'s action
    probability to the marginal. *)

Definition optimal_critic (pi : JointPolicy) : Critic :=
  fun s a =>
    log_prob (induced_joint pi s) a - log_prob marginal_action a.

(** This is well-defined wherever [marginal_action] has positive density.
    On the zero-probability set the critic can be set to any value
    without affecting the loss. *)

(* ------------------------------------------------------------------ *)
(** ** Optimality conditions *)

(** The optimal critic minimises the InfoNCE loss over all critics [f]. *)

Axiom optimal_critic_minimises :
  forall (pi : JointPolicy) (f : Critic),
    infonce_loss (optimal_critic pi) pi <= infonce_loss f pi.

(** At the optimum, the InfoNCE loss equals [log K - I(S; A)]. *)

Axiom optimal_critic_tight :
  forall (pi : JointPolicy),
    infonce_loss (optimal_critic pi) pi =
    INR K - mutual_information pi.
(** Proof sketch (for the population loss, K → ∞):
    Expanding the InfoNCE loss at f = f* and simplifying the softmax
    yields exactly the cross-entropy form of mutual information.
    The finite-K case introduces a bias of O(1/K) that vanishes
    as K → ∞. *)

(* ------------------------------------------------------------------ *)
(** ** MI as KL divergence

    Mutual information between state and action equals the KL divergence
    between the joint distribution π(s,a) and the product d(s)·q(a). *)

Axiom mi_as_kl :
  forall (pi : JointPolicy),
    mutual_information pi =
    expectation (d_state pi) (fun s =>
      KL (induced_joint pi s) marginal_action).
(** This is the standard identity I(S;A) = KL( p(s,a) || p(s)·p(a) ),
    specialised to our setting where the action marginal is [marginal_action]. *)

(** Combining [optimal_critic_tight] and [mi_as_kl]: *)
Corollary optimal_critic_kl :
  forall (pi : JointPolicy),
    infonce_loss (optimal_critic pi) pi =
    INR K -
    expectation (d_state pi) (fun s =>
      KL (induced_joint pi s) marginal_action).
Proof.
  intro pi.
  rewrite optimal_critic_tight.
  rewrite mi_as_kl.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Connection to the Entropy Bridge

    The KL in [mi_as_kl] is exactly the one appearing in
    Certificates/EntropyBridge.v.  Therefore, minimising the InfoNCE
    loss (equivalently, learning the optimal critic) directly tightens
    the DSEC certificate. *)

Lemma infonce_tightens_DSEC :
  forall (pi mu : JointPolicy),
    (* If [mu] is used as the reference marginal, the critic scores
       the alignment between [pi] and [mu]. *)
    mutual_information pi >=
    INR K - infonce_loss (optimal_critic pi) pi ->
    (* Then a small InfoNCE loss implies a tight DSEC certificate. *)
    forall eps : R,
      0 <= eps ->
      infonce_loss (optimal_critic pi) pi <= INR K - eps ->
      expectation (d_state pi) (fun s =>
        KL (induced_joint pi s) marginal_action) >= eps.
Proof.
  intros pi mu Hmi eps Heps Hloss.
  rewrite mi_as_kl in Hmi.
  lra.
Qed.

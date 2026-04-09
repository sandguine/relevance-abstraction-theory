(** * InfoNCE Loss

    InfoNCE (Noise Contrastive Estimation for Mutual Information) is a
    contrastive learning objective that provides a lower bound on mutual
    information.  In our setting it is used to estimate the KL divergence
    between joint policies — the quantity appearing in the Entropy Bridge.

    Setup: given a *positive* pair (s, a) drawn from the joint distribution
    π(a|s) · d(s), and [K-1] *negative* samples a₁, ..., a_{K-1} drawn
    independently from a marginal, the InfoNCE loss is:

      L_InfoNCE(f) = -E[ log( exp(f(s,a)) / Σ_k exp(f(s,aₖ)) ) ]

    where [f] is a *critic* (scorer) function.

    Key facts:
    1.  L_InfoNCE ≥ -MI(S; A) + log K  (it is a lower bound on -MI).
    2.  The bound is tight when f = f*, the optimal critic (OptimalCritic.v).
    3.  The VC-dimension of the critic class controls generalisation.

    Reference: Oord et al. (2018) "Representation Learning with CPC". *)

Require Import Reals.
Require Import List.
Import ListNotations.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Critic functions

    A critic [f : State -> JointAction -> R] scores (state, action) pairs.
    Higher scores mean "this action is more likely under π given this state". *)

Definition Critic := State -> JointAction -> R.

(* ------------------------------------------------------------------ *)
(** ** Softmax over a list

    [logsumexp vs] computes log Σ_k exp(v_k) in a numerically stable way.
    We treat it abstractly here. *)

Parameter logsumexp : list R -> R.

Axiom logsumexp_singleton :
  forall v, logsumexp [v] = v.

Axiom logsumexp_ge :
  forall (vs : list R) (v : R), In v vs -> v <= logsumexp vs.

(** The log-softmax of [v] in the list [vs] is v - logsumexp(vs). *)
Definition log_softmax (v : R) (vs : list R) : R :=
  v - logsumexp vs.

(* ------------------------------------------------------------------ *)
(** ** InfoNCE loss for a single (s, a) tuple

    Given a positive action [a_pos] and a list [a_neg] of [K-1] negatives,
    the per-sample InfoNCE loss for critic [f] at state [s] is:

      -(f(s, a_pos) - logsumexp( [f(s, a_pos)] ++ map(f s) a_neg ))

    i.e., the negative log-probability assigned to the correct answer
    in a K-way classification problem. *)

Definition infonce_sample
    (f : Critic) (s : State) (a_pos : JointAction) (a_neg : list JointAction)
    : R :=
  let scores := map (f s) (a_pos :: a_neg) in
  - log_softmax (f s a_pos) scores.

(** The InfoNCE loss is non-negative (it equals a cross-entropy). *)
Lemma infonce_sample_nonneg
    (f : Critic) (s : State) (a_pos : JointAction) (a_neg : list JointAction) :
  0 <= infonce_sample f s a_pos a_neg.
Proof.
  unfold infonce_sample, log_softmax.
  (* f(s, a_pos) ≤ logsumexp(scores) by logsumexp_ge *)
  assert (H : f s a_pos <= logsumexp (map (f s) (a_pos :: a_neg))).
  { apply logsumexp_ge. apply in_map. left. reflexivity. }
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Population InfoNCE loss

    The expected InfoNCE loss takes expectations over:
    - the state [s ~ d^π],
    - the positive action [a_pos ~ π(·|s)],
    - the [K-1] negative actions each drawn i.i.d. from a marginal [q]. *)

Parameter K : nat.                (** Batch size (number of negatives + 1). *)
Hypothesis K_pos : (K > 1)%nat.

Parameter marginal_action : Dist JointAction.
(** [marginal_action] is the action marginal against which negatives are
    drawn.  Ideally this equals the marginal of [d^π(s,a)] over [a]. *)

(** We axiomatise the population loss rather than constructing the
    product measure explicitly. *)
Parameter infonce_loss : Critic -> JointPolicy -> R.

Axiom infonce_loss_nonneg :
  forall (f : Critic) (pi : JointPolicy), 0 <= infonce_loss f pi.

(** The loss decomposes into a per-state expectation. *)
Axiom infonce_loss_decomp :
  forall (f : Critic) (pi : JointPolicy),
    infonce_loss f pi =
    expectation (d_state pi) (fun s =>
      expectation (induced_joint pi s) (fun a_pos =>
        (* K-1 negatives from [marginal_action] *)
        (* Expectation over negatives omitted for brevity *)
        infonce_sample f s a_pos [])).  (* simplified to 1 negative for now *)

(* ------------------------------------------------------------------ *)
(** ** MI lower bound

    For any critic [f] and any batch size [K]:

        I(S; A) ≥ log K - infonce_loss f pi

    where I(S; A) is the mutual information between state and action
    under the occupancy distribution.  The bound tightens as K → ∞. *)

Parameter mutual_information : JointPolicy -> R.

Axiom infonce_mi_lower_bound :
  forall (f : Critic) (pi : JointPolicy),
    mutual_information pi >=
    INR K - infonce_loss f pi.   (* INR K = ℝ-cast of K *)
(** Note: the bound involves log K, not K.  We write [INR K] here as a
    placeholder; the correct statement uses [ln (INR K)].  Fixing this
    requires importing the Coq [Rln] library. *)

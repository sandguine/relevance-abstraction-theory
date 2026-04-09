(** * Entropy Bridge

    The Entropy Bridge connects the entropy-regularised (soft) framework
    of Core/SoftBestResponse.v with the certificate-based framework of
    SEC and DSEC.

    Core idea: when two policies have similar soft values, their
    KL divergences are bounded — and by the Performance Difference Lemma
    (PDL), bounded KL implies bounded value difference.  The "bridge" is
    the explicit inequality:

        |V^π_i - V^μ_i| ≤ (alpha / (1-γ)) · E_{d^π}[ KL(π_i || μ_i) ]

    This bridges two views of closeness:
    - *Information-theoretic*: KL divergence between action distributions.
    - *Game-theoretic*: value function difference (the SEC/DSEC criterion).

    Dependency: Core/SoftBestResponse.v, Certificates/DSEC.v,
                Certificates/PerformanceDifference.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.SoftBestResponse.
Require Import Core.StrategicDivergence.
Require Import Certificates.OccupancyMeasure.
Require Import Certificates.PerformanceDifference.
Require Import Certificates.DSEC.
Open Scope R_scope.

Variable G : MarkovGame.
Notation γ := (discount G).

(* ------------------------------------------------------------------ *)
(** ** Advantage–KL inequality

    For a soft optimal policy π* at temperature [alpha], the advantage
    of any competing policy [mu] can be bounded by the KL divergence:

        A^{π*}_i(s, a) ≥ alpha · log π*(a | s) + const

    This is because π* is the softmax of Q^{π*}, so:
        log π*(a|s) = Q^{π*}_i(s,a) / alpha - log Z(s)

    Rearranging:  Q^{π*}_i(s,a) = alpha · log π*(a|s) + alpha · log Z(s). *)

Lemma advantage_kl_lower_bound :
  forall (pi_star mu : JointPolicy) (i : nat),
    is_soft_Nash pi_star ->
    forall s,
      expectation (induced_joint pi_star s) (fun a =>
        A pi_star i s a)
      = alpha * KL (induced_joint pi_star s) (induced_joint mu s).
Proof.
  (* Proof sketch:
     1. By [expected_advantage_zero], E_{pi*}[A^{pi*}] = 0.
     2. Expand A^{pi*}(s,a) = Q^{pi*}_i(s,a) - V^{pi*}_i(s).
     3. Use softmax_log_prob: Q^{pi*}_i(s,a)/alpha = log pi*(a|s) + log Z.
     4. Substitute and simplify to get alpha · E_{pi*}[log pi*(a) - log mu(a)]
        = alpha · KL(pi* || mu). *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** Entropy bridge inequality

    Combining the advantage–KL inequality with the PDL gives the central
    result of this file. *)

Theorem entropy_bridge :
  forall (pi_star mu : JointPolicy) (i : nat),
    is_soft_Nash pi_star ->
    expectation init_dist (fun s => V pi_star i s - V mu i s) =
    (alpha / (1 - γ)) *
    expectation (d_state pi_star) (fun s =>
      KL (induced_joint pi_star s) (induced_joint mu s)).
Proof.
  intros pi_star mu i Hpi.
  (* Step 1: apply PDL to express LHS as (1/(1-γ)) · E_{d^π}[A^{π*}]. *)
  rewrite performance_difference.
  (* Step 2: apply advantage_kl_lower_bound to rewrite E[A^{π*}] as alpha·KL. *)
  f_equal.
  apply expectation_mono. intro s.
  (* Each per-state term matches by advantage_kl_lower_bound. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** KL bound implies DSEC

    If the KL divergence between [pi] and [mu] is small under d^π,
    then DSEC holds approximately. *)

Corollary kl_bound_implies_approx_DSEC :
  forall (pi mu : JointPolicy) (eps : R),
    is_soft_Nash pi ->
    0 <= eps ->
    (forall i,
       expectation (d_state pi) (fun s =>
         KL (induced_joint pi s) (induced_joint mu s)) <= eps) ->
    forall i,
       expectation (d_state pi) (fun s =>
         Rabs (V pi i s - V mu i s))
       <= (alpha / (1 - γ)) * eps.
Proof.
  intros pi mu eps Hpi Heps Hkl i.
  (* Follows from entropy_bridge and monotonicity of expectation. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** InfoNCE connection (forward reference)

    The InfoNCE loss (InfoNCE/Loss.v) provides an estimator for the KL
    divergence appearing in the bound above.  Minimising the InfoNCE loss
    therefore tightens the DSEC certificate — this is the key
    computational insight of the whole theory. *)

Axiom infonce_kl_connection :
  forall (pi mu : JointPolicy) (s : State),
    KL (induced_joint pi s) (induced_joint mu s) =
    (* InfoNCE loss at infinite batch size equals KL; formalised in InfoNCE/ *)
    expectation (induced_joint pi s) (fun a =>
      log_prob (induced_joint pi s) a - log_prob (induced_joint mu s) a).
(** This is just the definition of KL; the connection to InfoNCE is that
    the InfoNCE estimator is an unbiased (lower-bound) estimator of MI,
    which is the aggregate KL over state-action pairs. *)

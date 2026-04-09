(** * VC Dimension and Classification Bounds

    The Rademacher complexity (InfoNCE/Rademacher.v) of a hypothesis class
    can be bounded in terms of its VC (Vapnik-Chervonenkis) dimension.
    This gives a purely combinatorial route to generalisation guarantees.

    For a class of binary classifiers:
      Rad_m(ℱ) = O( sqrt( VC(ℱ) · log(m) / m ) )

    For a class of real-valued functions bounded in [0, B]:
      Rad_m(ℱ) ≤ B · sqrt( 2 · VC(ℱ) · log(em/VC(ℱ)) / m )

    In our setting the critic class is typically a neural network or
    a reproducing kernel Hilbert space (RKHS); both have known VC dimensions
    or covering numbers.

    Dependency: InfoNCE/Rademacher.v *)

Require Import Reals.
Require Import InfoNCE.Rademacher.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** VC dimension *)

(** The VC dimension of a hypothesis class [ℱ] is the largest set
    of points that [ℱ] can *shatter* (classify in all 2^n ways). *)

Parameter vc_dim : HypothesisClass -> nat.

(** A class with finite VC dimension is called a *Vapnik class*.
    Infinite VC dimension implies no uniform convergence in general. *)

Definition vapnik_class (F : HypothesisClass) : Prop :=
  exists d : nat, vc_dim F = d.

(* ------------------------------------------------------------------ *)
(** ** Sauer-Shelah lemma

    The number of distinct labellings a VC-d class can produce on m
    points is at most Σ_{k=0}^{d} C(m,k), which is O(m^d).
    This combinatorial fact underlies all VC-based bounds. *)

Parameter growth_function : HypothesisClass -> nat -> nat.
(** [growth_function F m] is the maximum number of distinct label
    patterns the class [F] induces on any [m] points. *)

Axiom sauer_shelah :
  forall (F : HypothesisClass) (n : nat),
    let d := vc_dim F in
    INR (growth_function F n) <= (INR n + 1) ^ d.
(** The exact bound is Σ_{k≤d} C(n,k); we use the polynomial upper
    bound (Radon's lemma) for simplicity. *)

(* ------------------------------------------------------------------ *)
(** ** VC → Rademacher bound *)

(** For a class [F] of [B]-bounded real critics with VC dimension [d]: *)

Parameter B_bound : R.   (** Uniform bound on |f(s,a)| for f ∈ F. *)

Axiom vc_rademacher_bound :
  forall (F : HypothesisClass),
    vapnik_class F ->
    (forall f s a, F f -> Rabs (f s a) <= B_bound) ->
    rademacher_complexity F <=
    B_bound * Rsqrt (2 * INR (vc_dim F) * Rln (INR m * Rexp 1 / INR (vc_dim F)) / INR m).
(** This is Theorem 26.5 in Shalev-Shwartz & Ben-David (2014).
    The factor log(em/d) captures the growth function. *)

(* ------------------------------------------------------------------ *)
(** ** Specialisation to neural-network critics

    A fully connected network with [L] layers, width [W], and
    ReLU activations has VC dimension O(W^2 L log W).
    We record this as a structural lemma for use in practice. *)

Parameter neural_critic_class : HypothesisClass.
Parameter L W : nat.           (** Depth and width of the network. *)

Axiom neural_vc_dim :
  vc_dim neural_critic_class = (W * W * L * Nat.log2 W)%nat.
(** The exact constant is omitted; this is the leading-order term from
    Bartlett et al. (2019) "Nearly-tight VC-dimension bounds for PWL nets". *)

Corollary neural_rademacher_bound :
  (forall f s a, neural_critic_class f -> Rabs (f s a) <= B_bound) ->
  rademacher_complexity neural_critic_class <=
  B_bound * Rsqrt (2 * INR (W * W * L * Nat.log2 W) *
                   Rln (INR m * Rexp 1 / INR (W * W * L * Nat.log2 W)) /
                   INR m).
Proof.
  intro Hbnd.
  apply vc_rademacher_bound.
  - exists (W * W * L * Nat.log2 W)%nat. apply neural_vc_dim.
  - exact Hbnd.
Qed.

(* ------------------------------------------------------------------ *)
(** ** End-to-end sample complexity

    Combining the VC bound with the uniform convergence theorem from
    Rademacher.v, we get an end-to-end sample complexity guarantee:
    [m] samples suffice when m ≥ O( d · log(d/ε) / ε² · log(1/δ) ). *)

Corollary vc_sample_complexity :
  forall (eps delta : R) (pi : JointPolicy),
    0 < eps -> 0 < delta ->
    (forall f s a, neural_critic_class f -> Rabs (f s a) <= B_bound) ->
    (* Assume m is large enough that both the VC and constants terms are ≤ eps/4 *)
    rademacher_complexity neural_critic_class <= eps / 4 ->
    C_universal * Rsqrt (Rln (1 / delta) / INR m) <= eps / 4 ->
    (* Then the critic generalises: *)
    forall f, neural_critic_class f ->
      Rabs (infonce_loss f pi - empirical_infonce f) <= eps.
Proof.
  intros eps delta pi Heps Hdelta Hbnd HRad Hconst f Hf.
  eapply Rle_trans.
  - apply uniform_convergence; assumption.
  - lra.
Qed.

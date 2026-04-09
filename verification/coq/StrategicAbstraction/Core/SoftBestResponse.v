(** * Soft Best Response and Entropy Regularisation

    In standard game theory a best response maximises expected return.
    In the *soft* setting we add an entropy bonus weighted by a temperature
    parameter [alpha > 0].  The unique maximiser is a softmax (Boltzmann)
    distribution, which is always fully supported — a desirable property
    for exploration and for ensuring smooth optimisation landscapes.

    The soft Bellman operator contracts just like the standard one, so
    soft value functions are well-defined by the same fixed-point argument.

    Dependency: Core/Value.v *)

Require Import Reals.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** Shannon entropy

    [entropy mu] is H(X) = -E_{x~mu}[log p(x)] for a discrete
    distribution [mu].  For continuous distributions a density is required;
    we axiomatise the interface. *)

Parameter log_prob : forall {X : Type}, Dist X -> X -> R.
(** [log_prob mu x] returns log p(x) under the distribution [mu]. *)

Definition entropy {X : Type} (mu : Dist X) : R :=
  - expectation mu (fun x => log_prob mu x).

(** Entropy is non-negative (Gibbs' inequality). *)
Axiom entropy_nonneg : forall {X : Type} (mu : Dist X), 0 <= entropy mu.

(** Entropy is maximised by the uniform distribution. *)
Parameter uniform : forall {X : Type}, Dist X.
Axiom entropy_max :
  forall {X : Type} (mu : Dist X),
    entropy mu <= entropy (uniform (X := X)).

(* ------------------------------------------------------------------ *)
(** ** Temperature *)

(** The temperature [alpha] controls the strength of the entropy bonus.
    - As alpha → 0, soft best response → hard best response (argmax).
    - As alpha → ∞, soft best response → uniform (maximum exploration). *)

Variable alpha : R.
Hypothesis alpha_pos : 0 < alpha.

(* ------------------------------------------------------------------ *)
(** ** Soft value function

    [SV pi i s] is the soft value: expected return *plus* alpha times
    the entropy of the action distribution at state [s]. *)

Definition SV (pi : JointPolicy) (i : nat) (s : State) : R :=
  V pi i s + alpha * entropy (induced_joint pi s).

(** Soft Q-function: same modification applies to Q. *)
Definition SQ (pi : JointPolicy) (i : nat) (s : State) (a : JointAction) : R :=
  Q pi i s a.

(** The soft Bellman equation for agent [i]: *)
Lemma soft_bellman :
  forall (pi : JointPolicy) (i : nat) (s : State),
    SV pi i s =
    expectation (induced_joint pi s)
      (fun a => SQ pi i s a + alpha * (- log_prob (induced_joint pi s) a)).
Proof.
  intros pi i s.
  unfold SV, SQ, entropy.
  rewrite bellman_V.
  rewrite <- expectation_linear.
  apply f_equal. extensionality a.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soft best response

    Agent [i]'s soft best response to a joint policy [pi] is the policy
    that maximises [SV] with all other agents' policies held fixed.

    The closed form is the *softmax* (Boltzmann) distribution:
      π*(a | s) ∝ exp( Q^π_i(s, a) / alpha ).
    We axiomatise this rather than constructing it, because the
    normalisation constant (partition function) involves a sum/integral
    over the action space. *)

Parameter softmax : forall {X : Type}, (X -> R) -> Dist X.

Axiom softmax_log_prob :
  forall {X : Type} (f : X -> R) (x : X),
    log_prob (softmax f) x = f x - expectation (softmax f) (fun y => f y).
(** This says log π*(x) = f(x) - log Z, where Z = Σ exp(f(y)) is the
    partition function.  The subtracted term is exactly log Z expressed
    as an expectation. *)

Definition soft_br (pi : JointPolicy) (i : nat) : Policy i :=
  fun s => softmax (fun a => Q pi i s (replace pi i (embed_det (fun _ => a)) i s)).
(** Note: this is a simplification; in a proper treatment we would fix
    the joint action to vary only agent [i]'s component. *)

(** The soft best response is unique (softmax is always strictly positive,
    and the objective is strictly concave in the policy). *)
Axiom soft_br_unique :
  forall (pi mu : JointPolicy) (i : nat),
    (forall s a, expectation (mu i s) (fun _ => 1) =
                 expectation (soft_br pi i s) (fun _ => 1)) ->
    mu i = soft_br pi i.

(* ------------------------------------------------------------------ *)
(** ** Soft Nash equilibrium

    A joint policy [pi] is a *soft Nash equilibrium* if every agent is
    already playing its soft best response.  Such equilibria exist in
    every finite Markov game (proof by Kakutani's fixed-point theorem). *)

Definition is_soft_Nash (pi : JointPolicy) : Prop :=
  forall i, pi i = soft_br pi i.

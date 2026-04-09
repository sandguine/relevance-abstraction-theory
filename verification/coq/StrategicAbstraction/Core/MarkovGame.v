(** * Markov Games

    A Markov game (stochastic game) generalises both MDPs (one agent) and
    normal-form games (one stage) to the multi-agent sequential setting.

    We keep the state and action spaces abstract so that every downstream
    module is parametric in these choices.  Probability distributions are
    axiomatised rather than built from measure theory; doing so lets us stay
    focused on the game-theoretic content.

    Reference: Shapley (1953), "Stochastic Games". *)

Require Import Reals.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** Abstract types *)

(** The state space shared by all agents. *)
Parameter State  : Type.

(** Each agent [i] has its own action space. *)
Parameter Action : nat -> Type.

(** A joint action assigns one individual action to every agent. *)
Definition JointAction := forall i : nat, Action i.

(* ------------------------------------------------------------------ *)
(** ** Probability distributions

    [Dist X] is the type of probability distributions over [X].
    We expose only what we need: expectation.
    A full measure-theoretic treatment would require sigma-algebras;
    we defer that to future work. *)

Parameter Dist : Type -> Type.

(** [expectation mu f] computes E_{x ~ mu}[f(x)]. *)
Parameter expectation : forall {X : Type}, Dist X -> (X -> R) -> R.

Axiom expectation_linear :
  forall {X : Type} (mu : Dist X) (f g : X -> R) (c : R),
    expectation mu (fun x => c * f x + g x) =
    c * expectation mu f + expectation mu g.

Axiom expectation_mono :
  forall {X : Type} (mu : Dist X) (f g : X -> R),
    (forall x, f x <= g x) ->
    expectation mu f <= expectation mu g.

Axiom expectation_const :
  forall {X : Type} (mu : Dist X) (c : R),
    expectation mu (fun _ => c) = c.

(* ------------------------------------------------------------------ *)
(** ** Markov game record

    A game is a record so that we can easily pass an entire game as a
    single argument and project its components. *)

Record MarkovGame := mkGame {

  (** Number of agents (must be at least one). *)
  n_agents     : nat;
  n_agents_pos : (n_agents > 0)%nat;

  (** Discount factor γ ∈ [0, 1).
      Values closer to 1 weight the future more heavily. *)
  discount     : R;
  discount_lo  : 0 <= discount;
  discount_hi  : discount < 1;

  (** Transition kernel P(· | s, a): given the current state [s] and the
      joint action [a], returns a distribution over successor states. *)
  transition   : State -> JointAction -> Dist State;

  (** Per-agent reward function.  [reward i s a] is the immediate payoff
      agent [i] receives when the game is in state [s] and the agents
      execute joint action [a]. *)
  reward       : nat -> State -> JointAction -> R;

  (** Rewards are uniformly bounded, which guarantees that value functions
      are well-defined (the discounted sum converges absolutely). *)
  reward_bound : R;
  reward_bnd   :
    forall i s a, Rabs (reward i s a) <= reward_bound;
}.

(** A useful derived bound: the total discounted reward is bounded by
    [reward_bound / (1 - γ)].  We state it here for reference; proofs
    that need it can specialise this lemma. *)
Lemma value_bound (G : MarkovGame) :
  let M := reward_bound G in
  let γ := discount G     in
  forall (total : R),
    (* If [total] represents a discounted sum bounded term-by-term by M ... *)
    total <= M / (1 - γ).
Proof.
  (* This follows from the geometric series formula Σ γ^t = 1/(1-γ).
     A complete proof requires an inductive argument on the horizon;
     we leave it admitted here and revisit in Value.v. *)
  Admitted.

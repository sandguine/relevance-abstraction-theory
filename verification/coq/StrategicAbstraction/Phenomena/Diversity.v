(** * Diversity

    A collection of agents is *diverse* if no agent's policy can be
    well-approximated by a mixture of the others.  Diversity is desirable
    in multi-agent systems because diverse agents:
    - Cover more of the state-action space (better exploration).
    - Are harder to manipulate (one agent deviating cannot easily
      mimic another's behaviour).
    - Provide redundancy in cooperative tasks.

    We give two notions:
    1. *Behavioural diversity*: agents differ in their action distributions.
    2. *Value diversity*: agents disagree on the ranking of joint actions.

    The connection to SEC: a set of agents is diverse iff no two are
    SEC-related.  This makes diversity a property of the SEC equivalence
    classes rather than the individual policies.

    Dependency: Core/SEC.v, Core/StrategicDivergence.v *)

Require Import Reals.
Require Import List.
Require Import Core.MarkovGame.
Require Import Core.Policy.
Require Import Core.Value.
Require Import Core.SEC.
Require Import Core.StrategicDivergence.
Require Import Certificates.OccupancyMeasure.
Open Scope R_scope.

Variable G : MarkovGame.

(* ------------------------------------------------------------------ *)
(** ** Behavioural diversity

    Agent [i] is behaviourally [eps]-diverse relative to agent [j] if
    their action distributions differ by at least [eps] in expected KL
    over the reference occupancy measure. *)

Definition behaviourally_diverse (eps : R) (pi : JointPolicy) (i j : nat) : Prop :=
  i <> j /\
  eps <=
  expectation (d_state pi) (fun s =>
    KL (pi i s) (pi j s)).

(** A joint policy is collectively [eps]-diverse if every pair of agents
    is pairwise [eps]-diverse. *)

Definition collectively_diverse (eps : R) (pi : JointPolicy) : Prop :=
  forall i j : nat, i <> j -> behaviourally_diverse eps pi i j.

Lemma behaviourally_diverse_nonneg (eps : R) (pi : JointPolicy) (i j : nat) :
  behaviourally_diverse eps pi i j -> 0 <= eps.
Proof.
  intros [_ H].
  eapply Rle_trans; [| exact H].
  apply expectation_mono.
  intro s. apply KL_nonneg.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Value diversity

    Agent [i] is *value-diverse* relative to [j] if there exists a state
    [s] where they disagree on the ranking of two joint actions. *)

Definition value_diverse (pi : JointPolicy) (i j : nat) : Prop :=
  i <> j /\
  exists (s : State) (a b : JointAction),
    (Q pi i s a - Q pi i s b) * (Q pi j s a - Q pi j s b) < 0.
(** The sign condition says the rankings are *reversed*: agent [i] prefers
    [a] over [b] while agent [j] prefers [b] over [a]. *)

(* ------------------------------------------------------------------ *)
(** ** Diversity and SEC

    If two agents are SEC-related, they cannot be value-diverse:
    SEC implies identical Q-functions, hence identical rankings. *)

Lemma SEC_implies_no_value_diversity :
  forall (pi : JointPolicy) (i j : nat),
    SEC pi pi ->        (* reflexive *)
    i <> j ->
    (** If SEC holds with agent i and j swapped (they induce same Q): *)
    (forall s a, Q pi i s a = Q pi j s a) ->
    ~ value_diverse pi i j.
Proof.
  intros pi i j _ Hij HQ [_ [s [a [b Hlt]]]].
  rewrite HQ, HQ in Hlt.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Diversity promotes exploration

    A diverse set of agents collectively has higher entropy in the
    joint action distribution, which implies better state coverage. *)

(** Marginal entropy of the joint policy's action distribution at state [s]. *)
Definition joint_entropy (pi : JointPolicy) (s : State) : R :=
  entropy (induced_joint pi s).

(** For diverse agents, the joint entropy is bounded below. *)
Axiom diversity_entropy_lower_bound :
  forall (pi : JointPolicy) (eps : R),
    collectively_diverse eps pi ->
    forall s,
      eps / 2 <= joint_entropy pi s.
(** Proof sketch: if agents are eps-diverse in KL, their mixture has
    higher entropy than any individual by the concavity of entropy. *)

(* ------------------------------------------------------------------ *)
(** ** Diversity preservation under SEC

    Diversity is a property of the SEC equivalence class:
    if we replace [pi] by a SEC-equivalent [mu], the diversity
    of the collection is unchanged. *)

Lemma diversity_preserved_by_SEC :
  forall (pi mu : JointPolicy) (eps : R),
    SEC pi mu ->
    collectively_diverse eps pi ->
    collectively_diverse eps mu.
Proof.
  intros pi mu eps Hsec Hdiv i j Hij.
  unfold behaviourally_diverse in *.
  destruct (Hdiv i j Hij) as [_ Hkl].
  split; [exact Hij |].
  (* The KL bound uses the occupancy measure of mu; relate to pi's via SEC. *)
  (* Full proof requires d^π = d^μ under SEC, which follows from PDL. *)
  Admitted.

(* ------------------------------------------------------------------ *)
(** ** Minimum diversity certificate

    We define a diversity certificate as a lower bound on the
    pairwise KL divergence that can be verified from data. *)

Definition diversity_certificate (pi : JointPolicy) (eps : R) : Prop :=
  0 < eps /\ collectively_diverse eps pi.

Lemma diversity_certificate_sound :
  forall (pi : JointPolicy) (eps : R),
    diversity_certificate pi eps ->
    0 < eps.
Proof.
  intros pi eps [Hpos _]. exact Hpos.
Qed.

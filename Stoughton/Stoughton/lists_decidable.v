(** * Extra Lemmata about Lists *)

(** This library expands the standard library [Coq.Lists.List]
   where the base set [A] is a decidable type with respect to
   Coq's equality [eq].

   One might even generalize over the equality like the standard
   libraries such as [DecidableType], [DecidableTypeEx], etc.
   However, we choose the simplest way by using [eq]. *)

Set Implicit Arguments.

Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.

(*****************************************************************)
(** ** Extra properties about lists *)
(*****************************************************************)

(** Notations for [In] and [~ In] *)

Notation " x @ l " := (In x l) (at level 70).
Notation " x # l " := (~ In x l) (at level 70).

Hint Resolve in_or_app in_app_or : datatypes.

Lemma in_cons_1 : forall A (l : list A) (a b : A), 
  a <> b ->
  b @ (a::l) ->
  b @ l.
Proof.
  intros until 1; simpl; intuition. 
Qed.

Hint Resolve in_cons_1 : datatypes.
Hint Resolve in_eq in_cons : datatypes.

Lemma in_app_1 : forall A (a : A)(l m : list A),
  a @ l ->
  a @ (l ++ m).
Proof.
  intros; auto with datatypes.
Qed.

Lemma in_app_2 : forall A (a : A)(l m : list A),
  a @ m ->
  a @ (l ++ m).
Proof.
  intros; auto with datatypes.
Qed.

Hint Resolve in_app_1 in_app_2 : datatypes.

Lemma notin_app_1 : forall A (a : A) (l m : list A),
  a # l ->
  a # m ->
  a # (l ++ m).
Proof.
  intuition; elim (in_app_or _ _ _ H1); assumption.
Qed.

Lemma notin_app_2 : forall A (a : A) (l m : list A),
  a # (l ++ m) ->
  a # l /\ a # m.
Proof.
  firstorder with datatypes.
Qed.

Lemma notin_app_3 : forall A (a : A)(l m : list A),
  a # (l ++ m) -> a # l.
Proof.
  intros; firstorder with datatypes.
Qed.

Lemma notin_app_4 : forall A (a : A)(l m : list A),
  a # (l ++ m) -> a # m.
Proof.
  intros; firstorder with datatypes.
Qed.

Hint Resolve notin_app_1 notin_app_2 : datatypes.
Hint Resolve notin_app_3 notin_app_4 : datatypes.

Lemma notin_cons_1 : forall A (a b : A)(l : list A),
  a # (b :: l) ->
  a <> b.
Proof.
  firstorder with datatypes.
Qed.

Lemma notin_cons_2 : forall A (a b : A)(l : list A),
  a # (b :: l) ->
  a # l.
Proof.
  firstorder with datatypes.
Qed.

Lemma notin_cons_3 : forall A (a b : A) (l : list A),
  a <> b ->
  b # l ->
  b # (a :: l).
Proof.
  firstorder with datatypes.
Qed.

Hint Resolve notin_cons_1 notin_cons_2 notin_cons_3 : datatypes.

Lemma notin_singleton : forall A (a b : A),
  a <> b ->
  ~ In b (a :: nil).
Proof.
  firstorder.
Qed.

Lemma notin_empty : forall A (a : A),
  ~ In a nil.
Proof.
  firstorder.
Qed.

Hint Resolve notin_singleton notin_empty : datatypes.

Lemma notin_app_or : forall A (l m : list A) (x : A),
  x # (l ++ m) -> x # l /\ x # m.
Admitted.

Lemma notin_or_app : forall A (l m : list A) (x : A),
  x # l /\ x # m -> x # (l ++ m).
Admitted.

Tactic Notation "destr_app" :=
  match goal with
    | H : ?x @ ?l1 ++ ?l2 |- _ =>
      elim (in_app_or l1 l2 x H); clear H; intros
    | H : ?x # ?l1 ++ ?l2 |- _ =>
      elim (notin_app_or l1 l2 x H); clear H; intros
    | |- ?x # ?l1 ++ ?l2       =>
      apply (notin_or_app l1 l2 x)
  end.


(*****************************************************************)
(** ** Decidable Type *)
(*****************************************************************)

(** A type [A] is _decidable_ when the equality on [A] is decidable:
   [[
   forall (x y : A), {x = y} + {x <> y}
   ]]

   Definitions and lemmata below are hold for any decidable base type [A].

   In order to make general arguments, we adopt module types. *)

Module Type DecidableType.

  Parameter Inline X : Type.

  Axiom dec : forall (x y : X), {x = y} + {x <> y}. 

End DecidableType.

(** Module collecting extra lemmata w.r.t. lists on a decidable type *)

Module DecidableIn (Export modX : DecidableType).

  (** Being-in-a-list is decidable. *)

  Lemma dec_in : forall (x : X) (l : list X),
    {x @ l} + {x # l}.
  Proof.
    induction l as [| y]; simpl;
      [ right
        | destruct (dec y x); destruct IHl
      ]; intuition.
  Defined.

  Hint Resolve dec_in : datatypes.

  (** Notations and tactics for decidability *)

  Notation "x == y"  := (dec x y) (at level 70).
  Notation "x <-? l" := (dec_in x l) (at level 70).

  Ltac case_dec :=
    let ldestr x y := destruct (x == y); [try subst x | idtac] in
      match goal with
        | |- context [?x == ?y]      => ldestr x y
        | H: context [?x == ?y] |- _ => ldestr x y
      end.

  Ltac case_in :=
    match goal with
      | |- context [?x <-? ?l]       => destruct (x <-? l)
      | H : context [?x <-? ?l] |- _ => destruct (x <-? l)
    end.

  (** Notation for [remove] operation *)

  Notation " l \ { x } " := (remove dec x l) (at level 59).

  (** Properties about [remove] *)

  Lemma in_rm_1 : forall (a b : X) (l : list X),
    a @ (l \ {b}) ->
    a @ l.
  Proof.
    induction l; simpl; intros; auto.
    repeat case_dec; firstorder.
  Qed.

  Lemma in_rm_2 : forall (a b : X) (l : list X), 
    a <> b ->
    a @ l ->
    In a (l \ {b}).
  Proof.
    induction l; simpl; intros; auto.
    repeat case_dec; firstorder; congruence.
  Qed.

  Lemma in_rm_3 : forall (a b : X) (l : list X),
    a @ (l \ {b}) ->
    a <> b.
  Proof.
    induction l; simpl; intros; auto.
    case_dec; firstorder; congruence.
  Qed.

  Hint Resolve in_rm_1 in_rm_2 in_rm_3 : datatypes.

  Lemma notin_rm_1 : forall (a : X) (l : list X),
    a # (l \ {a}).
  Proof.
    induction l; simpl; intros; try case_dec; firstorder.
  Qed.

  Lemma notin_rm_2 : forall (a b : X) (l : list X),  
    a <> b ->
    a # (l \ {b}) ->
    a # l.
  Proof.
    firstorder using notin_rm_1.
  Qed.

  Hint Resolve notin_rm_1 notin_rm_2 : datatypes.

  Lemma notin_rm_3 : forall (x : X) (l : list X),
    x # l -> l \ {x} = l.
  Proof.
    induction l; simpl; try case_dec; firstorder. 
    rewrite H1; auto.
  Qed.

  Lemma notin_rm_4 : forall (x y : X) (l : list X),
    x # l -> x # l \ {y}.
  Proof.
    induction l; simpl; try case_dec; firstorder. 
  Qed.

  Hint Resolve notin_rm_3 notin_rm_4 : datatypes.

  Lemma eq_rm_cons : forall a b (l : list X),
    a <> b ->
    b :: (l \ {a}) = (b :: l) \ {a}.
  Proof.
    intros; simpl; destruct (dec a b);
      [ elim H
        | ];
      auto.
  Qed.

  Hint Resolve eq_rm_cons.

  Lemma rm_app : forall l m x,
    (l ++ m) \ {x} = l \ {x} ++ m \ {x}.
  Admitted.

  Hint Resolve rm_app.

  Tactic Notation "rewrite_app" :=
    match goal with
      | |- context [ (?l1 ++ ?l2) \ {?x} ] => rewrite (rm_app l1 l2 x)
    end.

End DecidableIn.


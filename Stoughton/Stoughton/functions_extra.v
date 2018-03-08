(** * About Functions  *)

Set Implicit Arguments.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import lists_decidable.
Require Import fresh_variables.
Require Import case_tac.

(** The following module contains extra definitions and properties
    about functions *) 

Module FunctionExtra (modX : DecidableType).

  Include DecidableIn modX.

  (** Updating a function by a new value *) 

  Definition up (E : Type) (f : X -> E) (e : E) (d : X) : X -> E :=
    fun x => if x == d then e else f x.

  Notation " f [[ e => d ]] " := (up f e d) (at level 70).

  (** Functional extensionality on a finite domain *)

  Definition f_ext (E : Type) (f g : X -> E) (L : list X) :=
    forall (x : X), x @ L -> f x = g x.

  Lemma up_new : forall E (f : X -> E) e d,
    f [[e => d]] d = e.
  Proof.
    unfold up; intros; case_dec; intuition.
  Qed.

  Lemma up_old : forall E (f : X -> E) e d x,
    x <> d -> f [[e => d]] x = f x.
  Proof.
    unfold up; intros; case_dec; intuition.
  Qed.

  Tactic Notation "rewrite_up" :=
    match goal with
      | [ H : context [ _ [[_ => ?d]] ?d ] |- _ ]
        => rewrite up_new in H
      | [ |- context [ _ [[_ => ?d]] ?d ] ]
        => rewrite up_new
      | [ H : context [ _ [[_ => ?d]] ?x ] |- _ ]
        => rewrite up_old in H; auto
      | [ |- context [ _ [[_ => ?d]] ?x ] ]
        => rewrite up_old ; auto
    end.

End FunctionExtra.


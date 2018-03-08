(** * Choice of fresh variables *)

(** We extend the signature [DecidableType] by an operator
   building a fresh one w.r.t. finite sets.

   The resulting signature ensures e.g. that choice of fresh variable
   is always possible given a finite list of terms. *)

Set Implicit Arguments.

Require Import Coq.Arith.Max.
Require Import lists_decidable.

Module Type DecidableTypeExt.

  Include DecidableType.

  Parameter Inline choice : list X -> X.

  Axiom choice_fresh : forall (l : list X), choice l # l.

End DecidableTypeExt.

(** The set of natural numbers is the standard example satisfying
   [DecidableTypeExt]. *)

Module Nat <: DecidableTypeExt.

  Definition X := nat.

  Definition dec := eq_nat_dec.

  (** The [choice] function could be arbitrary as long as
     [choice_fresh] is satisfied. Our choice is to take [lub(L) + 1]
     given a finite list [L] of natural numbers. *)

  Definition choice (l : list X) : X := S (fold_right max 0 l).

  Lemma choice_no_zero : forall (l : list X), choice l <> 0.
  Proof.
    unfold choice; intros; auto with arith.
  Qed.

  Lemma in_less : forall (n : X)(l : list X),
    n @ l ->
    n < choice l.
  Proof.
    unfold choice; induction l; simpl; intro H; elim H; intro; subst;
      [ auto with arith
        | apply lt_le_trans with (m := S (fold_right max 0 l));
          eauto 2 with arith
      ].
  Qed.

  Lemma choice_fresh : forall l : list X, (choice l) # l.
  Proof.
    intros l H.
    elim (lt_irrefl (choice l)).
    apply in_less; exact H.  
  Qed.
End Nat.


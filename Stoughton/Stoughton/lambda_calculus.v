(** * Untyped Lambda Calculus *)

Set Implicit Arguments.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import lists_decidable.
Require Import fresh_variables.
Require Import functions_extra.
Require Import case_tac.

(** The current work is a formalization of Allen Stoughton's paper
   _Substitution Revisited_.

    The structure of our work is the same as that of Stoughton.
    Even the numbering is the same *)


(*****************************************************************)
(** ** 1. Introduction *)
(*****************************************************************)

(** The characteristics of her paper are

   - using one sort of variable sets;
   - using simultaneous substitution instead of single substitution;
   - using unrestricted substitution for the untyped lambda calculus. *)

(*****************************************************************)
(** ** 2. Definitions *)
(*****************************************************************)

(** *** Untyped Lambda Terms *)

(** There is only one sort of variables. That is, no distinction
   between local and global variables.

   For simplicity, we use natural numbers to denote variable names.
   However, any type satisfying [DecidableTypeExt] could do the same
   job.

   The module [Nat] is defined in the module [fresh_variables]. *)

(** Importing the library about decidable [In] predicate and
   functional extensionality *)

Module Import Nat_dec := FunctionExtra Nat.

(** Notation for the set of variables *)

Notation var := nat.

(** The type of terms *)

Inductive term : Set :=
  Var : var -> term
| App : term -> term -> term
| Lam : var -> term -> term.

(** Notational convention:

   - u, v, w, x ,y range over variables.
   - M, N range over terms.
   - L, L' range over finite lists. *)

(** *** Free Variables *)

Fixpoint FV (M : term) : list var :=
  match M with
    | Var x     => x :: nil
    | App M0 M1 => FV M0 ++ FV M1
    | Lam x M'  => FV M' \ {x}
  end.

(** *** Substitution functions *)

(** The type of simultaneous substitutions =: [var -> term]. *)

Definition substitution := var -> term.

(** The identity substitution *)

Notation iota := (fun (x : X) => Var x).

(** Collecting free variables occurring during substitution *)

Fixpoint fv_coll (L : list var) (rho : substitution) : list var :=
  match L with
    | nil     => nil
    | x :: l0 => FV (rho x) ++ fv_coll l0 rho
  end.

(** In Stoughton's paper, an operation called _new_ builds sets of
   variables which do not occur in the values of a substitution.

   We use [old] as the dual function such that it constructs finite
   complement of _new_ operaton. That is, it collects all the
   variables occurring during a substitution.

   In combination with [old], [choice] operation provides a fresh
   variable w.r.t. a substitution. *)

Definition old (x : var) (M : term) (rho : substitution) : list var :=
  fv_coll (FV M \ {x}) rho.

Hint Unfold old.

(** Properties about [fv_coll] *)

Lemma fv_coll_app : forall (L L' : list var) (rho : substitution),
  fv_coll (L ++ L') rho =
  fv_coll L rho ++ fv_coll L' rho.
Proof.
  induction L; simpl; intros; auto.
  rewrite app_assoc_reverse.
  f_equal; auto.
Qed.

Lemma fv_coll_rm : forall (L : list var) (x y : var) (rho : substitution),
  y # fv_coll (L \ {x}) rho -> 
  fv_coll L (rho [[Var y => x]]) \ {y} = fv_coll (L \ {x}) rho.
Proof.
  induction L as [ | z]; simpl; intros; auto.
  case_dec; simpl.

  Case "x = z".
  rewrite_up; simpl; case_dec; intuition.

  Case "x <> z".
  rewrite_up. rewrite_app.
  simpl in *.
  f_equal; destr_app; auto.
  apply notin_rm_3; auto.
Qed.  

Lemma fv_coll_iota : forall (L : list var),
  L = fv_coll L iota.
Proof.
  induction L; simpl; [ | f_equal]; auto.
Qed.

Lemma fv_coll_iota_up : forall (L : list var) (x y z : var),
  y <> x ->
  y # fv_coll L (iota [[Var z => x]]) ->
  y # L.
Proof.
  induction L as [ | v L']; simpl; intros; auto.
  destr_app.
  destruct (x == v).

  Case "x = v".
  subst.
  rewrite_up; simpl in *. 
  red; intro Hor; elim Hor; clear Hor; auto.
  change (y # L'); eauto. 

  Case "x <> v".
  red; intro Hor; elim Hor; clear Hor; auto.

  SCase "/\-left".
  rewrite_up; simpl; firstorder.

  SCase "/\-right".
  change (y # L'); eauto.
Qed.

Lemma fresh_iota : forall (M : term) (x : var),
  choice (old x M iota) # FV M \ {x}.
Proof.
  unfold old; intros.
  rewrite <- fv_coll_iota.
  apply choice_fresh.
Qed.

(** *** Simultaneous substitution *)

Fixpoint subst (M : term) (rho : substitution) {struct M} : term :=
  match M with
    | Var x     => rho x
    | App M0 M1 => App (subst M0 rho) (subst M1 rho)
    | Lam x M'  => let y := choice (old x M' rho) in
                     Lam y (subst M' (rho [[Var y => x]]))
  end.

Notation " M {{ rho }} " := (subst M rho) (at level 55).

(** The following lemma [fv_coll_subst] is the most crucial lemma
   in the whole development.

   It reduces many of the lemmas about substitution and free
   variables to properties about collecting free variables. *)

Lemma fv_coll_subst : forall (M : term) (rho : substitution),
  FV (M {{rho}}) = fv_coll (FV M) rho.
Proof. 
  induction M as [x | | x M']; simpl; intros.

  Case "Var".
  auto using app_nil_end.

  Case "App".
  rewrite fv_coll_app.
  f_equal;auto.

  Case "Lam".
  rewrite IHM'.
  auto using fv_coll_rm, choice_fresh.
Qed.

(** N.B. Note that we use Coq's internal equality instead of any
   kind of set-theoretic equalities or setoid equalities. *)

(** Composition of simultaneous substitutions *)

Definition comp (eta rho : substitution) : substitution :=
  fun x => (rho x) {{eta}}.

(** *** alpha-congruence  *)

(** Notation for alpha-congruence *)

Reserved Notation "M 'Eq' N" (at level 75).

(** The following definition corresponds to [Corollary 3.10] in
   Stoughton's paper:

   - She gave first informal definition of alpha-congruence
     as the least equivalence relation on [term] such that

     - (mu) [M N Eq M' N'] if [M Eq N] and [M' Eq N']; and

     - (alpha) [Lam x M Eq Lam y N] if either 
       - [x = y] and [M Eq N], or
       - [y # FV M] and [M {{iota [[Var => x]]}} Eq N].
   - The condition (alpha) above is given a name:
    [[
    M(x) Eq N(y)
    ]]
   - Then [Corollary 3.10] shows that the alpha-congruence
     of two terms can be characterized by a structural
     induction.

     So we took [Corollary 3.10] as our definition of alpha-
     congruence and then shows below that it is a equivalence
     relation. *)

Inductive a_cong : term -> term -> Prop :=
| al_var : forall (x : var), (Var x) Eq (Var x)
| al_app : forall (M N M0 N0 : term),
  M Eq M0 ->
  N Eq N0 ->
  (App M N) Eq (App M0 N0)
| al_lam_eq : forall (x y : var) (M N : term),
  x = y ->
  M Eq N ->
  (Lam x M) Eq (Lam y N)
| al_lam_notin : forall (x y : var) (M N : term),
  y # FV M ->
  (M {{iota [[Var y => x]]}}) Eq N ->
  (Lam x M) Eq (Lam y N)
  
  where " M 'Eq' N " := (a_cong M N).

Hint Constructors a_cong.

(** Formal definition of [M(x) Eq N(y)] *)

Definition alpha_cond M x N y :=
  (x = y /\ M Eq N) \/ (y # FV M /\ M {{iota [[Var y => x]]}} Eq N).

(** The simple state that [M(x) Eq N(y)] implies [N(y) Eq M(x)]
   cannot be proved until some properties about substitution and
   alpha-congruence are proved.

   In fact, not until Theorem 3.5 in Stoughton's paper
   ([T3_5] in our formalization).

   It is closely related to the proof of the symmetry
   of the alpha-congruence. So, the fact that alpha-congruence is
   indeed an equivalence relation could be shown after [T3_5]. *)

(** alpha-congruence of substitutions *)

Definition subst_cong (rho eta : substitution) (L : list var) :=
  forall x, x @ L -> (rho x) Eq (eta x).

Definition subst_cong' (rho eta : substitution) :=
  forall x, rho x Eq eta x.


(*****************************************************************)
(** ** 3. Substitutions and alpha-congruence  *)
(*****************************************************************)

(** The reflexivity, symmetry, and transitivity of alpha-congruence
   are necessary in showing other properties about substitution and
   alpha-congruence. They will be shown when it is possible. *)

(** Reflexivity of alpha-congruence *)

Lemma a_cong_refl (M : term) : M Eq M.
Proof.
  induction M; auto.
Qed.

Lemma L3_1_i : forall (M : term) (x y : var),
  y # FV M -> Lam x M Eq Lam y (M {{iota [[Var y => x]]}}).
Proof.
  intros.
  apply al_lam_notin; auto using a_cong_refl.
Qed.

Lemma L3_1_ii' : forall (L : list var)(x : var)(rho : substitution),
  x @ fv_coll L rho <-> exists y : var, y @ L /\ x @ FV (rho y).
Proof.
  split; induction L; simpl; intros; firstorder.

  Case "->".
  destr_app;
    [exists a; firstorder
      | destruct (IHL) as [z]; auto; exists z; firstorder].

  Case "<-".
  subst; auto with datatypes. 
Qed.

Lemma L3_1_ii : forall (M : term)(x : var)(rho : substitution),
  x @ FV (M {{rho}}) <-> exists y :var,  y @ FV M /\ x @ FV (rho y).
Proof.
  split; intros.

  Case "->".
  rewrite fv_coll_subst in *.
  apply L3_1_ii'; auto.

  Case "<-".
  rewrite fv_coll_subst.
  apply L3_1_ii'; auto.
Qed.

Lemma L3_1_iii : forall (M N : term),
  M Eq N -> FV M = FV N.
Proof.
  induction 1; simpl; intros; intuition try congruence.

  Case "al_lam_notin".
  match goal with
    | [ H : FV _ = FV _ |- _ ] => rewrite <- H; auto
  end.
  rewrite fv_coll_subst.
  rewrite fv_coll_rm.
  apply fv_coll_iota.

  rewrite <- fv_coll_iota; auto with datatypes.
Qed.

Lemma L3_1_iv' : forall (rho eta : substitution)(L : list var),
  subst_cong rho eta L ->
  fv_coll L rho = fv_coll L eta.
Proof.
  unfold subst_cong; induction L; simpl; intros; auto.
  f_equal; auto using L3_1_iii.
Qed.

(** Note that [old] is the dual, finite countepart of [new] in
   Stoughton's original paper. *)

Lemma L3_1_iv : forall (M N :term)(x : var)(rho eta : substitution),
  M Eq N ->
  subst_cong rho eta (FV M \ {x}) ->
  old x M rho = old x N eta.
Proof.
  unfold old, subst_cong; intros M N x rho eta HEq Hcong.
  rewrite <- (L3_1_iii HEq).
  auto using L3_1_iv'.
Qed.

Lemma L3_1_v : forall (M : term)(rho eta : substitution),
  f_ext rho eta (FV M) ->
  M {{rho}} = M {{eta}}.
Proof.
  unfold f_ext; induction M as [y | | y M' HM']; simpl;
    intros rho eta Heq; auto.

  Case "M = App M1 M2".
  f_equal; auto using Heq with datatypes.

  Case "M = Lam y M'".
  f_equal.

    SCase "binder case".
    rewrite (@L3_1_iv M' M' y rho eta (a_cong_refl M')); auto.
    red; intros; rewrite Heq; auto using a_cong_refl.

    SCase "body case".
    apply HM'; intros; unfold up; case_dec.

    SSCase "x = y".
    rewrite (@L3_1_iv M' M' y rho eta (a_cong_refl M')); auto.
    red; intros; rewrite Heq; auto using a_cong_refl.

    SSCase "x <> y".
    auto using Heq, in_rm_2.
  Qed.

(** Functional extensionality w.r.t. the identity substitution *)

Lemma f_ext_iota : forall (L : list var) (x : var),
  f_ext (iota [[Var x => x]]) iota L.
Proof.
  red; intros.
  unfold up; case_dec; auto.
Qed.

Lemma iota_ext : forall (x : var), 
  iota [[Var x => x]] = iota.
Proof.
  intros.
  extensionality y.
  destruct (x == y).

  subst; rewrite_up; auto.
  rewrite_up; congruence.
Qed.

Lemma f_ext_notin : forall (M : term)(x : var)(L : list var),
  x # L -> 
  f_ext (iota [[M => x]]) iota L.
Proof.
  red; unfold up; intros.
  case_dec; intuition.
Qed.

Hint Resolve f_ext_iota f_ext_notin : datatypes.

(** The original proof of Lemma 3.1.(vi) is based on the symmetry
   of tha alpha congruence. So we give first its symmetric form and
   postpone the original form until Theorem 3.2., where we can prove
   the original form without using the symmetry of the
   alpha-congruence. *)

Lemma L3_1_vii : forall (M N : term)(x y : var)(rho : substitution),
  alpha_cond M x N y ->
  old x M rho = old y N rho.
Proof.
  unfold alpha_cond, old; intros.
  destruct H; destruct H as [H' HEq].

  Case "\/-left".
  rewrite (L3_1_iii HEq); subst; auto.

  Case "\/-right".
  rewrite <- (L3_1_iii HEq).
  rewrite fv_coll_subst.
  f_equal; rewrite fv_coll_rm;
    rewrite <- fv_coll_iota; auto with datatypes.
Qed.
  
Lemma L3_1_viii' : forall (L : list var)(x y : var)(rho eta : substitution),
  y # fv_coll (L \ {x}) rho ->
  fv_coll (L \ {x}) (comp eta rho) =
  fv_coll (fv_coll L (rho [[Var y => x]]) \ {y}) eta.
Proof.
  induction L as [ | z L' Hl']; simpl; intros; auto.

  Case "L = z :: L'".
  case_dec.                     (* x == z *)

  SCase "x = z".
  rewrite_up; simpl; case_dec; intuition.

  SCase "x <> z".
  rewrite_up; simpl; try congruence.
  rewrite_app; rewrite fv_coll_app.
  f_equal.

  SSCase "++=left".
  unfold comp; rewrite fv_coll_subst; simpl in *.
  destr_app; auto; rewrite notin_rm_3; auto.

  SSCase "++-right".
  simpl in *; destr_app; auto.
Qed.

Lemma L3_1_viii : forall (M : term)(x y : var)(rho eta : substitution),
  y # (old x M rho) ->
  old x M (comp eta rho) = old y (M {{rho [[Var y => x]]}}) eta.
Proof.
  unfold old; intros.
  rewrite fv_coll_subst.
  apply L3_1_viii'; auto.
Qed.

(** Syntactic Substitution Theorem:

   - Performaing the composition of two substitutions yields the same
     result as performing those substitutions sequentially. *)

Lemma fv_coll_notin_1 : forall (L : list var)(x x0 x1 y : var)(rho : substitution),
  y # fv_coll (L \ {x}) rho ->
  x0 @ L ->
  x <> x0 ->
  x1 @ FV (rho x0) ->
  x1 <> y.
Proof.
  red; intros.
  subst x1.
  elim H.
  apply L3_1_ii'.
  exists x0; firstorder.
Qed.

Lemma fv_coll_notin_2 : forall (L : list var)(x y : var),
  x <> y ->
  x # fv_coll L (iota [[Var y => x]]).
Proof.
  red; intros L x y Hneq Hin0.
  generalize (L3_1_ii' L x (iota [[Var y => x]])); intro Hand.
  destruct Hand as [HandL HandR]; clear HandR.
  destruct (HandL Hin0) as [z Hand1]; clear HandL Hin0.
  destruct Hand1 as [Hand1L Hand1R].
  unfold up in *.
  case_dec; simpl in *; intuition.
Qed.

Theorem T3_2 : forall (M : term) (rho eta : substitution),
  (M {{rho}}) {{eta}} = M {{comp eta rho}}.
Proof.
  induction M as [x | | x M' HM']; simpl; intros;
    [ | f_equal | ]; auto.

  Case "M = Lam x M'".
  remember (choice(old x M' rho)) as y.
  remember (choice(old y (M' {{rho [[Var y => x]]}}) eta)) as y'.
  remember (choice(old x M' (comp eta rho))) as z.

  assert (y' = z) as Heq.
    subst y' z; rewrite <- L3_1_viii; auto.
    subst y; apply choice_fresh.

  f_equal; auto.
  rewrite HM'. apply L3_1_v.
  red; unfold comp; intros; destruct (x == x0).

  SCase "x = x0".
  subst x0.
  do 2 rewrite_up; simpl.
  rewrite_up; congruence.

  SCase "x <> x0".
  do 2 rewrite_up.
  apply L3_1_v; red; intros.
  rewrite_up.
  generalize (choice_fresh (old x M' rho)); intro.
  rewrite <- Heqy in *.
  unfold old in *; eapply (fv_coll_notin_1); eauto.
Qed.

(** Now we can prove the original form of Lemma 3.1.(vi).
   The proof is a bit long because we cannot use the symmetry
   of the alpha congruence. Indeed, we need Lemma 3.1.(vi) in order to
   prove the symmetry of the alpha congruence.

   If we had the symmtry the proof will become much shortet as
   demonstrated by [L3_1_vi']. *)

Lemma L3_1_vi : forall (M : term), M {{iota}} Eq M.
Proof.
  induction M as [ | | x M']; simpl; auto.

  Case "M = Lam x M'".
  remember (choice (old x M' iota)) as y. destruct (x == y).

  SCase "x = y".
  subst x. apply al_lam_eq; auto.
  rewrite (@L3_1_v _ _ iota); auto using f_ext_iota.

  SCase "x <> y".
  apply al_lam_notin.

  SSCase "binder case".
  rewrite (fv_coll_subst). unfold old in *; rewrite <- fv_coll_iota in *.
  apply fv_coll_notin_2; auto.

  SSCase "body case".
  rewrite T3_2. rewrite (@L3_1_v _ _ iota); auto.
  unfold f_ext, comp; intros. destruct (x == x0).

  SSSCase "x = x0".
  subst x; do 2 (rewrite up_new; simpl); auto.

  SSSCase "x <> x0".
  rewrite up_old; auto; simpl; unfold old in *.
  assert (x0 <> y).
    generalize (choice_fresh (old x M' iota)); intro.
    unfold old in *; rewrite <- Heqy in *.
    eapply fv_coll_notin_1; eauto; simpl; auto.
  rewrite up_old; auto.
Qed.

(** From [L3_1_v] and [L3_1_vi], if [x # FV M] then
   [M {{iota [[N => x]]}} Eq M].*)

Remark R3_1_v_and_vi : forall (M N : term)(x : var),
  x # FV M ->
  M {{iota [[N => x]]}} Eq M.
Proof.
  intros.
  assert (M {{iota}} = M {{iota [[N => x]]}}) as Heq.
    apply L3_1_v.
    red; intros. rewrite up_old; intuition congruence.
  rewrite <- Heq; apply L3_1_vi.
Qed.

Corollary C3_3' : forall (M N : term)(x y : var)(rho : substitution),
  y # (FV M \ {x}) ->
  (M {{iota [[Var y => x]]}}) {{rho [[N => y]]}} = M {{rho [[N => x]]}}.
Proof.
  intros. rewrite T3_2. apply L3_1_v.
  unfold f_ext, comp; intros. destruct (x == x0).

  Case "x = x0".
  subst x0; repeat (rewrite up_new; simpl); reflexivity.

  Case "x <> x0".
  repeat (rewrite up_old; auto; simpl).
  red; intro; subst.
  elim H; auto with datatypes.
Qed.

Corollary C3_3 : forall (M N : term)(x y : var)(rho : substitution),
  y # FV M ->
  (M {{iota [[Var y => x]]}}) {{rho [[N => y]]}} = M {{rho [[N => x]]}}.
Proof.
  intros; auto using C3_3' with datatypes.
Qed.

Corollary C3_4_i_1 : forall (rho : substitution),
  subst_cong' (comp iota rho) rho.
Proof.
  unfold subst_cong'.
  unfold comp; intros.
  apply L3_1_vi.
Qed.

Corollary C3_4_i_2 : forall (rho : substitution),
  rho = (comp rho iota).
Proof.
  unfold comp; simpl; intros.
  extensionality x; auto.
Qed.

Corollary C3_4_ii : forall (rho1 rho2 rho3 : substitution),
  comp rho3 (comp rho2 rho1) = comp (comp rho3 rho2) rho1.
Proof.
  unfold comp; intros.
  extensionality x.
  rewrite T3_2; auto.
Qed.

Theorem T3_5 : forall (M N : term),
  M Eq N -> forall rho, M {{rho}} = N {{rho}}.
Proof.
  induction 1; simpl; intros; [ | f_equal | | ]; auto.

  Case "al_lam_eq".
  rewrite IHa_cong.
  rewrite (@L3_1_vii M N x y); [subst; reflexivity | ].
  unfold alpha_cond; firstorder.

  Case "al_lam_notin".
  remember (choice (old x M rho)) as z1.
  remember (choice (old y N rho)) as z2.
  assert (z1 = z2) as Heq.
    subst z1 z2. rewrite (@L3_1_vii M N x y); [reflexivity | ].
    unfold alpha_cond; right; auto.
  rewrite <- Heq. f_equal; rewrite <- (C3_3 M _ x y rho); auto.
Qed.

(** *** alpha-congruence is an equivalence relation. *)

(** Symmetry of alpha_equivalence *)

Lemma a_cong_sym (M N : term) :
  M Eq N -> N Eq M.
Proof.
  induction 1; auto.

  Case "al_lam_notin".
  apply al_lam_notin.

  SCase "binder case".
  cut (x # FV (M {{iota [[Var y => x]]}}));
    [ rewrite (L3_1_iii H0); auto | ].
  rewrite fv_coll_subst. destruct (x == y).

  SSCase "x = y"; subst.
  rewrite iota_ext; rewrite <- fv_coll_iota; auto.

  SSCase "x <> y".
  apply fv_coll_notin_2; auto.

  SCase "body hypothesis".
  rewrite (T3_5 IHa_cong (iota [[Var x => y]])).
  rewrite (C3_3); auto. rewrite iota_ext. apply L3_1_vi.
Qed.

(** Short proof of Lemma 3.1.(vi) with the help of the symmetry of
    alpha congruence.  *) 

Remark L3_1_vi' : forall (M : term), M {{iota}} Eq M.
Proof.
  induction M as [ | | x M']; simpl; auto.

  Case "M = Lam x M'".
  remember (choice (old x M' iota)) as y.
  destruct (x == y).

  SCase "x = y".
  subst x; apply al_lam_eq; auto.
  rewrite (@L3_1_v _ _ iota); auto using f_ext_iota.

  SCase "x <> y".
  apply a_cong_sym. apply L3_1_i.
  subst y; eauto using notin_rm_2, fresh_iota.   
Qed.

(** Transitivity of alpha_equivalence:

   - We prove first the transitivity w.r.t. identity substitution. *)

Lemma a_cong_trans_iota : forall (M N : term),
  M {{iota}} Eq N -> M Eq N.
Proof.
  induction M as [ | | x M]; simpl; intros N HEq;
    inversion HEq; clear HEq; subst; auto.

  Case "M = Lam x M using a_cong_eq".
  destruct (x == choice (old x M iota)) as [Hxfresh | ].

  SCase "x = fresh x M iota".
  rewrite <- Hxfresh in *.
  apply al_lam_eq; auto. apply IHM. rewrite iota_ext in *; auto.

  SCase "x <> fresh x M iota".
  apply al_lam_notin; auto.
  apply notin_rm_2 with (b := x); auto using fresh_iota.

  Case "M = Lam x M using al_lam_notin".
  remember (choice (old x M iota)) as z. 
  destruct (x == z) as [Hxfresh | ].

  SCase "x = z".
  rewrite fv_coll_subst in *.
  subst x. apply al_lam_notin.

  SSCase "binder case".
  rewrite iota_ext in *.
  rewrite <- fv_coll_iota in *; auto.

  SSCase "body case".
  rewrite C3_3' in *; auto; apply notin_rm_1.

  SCase "x <> z".
  destruct (x == y) as [Hxy | ].
  SSCase "x == y".
  subst y. apply al_lam_eq; auto.
  apply IHM. rewrite C3_3' in *.

  SSSCase "condition 1".
  rewrite iota_ext in *; auto.

  SSSCase "condition 2".
  subst z; apply fresh_iota.

  SSCase "x <> y".
  apply al_lam_notin.
  
  SSSCase "binder case".
  rewrite fv_coll_subst in *.
  apply (@fv_coll_iota_up _ x y z); auto.

  SSSCase "body case".
  rewrite C3_3' in *; auto.
  subst z; apply fresh_iota.
Qed.

Lemma a_cong_trans : forall (M N P : term),
  M Eq N -> 
  N Eq P -> 
  M Eq P.
Proof.
  intros M N P EqMN; generalize dependent P.
  induction EqMN; inversion 1; auto; subst P.

  Case "al_lam_eq & al_lam_eq".
  apply al_lam_eq; auto; congruence.

  Case "al_lam_eq & al_lam_notin".
  apply al_lam_notin.
  SCase "variable condition".
  rewrite (L3_1_iii EqMN); auto.
  SCase "body condition".
  subst x. rewrite (T3_5 EqMN); auto.

  Case "al_lam_notin & al_lam_eq".
  subst y0. apply al_lam_notin; auto.

  Case "al_lam_notin and al_lam_notin".
  subst. destruct (x == y0); [subst y0 | idtac].

  SCase "x = y0".
  apply al_lam_eq; auto. apply a_cong_trans_iota.
  rewrite (@L3_1_v _ iota (iota [[Var x => x]])).
  rewrite <- (C3_3 _ _ _ y); auto.
  rewrite (T3_5 EqMN); auto.
  rewrite iota_ext. unfold f_ext; firstorder.

  SCase "x <> y0".
  apply al_lam_notin.
  rewrite <- (L3_1_iii EqMN) in *. rewrite fv_coll_subst in H3.
  apply (@fv_coll_iota_up _ x y0 y); auto.
  rewrite <- (C3_3 _ _ x y); auto. rewrite (T3_5 EqMN); assumption.
Qed.

Corollary C3_6_i : forall (M N : term),
  M Eq N <-> M {{iota}} = N {{iota}}.
Proof.
  split; intros.

  Case "->".
  apply T3_5; auto.

  Case "<-".
  intros; apply a_cong_trans with (N := M {{iota}}).

  SCase "M Eq M {{iota}}".
  apply a_cong_sym; apply L3_1_vi.

  SCase "M {{iota}} Eq N".
  rewrite H; apply L3_1_vi.
Qed.

Corollary C3_6_ii : forall (rho eta : substitution)(L : list var),
  subst_cong rho eta L <->
  f_ext (comp iota rho) (comp iota eta) L.
Proof.
  unfold subst_cong, f_ext, comp; split; intros; apply C3_6_i; auto.
Qed.

(** The following corollary is already proved during the proof
   of [a_cong_symmetry]. *)

Corollary C3_7 : forall (M N : term)(x y : var),
  alpha_cond M x N y -> alpha_cond N y M x.
Proof.
  unfold alpha_cond; intros M N x y Hcond.
  destruct Hcond as [H | H].

  Case "x = y /\ M Eq N".
  left; split; firstorder using a_cong_sym.

  Case "y # FV M /\ M {{iota [[Var y => x]]}} Eq N".
  right; destruct H; split.

  SCase "binder case".
  cut (x # FV (M {{iota [[Var y => x]]}})).
  rewrite (L3_1_iii H0); auto. rewrite fv_coll_subst.
  destruct (x == y).

  SSCase "x = y"; subst.
  rewrite iota_ext. rewrite <- fv_coll_iota; auto.

  SSCase "x <> y".
  apply fv_coll_notin_2; auto.

  SCase "body case".
  rewrite <- (T3_5 H0 (iota [[Var x => y]])).
  rewrite (C3_3); auto. rewrite iota_ext. apply L3_1_vi.
Qed.

(** Substitution and alpha-congruence are compatible. *)

Corollary C3_8 : forall (M N : term)(rho eta : substitution),
  M Eq N -> 
  subst_cong rho eta (FV M) ->
  M {{rho}} Eq N {{eta}}.
Proof.
  intros; apply a_cong_trans with (N:= (M {{rho}}) {{iota}}).

  Case "M {{rho}} Eq (M {{rho}}) {{iota}}".
  auto using a_cong_sym, L3_1_vi.

  Case "(M {{rho}}) {{iota}} Eq N {{eta}}".
  rewrite T3_2.
  rewrite L3_1_v with (eta := comp iota eta);
    [ | apply C3_6_ii]; auto.
  rewrite T3_5 with (N := N); auto. rewrite <- T3_2. apply L3_1_vi.
Qed.

Corollary C3_9 : forall (M N : term)(x y : var)(rho : substitution),
  y # old x M rho ->
  (M {{rho [[Var y => x]]}}) {{iota [[N => y]]}} Eq M {{rho [[N => x]]}}.
Proof.
  intros M N x y rho Hnotin.
  rewrite T3_2. apply C3_8; auto using a_cong_refl.
  unfold subst_cong, comp; intros x0 H.
  destruct (x == x0).

  Case "x = x0".
  subst; repeat (rewrite_up; simpl); apply a_cong_refl.

  Case "x <> x0".
  repeat (rewrite_up; simpl).
  rewrite (@L3_1_v (rho x0) _ iota); auto using L3_1_vi.
  unfold f_ext; intros.
  cut (y <> x1); intro Hneq; auto using up_old; try congruence.
  subst; elim Hnotin.
  apply L3_1_ii'; exists x0; firstorder.
Qed.

(** Lemma 3.10 is trivial in our case because it is the definition
   itself:
   [[
   Corollary 3.10. If M Eq N, then one of the following conditions hold:

     (i) M and N are equal variables;

    (ii) M and N are applications M1 M2 and N1 N2 respectively, and
         Mi Eq Ni, for i = 1, 2.

   (iii) M and N are abstractions Lam x M' and Lam y N' respectively,
         and M'(x) Eq N'(y).
   ]]
   *)

(** Up to alpha-congruence, any element not from [old x M rho]
   may be chosen as the bound variable of [(Lam x M) rho].

   In particular, we have
   [[
   Lam x M Eq (Lam x M) iota
           Eq Lam y (M {{iota [[Var y => x]]}})
   ]]
   for all [y] not from [old x M rho]. *)

Lemma fv_coll_neq : forall (L : list var)(x y : var)(rho : substitution),
  y # fv_coll (L \ {x}) rho ->
  forall z, 
    y <> z ->
    y # fv_coll L (rho [[Var z => x]]).
Proof.
  induction L as [ | v L']; simpl; intros; auto. case_dec. 

  Case "x == v".
  rewrite_up; simpl; red; intro Hor; elim Hor; auto.
  apply IHL'; auto.

  Case "x <> v".
  rewrite_up; auto; simpl in H.
  repeat destr_app; split; auto.
Qed.  

Corollary C3_11 : forall (M : term)(x y : var)(rho : substitution),
  y # old x M rho ->
  (Lam x M) {{rho}} Eq Lam y (M {{rho [[Var y => x]]}}).
Proof.
  intros; simpl; destruct (y == choice (old x M rho)) as [Heq | Hneq].
  
  Case "y = choice (old x M rho)".
  rewrite <- Heq. apply a_cong_refl.

  Case "y <> choice (old x M rho)".
  apply al_lam_notin.

  SCase "binder case".
  rewrite fv_coll_subst. apply fv_coll_neq; auto.

  SCase "body case".
  apply a_cong_trans with (N := M {{rho [[Var y =>x]]}});
    auto using C3_9, choice_fresh, a_cong_refl.
Qed.

(************************************************************)
(** ** 4. Substitution and denotational semantics *)
(************************************************************)

(** This section consists of a proof of the "substitution lemma"
   of denotational semantics. The denotational semantics is based
   on cpo's.

   - E, a cpo of _expression values_, is a nontrivial solution
     to the isomorphism equation E ~ E -> E,
   - and [In : (E -> E) -> E] and [Out : E -> (E -> E)] are
     continuous functions such that
     - [compose Out In = id_{E -> E}] and
     - [compose In Out = id_E]. *)

(** Here we just assume that such a cpo [E] with two continuous
   functions [In] and [Out] are given. *)

Parameter E : Type.

Parameter In : (E -> E) -> E.
Parameter Out : E -> (E -> E).

Axiom OutIn : forall (f : E -> E), Out (In f) = f.
Axiom InOut : forall (x : E), In (Out x) = x.

(** [U] is the cpo of environments [var -> E], ordered componentwise. *)

Notation U := (var -> E).

(************************************************************)
(** *** Definition of a denotational semantics *)
(************************************************************)

Fixpoint DS (M : term) : U -> E :=
  match M with
    | Var x     => fun tau => tau x
    | App M1 M2 => fun tau => (Out (DS M1 tau)) (DS M2 tau)
    | Lam x M'  => fun tau => In (fun e => DS M' (tau [[e => x]]))
  end.

(** Composition of an environment [tau] and a substitution [rho] *)

Definition e_comp (tau : U) (rho : substitution) : U :=
  fun x => DS (rho x) tau.

Lemma L4_1 : forall (M : term)(tau1 tau2 : U),
  f_ext tau1 tau2 (FV M) ->
  DS M tau1 = DS M tau2.
Proof.
  unfold f_ext; induction M as [ | | x M]; simpl; intros; auto.

  Case "M = App M1 M2".
  f_equal; eauto with datatypes.

  Case "M = Lam x M".
  f_equal. extensionality e. apply IHM.
  intros x0 Hin; unfold up; case_dec; eauto with datatypes.
Qed.

(** Semantic Substitution Theorem: semantic analogue of [T3_2] *)

Theorem T4_2 : forall (M : term)(rho : substitution)(tau : U),
  DS (M {{rho}}) tau = DS M (e_comp tau rho).
Proof.  
  induction M as [ | | x M]; simpl; intros; f_equal; auto.

  Case "M = Lam x M".
  remember (choice (old x M rho)) as y.
  extensionality e. rewrite IHM. apply L4_1.
  unfold f_ext, e_comp, up; intros z Hz; case_dec.

  SCase "z = x".
  simpl; case_dec; intuition.

  SCase "z <> x".
  apply L4_1; unfold f_ext; intros w Hw.
  cut (w <> y); intros;
    [case_dec; intuition
      | apply (@fv_coll_notin_1 (FV M) x z w y rho); auto; 
        unfold old in *; subst y; auto using choice_fresh].
Qed.

Corollary C4_3 : forall (M N : term)(x : var)(tau : U), 
  DS (M {{iota [[N => x]] }}) tau = DS M (tau [[DS N tau => x]]).
Proof.
  intros; rewrite T4_2. apply L4_1.
  unfold f_ext, e_comp, up; intros; case_dec; auto.
Qed.

Corollary C4_4_i : forall (tau : U),
  e_comp tau iota = tau.
Proof.
  unfold e_comp; simpl; intros.
  extensionality x; auto.
Qed.

Corollary C4_4_ii : forall (tau : U)(rho1 rho2 : substitution),
  e_comp tau (comp rho2 rho1) = e_comp (e_comp tau rho2) rho1.
Proof.
  unfold e_comp, comp; intros.
  extensionality x. rewrite T4_2; reflexivity.
Qed.

Corollary C4_5 : forall (M N : term),
  M Eq N ->
  DS M = DS N.
Proof.
  intros; extensionality tau.
  pattern tau; rewrite <- C4_4_i.
  repeat rewrite <- T4_2; f_equal; apply (C3_6_i); auto.
Qed.
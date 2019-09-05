Require Import List FunctionalExtensionality.

From PT Require Import Common PT.

Inductive Partial : Type -> Type :=
| AbortE : Partial void.

Definition abort {A}: Free Partial A :=
  Vis AbortE (fun (v : void) => match v with end).

(** Division *)

Inductive Expr :=
| Val : nat -> Expr
| Div : Expr -> Expr -> Expr.

Inductive step_rel : Expr -> nat -> Prop :=
| Base : forall n, step_rel (Val n) n
| Step : forall l r v1 v2,
    step_rel l v1 ->
    step_rel r (S v2) ->
    step_rel (Div l r) (Nat.div v1 (S v2)).

Definition PartialF := Free Partial.

Definition partial_div (n1 n2 : nat) : PartialF nat :=
  match n2 with
  | O => abort
  | S n => ret (Nat.div n1 (S n))
  end.

Fixpoint interp (e : Expr) : PartialF nat :=
  match e with
  | Val n => ret n
  | Div e1 e2 => bind (interp e1)
                     (fun v1 => bind (interp e2)
                                  (fun v2 => partial_div v1 v2))
  end.

Section WP_Partial.

  Variables X : Type.
  Variable F : Type -> Type.

  Definition mustPT
             (P : X -> F X -> Prop)
             (x: X) (p : PartialF (F X)) : Prop :=
    match p with
    | Ret a => P x a
    | Vis e _ => match e with
                | AbortE => False
                end
    end.

  Definition PF X := PartialF (F X).
  
  Definition wpPartial
             (f : X -> PartialF (F X))
             (P : X -> F X -> Prop) : X -> Prop.
    unfold PartialF in f.
    assert (Free Partial (F X) = PF X).
    { reflexivity. }
    rewrite H in f.
    exact (wp f (mustPT P)).
  Defined.

End WP_Partial.

Arguments wpPartial {_} {_}.
Hint Unfold wpPartial.

Hint Unfold mustPT.

Definition toNat (x : Type) : Type := nat.

Fixpoint safeDiv (e : Expr) : Prop :=
  match e with
  | Val n => True
  | Div e1 e2 =>
    ~step_rel e2 O /\ safeDiv e1 /\ safeDiv e2
  end.

Ltac autounfold_with_tac tac  :=
  repeat (autounfold; tac).

Ltac comp_analysis e1 e2 :=
  let He1 := fresh "He1" in
  let He2 := fresh "He2" in
  destruct (interp e1) eqn:He1;
  destruct (interp e2) eqn:He2; simpl;
  repeat match goal with
         | [p : Partial _ |- _] =>
           destruct p
         end; auto.

Ltac partial_div_analysis :=
  match goal with
  | |- context[partial_div ?n ?n'] =>
    destruct n'; simpl;
    try contradiction; try constructor; try auto
  end.

Lemma wpPartial_div : forall e1 e2,
    @wpPartial _ toNat interp step_rel e1 ->
    @wpPartial _ toNat interp step_rel e2 ->
    ~ step_rel e2 0 ->
    @wpPartial _ toNat interp step_rel (Div e1 e2).
Proof.
  intros e1 e2.
  autounfold_with_tac simpl.
  comp_analysis e1 e2.
  partial_div_analysis.
Qed.

Lemma correct : safeDiv ⊆ @wpPartial _ toNat interp step_rel.
Proof.
  intros e. induction e.
  - cbv. constructor.
  - inversion 1. destruct H1.
    apply IHe1 in H1. apply IHe2 in H2.
    apply wpPartial_div; auto.
Qed.

Definition dom {X F} (f : X -> PartialF (F X)) : X -> Prop :=
  wpPartial f (fun _ _ => True).

Hint Unfold dom.

Lemma sound : @dom _ toNat interp ⊆ @wpPartial _ toNat interp step_rel.
Proof.
  intros e. induction e.
  - cbv. constructor.
  - revert IHe1 IHe2.
    autounfold_with_tac simpl.
    comp_analysis e1 e2.
    partial_div_analysis.
Qed.

Lemma complete : @wpPartial _ toNat interp step_rel ⊆ @dom _ toNat interp.
Proof.
  intros e. induction e.
  - cbv. constructor.
  - autounfold_with_tac simpl.
    comp_analysis e1 e2.
    partial_div_analysis.
Qed.

Hint Unfold subset.
Hint Unfold refinement.

Lemma refinement_spec_partial {A B} : forall (f g : A -> PartialF B),
    (wpPartial f ⊑ wpPartial g) <-> (forall x, (f x = g x) \/ (f x = abort)).
Proof.
  intros f g. split.
  - autounfold_with_tac simpl. intros.
    specialize (H (fun x a => f x = Ret a \/ f x = abort) x).
    simpl in H. 
    remember (f x) as fx.
    remember (g x) as gx.
    destruct fx.
    + left. intuition. destruct gx.
      * intuition. inversion H0.
      * destruct p. contradiction.
    + right. destruct p. unfold abort.
      f_equal. (* Can I do this without extensionality? *)
      extensionality a. destruct a.
  - autounfold_with_tac simpl. intros.
    specialize (H x). destruct H.
    + rewrite <- H. assumption.
    + rewrite H in H0. simpl in H0. destruct H0.
Qed.

Print Assumptions refinement_spec_partial.

(** Add *)

Record Spec (A : Type) (B : A -> Type) : Type :=
  MkSpec { pre : A -> Prop;
           post (x : A) : B x -> Prop}.

Arguments MkSpec {_} {_}.

Notation "[ P , Q ]" := (MkSpec P Q) (at level 42).

Definition K { A B } (a : A) (b : B) := a.

Definition SpecK A B := @Spec A (K B).

Inductive Add : list nat -> list nat -> Prop :=
| AddStep : forall x1 x2 xs, Add (x1 :: x2 :: xs) (x1 + x2 :: xs).

Definition addSpec : SpecK (list nat) (list nat) :=
  [fun xs => length xs > 1, Add].

Definition wpSpec {A B} (spec: @Spec A B) (P : forall (X: A), B X -> Prop) (x : A) : Prop :=
  match spec with
  | MkSpec pre post => (pre x) /\ (post x ⊆ P x)
  end.

Definition pop {A} (l : list A) : PartialF (A * list A) :=
  match l with
  | nil => abort
  | x :: xs => ret (x, xs)
  end.

Definition add (l : list nat) : PartialF (list nat) :=
  bind (pop l)
       (fun '(a, b) =>
          bind (pop b)
               (fun '(c, d) =>
                  ret (a + c :: d))).

Definition toListNat (_ : list nat) := list nat.

Lemma correctness : @wpSpec (list nat) (fun _ => list nat) addSpec
                            ⊑ @wpPartial _ (fun _ => list nat) add.
Proof.
  intros P l. autounfold_with_tac simpl.
  intros [H1 H2]. destruct l.
  - simpl. inversion H1.
  - unfold add. simpl. destruct l.
    + inversion H1. inversion H0.
    + simpl. apply H2. constructor.
Qed.

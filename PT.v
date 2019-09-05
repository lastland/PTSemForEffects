Require Import RelationClasses.

(* The free monad we use here is more similar to that of
   [https://github.com/DeepSpec/InteractionTrees], but not
   coinductive. *)
Inductive Free E A :=
| Ret: A -> Free E A
| Vis: forall X, E X -> (X -> Free E A) -> Free E A.

Arguments Ret {_} {_}.
Arguments Vis {_} {_} {_}.

Set Implicit Arguments.

Section Free.

  Variables A B : Type.

  Variable E : Type -> Type.

  Fixpoint map (f : A -> B) (a : Free E A) : Free E B :=
    match a with
    | Ret x => Ret (f x)
    | Vis e h => Vis e (fun x => map f (h x))
    end.

  Definition ret : A -> Free E A := Ret.

  Fixpoint bind (m : Free E A) (f : A -> Free E B) : Free E B :=
    match m with
    | Ret x => f x
    | Vis e h => Vis e (fun x => bind (h x) f)
    end.

End Free.

Arguments ret {_} {_}.

Section WP.

  Variables A B X : Type.
  Variable F : Type -> Type.

  Definition wp (f: X -> F X) (P : X -> F X -> Prop) (x : X) : Prop :=
    P x (f x).

  Definition subset (P : A -> Prop) (Q : A -> Prop) : Prop :=
    forall x, P x -> Q x.

End WP.

Arguments wp {_} {_}.
Hint Unfold wp.

Notation "P ⊆ Q" := (subset P Q) (at level 42).
Hint Unfold subset.

Section Refinement.

  Variable X : Type.
  Variable F : Type -> Type.

  Definition refinement (pt1 pt2 : (X -> F X -> Prop) -> X -> Prop) : Prop :=
    forall P, pt1 P ⊆ pt2 P.

  Instance refinment_trans {X : Type} {F : Type -> Type} : Transitive refinement.
  Proof.
    intros pa pb pc. unfold refinement, subset. auto.
  Defined.

  Instance refinement_refl : Reflexive refinement.
  Proof.
    intros pt. unfold refinement, subset. auto.
  Defined.
  
End Refinement.

Arguments refinement {_} {_}.
Hint Unfold refinement.

Notation "pt1 ⊑ pt2" := (refinement pt1 pt2) (at level 42).

Lemma leibniz : forall {A} (x y : A),
    (forall (P : A -> Prop), P x -> P y) -> x = y.
Proof.
  intros. specialize (H (fun a => x = a)). simpl in H. auto.
Qed.

Lemma refinement_spec : forall A B (f g : A -> B),
    (wp f ⊑ wp g) <-> (forall x, f x = g x).
Proof.
  intros. split.
  - autounfold.
    intros. apply leibniz. intros.
    specialize (H (fun _ => P)). simpl in H. auto.
  - intros. repeat autounfold. intros.
    rewrite <- H. assumption.
Qed.

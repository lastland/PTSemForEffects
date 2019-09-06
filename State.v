From PT Require Import Common PT.

Set Implicit Arguments.

Section State.

  Variable S A : Type.

  Inductive State : Type -> Type :=
  | GetE : State S
  | PutE : S -> State unit.

  Definition StateF := Free State.

  Definition get : StateF S :=
    Vis GetE ret.

  Definition put (s : S) : StateF unit :=
    Vis (PutE s) ret.

  Fixpoint run (m : StateF A) (s : S) : A * S := 
    match m with
    | Ret a => (a, s)
    | Vis e k => match e in (State T) return ((T -> StateF A) -> A * S) with
                | GetE => fun k => run (k s) s
                | PutE s' => fun k => run (k tt) s'
                end k
    end.

  Fixpoint statePT (P : A * S -> Prop) (f : StateF A) (s : S) : Prop :=
    match f with
    | Ret a => P (a, s)
    | Vis e k => match e in (State T) return ((T -> StateF A) -> Prop) with
                | GetE => fun k => statePT P (k s) s
                | PutE s' => fun k => statePT P (k tt) s'
                end k
    end.

  Definition statePT' (P : S -> A * S -> Prop) (f : StateF A) (s : S) : Prop :=
    statePT (P s) f s.
  
End State.

Hint Unfold statePT.
Hint Unfold statePT'.

Arguments StateF {_}.

Definition wpState {S A B} (f : A -> @StateF S B)
           (P : A * S -> B * S -> Prop) (t : A * S) : Prop :=
  match t with
  | (a, s) => wp f (fun x y => statePT' (fun s' => P (x, s')) y s) a
  end.

Hint Unfold wpState.

Lemma soundness {S A B} : forall (P : A * S -> B * S -> Prop) (f : A -> StateF B),
    forall a s, wpState f P (a, s) -> P (a, s) (run (f a) s).
Proof.
  intros P f a s. autounfold.
  assert (forall s1 s2, statePT (P (a, s1)) (f a) s2 ->
                   P (a, s1) (run (f a) s2)).
  { induction (f a); simpl; auto.
    destruct e; intros; auto. }
  apply H.
Qed.

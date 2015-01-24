Require Import List.

Fixpoint nth {A} (l:list A) (i:nat) : option A :=
  match l with
    | nil => None
    | x :: xs => match i with
                   | 0 => Some x
                   | S j => nth xs j
                 end
  end.

Lemma nth_map A B (r : A) l i (f : A -> B) : nth l i = Some r -> nth (map f l) i = Some (f r).
Proof.
  intros.
  generalize dependent i.
  generalize dependent r.
  induction l; intros; simpl. inversion H.

  destruct i. inversion H. reflexivity. auto.
Qed.

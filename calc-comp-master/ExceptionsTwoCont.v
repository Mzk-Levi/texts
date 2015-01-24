(** Calculation for arithmetic + exceptions with two continuations. *)

Require Import List.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (e: Expr) : option nat :=
  match e with
    | Val n => Some n
    | Add x y => match eval x with
                   | Some n => match eval y with
                                 | Some m => Some (n + m)
                                 | None => None
                               end
                   | None => None
                 end
    | Throw => None
    | Catch x y => match eval x with
                     | Some n => Some n
                     | None => eval y
                   end
  end.

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| POP : Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (s : Code) (f : Code) : Code :=
  match e with
    | Val n =>  PUSH n s
    | Add x y => comp' x (comp' y (ADD s) (POP f)) f 
    | Throw => f
    | Catch x h => comp' x s (comp' h s f)
  end.

Definition comp (e : Expr) : Code := comp' e HALT HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Conf.

Notation "⟨ x , y ⟩" := (conf x y).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c k : ⟨PUSH n c, k⟩ ==> ⟨ c , VAL n :: k ⟩
| vm_add c k m n : ⟨ADD c, VAL m :: VAL n :: k⟩ ==> ⟨c, VAL (n + m) :: k⟩
| vm_pop c n k : ⟨POP c, VAL n :: k⟩ ==> ⟨c, k⟩
where "x ==> y" := (VM x y).

Hint Constructors VM.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec e s f k : ⟨comp' e s f, k⟩
                       =>> match eval e with
                            | Some n => ⟨s , VAL n :: k⟩
                            | None => ⟨f , k⟩
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent s.
  generalize dependent f.
  generalize dependent k.
  induction e;intros.

(** Calculation of the compiler *)

(** - [e = Val n]: *)

  begin
  ⟨s, VAL n :: k⟩.
  <== { apply vm_push }
  ⟨PUSH n s, k⟩.
  [].

(** - [e = Add e1 e2]: *)
  
  begin
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ s, VAL (m + n) :: k ⟩
                  | None => ⟨ f, k ⟩
                  end
     | None => ⟨ f, k ⟩
     end).
  <<= { apply vm_add }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD s, VAL n :: VAL m :: k ⟩
                  | None => ⟨ f, k ⟩
                  end
     | None => ⟨ f, k ⟩
     end).
  <<= { apply vm_pop }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD s, VAL n :: VAL m :: k ⟩
                  | None => ⟨ POP f, VAL m :: k ⟩
                  end
     | None => ⟨ f, k ⟩
     end).
  <<= { apply IHe2 }
   (match eval e1 with
     | Some m =>  ⟨ (comp' e2 (ADD s) (POP f)), VAL m :: k⟩
     | None => ⟨ f, k ⟩
     end).
  <<= { apply IHe1 }
      ⟨ comp' e1 (comp' e2 (ADD s) (POP f)) f, k ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟨ f, k⟩.
  [].

(** - [e = Catch e1 e2]: *)

  begin
    (match eval e1 with
         | Some m => ⟨ s, VAL m :: k⟩
         | None => match eval e2 with
                     | Some n => ⟨s, VAL n :: k⟩
                     | None => ⟨f, k⟩
                   end
    end).
   <<= { apply IHe2 }
    (match eval e1 with
         | Some m => ⟨ s, VAL m :: k⟩
         | None => ⟨comp' e2 s f, k⟩
    end).
   <<= { apply IHe1 }
       ⟨ comp' e1 s (comp' e2 s f) , k⟩.
   [].
Qed.

(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.
  
Lemma term_vm x :  ~ (exists C, match x with
                             | Some n => ⟨HALT , VAL n :: nil⟩
                             | None =>  ⟨HALT , nil⟩
                           end  ==> C).
Proof.
  destruct x; intro Contra; destruct Contra; subst; inversion H.
Qed.



Theorem sound e C : ⟨comp e, nil⟩ =>>! C -> C = match eval e with
                                                  | Some n => ⟨HALT , VAL n :: nil⟩
                                                  | None =>  ⟨HALT , nil⟩
                                                end.
Proof.
  intros.
  pose (spec e HALT HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.
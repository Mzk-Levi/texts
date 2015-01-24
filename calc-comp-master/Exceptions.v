(** Calculation for arithmetic + exceptions. *)

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
| FAIL : Code
| UNMARK : Code -> Code
| MARK : Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Throw => FAIL
    | Catch x h => MARK (comp' h c) (comp' x (UNMARK c))
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| HAN : Code -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Conf
| fail : Stack -> Conf.

Notation "⟨ x , y ⟩" := (conf x y).
Notation "⟪ x ⟫" := (fail x ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s : ⟨PUSH n c, s⟩ ==> ⟨ c , VAL n :: s ⟩
| vm_add c s m n : ⟨ADD c, VAL m :: VAL n :: s⟩ ==> ⟨c, VAL (n + m) :: s⟩
| vm_fail_val n s : ⟪VAL n :: s ⟫ ==> ⟪s⟫
| vm_fail s : ⟨ FAIL, s⟩ ==> ⟪s⟫
| vm_fail_han c s : ⟪HAN c :: s ⟫ ==> ⟨c, s⟩
| vm_unmark c n h s : ⟨UNMARK c, VAL n :: HAN h :: s⟩ ==> ⟨c, VAL n :: s⟩
| vm_mark c h s : ⟨MARK h c, s⟩ ==> ⟨c, HAN h :: s⟩
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

Theorem spec e c s : ⟨comp' e c, s⟩
                       =>> match eval e with
                            | Some n => ⟨c , VAL n :: s⟩
                            | None => ⟪ s ⟫
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction e;intros.

(** Calculation of the compiler *)

(** - [e = Val n]: *)

  begin
  ⟨c, VAL n :: s⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s⟩.
  [].

(** - [e = Add e1 e2]: *)

  begin
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ c, VAL (m + n) :: s ⟩
                  | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_add }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD c, VAL n :: VAL m :: s ⟩
                  | None => ⟪ s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply vm_fail_val }
   (match eval e1 with
     | Some m => match eval e2 with
                  | Some n => ⟨ ADD c, VAL n :: VAL m :: s ⟩
                  | None => ⟪ VAL m :: s ⟫
                  end
     | None => ⟪ s ⟫
     end).
  <<= { apply IHe2 }
   (match eval e1 with
     | Some m =>  ⟨ comp' e2 (ADD c), VAL m :: s ⟩
     | None => ⟪ s ⟫
     end).
  <<= { apply IHe1 }
      ⟨ comp' e1 (comp' e2 (ADD c)), s ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟪s⟫.
  <== { apply vm_fail }
    ⟨ FAIL, s⟩.
  [].

(** - [e = Catch e1 e2]: *)

  begin
    (match eval e1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => match eval e2 with
                     | Some n => ⟨c, VAL n :: s⟩
                     | None => ⟪s⟫
                   end
    end).
   <<= { apply IHe2 }
    (match eval e1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => ⟨comp' e2 c, s⟩
    end).
   <<= { apply vm_fail_han }
    (match eval e1 with
         | Some m => ⟨ c, VAL m :: s⟩
         | None => ⟪ HAN (comp' e2 c) :: s⟫
    end).
   <<= { apply vm_unmark }
    (match eval e1 with
         | Some m => ⟨ UNMARK c, VAL m :: HAN (comp' e2 c) :: s⟩
         | None => ⟪ HAN (comp' e2 c) :: s⟫
    end).
   <<= { apply IHe1 }
       ⟨ comp' e1 (UNMARK c), HAN (comp' e2 c) :: s⟩.
   <<= { apply vm_mark }
       ⟨ MARK (comp' e2 c) (comp' e1 (UNMARK c)),  s⟩.
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
                             | None =>  ⟪nil⟫ 
                           end  ==> C).
Proof.
  destruct x; intro Contra; destruct Contra; subst; inversion H.
Qed.

Theorem sound e C : ⟨comp e, nil⟩ =>>! C -> C = match eval e with
                                                  | Some n => ⟨HALT , VAL n :: nil⟩
                                                  | None =>  ⟪nil⟫ 
                                                end.
Proof.
  intros.
  pose (spec e HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.
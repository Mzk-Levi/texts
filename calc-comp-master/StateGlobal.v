(** Calculation for arithmetic + exceptions + global state. *)

Require Import List.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr
| Get : Expr
| Put : Expr -> Expr -> Expr.

(** * Semantics *)

Definition State := nat.

Fixpoint eval (e: Expr) (s : State) : (option nat * State) :=
  match e with
    | Val n => (Some n , s)
    | Add x y => match eval x s with
                   | (Some n, s') => match eval y s' with
                                       | (Some m, s'') => (Some (n + m), s'')
                                       | (None, s'') => (None, s'')
                               end
                   | (None, s') => (None, s')
                 end
    | Throw => (None, s)
    | Catch x y => match eval x s with
                     | (Some n, s') => (Some n, s')
                     | (None, s') => eval y s'
                   end
    | Get => (Some s,s)
    | Put x y => match eval x s with
                     | (Some n, s') => eval y n
                     | (None, s') => (None, s')
                   end
  end.

(** * Compiler *)

Inductive Code : Set :=
| HALT : Code
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| FAIL : Code 
| MARK : Code -> Code -> Code
| UNMARK : Code -> Code
| LOAD : Code -> Code
| SAVE : Code -> Code
.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Throw => FAIL
    | Catch x h => MARK (comp' h c) (comp' x (UNMARK c))
    | Get => LOAD c
    | Put x y => comp' x (SAVE (comp' y c))
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| HAN : Code -> Elem 
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> State -> Conf
| fail : Stack -> State -> Conf.

Notation "⟨ c , k , s ⟩" := (conf c k s).
Notation "⟪ k , s ⟫" := (fail k s ).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c k s : ⟨PUSH n c, k, s⟩ ==> ⟨ c , VAL n :: k, s ⟩
| vm_add c k s m n : ⟨ADD c, VAL m :: VAL n :: k, s⟩ ==> ⟨c, VAL (n + m) :: k, s⟩
| vm_fail k s : ⟨ FAIL, k, s⟩ ==> ⟪k,s⟫
| vm_mark c h k s : ⟨MARK h c, k, s⟩ ==> ⟨c, HAN h :: k, s⟩
| vm_unmark c n h k s : ⟨UNMARK c, VAL n :: HAN h :: k, s⟩ ==> ⟨c, VAL n :: k, s⟩
| vm_load c k s : ⟨LOAD c, k, s⟩ ==> ⟨c, VAL s :: k, s⟩
| vm_save c n k s : ⟨SAVE c, VAL n :: k, s⟩ ==> ⟨c, k, n⟩
| vm_fail_val n k s : ⟪VAL n :: k, s ⟫ ==> ⟪k, s⟫
| vm_fail_han c k s : ⟪HAN c :: k, s ⟫ ==> ⟨c, k, s⟩
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

Theorem spec e c k s : ⟨comp' e c, k, s⟩
                       =>> match eval e s with
                            | (Some n, s') => ⟨c , VAL n :: k, s'⟩
                            | (None, s') => ⟪ k, s' ⟫
                           end.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent k.
  generalize dependent s.
  induction e;intros.

(** Calculation of the compiler *)

(** - [e = Val n]: *)

  begin
  ⟨c, VAL n :: k, s⟩.
  <== { apply vm_push }
  ⟨PUSH n c, k, s⟩.
  [].

(** - [e = Add e1 e2]: *)
  
  begin
   (match eval e1 s with
     | (Some m, s') => match eval e2 s' with
                         | (Some n, s'') => ⟨ c, VAL (m + n) :: k, s'' ⟩
                         | (None, s'') => ⟪ k, s'' ⟫
                  end
     | (None, s') => ⟪ k, s' ⟫
     end).
  <<= { apply vm_add }
   (match eval e1 s with
     | (Some m, s') => match eval e2 s' with
                         | (Some n, s'') => ⟨ ADD c, VAL n :: VAL m :: k, s'' ⟩
                         | (None, s'') => ⟪ k, s'' ⟫
                  end
     | (None, s') => ⟪ k, s' ⟫
     end).
  <<= { apply vm_fail_val }
   (match eval e1 s with
     | (Some m, s') => match eval e2 s' with
                         | (Some n, s'') => ⟨ ADD c, VAL n :: VAL m :: k, s'' ⟩
                         | (None, s'') => ⟪ VAL m :: k, s'' ⟫
                  end
     | (None, s') => ⟪ k, s' ⟫
     end).
  <<= { apply IHe2 }
   (match eval e1 s with
     | (Some m, s') =>  ⟨ comp' e2 (ADD c), VAL m :: k, s' ⟩
     | (None, s') => ⟪ k, s' ⟫
     end).
  <<= { apply IHe1 }
      ⟨ comp' e1 (comp' e2 (ADD c)), k, s ⟩.
  [].

(** - [e = Throw]: *)

  begin
    ⟪k, s⟫.
  <== { apply vm_fail }
    ⟨ FAIL, k, s⟩.
  [].

(** - [e = Catch e1 e2]: *)

  begin
    (match eval e1 s with
         | (Some m, s') => ⟨ c, VAL m :: k, s'⟩
         | (None, s') => match eval e2 s' with
                           | (Some n, s'') => ⟨c, VAL n :: k, s''⟩
                           | (None, s'') => ⟪k, s''⟫
                         end
    end).
   <<= { apply IHe2 }
    (match eval e1 s with
         | (Some m, s') => ⟨ c, VAL m :: k, s'⟩
         | (None, s') => ⟨comp' e2 c, k, s'⟩
    end).
   <<= { apply vm_fail_han }
    (match eval e1 s with
         | (Some m, s') => ⟨ c, VAL m :: k, s'⟩
         | (None, s') => ⟪ HAN (comp' e2 c) :: k, s'⟫
    end).
   <<= { apply vm_unmark }
    (match eval e1 s with
         | (Some m, s') => ⟨ UNMARK c, VAL m :: HAN (comp' e2 c) :: k, s'⟩
         | (None, s') => ⟪ HAN (comp' e2 c) :: k, s'⟫
    end).
   <<= { apply IHe1 }
       ⟨ comp' e1 (UNMARK c), HAN (comp' e2 c) :: k, s⟩.
   <<= { apply vm_mark }
       ⟨ MARK (comp' e2 c) (comp' e1 (UNMARK c)),  k, s⟩.
   [].

(** - [e = Get]: *)

   begin
     ⟨ c, VAL s :: k, s⟩.
   <== { apply vm_load }
     ⟨ LOAD c, k, s⟩.
   [].

(** - [e = Put e1 e2]: *)

   begin
     (match eval e1 s with
          | (Some n, s') => match eval e2 n with
                                | (Some m, s'') => ⟨c, VAL m :: k, s''⟩
                                | (None, s'') => ⟪k, s''⟫
                            end
          | (None, s') => ⟪k, s'⟫
      end).
   <<= { apply IHe2 }
       (match eval e1 s with
          | (Some n, s') => ⟨comp' e2 c, k, n⟩
          | (None, s') => ⟪k, s'⟫
        end).
   <<= { apply vm_save }
       (match eval e1 s with
          | (Some n, s') => ⟨SAVE (comp' e2 c), VAL n :: k, s'⟩
          | (None, s') => ⟪k, s'⟫
        end).
   <<= { apply IHe1 }
       ⟨comp' e1 (SAVE (comp' e2 c)), k, s⟩.
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
                             | (Some n, s) => ⟨HALT , VAL n :: nil, s⟩
                             | (None, s) =>  ⟪nil, s⟫ 
                           end  ==> C).
Proof.
  destruct x; destruct o; intro Contra; destruct Contra; subst; inversion H.
Qed.

Theorem sound e C s : ⟨comp e, nil, s⟩ =>>! C -> C = match eval e s with
                                                  | (Some n, s') => ⟨HALT , VAL n :: nil, s'⟩
                                                  | (None, s') =>  ⟪nil, s'⟫ 
                                                end.
Proof.
  intros.
  pose (spec e HALT nil) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply term_vm.
Qed.
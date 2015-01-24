(** Calculation of a compiler for the call-by-value lambda calculus +
arithmetic. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is given as follows (as in the
paper):
<<
type Env = [Value]
data Value =  Num Int | Fun (Value -> Value)


eval ::  Expr -> Env -> Value
eval (Val n) e   = Num n
eval (Add x y) e = case eval x e of
                     Num n -> case eval y e of
                                Num m -> Num (n+m)
eval (Var i) e   = e !! i
eval (Abs x) e   = Fun (\v -> eval x (v:e))
eval (App x y) e = case eval x e of
                     Fun f -> f (eval y e)
>>
After defunctionalisation and translation into relational form we
obtain the semantics below. *)

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> list Value -> Value.

Definition Env := list Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Value -> Prop :=
| eval_val e n : Val n ⇓[e] Num n
| eval_add e x y m n : x ⇓[e] Num m -> y ⇓[e] Num n -> Add x y ⇓[e] Num (m + n)
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' x'' y y' : x ⇓[e] Clo x' e' -> y ⇓[e] y' -> x' ⇓[y' :: e'] x'' -> App x y ⇓[e] x''
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : Code -> Code
| ABS : Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Var i => LOOKUP i c
    | App x y => comp' x (comp' y (APP c))
    | Abs x => ABS (comp' x RET) c
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> list Value' -> Value'.

Definition Env' := list Value'.

Inductive Elem : Set :=
| VAL : Value' -> Elem 
| CLO : Code -> Env' -> Elem
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Env' -> Conf.

Notation "⟨ x , y , e ⟩" := (conf x y e).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s e :  ⟨PUSH n c, s, e⟩ ==> ⟨c, VAL (Num' n) :: s, e⟩
| vm_add c m n s e : ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e⟩ 
                       ==> ⟨c, VAL (Num'(m + n)) :: s, e⟩
| vm_lookup e i c v s : nth e i = Some v -> ⟨LOOKUP i c, s, e ⟩ ==> ⟨c, VAL v :: s, e ⟩
| vm_env v c e e' s  : ⟨RET, VAL v :: CLO c e :: s, e'⟩ ==> ⟨c, VAL v :: s, e⟩
| vm_app c c' e e' v s : ⟨APP c, VAL v :: VAL (Clo' c' e') :: s, e⟩
              ==> ⟨c', CLO c e :: s, v :: e'⟩
| vm_abs c c' s e : ⟨ABS c' c, s, e ⟩ ==> ⟨c, VAL (Clo' c' e) :: s, e ⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (comp' x RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec p e r c s : p ⇓[e] r -> ⟨comp' p c, s, convE e⟩ 
                                 =>> ⟨c , VAL (conv r) :: s, convE e⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, VAL (Num' n) :: s, convE e⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, convE e⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
    ⟨c, VAL (Num' (m + n)) :: s, convE e ⟩.
  <== { apply vm_add }
    ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, convE e⟩. 
  <<= { apply IHeval2 }
  ⟨comp' y (ADD c), VAL (Num' m) :: s, convE e⟩.
  <<= { apply IHeval1 }
  ⟨comp' x (comp' y (ADD c)), s, convE e⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, VAL (conv v) :: s, convE e ⟩.
  <== {apply vm_lookup; unfold convE; erewrite nth_map; eauto}
    ⟨LOOKUP i c, s, convE e ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, VAL (Clo' (comp' x RET) (convE e)) :: s, convE e ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x RET) c, s, convE e ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    ⟨c, VAL (conv x'') :: s, convE e ⟩.
  <== { apply vm_env }
    ⟨RET, VAL (conv x'') :: CLO c (convE e) :: s, convE (y' :: e') ⟩.
  <<= { apply IHeval3 }
    ⟨comp' x' RET, CLO c (convE e) :: s, convE (y' :: e') ⟩.
  = {reflexivity}
    ⟨comp' x' RET, CLO c (convE e) :: s, conv y' :: convE e' ⟩.
  <== { apply vm_app }
    ⟨APP c, VAL (conv y') :: VAL (Clo' (comp' x' RET) (convE e')) :: s, convE e ⟩.
  <<= { apply IHeval2 }
    ⟨comp' y (APP c), VAL (Clo' (comp' x' RET) (convE e')) :: s, convE e ⟩.
  = {reflexivity}
    ⟨comp' y (APP c), VAL (conv (Clo x' e')) :: s, convE e ⟩.
  <<= { apply IHeval1 }
    ⟨comp' x (comp' y (APP c)), s, convE e ⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; try reflexivity.
  rewrite H in H5. inversion H5. reflexivity.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p s C : terminates p -> ⟨comp p, s, nil⟩ =>>! C -> 
                          exists r, C = ⟨HALT , VAL (conv r) :: s, nil⟩ /\ p ⇓[nil] r.
Proof.
  unfold terminates. intros. destruct H as [r T].
  
  pose (spec p nil r HALT s) as H'. exists r. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. auto. intro. destruct H. 
  inversion H. assumption.
Qed.
  
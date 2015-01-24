(** Calculation of a compiler for an imperative language with
unbounded loops. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Get : Expr.

Inductive Stmt : Set :=
| Put : Expr -> Stmt
| Seqn : Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt.

(** * Semantics *)

Definition State := nat.
Reserved Notation "x ⇓[ s ] y" (at level 80, no associativity).

Inductive eval : Expr -> State -> nat -> Prop :=
| eval_val s n : Val n ⇓[s] n
| eval_add s x y m n : x ⇓[s] m -> y ⇓[s] n -> Add x y ⇓[s] (m + n)
| eval_get s : Get ⇓[s] s
where "x ⇓[ s ] y" := (eval x s y).

Reserved Notation "x ↓[ s ] s'" (at level 80, no associativity).

Inductive run : Stmt -> State -> State -> Prop :=
| run_put e s v : e ⇓[s] v -> Put e ↓[s] v
| run_seqn e1 e2 s1 s2 s3 : e1 ↓[s1] s2 -> e2 ↓[s2] s3 -> Seqn e1 e2 ↓[s1] s3
| run_while_exit e1 e2 s : e1 ⇓[s] 0 -> While e1 e2 ↓[s] s
| run_while_cont v e1 e2 s1 s2 s3 : e1 ⇓[s1] v -> v > 0 -> e2 ↓[s1] s2 -> While e1 e2 ↓[s2] s3 
                   -> While e1 e2 ↓[s1] s3
where "x ↓[ s ] y" := (run x s y).

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| GET : Code -> Code
| PUT : Code -> Code
| LOOP : Code
| JMP : Code -> Code -> Code
| ENTER : Code -> Code
| HALT : Code.

Fixpoint compE (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => compE x (compE y (ADD c))
    | Get => GET c
  end.

Fixpoint compS (e : Stmt) (c : Code) : Code :=
  match e with
    | Put e => compE e (PUT c)
    | Seqn e1 e2 => compS e1 (compS e2 c)
    | While e1 e2 => ENTER (compE e1 (JMP c (compS e2 LOOP)))
  end.

Definition comp (e : Stmt) : Code := compS e HALT.

(** * Virtual Machine *)

Inductive Elem : Set :=
| VAL : nat -> Elem 
| CON : Code -> Elem
.

Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> State -> Conf.

Notation "⟨ c , k , s ⟩" := (conf c k s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s k :  ⟨PUSH n c, k, s⟩ ==> ⟨c, VAL n :: k, s⟩ 
| vm_add c m n s k : ⟨ADD c, VAL n :: VAL m :: k, s⟩ 
                        ==> ⟨c, VAL (m + n) :: k, s⟩
| vm_get c s k : ⟨GET c, k, s⟩ ==> ⟨c, VAL s :: k, s⟩
| vm_put c v k s : ⟨PUT c, VAL v :: k, s⟩ ==> ⟨c, k, v⟩
| vm_loop c k s : ⟨LOOP, CON c :: k, s⟩ ==> ⟨c, k, s⟩
| vm_jmp_yes v c c' k s : v > 0 -> ⟨JMP c' c, VAL v :: k, s⟩ ==> ⟨c, k, s⟩
| vm_jmp_no  c c' c'' k s : ⟨JMP c' c, VAL 0 :: CON c'' :: k, s⟩ ==> ⟨c', k, s⟩
| vm_enter c k s : ⟨ENTER c, k, s⟩ ==> ⟨c, CON (ENTER c) :: k, s⟩
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler for expressions *)
Theorem specExpr e s v k c : e ⇓[s] v -> ⟨compE e c, k, s⟩ 
                                 =>> ⟨c , VAL v :: k, s⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent k.
  induction H;intros.

(** Calculation of the compiler for expressions *)

(** - [Val n ⇓[s] n]: *)

  begin
  ⟨c, VAL n :: k, s⟩.
  <== { apply vm_push }
  ⟨PUSH n c, k, s⟩.
  [].

(** - [Add x y ⇓[s] (m + n)]: *)

  begin
    ⟨c, VAL (m + n) :: k, s ⟩.
  <== { apply vm_add }
    ⟨ADD c, VAL n :: VAL m :: k, s⟩. 
  <<= { apply IHeval2 }
  ⟨compE y (ADD c), VAL m :: k, s⟩.
  <<= { apply IHeval1 }
  ⟨compE x (compE y (ADD c)), k, s⟩.
  [].

(** - [Get ⇓[s] s]: *)

  begin
    ⟨c, VAL s :: k, s⟩.
  <== {apply vm_get}
    ⟨GET c, k, s ⟩.
   [].
Qed.
  
(** Specification of the compiler for statements *)
Theorem specStmt e s s' k c : e ↓[s] s' -> ⟨compS e c, k, s⟩ 
                                 =>> ⟨c , k, s'⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent k.
  induction H;intros.

(** Calculation of the compiler for expressions *)

(** - [Put e ↓[s] v]: *)

  begin
    ⟨c, k, v⟩.
  <== {apply vm_put}
    ⟨PUT c, VAL v :: k, s⟩.
  <<= {apply specExpr}
    ⟨compE e (PUT c), k, s⟩.
  [].

(** - [Seqn e1 e2 ↓[s1] s3]: *)
  
  begin
    ⟨c, k, s3⟩.
  <<= {apply IHrun2}
    ⟨compS e2 c, k, s2⟩.
  <<= {apply IHrun1}
    ⟨compS e1 (compS e2 c), k, s1⟩.
  [].

(** - [While e1 e2 ↓[s] s] ([run_while_exit]): *)

  begin
    ⟨c, k, s⟩.
  <== {apply vm_jmp_no}
    ⟨JMP c (compS e2 LOOP), VAL 0 :: CON (compS (While e1 e2) c) :: k, s⟩.
  <<= {apply specExpr}
    ⟨compE e1 (JMP c (compS e2 LOOP)), CON (compS (While e1 e2) c) :: k, s ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE e1 (JMP c (compS e2 LOOP))), k, s ⟩.
  [].

(** - [While e1 e2 ↓[s1] s3] ([run_while_cont]): *)

  begin
    ⟨c, k, s3⟩.
  <<= {apply IHrun2}
    ⟨compS (While e1 e2) c, k, s2 ⟩.
  <== {apply vm_loop}
    ⟨LOOP, CON (compS (While e1 e2) c) :: k, s2 ⟩.
  <<= {apply IHrun1}
    ⟨compS e2 LOOP, CON (compS (While e1 e2) c) :: k, s1 ⟩.
  <== {apply vm_jmp_yes}
    ⟨JMP c (compS e2 LOOP), VAL v :: CON (compS (While e1 e2) c) :: k, s1 ⟩.
  <<= {apply specExpr}
    ⟨compE e1 (JMP c (compS e2 LOOP)), CON (compS (While e1 e2) c) :: k, s1 ⟩.
  <== {apply vm_enter}
    ⟨ENTER (compE e1 (JMP c (compS e2 LOOP))), k, s1 ⟩.
  [].

Qed.
  
(** * Soundness *)
  
Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; try reflexivity.
  inversion H. inversion H5.
Qed.
  

Definition terminates (e : Stmt) : Prop := exists s, e ↓[0] s.

Theorem sound e C : terminates e -> ⟨comp e, nil, 0⟩ =>>! C -> 
                          exists s, C = ⟨HALT, nil, s⟩ /\ e ↓[0] s.
Proof.
  unfold terminates. intros. destruct H as [s T].
  
  pose (specStmt e 0 s nil HALT) as H'. exists s. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. auto. intro. destruct H. 
  inversion H. assumption.
Qed.
  
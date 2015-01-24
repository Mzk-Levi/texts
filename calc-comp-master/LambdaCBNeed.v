(** Calculation of a compiler for the call-by-need lambda calculus +
arithmetic. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Heap.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is taken from Ager et al. "A
functional correspondence between call-by-need evaluators and lazy
abstract machines". We use Haskell syntax to define the
evaluator. Moreover, we use an abstract interface to a heap
implementation:
<<
type Heap a
type Loc

empty :: Heap a
deref :: Heap a -> Loc -> a
update :: Heap a -> Loc -> a -> Heap a
alloc :: Heap a -> a -> (Heap a, Loc)
>>
Moreover, we assume that `Heap` forms a functor with an associated function
<<
hmap :: (a -> b) -> Heap a -> Heap b
>>
which in addition to functoriality also satisfies the following laws:
<<
hmap f empty = empty                                             (hmap-empty)
deref (hmap f h) l = f (deref h l)                               (hmap-deref)
hmap f (update h l e) = update (hmap f h) l (f e)                (hmap-update)
alloc (hmap f h) (f e) = (h', l) <=> alloc h e = (hmap f h', l)  (hmap-alloc)
>>

The evaluator itself is defined as follows:
<<
type Env   = [Loc]
data HElem = Thunk (Heap HElem -> (Value, Heap HElem)) | Value Value
data Value = Num Int | Clo (Loc -> Heap HElem -> (Value, Heap HElem))
	

eval :: Expr -> Env -> Heap HElem -> (Value, Heap HElem)
eval (Val n)   e h = (Num n, h)
eval (Add x y) e h = case eval x e h of
                       (Num n, h') -> case eval y e h' of
                                        (Num m, h'') -> (Num (n + m), h'')
eval (Var i)   e h = case deref h (e !! i) of
                       Thunk t -> let (v, h') = t h
                                  in (v, update h' (e !! i) (Value v))
                       Value v -> (v, h)
eval (Abs x)   e h = (Clo (\ l h' -> eval x (l : e) h') , h)
eval (App x y) e h = case eval x e h of
                       (Clo , h') -> let (h'',l) = alloc h' (Thunk (\h -> eval y e h))
                                     in f l h''
>>
After defunctionalisation and translation into relational form we
obtain the semantics below.  *)

Definition Env : Set := list Loc.

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> Env -> Value.

Inductive HElem : Set  :=
  | thunk : Expr -> Env -> HElem
  | value : Value -> HElem.


Definition Heap := Heap.Heap HElem.

Reserved Notation "x ⇓[ e , h , h' ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Heap -> Heap -> Value -> Prop :=
| eval_val e n (h h' : Heap) : Val n ⇓[e,h,h] Num n
| eval_add e x y m n h h' h'' : x ⇓[e,h,h'] Num m -> y ⇓[e,h',h''] Num n -> Add x y ⇓[e,h,h''] Num (m + n)
| eval_var_thunk e e' x i l v h h' : nth e i = Some l -> deref h l = Some (thunk x e') -> x ⇓[e',h,h'] v -> 
                          Var i ⇓[e,h,update h' l (value v)] v
| eval_var_val e i l v h : nth e i = Some l -> deref h l = Some (value v) -> 
                          Var i ⇓[e,h,h] v
| eval_abs e x h : Abs x ⇓[e,h,h] Clo x e
| eval_app e e' x x' x'' y l h h' h'' h''' : x ⇓[e,h,h'] Clo x' e' -> alloc h' (thunk y e) = (h'',l) ->
                              x' ⇓[l :: e',h'',h'''] x'' -> App x y ⇓[e,h,h'''] x''
where "x ⇓[ e , h , h' ] y" := (eval x e h h' y).

(** * Compiler *)

Inductive Code : Set :=
| PUSH : nat -> Code -> Code
| ADD : Code -> Code
| WRITE : Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : Code -> Code -> Code
| ABS : Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => PUSH n c
    | Add x y => comp' x (comp' y (ADD c))
    | Var i => LOOKUP i c
    | App x y => comp' x (APP (comp' y WRITE) c)
    | Abs x => ABS (comp' x RET) c
  end.

Definition comp (e : Expr) : Code := comp' e HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> Env -> Value'.

Inductive HElem' : Set  :=
  | thunk' : Code -> Env -> HElem'
  | value' : Value' -> HElem'.

Definition Heap' := Heap.Heap HElem'.

Inductive Elem : Set :=
| VAL : Value' -> Elem 
| THU : Loc -> Code -> Env -> Elem
| FUN : Code -> Env -> Elem
.
Definition Stack : Set := list Elem.

Inductive Conf : Set := 
| conf : Code -> Stack -> Env -> Heap' -> Conf.

Notation "⟨ x , y , e , h ⟩" := (conf x y e h).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_push n c s e h :  ⟨PUSH n c, s, e, h⟩ ==> ⟨c, VAL (Num' n) :: s, e, h⟩
| vm_add c m n s e h : ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e, h⟩
                       ==> ⟨c, VAL (Num'(m + n)) :: s, e, h⟩
| vm_write e e' l v c s h : ⟨WRITE, VAL v :: THU l c e :: s, e', h⟩ ==> ⟨c, VAL v :: s,e,update h l (value' v)⟩
| vm_lookup_thunk e e' i c c' h l s : nth e i = Some l -> deref h l = Some (thunk' c' e') ->
                               ⟨LOOKUP i c, s, e, h⟩ ==> ⟨c', THU l c e :: s, e', h⟩
| vm_lookup_value e i c h l v s : nth e i = Some l -> deref h l = Some (value' v) ->
                               ⟨LOOKUP i c, s, e, h⟩ ==> ⟨c, VAL v :: s, e, h⟩
| vm_ret v c e e' h s  : ⟨RET, VAL v :: FUN c e :: s, e', h⟩ ==> ⟨c, VAL v :: s, e, h⟩
| vm_app c c' c'' e e' s h h' l : alloc h (thunk' c' e) = (h',l) -> 
                           ⟨APP c' c, VAL (Clo' c'' e') :: s, e, h⟩
                            ==> ⟨c'', FUN c e :: s, l :: e', h'⟩
| vm_abs c c' s e h : ⟨ABS c' c, s, e, h⟩ ==> ⟨c, VAL (Clo' c' e) :: s, e, h⟩ 
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint convV (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (comp' x RET) e
  end.

Fixpoint convHE (t : HElem) : HElem' :=
  match t with
    | value v => value' (convV v)
    | thunk x e => thunk' (comp' x WRITE) e
  end.

Definition convH : Heap -> Heap' := hmap convHE.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec p e r c s h h' : p ⇓[e,h,h'] r -> ⟨comp' p c, s, e, convH h⟩ 
                                 =>> ⟨c , VAL (convV r) :: s, e, convH h'⟩.

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  induction H;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e,h,h] Num n]: *)

  begin
  ⟨c, VAL (Num' n) :: s, e, convH h⟩.
  <== { apply vm_push }
  ⟨PUSH n c, s, e, convH h⟩.
  [].

(** - [Add x y ⇓[e,h,h''] Num (m + n)]: *)

  begin
    ⟨c, VAL (Num' (m + n)) :: s, e, convH h'' ⟩.
  <== { apply vm_add }
    ⟨ADD c, VAL (Num' n) :: VAL (Num' m) :: s, e, convH h''⟩. 
  <<= { apply IHeval2 }
  ⟨comp' y (ADD c), VAL (Num' m) :: s, e, convH h'⟩.
  <<= { apply IHeval1 }
  ⟨comp' x (comp' y (ADD c)), s, e, convH h⟩.
  [].

(** - [Var i ⇓[e,h,update h' l (value v)] v] *)

  assert (deref (convH h) l = Some (thunk' (comp' x WRITE) e'))
    by (unfold convH; rewrite hmap_deref; rewrite H0; reflexivity).
  begin
    ⟨c, VAL (convV v) :: s, e, convH (update h' l (value v)) ⟩.
  = {unfold convH; rewrite <- hmap_update}
    ⟨c, VAL (convV v) :: s, e, update (convH h') l (value' (convV v)) ⟩.
  <== {apply vm_write}
    ⟨WRITE, VAL (convV v) :: THU l c e :: s, e', convH h'⟩.
  <<= {apply IHeval}
    ⟨comp' x WRITE, THU l c e :: s, e', convH h⟩.
  <== {eapply vm_lookup_thunk}
    ⟨LOOKUP i c, s, e, convH h ⟩.
  [].

(** - [Var i ⇓[e,h,h] v] *)

  assert (deref (convH h) l = Some (value' (convV v)))
    by (unfold convH; rewrite hmap_deref; rewrite H0; reflexivity).
  begin
    ⟨c, VAL (convV v) :: s, e, convH h ⟩.
  <== {eapply vm_lookup_value }
    ⟨LOOKUP i c, s, e, convH h ⟩.
  [].

(** - [Abs x ⇓[e,h,h] Clo x e] *)

  begin
    ⟨c, VAL (Clo' (comp' x RET) e) :: s, e, convH h ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x RET) c, s, e, convH h ⟩.
  [].
  
(** - [App x y ⇓[e,h,h'''] x''] *)
  
  assert (alloc (convH h') (convHE (thunk y e)) = (convH h'', l)).
  unfold convH. eapply hmap_alloc in H0. apply H0.
  
  begin
    ⟨c, VAL (convV x'') :: s, e, convH h''' ⟩.
  <== { apply vm_ret }
    ⟨RET, VAL (convV x'') :: FUN c e :: s, l :: e', convH h''' ⟩.
  <<= { apply IHeval2 }
    ⟨comp' x' RET, FUN c e :: s, l :: e', convH h'' ⟩.
  <== {apply vm_app}
    ⟨APP (comp' y WRITE) c, VAL (Clo' (comp' x' RET) e') :: s, e, convH h'⟩.
   = {reflexivity}
    ⟨APP (comp' y WRITE) c, VAL (convV (Clo x' e')) :: s, e, convH h'⟩.
  <<= { apply IHeval1 }
    ⟨comp' x (APP (comp' y WRITE) c), s, e, convH h⟩.
  [].
Qed.
    
(** * Soundness *)


(** Custom tactic to apply inversion *)
Ltac inv := match goal with
              | [H1 : nth ?e ?i = Some ?l1,
                 H2 : nth ?e ?i = Some ?l2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : deref ?h ?l = Some ?v1,
                 H2 : deref ?h ?l = Some ?v2 |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | [H1 : alloc ?h ?l = _,
                 H2 : alloc ?h ?l = _ |- _] => rewrite H1 in H2; inversion H2; subst; clear H1 H2
              | _ => idtac
            end.

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; repeat inv; try reflexivity.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r h, p ⇓[nil,empty,h] r.

Theorem sound p s C : terminates p -> ⟨comp p, s, nil, empty⟩ =>>! C -> 
                          exists r h, C = ⟨HALT , VAL (convV r) :: s, nil, convH h⟩ 
                                    /\ p ⇓[nil, empty, h] r.
Proof.
  unfold terminates. intros. destruct H as [r T]. destruct T as [h T].
  
  pose (spec p nil r HALT s) as H'. exists r. exists h. split. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. eassumption. split. pose (H' empty h) as H. unfold convH in H. 
  rewrite hmap_empty in H. apply H. assumption. intro Con. destruct Con. 
  inversion H. assumption.
Qed.

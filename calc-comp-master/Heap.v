Parameter Heap : Set -> Set.
Parameter Loc : Set.

Parameter empty : forall {A}, Heap A.
Parameter deref : forall {A}, Heap A -> Loc -> option A.
Parameter update : forall {A}, Heap A -> Loc -> A -> Heap A.
Parameter alloc : forall {A}, Heap A -> A -> (Heap A * Loc).

Parameter hmap: forall {A B : Set}, (A -> B) -> Heap A -> Heap B.

Axiom hmap_empty : forall {A B : Set} {f : A -> B}, hmap f empty = empty.
Axiom hmap_deref : forall {A B : Set} {f : A -> B} h l, deref (hmap f h) l = option_map f (deref h l).
Axiom hmap_update : forall {A B : Set} {f : A -> B} h l e, update (hmap f h) l (f e) = hmap f (update h l e).
Axiom hmap_alloc : forall {A B : Set} {f : A -> B} {h : Heap A} {h' : Heap A} l e, 
                     alloc (hmap f h) (f e) = (hmap f h', l)
                     <-> alloc h e = (h', l).
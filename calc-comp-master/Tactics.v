Definition Admit {A} : A. admit. Defined.

Module Type Preorder.

Parameter Conf : Type.
Parameter VM : Conf -> Conf -> Prop.

End Preorder.

Module Calculation (Ord : Preorder).
Import Ord.

Notation "x ==> y" := (VM x y) (at level 80, no associativity).

Reserved Notation "x =>> y" (at level 80, no associativity).
Inductive trc : Conf -> Conf -> Prop :=
| trc_refl c : c =>> c
| trc_step_trans c1 c2 c3 : c1 ==> c2 -> c2 =>> c3 -> c1 =>> c3
 where "x =>> y" := (trc x y).


Lemma trc_step c1 c2 : c1 ==> c2 -> c1 =>> c2.
Proof.
  intros.
  eapply trc_step_trans. eassumption. apply trc_refl.
Qed.

Lemma trc_trans c1 c2 c3 : c1 =>> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof.
  intros T S.
  induction T. assumption. eapply trc_step_trans. eassumption. apply IHT.  assumption. 
Qed.


Corollary trc_step_trans' c1 c2 c3 : c1 =>> c2 -> c2 ==> c3 -> c1 =>> c3.
Proof.
  intros. eapply trc_trans. eassumption. apply trc_step. assumption.
Qed.

Corollary trc_eq_trans c1 c2 c3 : c1 =>> c2 -> c2 = c3 -> c1 =>> c3.
Proof.
  intros. eapply trc_trans. eassumption. subst. apply trc_refl. 
Qed.

Ltac dist t := idtac; simpl; try solve [t;eauto|apply trc_step;t;eauto|apply trc_refl;t;eauto] ; match goal with
                        | [ |- context [let _ := ?x in _] ] => destruct x;dist t
                        | [ |- context [match ?x with 
                                          | _ => _ 
                                        end]] => destruct x; dist t
                      end.

Ltac dist_refl := dist reflexivity.


Ltac check_exp' x y t := let h := fresh "check" in assert (h: x = y) by t; try rewrite <- h; clear h.
Ltac check_exp x y := let h := fresh "check" in assert (h: x = y) by reflexivity; clear h.

Ltac check_rel R Rel := first [check_exp R Rel|
                             fail 2 "wrong goal; expected relation" R "but found" Rel].



Tactic Notation "[]" := apply trc_refl.




Ltac step rel lem t1 e2 :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel trc Rel;
        first [let h := fresh "rewriting" in 
               assert(h : rel e2 rhs) by (dist t1) ; apply (fun x => lem _ _ _ x h); clear h | fail 2]
    | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<<=" "{"tactic(t) "}" constr(e) := 
  step trc trc_trans t e.

Tactic Notation  (at level 2)    "=" "{"tactic(t) "}" constr(e) := 
  step (@eq Conf) trc_eq_trans t e.

Tactic Notation  (at level 2)    "<==" "{"tactic(t) "}" constr(e) := 
  step VM trc_step_trans' t e.

Ltac step_try rel e2 :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel trc Rel; 
                            first [let h := fresh "step_try" in assert(h : rel e2 rhs)|fail 2]
    | _ => fail 1 "goal is not a VM"
  end.

Tactic Notation  (at level 2)    "<<=" "{?}" constr(e) := step_try trc e.
Tactic Notation  (at level 2)    "<==" "{?}" constr(e) := step_try VM e.
Tactic Notation  (at level 2)    "=" "{?}" constr(e) := step_try (@eq Conf) e.

Tactic Notation  (at level 2)    "<==" "{"tactic(t1) "}?"  := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel trc Rel;
        first [eapply trc_trans; [idtac|solve[t1]] | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)  "begin" constr(rhs) :=  match goal with
    | [|- ?Rel ?lhs ?rhs'] => check_rel trc Rel; check_exp' rhs rhs' dist_refl
      | _ => fail 1 "rhs does not match"
    end.


Inductive barred (P : Conf -> Prop) : Conf -> Prop :=
| barred_here c : P c -> barred P c
| barred_next c : (forall c', c ==> c' -> barred P c') -> barred P c.

Lemma barred_if c (P Q : Conf -> Prop) : (forall c, P c -> Q c) -> barred P c -> barred Q c.
Proof.
  intros. induction H0. apply barred_here. auto.
  apply barred_next. assumption.
Qed.

Lemma barred_step (P : Conf -> Prop) c :(forall c', c ==> c' -> P c') -> barred P c.
Proof.
  intros. apply barred_next. intros. apply barred_here. auto.
Qed.

Definition determ {A} (R : A -> A -> Prop) : Prop := forall C C1 C2, R C C1 -> R C C2 -> C1 = C2.


Definition trc' C C' :=  C =>> C' /\ ~ exists C'', C' ==> C''.

Notation "x =>>! y" := (trc' x y) (at level 80, no associativity).


Lemma determ_factor C1 C2 C3 : determ VM -> C1 ==> C2 -> C1 =>>! C3 -> C2 =>> C3.
Proof.
  unfold determ. intros. destruct H1.
  destruct H1. exfalso. apply H2. eexists. eassumption.

  assert (c2 = C2). eapply H. apply H1. apply H0. subst. assumption.
Qed.


Lemma determ_trc : determ VM -> determ trc'.
Proof.
  intros. unfold determ. intros. destruct H0. 
  induction H0. 

  destruct H1. destruct H0. reflexivity. exfalso. apply H2. eexists. eassumption.

  apply IHtrc. apply H2. split. eapply determ_factor; eassumption. destruct H1. assumption.
Qed.


End Calculation.
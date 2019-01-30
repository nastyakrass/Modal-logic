Require Export List.
Require Import Classical.
Export ListNotations.
Set Implicit Arguments.



Inductive var:Set:= p : nat->var.
Check (p (S(S(S O)))).
Inductive formula:Set:=
Atom : var->formula
|Top : formula
|Bottom : formula
|Not : formula->formula
|And : formula->formula->formula
|Or : formula->formula->formula
|Imp : formula->formula->formula
|BiImp : formula->formula->formula
|Box : formula->formula.


Infix  "-->"  := Imp (at level 8, right associativity).
Infix "||" := Or.
Infix "&&" := And.

Definition BiImp1 phi psi: formula:=
(phi --> psi) && (psi --> phi).
Definition Diamond phi: formula :=(Not (Box (Not phi))).

Infix "<-->" := BiImp1 (at level 8, right associativity).
(*Check (Box(Atom(p O))) --> (Box(Atom(p O))||(Atom(p(S O)))).*)
Record frame:Type:={
W : Set; (* worlds *)
R : W->W->Prop}. (*accessibility relation R \subseteq W x W *)
Record kripke: Type:={
F : frame; (* F=(W,R) *)
L : (W F)->var->Prop}.
(* labelling function L : W -> Atomomic
-> {True,False} *)
(* M,x ||- phi *)
Fixpoint satisfies (M: kripke)(x :(W (F M))) (phi:formula) :Prop:=
match phi with
| Top => True
| Bottom => False
| (Atom phi)  => (L M x phi)
| (Not phi) => ~(satisfies M x  phi)
| (And phi_1 phi_2) =>
(satisfies M x  phi_1) /\ (satisfies M x  phi_2)
|(Or phi_1 phi_2) =>
(satisfies M x  phi_1) \/ (satisfies M x  phi_2)
|(Imp phi_1 phi_2) =>
(satisfies M x  phi_1) -> (satisfies M x  phi_2)
|(BiImp phi_1 phi_2) =>
(satisfies M x  phi_1) <-> (satisfies M x  phi_2)
|(Box phi) =>
(forall y:(W (F M)),(R (F M) x y) -> (satisfies M y  phi))
end.
(* M ||- phi *)
Definition M_satisfies M phi  := forall w:(W (F M)), (satisfies M w  phi).
(* F |= phi *)
Definition valid_in_frame F phi :=
forall L, (M_satisfies (Build_kripke F L) phi).
(* |= phi *)
Definition valid phi:= forall F, (valid_in_frame F phi).
Definition Satisfies F L Γ w := forall phi, In phi  Γ -> satisfies (Build_kripke F L) w phi.
Definition Entailment F Γ L psi :=   forall w, (Satisfies F L Γ w  -> satisfies (Build_kripke F L) w psi).
(*Definition Entailment Γ F phi := forall L, (Satisfies F Γ L -> M_satisfies (Build_kripke F L) phi).*)

Definition Entailment1 Γ phi := forall F,forall L,  Entailment F Γ L phi.
Definition Entailment2 phi := Entailment1 nil phi.
(*Definition Correct F Γ := forall phi, (In phi Γ -> Entailment nil F phi).*)

(*Аксиомы рефлексивности, транзитивности и симметричности,
 которые нужны для обоснования последних трех правил вывода*)

Axiom reff:  forall (M: kripke), forall y: (W (F M)),(R (F M)  y y).


Axiom trans:  forall (M: kripke), forall x y z: (W (F M)),((R (F M)  x y /\ R (F M)  y z) -> R (F M)  x z ).

Axiom symm:  forall (M: kripke), forall x y: (W (F M)),(R (F M)  x y  -> R (F M)  y x).

(*Provability*)

Inductive label: Set :=
o: label 
|i : label.

Inductive level : Set :=
nil : level |
consn : label -> level -> level.

Definition Increase l: level := (consn i l).

(* add i in front of the list *)
Fixpoint Decrease (l:level): level:=
match l with
|nil => nil|
(consn o l') => (consn o (Decrease l'))|
(consn i l') => (consn o l')
end. 

Fixpoint Remove_o (l: level): level :=
match l with
|nil => nil |
(consn e l') => match e with
|o => (Remove_o l') |
i => (consn e l')
end
end.
(* remove all o's at the front of the list *)
Definition EqLevel (l l': level) :=(Remove_o l)=(Remove_o l').
(* two lists are equivalent if they are the same after
removing all o's at the front of the lists *)
Parameter Ass:level->formula->Prop.
Reserved Notation "Γ ⊢ A" (at level 80).

Inductive Provable:list formula -> level->formula->Prop:=
|truth : forall Γ, forall n:level,(Provable Γ n Top)
|ass : forall Γ, forall phi:formula, forall n:level,(In phi Γ)-> (Provable Γ n phi)
(*|ass_at : forall Γ, forall phi:formula, forall l m:level,
(EqLevel l m) -> ((Provable Γ l phi) -> (Provable Γ m phi))*)
|andI : forall Γ, forall phi1 psi2:formula, forall n:level,
(Provable Γ n phi1) -> (Provable Γ n psi2) ->
(Provable Γ n (And phi1 psi2))
|andE1 : forall Γ, forall phi1 phi2:formula, forall n:level,
(Provable Γ n (And phi1 phi2)) -> (Provable  Γ n phi1)
|andE2 : forall Γ, forall phi1 phi2:formula, forall n:level,
(Provable Γ n (And phi1 phi2)) -> (Provable Γ n phi2)
|orI1 : forall Γ, forall phi1 phi2:formula, forall n:level,
(Provable Γ n phi1) -> (Provable Γ n (Or phi1 phi2))
|orI2 : forall Γ, forall phi1 phi2:formula, forall n:level,
(Provable Γ n phi2) -> (Provable Γ n (Or phi1 phi2))
|orE : forall Γ, forall phi1 phi2 psi:formula, forall n:level,
(Provable Γ n (Or phi1 phi2)) ->
((Provable (phi1::Γ) n  psi) ->
((Provable (phi2::Γ) n  psi) -> (Provable Γ n psi)))
|impI : forall Γ, forall phi1 phi2:formula, forall n:level,
(Provable (phi1::Γ) n phi2) ->
(Provable Γ n (Imp phi1 phi2))
|impE : forall Γ, forall phi1 phi2:formula,forall n:level,
(Provable Γ n (Imp phi1 phi2)) ->
(Provable Γ n phi1) -> (Provable Γ n phi2)
|notI : forall Γ, forall phi:formula, forall n:level,
(Provable (phi::Γ) n Bottom) ->
(Provable Γ n (Not phi))
|notC : forall Γ, forall phi:formula, forall n:level,
(Provable ((Not phi)::Γ) n Bottom) ->
(Provable Γ n phi)
|notE : forall Γ, forall psi:formula, forall n:level,
(Provable Γ n psi) ->
((Provable Γ n (Not psi)) -> (Provable Γ n Bottom))
|botE : forall Γ, forall phi:formula, forall n:level, 
(Provable Γ n Bottom) -> (Provable Γ n phi)
|notnotE : forall Γ, forall phi:formula, forall n:level,
(Provable Γ n (Not (Not phi))) -> (Provable Γ n phi)
|boxE : forall Γ, forall phi:formula, forall n:level,
((Remove_o n)<> nil) -> (* there must be a box *)
(Provable Γ (Decrease n) (Box phi)) -> (Provable Γ n phi)
|boxI : forall Γ, forall phi:formula, forall n:level,
(Provable Γ (Increase n) phi) -> (Provable Γ n (Box phi))
|t : forall Γ, forall phi:formula, forall n:level,
(Provable Γ n (Box phi)) -> (Provable Γ n phi)
|four : forall Γ, forall phi:formula, forall n:level,
(Provable Γ n (Box phi)) -> (Provable Γ n (Box (Box phi)))
|five : forall Γ, forall phi:formula, forall n:level,
(Provable Γ n (Not phi)) ->
(Provable Γ n (Box (Not (Box  phi)))).



(*Аксиомы sat и sat1 играют техническую роль и утверждают следующее:
т.к. модальные правила вывода не добавляют в список допущений Γ новых формул
(не вводят новых допущений), то истинность допущений из Γ не зависит
 от возможных миров (этот параметр является фиктивным для допущений), и поэтому
их можно свободно "таскать" вверх-вниз по мирам.*)


Axiom sat:  forall (M: kripke), forall Γ, forall y w: (W (F M)),(Satisfies (F M) (L M) Γ w /\R (F M)  w y)->Satisfies (F M) (L M) Γ y.

Axiom sat1:  forall (M: kripke), forall Γ, forall y w: (W (F M)),(Satisfies (F M) (L M) Γ y /\R (F M)  w y)->Satisfies (F M) (L M) Γ w.

Definition Prop_Soundness :=  forall Γ, forall phi:formula, forall n:level, (Provable Γ n  phi) -> Entailment1 Γ phi.

Definition Prop_Soundness1 := forall phi:formula, forall n:level, (Provable [] n  phi) -> Entailment1 [] phi.

Ltac Truth := apply truth.
Ltac Assumed := apply ass; intuition.


Lemma conseqw : forall Γ, forall phi psi: formula, forall n: level, Provable Γ n (phi -->(psi -->phi)).
intros. apply impI. apply impI. Assumed.
Qed.

Lemma dis : forall Γ, forall phi psi: formula, forall n: level, Provable Γ n (Or phi  psi) --> (Or psi phi).
intros.
apply impI. apply orE with phi psi. apply ass. intuition. apply orI2. apply ass. intuition. apply orI1. apply ass. intuition.
Qed.

Lemma Excluded_Middle : forall Γ, forall phi: formula, forall n: level, Provable Γ n (phi || Not phi).
intros. apply notC. assert (H: Provable (Not (phi || Not phi) :: Γ) n (Not phi && Not (Not phi))). apply andI. apply notI. assert (H0: Provable (phi :: Not (phi || Not phi) :: Γ) n (phi || Not phi)). apply orI1. Assumed. assert (H1: Provable (phi :: Not (phi || Not phi) :: Γ) n (Not (phi || Not phi))). Assumed. apply notE with (phi || Not phi). exact H0.  exact H1.  apply notI. assert (H0: Provable (Not phi :: Not (phi || Not phi) :: Γ) n (phi || Not phi)). apply orI2. Assumed. assert (H1: Provable (Not phi :: Not (phi || Not phi) :: Γ) n (Not (phi || Not phi))). apply ass; intuition. apply notE with (phi || Not phi). exact H0. exact H1. apply notE with (Not phi). apply andE1 in H. exact H. apply andE2 in H. exact H.
Qed.
Lemma contr1 : forall Γ, forall phi psi: formula, forall n: level, Provable Γ n (phi -->psi) -->((Not psi) --> (Not phi)). 
intros. apply impI. apply impI.  apply notI.  assert (H: Provable (phi :: Not psi :: phi --> psi :: Γ) n phi). apply ass. intuition. assert (H0: Provable (phi :: Not psi :: phi --> psi :: Γ) n psi). apply impE with phi. apply ass; intuition. apply ass;intuition. apply notE with psi.  exact H0. apply ass; intuition.
Qed. 


Lemma mod1: forall Γ, forall phi psi: formula, forall n: level, Provable Γ n ((Box (phi && psi)) --> ((Box phi) && (Box psi))).
intros. apply impI. apply andI. apply boxI. unfold Increase. assert (H: (Provable (Box (phi && psi) :: Γ) (consn i n) (phi && psi))).  apply boxE. intuition. unfold Remove_o; discriminate. apply ass. intuition. apply andE1 in H. assumption. apply boxI. unfold Increase. assert (H: (Provable (Box (phi && psi) :: Γ) (consn i n) (phi && psi))).  apply boxE. intuition. unfold Remove_o; discriminate. apply ass. intuition. apply andE2 in H. assumption.
Qed.

Theorem Soundness : Prop_Soundness.
unfold Prop_Soundness. intros. induction H;simpl;intros.
(*True*)
unfold Entailment1. intros. unfold Entailment. intros. unfold satisfies. intuition. 

(*Assumption*)

unfold Entailment1. intros. unfold Entailment. intros.   unfold Satisfies in H0. apply H0.  exact H.

(*Conjunction1*)

unfold Entailment1.  split. unfold Entailment1 in IHProvable1.  unfold Entailment in IHProvable1.  unfold Satisfies in IHProvable1.  apply IHProvable1.  exact H1. 
unfold Entailment1 in IHProvable2.  unfold Entailment in IHProvable2.  unfold Satisfies in IHProvable2.  apply IHProvable2.  exact H1.

(*Conjunction2*)

unfold Entailment1. intros. unfold  Entailment. intros. unfold Entailment in IHProvable. unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.  generalize (IHProvable F0); intro.  generalize (H1 L0); intro.  generalize (H2 w); intro. apply H3. exact H0. 
unfold Entailment1. intros. unfold  Entailment. intros. unfold Entailment in IHProvable. unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.  generalize(IHProvable F0);intro. generalize(H1 L0);intro. generalize(H2 w);intro.  apply H3. exact H0.

(*Disjunction1*)

unfold Entailment1.  intros. unfold Entailment. intros. unfold Entailment1 in IHProvable.  unfold Entailment in IHProvable. left. generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro. apply H3. exact H0.
unfold Entailment1.  intros. unfold Entailment. intros. unfold Entailment1 in IHProvable.  unfold Entailment in IHProvable. right. generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.    apply H3. exact H0. 

(*Disjunction2*)

unfold Entailment1.  
intros. unfold Entailment. intros.  unfold Entailment1 in IHProvable1. unfold Entailment in IHProvable1. generalize (IHProvable1 F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro. elim H5. intro.
unfold Entailment1 in  IHProvable2. unfold Entailment in  IHProvable2. generalize (IHProvable2 F0); intro. generalize (H7 L0); intro. generalize (H8 w); intro.

unfold Satisfies in H9.
try simpl in H9. apply H9. intros.
elim H10.  intro. symmetry in H11. subst. exact H6.

unfold Satisfies in H2. generalize (H2 phi); intro. exact H11. 

intro. unfold Entailment1 in  IHProvable3. unfold Entailment in  IHProvable3. generalize (IHProvable3 F0); intro. generalize (H7 L0); intro. generalize (H8 w); intro.

unfold Satisfies in H9.
try simpl in H9. apply H9. intros.
elim H10.  intro. symmetry in H11. subst. exact H6.

unfold Satisfies in H2. generalize (H2 phi); intro. exact H11. exact H2.

(*Implication1*)
unfold Entailment1. intros. unfold Entailment. intros.
try simpl in |-*. intro.
unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. generalize(IHProvable F0); intro. generalize(H2 L0); intro. generalize(H3 w); intro. unfold Satisfies in H3. 
try simpl in H3. apply H3. intros.
elim H5. intro. symmetry in H6. subst. exact H1.

unfold Satisfies in H0. generalize (H0 phi). intros. apply H6.  exact H7.

(*Implication2*)

unfold Entailment1. intros. unfold Entailment. intros. 

unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in IHProvable1. unfold Entailment in IHProvable1.

try simpl in IHProvable1.

generalize (IHProvable1 F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro.
apply H4. exact H1.

unfold Entailment1 in IHProvable2. unfold Entailment in IHProvable2.

generalize (IHProvable2 F0); intro. generalize (H5 L0); intro. generalize (H6 w); intro.
apply H7. exact H1.

(*Negation1*)

unfold Entailment1. intros. unfold Entailment. intros.

try simpl in |-*. intro.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

unfold Satisfies in IHProvable.

try simpl in IHProvable.



generalize (IHProvable F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro.

apply H4.  intros. elim H5. intro. symmetry in H6. subst. exact H1.
unfold Satisfies in H0. intro.

generalize (H0 phi0). intros. apply H7. exact H6.

(*Negation2*)

assert (H0: Entailment1 Γ (Not(Not phi))).

unfold Entailment1. intros. unfold Entailment. intros.

try simpl in |-*. intro. simpl in H1.



unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

unfold Satisfies in IHProvable.

try simpl in IHProvable.



generalize (IHProvable F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro.

apply H4.  intros. elim H5. intro. symmetry in H6. subst. try simpl in |-*. exact H1.
unfold Satisfies in H0. intro.

generalize (H0 phi0). intros. apply H7. exact H6.
(*double negation*)
unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in H0. unfold Entailment in H0.

unfold Satisfies in H0.

try simpl in H0.

generalize (H0 F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro.

assert (H5:  ~ ~ satisfies {| F := F0; L := L0 |} w phi -> satisfies {| F := F0; L := L0 |} w phi).

intro. 
assert ((satisfies {| F := F0; L := L0 |} w phi)\/~ satisfies {| F := F0; L := L0 |} w phi) as H6. apply classic.
elim H6; intro.

assumption.
contradict H5.
assumption.

assert (H6: ((forall phi : formula,In phi Γ -> satisfies {| F := F0; L := L0 |} w phi) -> ~ ~ satisfies {| F := F0; L := L0 |} w phi) /\ (~ ~ satisfies {| F := F0; L := L0 |} w phi -> satisfies {| F := F0; L := L0 |} w phi) -> (forall phi : formula, In phi Γ -> satisfies {| F := F0; L := L0 |} w phi) -> satisfies {| F := F0; L := L0 |} w phi).
intros. elim H6. intros. apply H9. apply H8. exact H7. apply H6. intros. split. exact H4. exact H5.

intro.

generalize (H1 phi0). intros. apply H7. exact H8.


(*Bottom1*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*.

unfold Entailment1 in IHProvable1. unfold Entailment in IHProvable1.

unfold Entailment1 in IHProvable2. unfold Entailment in IHProvable2. try simpl in IHProvable2. 

generalize (IHProvable2 F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro.

try simpl H4. apply H4. exact H1.

generalize (IHProvable1 F0); intro. generalize (H5 L0); intro. generalize (H6 w); intro.
apply H7. exact H1.

(*Bottom2*)

unfold Entailment1. intros. unfold Entailment. intros. 

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. simpl in IHProvable.
generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.

contradict H3. exact H0.

(*DN*)

unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

unfold Satisfies in IHProvable.

try simpl in IHProvable.

generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.

assert (H4:  ~ ~ satisfies {| F := F0; L := L0 |} w phi -> satisfies {| F := F0; L := L0 |} w phi).

intro. 
assert ((satisfies {| F := F0; L := L0 |} w phi)\/~ satisfies {| F := F0; L := L0 |} w phi) as H6. apply classic.
elim H6; intro.

assumption.
contradict H4.
assumption.

assert (H5: ((forall phi : formula,In phi Γ -> satisfies {| F := F0; L := L0 |} w phi) -> ~ ~ satisfies {| F := F0; L := L0 |} w phi) /\ (~ ~ satisfies {| F := F0; L := L0 |} w phi -> satisfies {| F := F0; L := L0 |} w phi) -> (forall phi : formula, In phi Γ -> satisfies {| F := F0; L := L0 |} w phi) -> satisfies {| F := F0; L := L0 |} w phi).
intros. elim H5. intros. apply H8. apply H7. exact H6. apply H5. intros. split. exact H3. exact H4.

intro.

unfold Satisfies in H0.

generalize (H0 phi0). intros. apply H6. exact H7.

(*Box1, требуется dec1  и  sat*)

unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. try simpl in IHProvable. 
assert(H5: forall (M: kripke),  forall x: (W (F M)), (R (F M) x x)).
apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.


generalize (IHProvable F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro. 
apply H6.
exact H1.
generalize (H2 w);intro. exact H7.


(*Box2, требуется sat1*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. assert (H2: forall (M : kripke) (Γ : list formula) (y w : W (F M)),
 Satisfies (F M) (L M) Γ w /\ R (F M) w y -> Satisfies (F M) (L M) Γ y). apply sat. generalize (H2 {| F := F0; L := L0 |}). simpl. intros. generalize (H3  Γ); intros. generalize (H4 y); intros. generalize (H5 w); intros.

generalize (IHProvable F0); intro. generalize (H7 L0); intro. generalize (H8 y); intro. apply H9. apply H5 with  w. split. auto. exact H1. 

(*reflexivity*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.  
try simpl in H3.
apply H3. exact H0. assert (H5: forall (M : kripke) (y : W (F M)), R (F M) y y). apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros. generalize (H4 w). intro. exact H6. 

(*transitivity*)
unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

generalize (IHProvable F0); intro. generalize (H3 L0); intro. simpl in H4. generalize (H4 w); intro.  

apply H5. exact H0. assert (H6: forall (M: kripke), forall x y z: (W (F M)),((R (F M)  x y /\ R (F M)  y z) -> R (F M)  x z )). apply trans.
generalize (H6 {| F := F0; L := L0 |}). simpl. intros. generalize (H7 w); intro. generalize (H8 y); intro. generalize (H9 y0); intro. apply H10.  split. exact H1.   exact H2.

(*symmetry*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.
 intro.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. 

generalize (IHProvable F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro.  
simpl in H5. apply H5. exact H0.
generalize (H2 w); intro.  apply H6. assert (H7: forall (M: kripke), forall x y: (W (F M)),(R (F M)  x y  -> R (F M)  y x)).
apply symm. 

generalize (H7 {| F := F0; L := L0 |}). simpl. intros. generalize (H8 w). intro. generalize (H9 y);intro.  apply H10. exact H1.
Qed.

Theorem Soundness1 : Prop_Soundness1.
unfold Prop_Soundness1. intros. assert (H1: Prop_Soundness). apply Soundness. unfold Prop_Soundness in H1. generalize (H1 []); intro. 
 generalize (H0 phi); intro.  generalize (H2 n); intro. apply H3. exact H.
Qed.
 


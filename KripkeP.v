Require Export List.
Require Import Classical.
Export ListNotations.
Set Implicit Arguments.

Definition agent:=nat.
Inductive var:Set:=p:agent->var.
Inductive formula:Set:=
Top : formula
|Bottom : formula
|Atom : var->formula
|Not : formula->formula
|And : formula->formula->formula
|Or : formula->formula->formula
|Imp : formula->formula->formula
|BiImp : formula->formula->formula
|K : agent->formula->formula
|C : formula->formula.


Infix  "-->"  := Imp (at level 8, right associativity).
Infix "||" := Or.
Infix "&&" := And.

Definition BiImp1 phi psi: formula:=
(phi --> psi) && (psi --> phi).


Infix "<-->" := BiImp1 (at level 8, right associativity).
(*Check (Box(Atom(p O))) --> (Box(Atom(p O))||(Atom(p(S O)))).*)
Record frame:Type:={
W : Set; (* worlds *)
R: agent->(W->(W->Prop))}. (*accessibility relation R \subseteq W x W *)
Record kripke: Type:={
F : frame; (* F=(W,R) *)
L : (W F)->var->Prop}.


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
|(K i phi) =>
(forall y:(W (F M)),(R (F M) i x y) -> (satisfies M y  phi))
|(C  phi) =>
(forall y:(W (F M)), forall i: agent, (R (F M) i x y) -> (satisfies M y  phi))
end.
(*Для истинности формулы с  оператором  общего знания С нам достаточно потребовать
истинности каждого K i, т.к. на каждый K i мы можем навесить в силу
свойства универсальной модальности (см. ниже док-во теоремы pseudotrans!)
произвольное количество K j, j пробегает все индексы из множества,
нумерующего агентов,  и получить потенциально бесконечную конъюнкцию
соответствующих формул,
что для истинности оператора общего знания и требуется.
И обратно, распустив конъюнкцию, мы можем снять любой K j
в силу рефлексивности каждого R j   и таким образом добраться до начальных K i.
Поэтому данное определение истинности для С необходимо и достаточно. *)
Definition M_satisfies M phi  := forall w:(W (F M)), (satisfies M w  phi).

Definition valid_in_frame F phi :=
forall L, (M_satisfies (Build_kripke F L) phi).
(* |= phi *)
Definition valid phi:= forall F, (valid_in_frame F phi).
Definition Satisfies F L Γ w := forall phi, In phi  Γ -> satisfies (Build_kripke F L) w phi.
Definition Entailment F Γ L psi :=   forall w, (Satisfies F L Γ w  -> satisfies (Build_kripke F L) w psi).


Definition Entailment1 Γ phi := forall F,forall L,  Entailment F Γ L phi.
Definition Entailment2 phi := Entailment1 nil phi.


(*Аксиомы рефлексивности, транзитивности и симметричности,
 которые нужны для обоснования последних трех правил вывода*)

Axiom reff:  forall (M: kripke), forall i: agent, forall y: (W (F M)),(R  (F M) i y y).


Axiom trans:  forall (M: kripke), forall i: agent, forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i y z) -> R (F M) i x z ).


Axiom un:  forall (M: kripke), forall i: agent, forall x y : (W (F M)),(R (F M) i x y).
(*аксиома универсальной модальности: все отношения Ri  у нас универсальны,
 поэтому из каждой точки видно все остальные точки. Нужно для доказательства 
транзитивности С4 и корректности определения истинности для оператора С.
Ниже будет показано, что из данной аксиомы выводятся рефлексивность, симметричность и транзитивность. *)
Axiom symm:  forall (M: kripke), forall i: agent, forall x y: (W (F M)),(R (F M) i x y  -> R (F M) i y x).

Theorem reflax:  forall phi: formula, forall i: agent, valid  ((K i phi) -->  phi).
intros.
unfold valid.
unfold valid_in_frame.
unfold M_satisfies.
intros.
simpl in |-*.
intros.
generalize (H w); intro.
apply H0.
assert (H3: forall (M: kripke), forall i: agent, forall x : (W (F M)),(R (F M) i x x)).
apply reff.
generalize (H3 (Build_kripke F0 L0)).
intros.
simpl.
generalize (H1 i); intros.
generalize (H2 w); intro.
simpl in  H4.
exact H4.
Qed.



Theorem pseudotrans:  forall phi: formula, forall i j: agent, valid  ((K i phi) --> (K j (K i phi))).
intros.
unfold valid.
intros.
unfold valid_in_frame.
intros.
unfold M_satisfies.
intros.
simpl in |-*.
intros.
generalize (H y0); intro.
apply H2.
assert (H3: forall (M: kripke), forall i: agent, forall x y : (W (F M)),(R (F M) i x y)).
apply un.
generalize (H3 (Build_kripke F0 L0)).
intros.
simpl.
generalize (H4 i); intros.
generalize (H5 w); intro.
generalize (H6 y0); intro.
simpl in  H7.
exact H7.
Qed.

Theorem refl: forall (M : kripke) (i : agent), (forall x y : W (F M),R (F M) i x y) -> forall x: W (F M), R (F M) i x x.
intros.
generalize (H x); intro.
generalize (H0 x); intro.
auto.
Qed.


Theorem symmetry: forall (M : kripke) (i : agent), (forall x y : W (F M),R (F M) i x y) -> forall x y: W (F M), (R (F M) i x y -> R (F M) i y x).
intros.
generalize (H y); intro.
generalize (H1 x); intro.
auto.
Qed.

Theorem transit: forall (M : kripke) (i : agent), (forall x y : W (F M),R (F M) i x y) -> forall x y z: W (F M), ((R (F M) i x y /\ R (F M) i y z)-> R (F M) i x z).
intros.
generalize (H x); intro.
generalize (H1 z); intro.
auto.
Qed.


(*Provability*)


Inductive label : Set :=
o : label | k : agent->label | c: label.
(* k and c
are labels for the modal
connectives K and C *)
Inductive level : Set :=
nil : level |
cons : label -> level -> level.
Definition Increase (l:level) (lab: label) :level :=(cons lab l).
(* add a label in front of the list *)
Fixpoint Decrease (l:level): level:=
match l with
|nil => nil|
(cons o l') => (cons o (Decrease l'))|
(cons (k i) l') => (cons o l')|
(cons c l') => (cons o l')
end. 
(* replace the first modal
onnective label in the list with o *)
Fixpoint Remove_o (l: level): level :=
match l with
|nil => nil |
(cons e l') => match e with
|o => (Remove_o l') |
(k i) => (cons e l')|
c => (cons e l')
end
end.
(* remove all o's at the front of the list *)


Fixpoint Check_c (l:level): Prop:=
match l with
nil => False |
(cons o l') => (Check_c l') |
(cons (k i) l') => False |
(cons c l') => True
end.
Fixpoint Check_k(i:agent) (l:level): Prop:=
match l with
nil => False |
(cons o l') => (Check_k i l') |
(cons c l') => False |
(cons (k a) l') => i=a
end.
Definition EqLevel (l l': level) :=(Remove_o l)=(Remove_o l').
(* two lists are equivalent if they are the same after
removing all o's at the front of the lists *)
Parameter Ass:level->formula->Prop.
Reserved Notation "Γ ⊢ A" (at level 80).

Inductive Provable:list formula -> level->formula->Prop:=
|truth : forall Γ, forall n:level,(Provable Γ n Top)
|ass : forall Γ, forall phi:formula, forall n:level,(In phi Γ)-> (Provable Γ n phi)
|ass_at : forall Γ, forall phi:formula, forall l m:level,
(EqLevel l m) -> ((Provable Γ l phi) -> (Provable Γ m phi))
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
|KiE : forall Γ, forall phi:formula, forall i: agent, forall n:level,
((Check_k i n) -> (Provable Γ (Decrease n) (K i phi)) -> (Provable Γ n phi))
|KiI : forall Γ, forall phi:formula, forall i: agent, forall n:level,
(Provable Γ (Increase n(k i)) phi) -> (Provable Γ n (K i phi))
|CK: forall Γ, forall phi:formula, forall i: agent, forall n:level, (*данное правило утверждает, что из С мы можем получить любой K i*)
(Provable Γ n (C phi)) -> (Provable Γ n (K i phi))
|CE : forall Γ, forall phi:formula, forall i: agent, forall n:level,
((Check_c n) -> (Provable Γ (Decrease n) (C phi)) -> (Provable Γ n phi))
|CI : forall Γ, forall phi:formula, forall i: agent,forall n:level,
(Provable Γ (Increase n c) phi) -> (Provable Γ n (C phi))
|t : forall Γ, forall phi:formula, forall i: agent, forall n:level,
(Provable Γ n (K i phi)) -> (Provable Γ n phi)
|four : forall Γ, forall phi:formula, forall i: agent, forall n:level,
(Provable Γ n (K i phi)) -> (Provable Γ n (K i (K i phi)))
|five : forall Γ, forall phi:formula, forall n:level, forall i: agent,
(Provable Γ n (Not (K i phi))) ->
(Provable Γ n (K i (Not (K i  phi))))
|Cf : forall Γ, forall phi:formula, forall i: agent, forall n:level,
(Provable Γ n (C phi)) -> (Provable Γ n (C (C phi)))
|Weak : forall Γ, forall phi psi: formula, forall n: level, Provable Γ n phi -> Provable (psi :: Γ) n phi.


(*Аксиомы sat и sat1 играют техническую роль и утверждают следующее:
т.к. множества допущений у нас по условию общезначимы -- это и говорит теорема корректности -- и поэтому
их можно свободно "таскать" вверх-вниз по мирам.*)


Axiom sat:  forall (M: kripke), forall Γ, forall i: agent,  forall y w: (W (F M)),(Satisfies (F M) (L M) Γ w /\R (F M) i  w y)->Satisfies (F M) (L M) Γ y.

Axiom sat1:  forall (M: kripke), forall Γ, forall i: agent, forall y w: (W (F M)),(Satisfies (F M) (L M) Γ y /\R (F M) i w y)->Satisfies (F M) (L M) Γ w.

Definition Prop_Soundness :=  forall Γ, forall phi:formula, forall n:level, (Provable Γ n  phi) -> Entailment1 Γ phi.

Definition Prop_Soundness1 := forall phi:formula, forall n:level, (Provable [] n  phi) -> Entailment1 [] phi.

Ltac Truth := apply truth.
Ltac Assumed := apply ass; intuition.


Theorem Soundness : Prop_Soundness.
unfold Prop_Soundness. intros. induction H;simpl;intros.
(*True*)
unfold Entailment1. intros. unfold Entailment. intros. unfold satisfies. intuition. 

(*Assumption*)

unfold Entailment1. intros. unfold Entailment. intros.   unfold Satisfies in H0. apply H0.  exact H.

(*Assumption at equal levels*)
unfold Entailment1. intros. unfold Entailment1 in IHProvable. apply IHProvable. 
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
unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. generalize(IHProvable F0); intro. 
generalize(H2 L0); intro. generalize(H3 w); intro. unfold Satisfies in H3. 
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

(*Ki1*)

unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. try simpl in IHProvable. 
assert(H5: forall (M: kripke), forall i: agent, forall x: (W (F M)), (R (F M)i x x)).
apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.


generalize (IHProvable F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro. 
apply H6.
exact H1.
generalize (H2 i);intro.  generalize (H7 w); intro. exact H8.


(*Ki2, требуется sat*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. assert (H2: forall (M : kripke) (Γ : list formula)(i: agent) (y w : W (F M)),
 Satisfies (F M) (L M) Γ w /\ R (F M)i w y -> Satisfies (F M) (L M) Γ y). apply sat. generalize (H2 {| F := F0; L := L0 |}). simpl. intros. generalize (H3  Γ); intros. generalize (H4 i); intros.
generalize (H5 y); intros. generalize (H6 w); intros.

generalize (IHProvable F0); intro. generalize (H8 L0); intro. generalize (H9 y); intro. apply H10. apply H6 with  w. split. auto. exact H1.

(*CK*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. 
simpl in IHProvable.


generalize (IHProvable F0); intro. generalize (H2 L0); intro. generalize (H3 w); intro. apply H4 with i. 
exact H0. exact H1. 

(*C1*)

unfold Entailment1. intros. unfold Entailment. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. try simpl in IHProvable. 
assert(H5: forall (M: kripke), forall i: agent, forall x: (W (F M)), (R (F M)i x x)).
apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.


generalize (IHProvable F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro. 
apply H6 with i.
exact H1.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.
generalize (H7 i);intro.  generalize (H8 w); intro. exact H9.


(*C2, требуется sat*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable. assert (H2: forall (M : kripke) (Γ : list formula)(i: agent) (y w : W (F M)),
 Satisfies (F M) (L M) Γ w /\ R (F M)i w y -> Satisfies (F M) (L M) Γ y). apply sat. generalize (H2 {| F := F0; L := L0 |}). simpl. intros. generalize (H3  Γ); intros. generalize (H4 i0); intros.
generalize (H5 y); intros. generalize (H6 w); intros.

generalize (IHProvable F0); intro. generalize (H8 L0); intro. generalize (H9 y); intro. apply H10. apply H6 with  w. split. auto. exact H1.

(*reflexivity*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.  
try simpl in H3.
apply H3. exact H0. assert (H5: forall (M : kripke)(i: agent) (y : W (F M)), R (F M) i y y). apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros. generalize (H4 i). intro. generalize (H6 w). intro. exact H7. 

(*transitivity*)
unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

generalize (IHProvable F0); intro. generalize (H3 L0); intro. simpl in H4. generalize (H4 w); intro.  

apply H5. exact H0. assert (H6: forall (M: kripke), forall i: agent,forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i  y z) -> R (F M) i x z )). apply trans.
generalize (H6 {| F := F0; L := L0 |}). simpl. intros. generalize (H7 i); intro. generalize (H8 w); intro. generalize (H9 y); intro. generalize (H10 y0); intro. apply H11.  split. exact H1.   exact H2.

(*symmetry*)

unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.
 intro.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.  

generalize (IHProvable F0); intro. generalize (H3 L0); intro. generalize (H4 w); intro.  
simpl in H5. apply H5. exact H0. intros.
apply H2.

assert (H7: forall (M: kripke), forall i:agent ,forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i y z)-> R (F M) i x z)).

apply trans.

generalize (H7 {| F := F0; L := L0 |}). simpl. intros. generalize (H8 i); intro. generalize (H9 y). intro. generalize (H10 w);intro.  
generalize (H11 y0);intro.
apply H12. split.


assert (H13: forall (M: kripke), forall i:agent ,forall x y: (W (F M)),(R (F M) i x y  -> R (F M) i y x)).
apply symm.

generalize (H13 {| F := F0; L := L0 |}). simpl. intros. generalize (H14 i); intro. generalize (H15 w). intro. generalize (H16 y);intro.  apply H17. exact H1. 
exact H6.

(*transitivity for C*)
unfold Entailment1. intros. unfold Entailment. intros. try simpl in |-*. intros.

unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.

generalize (IHProvable F0); intro. generalize (H3 L0); intro. simpl in H4. generalize (H4 w); intro.  

apply H5 with i1. exact H0. assert (H6: forall (M: kripke), forall i: agent,forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i  y z) -> R (F M) i x z )). apply trans.
generalize (H6 {| F := F0; L := L0 |}). simpl. intros. generalize (H7 i1); intro.  generalize (H8 w); intro. generalize (H9 y); intro. generalize (H10 y0); intro. apply H11.  split. 
assert(H12:  forall (M: kripke), forall i: agent, forall x y : (W (F M)),(R (F M) i x y)). apply un. 
generalize (H12 {| F := F0; L := L0 |}). simpl. intros. generalize (H13 i1); intro.  generalize (H14 w); intro. generalize (H15 y); intro. exact H16.   exact H2.

(*Weak*)
unfold Entailment1. intros. unfold Entailment. try simpl in |-*. intros. unfold Satisfies  in H0.
try simpl in H0. (*apply H0. generalize (H0 phi); intro. *)


unfold Entailment1 in IHProvable. unfold Entailment in IHProvable.
generalize (IHProvable F0); intros. generalize (H1 L0); intros. generalize (H2 w); intros.
unfold Satisfies in H3. 
apply H3. intros. generalize (H0 phi0); intros. 
apply H5. right. exact H4.


Qed.



Theorem Soundness1 : Prop_Soundness1.
unfold Prop_Soundness1. intros. assert (H1: Prop_Soundness). apply Soundness. unfold Prop_Soundness in H1. generalize (H1 []); intro. 
 generalize (H0 phi); intro.  generalize (H2 n); intro. apply H3. exact H.
Qed.
 


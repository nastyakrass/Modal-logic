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

Record frame:Type:={
W : Set; (* worlds *)
R: agent->(W->(W->Prop));
RU: W->(W->Prop)}. 
Record kripke: Type:={
F : frame; (* F=(W,R, RU) *)
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
(forall y:(W (F M)), (RU (F M)  x y) -> (satisfies M y  phi))
end.

Definition M_satisfies M phi  := forall w:(W (F M)), (satisfies M w  phi).

Definition valid_in_frame F phi :=
forall L, (M_satisfies (Build_kripke F L) phi).
(* |= phi *)
Definition valid phi:= forall F, (valid_in_frame F phi).
(*Γ|= phi*)
Definition Satisfies F L Γ w := forall phi, In phi  Γ -> satisfies (Build_kripke F L) w phi.
Definition Entailment F Γ L psi :=   forall w, (Satisfies F L Γ w  -> satisfies (Build_kripke F L) w psi).
Definition Entailment1 Γ phi := forall F,forall L,  Entailment F Γ L phi.
Definition Entailment2 phi := Entailment1 nil phi.


(*Axioms of reflexivity, transitivity, universal modality and symmetry*)

Axiom reff:  forall (M: kripke), forall i: agent, forall y: (W (F M)),(R  (F M) i y y).


Axiom trans:  forall (M: kripke), forall i: agent, forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i y z) -> R (F M) i x z ).


Axiom un:  forall (M: kripke),  forall x y : (W (F M)),(RU(F M)  x y ).


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



Theorem pseudotrans:  forall phi: formula, forall i j: agent, valid ((C phi) -->(K i phi) --> (K j (K i phi))).
intros.
unfold valid.
intros.
unfold valid_in_frame.
intros.
unfold M_satisfies.
intros.
simpl in |-*.
intros.
apply H.
assert (H3: forall (M: kripke), forall x y : (W (F M)),(RU (F M) x y)).
apply un.
generalize (H3 (Build_kripke F0 L0)).
intros.
simpl.
apply H4.
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
(*two lists are equivalent if they are the same after
removing all o's at the front of the lists *)
Parameter Ass:level->formula->Prop.
Reserved Notation "Γ ⊢ A" (at level 80).

Inductive Provable: level->formula->Prop:=
|truth : forall n:level,(Provable n Top)
|ass_at :  forall phi:formula, forall l m:level,
(EqLevel l m) -> ((Provable l phi) -> (Provable  m phi))
|andI :  forall phi1 psi2:formula, forall n:level,
(Provable n phi1) -> (Provable  n psi2) ->
(Provable  n (And phi1 psi2))
|andE1 :  forall phi1 phi2:formula, forall n:level,
(Provable n (And phi1 phi2)) -> (Provable n phi1)
|andE2 : forall phi1 phi2:formula, forall n:level,
(Provable  n (And phi1 phi2)) -> (Provable  n phi2)
|orI1 :  forall phi1 phi2:formula, forall n:level,
(Provable  n phi1) -> (Provable n (Or phi1 phi2))
|orI2 :  forall phi1 phi2:formula, forall n:level,
(Provable n phi2) -> (Provable n (Or phi1 phi2))
|orE :  forall phi1 phi2 psi:formula, forall n:level,
(Provable  n (Or phi1 phi2)) ->
(Provable  n (phi1 --> psi)) ->
(Provable n  (phi2 --> psi)) -> (Provable  n psi)
|impI : forall phi1 phi2:formula, forall n:level,
((Ass n phi1) -> (Provable n phi2))->
(Provable  n (Imp phi1 phi2))
|impE :  forall phi1 phi2:formula,forall n:level,
(Provable  n (Imp phi1 phi2)) ->
(Provable  n phi1) -> (Provable  n phi2)
|notI : forall phi:formula, forall n:level,
(Provable n (phi --> Bottom)) ->
(Provable  n (Not phi))
|notE :  forall psi:formula, forall n:level,
(Provable  n psi) ->
((Provable  n (Not psi)) -> (Provable  n Bottom))
|botE : forall phi:formula, forall n:level, 
(Provable  n Bottom) -> (Provable  n phi)
|notnotE :  forall phi:formula, forall n:level,
(Provable  n (Not (Not phi))) -> (Provable  n phi)
|KiE :  forall phi:formula, forall i: agent, forall n:level,
((Check_k i n) -> (Provable (Decrease n) (K i phi)) -> (Provable n phi))
|KiI :  forall phi:formula, forall i: agent, forall n:level,
(Provable  (Increase n(k i)) phi) -> (Provable  n (K i phi))
|CK:  forall phi:formula, forall i: agent, forall n:level, 
(Provable  n (C phi)) -> (Provable  n (K i phi))
|CE :  forall phi:formula, forall i: agent, forall n:level,
((Check_c n) -> (Provable  (Decrease n) (C phi)) -> (Provable  n phi))
|CI :  forall phi:formula, forall i: agent,forall n:level,
(Provable (Increase n c) phi) -> (Provable  n (C phi))
|t :  forall phi:formula, forall i: agent, forall n:level,
(Provable  n (K i phi)) -> (Provable n phi)
|four :  forall phi:formula, forall i: agent, forall n:level,
(Provable  n (K i phi)) -> (Provable  n (K i (K i phi)))
|five :  forall phi:formula, forall n:level, forall i: agent,
(Provable  n (Not (K i phi))) ->
(Provable  n (K i (Not (K i  phi))))
|Cf :  forall phi:formula, forall i: agent, forall n:level,
(Provable  n (C phi)) -> (Provable  n (C (C phi))).

(*The special axiom to work with assumptions*)
Axiom Prov: forall phi:formula, forall n:level,(Ass n phi)-> (Provable  n phi).
(*Examples of theorems*)

Lemma propDis:  forall phi psi: formula,   Provable  nil (psi || phi) --> (phi || psi).
intros. apply impI. intro.
assert (H1: Provable nil (psi || phi)).
apply Prov. auto.
apply orE with psi phi.
auto.
apply impI; intro.
apply orI2.
apply Prov.
auto.
apply impI; intro.
apply orI1.
apply Prov.
auto.
Qed.

Lemma mod2:  forall phi psi: formula, forall i: agent,  Provable  nil ((K i((phi --> psi))) --> ((K i phi) -->  (K i psi))).
intros. apply impI. intro. 
apply impI. intro.
apply KiI. unfold Increase.
assert (H1: Provable nil (K i phi)). apply Prov. exact H0.
assert (H2: Provable nil (K i (phi --> psi))). apply Prov. exact H.
assert (H3: Provable (cons (k i) nil )(phi --> psi)).  
apply KiE with i. unfold Check_k. tauto. unfold Decrease. simpl in |-*.
apply ass_at with nil.
unfold EqLevel.
unfold Remove_o.
reflexivity.
auto.
assert (H4: Provable (cons (k i) nil) phi).  
apply KiE with i. unfold Check_k. tauto. unfold Decrease. simpl in |-*.
apply ass_at with nil.
unfold EqLevel.
unfold Remove_o.
reflexivity.
auto.
apply impE with phi. auto. auto.
Qed.

Lemma mod5:  forall phi psi: formula, forall i: agent,  Provable  nil (phi --> phi) --> (K i (phi --> phi)).
intros. apply impI. intro.
apply KiI.
apply impI.
intros.
apply Prov.
auto.
Qed.

(*A postulate to operate with satisfiable assumptions*)

Axiom IAss: forall phi psi:formula, forall F, forall L, forall l: level, forall w, (((Ass l phi) -> satisfies (Build_kripke F L) w psi) /\ satisfies (Build_kripke F L) w phi)->   satisfies (Build_kripke F L) w psi.

(*This technical  axiom states that two arbitrary levels differing only in leading 0's are equal*)
Axiom Check: forall n: level, cons o n = n.

Definition Prop_Soundness :=  forall phi:formula,   Provable  nil  phi -> valid phi.

Theorem Soundness: Prop_Soundness.

unfold Prop_Soundness. intros.
induction H.  simpl;intros.

(*True*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. unfold satisfies.
intuition.  

(*Assumption at equal levels*)
auto.

(*Conjunction1*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  split.
unfold valid in IHProvable1. 
unfold valid_in_frame in IHProvable1.
unfold M_satisfies in IHProvable1.  apply IHProvable1.  
unfold valid in IHProvable2.
unfold valid_in_frame in IHProvable2. 
unfold M_satisfies in IHProvable2.  apply IHProvable2.  

(*Conjunction2*)
unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros. 


unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.  apply IHProvable. 
unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.   
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.  apply IHProvable.   

(*Disjunction1*)

unfold valid. intros. unfold valid_in_frame. intros.
unfold M_satisfies. intros. left.
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.  apply IHProvable. 
unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros. right.
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.  apply IHProvable. 
 
(*Disjunction2*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros. 

unfold valid in IHProvable1.
unfold valid_in_frame in IHProvable1. 
unfold M_satisfies in IHProvable1. 
unfold valid in IHProvable2.
unfold valid_in_frame in IHProvable2.
unfold M_satisfies in IHProvable2.
unfold valid in IHProvable3.
unfold valid_in_frame in IHProvable3. 
unfold M_satisfies in IHProvable3. 
 
generalize (IHProvable1 F0); intro.
generalize (H2 L0); intro.
generalize (H3 w); intro. 
generalize (IHProvable2 F0); intro.
generalize (H5 L0); intro.
generalize (H6 w); intro.
generalize (IHProvable3 F0);
intro. generalize (H8 L0);
intro. generalize (H9 w); intro.
simpl in H10.
simpl in H7.
elim H4.
auto.
auto.

(*Implication1*)
unfold valid. intros. unfold valid_in_frame. intros.
unfold M_satisfies. intros. 
try simpl in |-*. intro.
unfold valid in H0.  unfold valid_in_frame in H0.
unfold M_satisfies in H0.
apply IAss with  phi1 n.
split.
intro.
apply H0.
auto.
auto.


(*Implication2*)

unfold valid. intros. unfold valid_in_frame. 
intros. unfold M_satisfies. intros. 

unfold valid in IHProvable1.  unfold valid_in_frame in IHProvable1.
unfold M_satisfies in IHProvable1. 
unfold valid in IHProvable2.  unfold valid_in_frame in IHProvable2. 
unfold M_satisfies in IHProvable2.
simpl in IHProvable1.
generalize (IHProvable2 F0); intro.
generalize (H1 L0); intro. generalize (H2 w); intro.
generalize (IHProvable1 F0); intro. 
generalize (H4 L0); intro. generalize (H5 w); intro.
apply H6.
auto.

(*Negation1*)
unfold valid. intros. unfold valid_in_frame. 
intros. unfold M_satisfies. intros. 
try simpl in |-*. intro.
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.
simpl in IHProvable.
apply IHProvable with F0 L0 w.
auto.




(*Bottom1*)
unfold valid. intros. unfold valid_in_frame. 
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable1.  unfold valid_in_frame in IHProvable1.
unfold M_satisfies in IHProvable1.    
unfold valid in IHProvable2.  unfold valid_in_frame in IHProvable2. 
unfold M_satisfies in IHProvable2.  
simpl in IHProvable2. simpl in |-*.
generalize (IHProvable1 F0); intro. generalize (H1 L0);
intro. generalize (H2 w); intro. 
generalize (IHProvable2 F0); intro. generalize (H4 L0);
intro. generalize (H5 w); intro.
apply H6.
auto.

(*Bottom2*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
generalize (IHProvable F0); intro. generalize (H0 L0);
intro. generalize (H1 w); intro.
contradict H2. 



(*Double Negation*)

unfold valid. intros. unfold valid_in_frame. 
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.    
try simpl in IHProvable.

generalize (IHProvable F0); intro.
generalize (H0 L0); intro. generalize (H1 w); intro.

assert (H4:  ~ ~ satisfies {| F := F0; L := L0 |} w phi -> satisfies {| F := F0; L := L0 |} w phi).
intro. 
assert ((satisfies {| F := F0; L := L0 |} w phi)\/~ satisfies {| F := F0; L := L0 |} w phi) as H6. apply classic.
elim H6; intro.
assumption.
contradict H3.
auto.
apply H4.
auto.


(*Ki1*)
induction n.
simpl in H0.
simpl in H.
contradict H.
induction l.
simpl in H.
try simpl in H0.
apply IHn.
auto.

apply ass_at with (cons o (Decrease n)).

unfold Decrease.
unfold EqLevel.
unfold Remove_o.
reflexivity.
exact H0.
simpl in H.
simpl in IHn.
simpl in H0.



unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.    

try simpl in IHProvable.

generalize (IHProvable F0); intro. generalize (H1 L0); intro. generalize (H2 w); intro.

apply H3.
assert(H5: forall (M: kripke), forall i: agent, forall x: (W (F M)), (R (F M)i x x)).
apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.
apply H4.
simpl in H.
contradict H.

(*Ki2*)
induction n.
simpl in H.
unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
try simpl in IHProvable.
intros.
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
simpl. intros.
apply H1.
induction l.
simpl in H.
simpl in IHn.
apply IHn.
apply ass_at with (Increase (cons o n) (k i)).
unfold EqLevel.
unfold Remove_o.
simpl.
subst.
assert (H0: cons o n = n).
apply Check.
symmetry in H0.
rewrite <- H0.
tauto.

exact H.
simpl in H.

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
try simpl in IHProvable.
intros.
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
simpl. intros.
apply H1.
unfold valid. intros. unfold valid_in_frame. 
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
try simpl in IHProvable.
intros.
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
simpl. intros.
apply H1.







(*CK*)

unfold valid. intros. unfold valid_in_frame. intros.
unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.    
try simpl.
try simpl in IHProvable.
generalize (IHProvable F0); intro.
generalize (H0 L0); intros. generalize (H1 w); intro.
apply H3.
assert (H5:forall (M: kripke),  forall x y : (W (F M)),(RU(F M)  x y )).
apply un.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.
apply H4.
 

(*C1*)

induction n.

simpl in H0.
simpl in H.
contradict H.
induction l.
simpl in H.
try simpl in H0.
apply IHn.
auto.

apply ass_at with (cons o (Decrease n)).

unfold Decrease.
unfold EqLevel.
unfold Remove_o.
reflexivity.
exact H0.
induction i. 
simpl in H.
contradict H.
auto.
simpl in IHn.
simpl in H0.
subst.


unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
try simpl.
try simpl in IHProvable.
assert (H5:forall (M: kripke),  forall x y : (W (F M)),(RU(F M)  x y )).
apply un.
generalize (IHProvable F0); intro.
generalize (H1 L0); intros. generalize (H2 w); intro.
apply H3.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.
apply H4.

(*C2*)

induction n.
simpl in H.

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable.
unfold M_satisfies in IHProvable.    
try simpl in IHProvable.
intros.
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
simpl. intros.
apply H1.

induction l.
simpl in H.
simpl in IHn.
apply IHn.
apply ass_at with (Increase (cons o n) (c)).


unfold EqLevel.
unfold Remove_o.
simpl.
subst.
assert (H0: cons o n = n).
apply Check.
symmetry in H0.
rewrite <- H0.
tauto.
exact H.


unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    

try simpl.
intros.
generalize (IHProvable F0); intro. generalize (H1 L0); intro. 
generalize (H2 y); intro.
auto.

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.    
try simpl.
intros.
generalize (IHProvable F0); intro. generalize (H1 L0); intro.
generalize (H2 y); intro.
auto.

(*reflexivity*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.
simpl in IHProvable.    

generalize (IHProvable F0); intro.
generalize (H0 L0); intro. generalize (H1 w); intro.
apply H2.  

assert (H5: forall (M : kripke)(i: agent) (y : W (F M)), R (F M) i y y). 
apply reff.
generalize (H5 {| F := F0; L := L0 |}). simpl. intros.
generalize (H3 i). intro. apply H4.
(*transitivity*)
unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable. 
unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.
simpl in IHProvable.    

generalize (IHProvable F0); intro.
generalize (H0 L0); intro. generalize (H1 w); intro.
simpl. intros.
apply H2.  

assert (H6: forall (M: kripke), forall i: agent,forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i  y z) -> R (F M) i x z )). apply trans.
generalize (H6 {| F := F0; L := L0 |}). simpl.
intros. generalize (H5 i); intro. generalize (H7 w); intro. 
generalize (H8 y); intro. generalize (H9 y0); intro.
apply H10.  split. exact H3.   exact H4.

(*symmetry*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.
simpl in IHProvable.    
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
generalize (H1 w); intro.
simpl. intros.
intro.  
apply H2.
intro.


assert (H7: forall (M: kripke), forall i:agent ,forall x y z: (W (F M)),((R (F M) i x y /\ R (F M) i y z)-> R (F M) i x z)).
apply trans.
generalize (H7 {| F := F0; L := L0 |}). simpl. intros.
generalize (H5 i); intro. generalize (H8 y). intro. generalize (H9 w);intro.  
generalize (H10 y0);intro.
apply H4.
apply H11. split.
assert (H13: forall (M: kripke), forall i:agent ,forall x y: (W (F M)),(R (F M) i x y  -> R (F M) i y x)).
apply symm.
generalize (H13 {| F := F0; L := L0 |}). simpl. intros.
generalize (H12 i); intro. generalize (H14 w). intro. 
generalize (H15 y);intro.  apply H16. auto. 
auto.


(*transitivity for C*)

unfold valid. intros. unfold valid_in_frame.
intros. unfold M_satisfies. intros.  
unfold valid in IHProvable.  unfold valid_in_frame in IHProvable. 
unfold M_satisfies in IHProvable.
simpl in IHProvable.    
generalize (IHProvable F0); intro. generalize (H0 L0); intro.
generalize (H1 w); intro.
simpl. intros.
apply H2.  
assert (H6:forall (M: kripke),  forall x y : (W (F M)),(RU(F M)  x y )).
apply un.
generalize (H6 {| F := F0; L := L0 |}). simpl.
intros. generalize (H5 w); intro.
generalize (H7 y0); intro. exact H8. 

Qed.




 


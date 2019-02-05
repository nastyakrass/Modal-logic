Load "C:\Program Files (x86)\Coq\bin\KripkeP". (* load the Coq
code*)
(* We define a type set to represent sets of agents
and a few functions on sets. *)
Require Export List.
Require Import Classical.
Export ListNotations.
Set Implicit Arguments.
 

Inductive set : Set := nil' : set |
cons' : agent -> set -> set.
Fixpoint In (l:set) (i : agent): Prop := (* l In
ludes i *)
match  l with
|nil' => False
| (cons' j m) => (j= i)\/(In m i)
end.
Fixpoint Size (l:set) : nat:=
match l with
|nil' => 0
|(cons' e l') => (S (Size l'))
end.
Definition Incl (l m: set) := forall i:agent, ((In m i)->(In l i)).
(* l Includes m *)
(* (BigOr S P phi) is the disjun
tion of all formulas (phi s)
with s:S and (P s) *)
Parameter BigOr: forall S: Set, (S->Prop)->(S->formula)->formula.
(*
The following axioms say that if an s exists with property P we
have that (phi s) is provable, then we have that
(BigOr S P phi) is provable, and vice versa
*)
Axiom BigOrI: forall Γ, forall S: Set, forall P: S ->Prop, forall phi:S ->formula, forall n:level,
(exists s: S, (P s)/\(Provable Γ n (phi s))) ->
(Provable Γ n (BigOr (P) (phi))).

Axiom BigOrE: forall Γ, forall S: Set, forall P: S ->Prop, forall phi:S ->formula, forall n:level,
(Provable Γ n (BigOr(P) (phi) ))->(exists s: S, (P s)/\(Provable Γ n (phi s))).

(*BigAnd S P phi) is the
conjunction of all formulas (phi s)
with s:S and (P s) *)
Parameter BigAnd:forall S: Set,(S -> Prop)->(S -> formula)->formula.
(*
The following axioms say that if for all s with property P we
have that (phi s) is provable, then we have that
(BigAnd S P phi) is provable, and vice versa
*)
Axiom BigAndI: forall Γ, forall S: Set, forall P: S ->Prop, forall phi:S ->formula, forall n:level,
(forall s: S, (P s)->(Provable Γ n (phi s))) ->
(Provable Γ n (BigAnd(P) (phi) )).

Axiom BigAndE: forall Γ, forall S: Set, forall P: S ->Prop, forall phi:S ->formula, forall n:level,
(Provable Γ n (BigAnd(P) (phi) ))->(forall s: S, (P s)->(Provable Γ n (phi s))).

Definition muddy (i:agent): formula := (Atom (p i)).
Definition not_muddy (i: agent): formula:= (Not (muddy i)).
Definition uneq (A: Set) := forall x y: A,(eq x y)->False.
Definition NotIn (l: set):= forall x: agent, (In l x)->False.

Check (BigAnd (In 
(cons' (S O) (
cons' (S(S O)) (
cons' (S(S(S O))) nil'))))
(fun x: agent =>(muddy O)-->(K x (muddy O)))).

(*
We will prove two entailments that
can be used to prove
that if there are n muddy
children, and n-1 times everyone
announces that they don't know whether they are muddy, all the

muddy
children
can
conclude they are muddy
*)
Require Classical. (*
lassi
: (P:Prop)P\/~P *)
(* We use the following 8 lemmas to reason with the
BigAnd and BigOr: *)
Lemma L1: forall S:Set, forall Γ, forall l:level, forall phi:S->formula, forall cond cond':S->Prop, (Provable Γ l (BigAnd (cond) (phi))) ->
(forall j:S,(cond' j)->(cond j)) ->
(Provable Γ l (BigAnd (cond') (phi))).
intros.
apply BigAndI.
intros.
apply BigAndE with cond.
exact H.

apply H0; assumption.
Qed.

Lemma L2: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ l (BigAnd (cond) (fun j: S => (C (phi j)))))->
(Provable Γ l (BigAnd (cond)(fun j: S => (K i (phi j))))).
intros.

apply BigAndI.
intros.
apply CK.
change (Provable Γ l ((fun j : S => (C (phi j)))s)).


apply BigAndE with cond.
exact H.
exact H0.
Qed.

Lemma L3: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ l (BigAnd (cond) (fun j: S => (K i (phi j)))))->
(Provable Γ l (BigAnd (cond) (phi))).
intros.

apply BigAndI.
intros.
apply t with i.
change (Provable Γ l ((fun j : S => (K i (phi j)))s)).


apply BigAndE with cond.
exact H.
exact H0.
Qed.


Lemma L4: forall S:Set,forall Γ, forall l:level, forall phi psi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ l (BigAnd (cond) (phi)))->
(Provable Γ l (BigAnd (cond)(fun j: S => ((phi j) --> (psi j)))))->(Provable Γ l (BigAnd (cond) (psi))).
intros.

apply BigAndI.
intros.
apply impE with (phi s).
change (Provable Γ l ((fun j : S => ((phi j) --> (psi j)))s)).


apply BigAndE with cond.
exact H0.
exact H1.
apply BigAndE with cond.
exact H.
exact H1.
Qed.

Lemma L5: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ (Increase (l)(o)) (BigAnd (cond) (fun j: S => (K i (phi j)))))->
(Provable Γ (Increase (l)(k i)) (BigAnd (cond) (phi))).
intros.

apply BigAndI.
intros.
apply KiE with i.
unfold Check_k.
reflexivity.
simpl in |-*.
change (Provable Γ (Increase l o) ((fun j : S => (K i (phi j)))s)).


apply BigAndE with cond.
exact H.
exact H0.
Qed.


Lemma L8: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ (Increase (l)(o)) (BigAnd (cond) (fun j: S => (C (phi j)))))->
(Provable Γ (Increase (l)(c)) (BigAnd (cond) (phi))).
intros.

apply BigAndI.
intros.
apply CE.
auto.
unfold Check_c.

reflexivity.
simpl in |-*.
change (Provable Γ (Increase l o) ((fun j : S => (C (phi j)))s)).


apply BigAndE with cond.
exact H.
exact H0.
Qed.

Lemma L6: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond:S->Prop,
(Provable Γ l (Not(BigOr (cond) (phi))))->
(Provable Γ l  (BigAnd (cond) (fun s: S => (Not(phi s))))).
intros.

apply BigAndI.
intros.
apply notI.
apply notE with (BigOr cond phi).
cut(exists s:S,(cond s)/\(Provable  (phi s :: Γ) l (phi s))).
intro.
apply BigOrI.
exists s.
split.
exact H0.
Assumed.
exists s.
split.
exact H0.
Assumed.
apply Weak.
exact H.
Qed.

Lemma L7: forall S:Set,forall Γ, forall l:level, forall phi:S->formula, forall i:agent,
forall cond cond':S->Prop,
(Provable Γ l (BigAnd (fun g:S => (cond g)) (phi)))->
(Provable Γ l (BigAnd (fun g:S => (cond' g)) (phi)))->
(Provable Γ l (BigAnd (fun g:S => ((cond g)\/(cond' g))) (phi))).
intros.
apply BigAndI.
intros.
elim H1.
intro.


apply BigAndE with (fun g:S => (cond g)).
exact H.
auto.
intro.
apply BigAndE with (fun g:S => (cond' g)).
exact H0.
auto.
Qed.

Parameter A:set. (* Suppose the group of
hildren is A *)
Definition alpha (G: set):formula:=
(BigAnd (fun i: agent => ((In A i)/\(In G i))) (muddy)) &&
(BigAnd (fun i:agent =>((In A i)/\((In G i)->False)))(not_muddy)).
(* (alpha H) means exactly the
children In H are muddy *)


Section Entailment_1.
(*
In this section we prove the first entailment: if there are n
children with mud on their foreheads, and it is
common knowledge
that there are at least n
children with mud on their foreheads,
then they all know they are muddy, since they
can see each other
*)
Variable L:level.
(* Our "start level" for the proof is L (see S5n) *)
(* We use the premises after having
closed one or two boxes, as
we will discover in the proof below, hence the level of the
premises is (cons o L) or (cons o (cons o L)) instead of L *)



Variable m:agent.

Hypothesis In_A_m: forall m: agent, (In A m).
(* Take an arbitrary agent m *)
(* from the group A of
children *)

Variable  H: set. (* Take a set H of agents *)

Hypothesis Incl_A_H: forall H: set, (Incl A H).
(* su
h that H is a subset of A *)
Hypothesis In_H_m:  forall H: set, (In H m).
(* and m is an element of H *)

(* and exactly the
children in H are muddy *)
(* Suppose it is
common knowledge that the number
of muddy
children is at least the size of H *)
Definition Size_lt(n:nat) (G:set):Prop:=(lt (Size G) n).



Axiom setminus:
forall G:set, forall i:agent, (* For all sets G and agents i such that *)
(In G i) -> (* G includes i, *)
(exists G':set, (* a set G' exists, such that *)
(S (Size G'))=(Size G) (* the size of G = the size of G'+1, *)
/\ ~(In G' i) (* and i is not an element of G', *)
/\ (Incl G G')(* and G' is a subset of G, *)
/\ forall j:agent,(In G j)->(j<> i<->(In G' i))).
(* and all agents from G besides i are in G' *)
(* so G'=G\{i} *)
(*
We prove that m knows he's muddy
The numbers in
comment
correspond to the line numbers of the
natural deduction proof in Chapter 4 of the thesis
*)
Lemma entailment_1:forall Γ, forall l: level,(Provable Γ (Increase (l) (o))
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (muddy j)-->(K i (muddy j))))))))->(Provable  Γ (Increase (l) (o))
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (not_muddy j)-->(K i (not_muddy j))))))))-> 
((fun H: set=>(Provable Γ (Increase (l) (o)) (alpha H)))H)->
((fun H: set=>(Provable  Γ (Increase(Increase (l) (o)) (o))
(C (BigAnd  (fun G: set =>(Incl A G)/\(Size_lt (Size H) G))
(fun G:set=>(Not(alpha G)))))))H)->
 Provable  Γ l (K m (muddy m)).
intro.
intro.
intro see_muddy_others.
intro see_clean_others.

intro muddy_H.

intro at_least_size_H.



apply KiI.
apply notnotE.
apply notI.
elim (setminus H m).
intro H'.
intros.
elim H0.
intros.
elim H2.
intros.
elim H4.
intros.
clear H0.
clear H2.
clear H4.
apply notE with (alpha H').
unfold alpha.
apply andI.
apply L5.
apply L4 with muddy.
auto.
apply L1 with (fun j:agent =>(In A j)/\(In H j)).
unfold alpha in muddy_H.
apply andE1 with(BigAnd  (fun j:agent=>(In A j)/\(In H j->False)) (not_muddy)).
apply Weak.
apply muddy_H.
intros.
split.
elim H0.
intros.
exact H2.
apply H5.
elim H0.
intros.
exact H4.
apply L3 with m.
change (Provable (Not (muddy m):: Γ)(Increase l o)
(BigAnd  (fun j:agent => (In A j)/\(In H' j))
(fun j:agent => (K m ((fun j':agent=>((muddy j')-->(K m (muddy j'))))j))))).
apply L2.
apply L1 with (fun j:agent=>(In A j)/\( m <> j)).
change(Provable (Not (muddy m):: Γ) (Increase l o)
  ((fun i:agent =>(BigAnd (fun j : agent => In A j /\ i <> j)
     (fun j : agent => C (muddy j) --> (K i (muddy j)))))m)).
apply BigAndE with (In A).
apply Weak.
auto.
auto.
intro.
(*apply Incl_A_H.
auto.*)
intros.
split.
elim H0; intros.
auto.
intro.
apply H3.
elim H0;intros.
subst.
exact H7.
apply L1 with (fun i:agent=>(In A i)/\(m = i) \/
(In A i)/\((In H i)->False)).
change(Provable (Not (muddy m):: Γ) (Increase l (k m))
  (BigAnd (fun j: agent=> ((fun i : agent => In A i /\ (m = i))j) \/ (fun i: agent=>(In A i /\ (In H i -> False)))j)not_muddy)).
apply L7.
auto.
apply BigAndI.
intros.
elim H0;intros.
rewrite <- H4.
unfold not_muddy.
Assumed.
apply L5.
apply L4 with not_muddy.
auto.
unfold alpha in muddy_H.
unfold NotIn in muddy_H.
apply andE2 with(BigAnd (fun j:agent=>(In A j)/\(In H j)) muddy).
unfold not.
apply Weak.
exact muddy_H.
apply L3 with m.
change (Provable (Not (muddy m):: Γ)(Increase l o)
(BigAnd  (fun g:agent => (In A g)/\(In H g -> False))
(fun j:agent => (K m ((fun j':agent=>((not_muddy j')-->(K m (not_muddy j'))))j))))).
apply L2.
apply L1 with (fun j:agent=>(In A j)/\(m <>j)).
change(Provable (Not (muddy m):: Γ) (Increase l o)
  ((fun i:agent =>(BigAnd (fun j : agent => In A j /\ i <> j)
     (fun j : agent => C (not_muddy j) --> (K i (not_muddy j)))))m)).
apply BigAndE with (In A).
apply Weak.
auto.
(*apply Incl_A_H.*)
auto.
intros.
split.
elim H0; intros.
auto.
intro.
elim H0;intros.
apply H7.
subst.
auto.
intros.
elim H0; intros.
elim classic with (j=m).
intros.
left.
subst.
split.
auto.
reflexivity.
trivial.
right.
split.
auto.
intro.
apply H3.
elim H6 with j.
intros.
apply H9.
auto.
auto.
apply KiE with m.
unfold Check_k.
reflexivity.
simpl in |-*.
apply CK.
 apply CI.
auto.
change(Provable (Not (muddy m):: Γ) (Increase (Top.cons o l) c) ((fun G: set=> (Not (alpha G)))H')).
apply BigAndE with (fun G:set=>(Incl A G)/\(Size_lt (Size H) G)).

apply CE.
auto.
unfold Check_c.
reflexivity.
simpl in |-*.
apply Weak.
auto.
unfold Size_lt.
rewrite <- H1.
split.
unfold Incl.
intros.
(*apply Incl_A_H.*)
apply In_A_m.

constructor.
auto.

Qed.
End Entailment_1.

(*Now we prove that if it is
common knowledge that there are at
least n muddy
children, then, after the announcement that no one
knows whether he's muddy or not, it will be
common knowledge that
there are at least n+1 muddy
children *)
Definition Size_is(n:nat) (G:set):=(Size G)=n.
(*Hypothesis see_muddy: *)
Variable M: level.
Variable  H: set.
Variable m:agent.
Hypothesis In_A_m: forall m: agent,(In A m).
Hypothesis Incl_A_H:forall H: set,(Incl A H).
Hypothesis In_H_m:  forall m: agent, forall H: set,(In H m).


Hypothesis see_muddy: forall Γ, forall l: level, (Provable Γ l
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (muddy j)-->(K i (muddy j)))))))).

(* ~i=j -> C(p_i -> K_j p_i)
because the
children
can see each other *)
Hypothesis see_clean: forall Γ, forall l: level, (Provable Γ l
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (not_muddy j)-->(K i (not_muddy j)))))))).

(* ~i=j -> C(~p_i -> K_j~p_i)
because the children
can see each other *)

Lemma entailment_2: forall n:nat, forall l: level, forall k: agent, 
(Provable [] l
(C (BigAnd  (fun G:set =>(Incl A G)/\(Size_lt (S n) G))
(fun G:set=>(Not (alpha G)))))) ->
(Provable [] l (BigAnd  (In A)
(fun j : agent => C (Not (K j (muddy j)) && Not (K j (not_muddy j)))))) ->
(Provable [] l
(C (BigAnd  (fun G:set=>(Incl A G)/\(Size_lt (S(S n)) G))
(fun G:set=>(Not (alpha G)))))).
intro n.
intro l.
intro.
(*intro Γ.*)
intro at_least_Sn_muddy.
intro no_one_knows.
apply CI.
auto.
apply L1 with ((fun g:set=>(Incl A g)/\(Size_is (S n) g) \/
(Incl A g)/\(Size_lt (S n) g))).
change(Provable [] (Increase l c)
  (BigAnd
    ((fun h: set=> (fun g : set =>
      Incl A g /\ (Size_is (S n) g))h \/ (fun g : set =>Incl A g /\ Size_lt (S n) g)h))
     (fun G : set => Not (alpha G)))).
apply L7.
auto.
apply L6.
auto.
apply notI.
cut(exists G:set,((Incl A G)/\(Size_is (S n) G)) /\
(Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha](Increase(Increase (l) (c)) (o)) (alpha G))).
intros.
elim H0.
intro G'.
intros.
clear H0.
elim H1;intro.
clear H1.
elim H0; intros.
apply notE  with (BigAnd  (In G') (fun i:agent=>(K i (muddy i)))).
apply BigAndI.
intro m.
intros.
assert(H21: forall Γ, forall l: level,(Provable Γ (Increase (l) (o))
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (muddy j)-->(K i (muddy j))))))))->(Provable  Γ (Increase (l) (o))
(BigAnd (In A)
(fun i:agent => (BigAnd (fun j:agent=> (In A j)/\(i<>j))
(fun j:agent=>(C (not_muddy j)-->(K i (not_muddy j))))))))-> 
((fun H: set=>(Provable Γ (Increase (l) (o)) (alpha H)))G')->
((fun H: set=>(Provable  Γ (Increase(Increase (l) (o)) (o))
(C (BigAnd  (fun G: set =>(Incl A G)/\(Size_lt (Size H) G))
(fun G:set=>(Not(alpha G)))))))G')->
 Provable  Γ l (K m (muddy m))).


apply entailment_1.
apply In_A_m.
(*apply Incl_A_H.*)
apply In_H_m.
apply H21.
apply BigAndI.
 intro i.
 intros.
apply BigAndI.
intro j. 
intros.
apply CE.
auto.
unfold Check_c.
reflexivity.
simpl in |-*.
apply Cf.
auto.
change(Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Top.cons o (Top.cons o l)) ((fun a: agent =>(C (muddy a) --> (K i (muddy a))))j)).
apply BigAndE with (fun a:agent=>(In A a)/\(i <> a)).
change(Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Top.cons o (Top.cons o l))
  ((fun i:agent=>(BigAnd (fun a : agent => In A a /\ i <> a)
     (fun a : agent => C (muddy a) --> (K i (muddy a)))))i)).
apply BigAndE with  (In A).
simpl in |-*.
apply Weak.
apply see_muddy.
elim H6.
intros.
auto.
auto.
apply BigAndI.
 intro i.
 intros.
apply BigAndI.
intro j. 
intros.
apply CE.
auto.
unfold Check_c.
reflexivity.

apply Cf.
auto.
change(Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Decrease (Increase (Increase l c) o)) ((fun a: agent =>(C (not_muddy a) --> (K i (not_muddy a))))j)).
apply BigAndE with (fun a:agent=>(In A a)/\(i <> a)).
change(Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Decrease (Increase (Increase l c) o))
  ((fun i:agent=>(BigAnd (fun a : agent => In A a /\ i <> a)
     (fun a : agent => C (not_muddy a) --> (K i (not_muddy a)))))i)).
apply BigAndE with  (In A).

apply see_clean.
elim H6.
intros.
auto.
auto.
apply H3.
auto.
auto.
apply CE.
auto.
unfold Check_c.
reflexivity.

apply Cf.
auto.
auto.

replace (Size G') with (S n).

unfold Decrease.
unfold Remove_o.

unfold EqLevel.
unfold Increase.
apply ass_at with l.
unfold EqLevel.
unfold Remove_o.
reflexivity.
auto.
apply Weak.
auto.

apply notI.
cut (exists a:agent, (In G' a)).
intro.
elim H4. intro i'. clear H4.
intros.
apply notE with (K i' (muddy i')).
change(Provable
  [BigAnd (In G') (fun i : agent => K i (muddy i));
  BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Increase l c)
  ((fun i:agent=>(K i (muddy i)))i')).

apply BigAndE with (In G').
Assumed.
auto.
apply andE1 with (Not (K i' (not_muddy i'))).
change(Provable
  [BigAnd (In G') (fun i : agent => K i (muddy i));
  BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Increase l c)
  ((fun x:agent=>(Not (K x (muddy x)) && Not (K x (not_muddy x))))i')).
apply BigAndE with (In A).
apply L8.
auto.
apply Weak.
(*assert(H10: Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Increase l o) (BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha)).*)

(*apply Weak.*)
apply ass_at with l.
unfold Increase.
unfold EqLevel.
unfold Remove_o.
reflexivity.
apply Weak.
apply no_one_knows.



apply H0.
auto.
cut (Size_is (S n) G').
case G'.
unfold Size_is.
unfold Size.
intro.
inversion H4.
intro i.
intros.
exists i.
compute.
left;trivial.
assumption.
change(exists G : set,
  ((fun G':set=>(Incl A G' /\ Size_is (S n) G'))G) /\
  Provable [BigOr (fun g : set => Incl A g /\ Size_is (S n) g) alpha] (Increase (Increase l c) o) (alpha G)).
apply BigOrE.
simpl in |-*.
apply CE.
auto.
unfold Check_c.
reflexivity.
apply ass_at with l.
unfold Increase.
unfold EqLevel.
unfold Remove_o.
reflexivity.
apply CI.
auto.
Assumed.
apply CE.
auto.
unfold Check_c.
reflexivity.
simpl in |-*.
apply ass_at with l.
unfold Increase.
unfold EqLevel.
unfold Remove_o.
reflexivity.
auto.
intros.
elim H0.
intros.
inversion H2.
left.
unfold Size_is.
(*unfold Size_lt.*)
split.
assumption.
trivial.

right.
unfold Size_lt.

unfold lt.
split.
assumption.
assumption.
Qed.


From Baire Require Export BOrder.

(*
	ESPACE TOPOLOGIQUE
*)

Record TopSpace : Type := {
	Point :> Type;
  	Open : Ens Point -> Prop;
  
	OpenFull : Open (@Full Point);
	OpenInter (A B : Ens Point) : Open A -> Open B -> Open (Inter A B);
	OpenUnion (F : Fam (Ens Point)) :
		(forall A : Ens Point, F A -> Open A) -> Open (FamUnion F);
	Closed (A:Ens Point) := Open (Compl A)
}.

Arguments Open {t}.
Arguments OpenUnion {t}.
Arguments OpenInter {t}.
Arguments Closed {t}.

Lemma EmptyOpen {X:TopSpace} : Open (@Empty X).
Proof.
	rewrite <- EmptyUnionEqEmpty.
	now apply OpenUnion.
Qed.

(*
	CLOTURE
*)

Definition Closure {X:TopSpace} (A:Ens X) : Ens X :=
	FamInter (fun E:Ens X => Closed E /\ A c= E).

Lemma ClosureBigger {X:TopSpace} (A:Ens X) :
	A c= Closure A.
Proof.
	firstorder.
Qed.

Lemma ClosureOfClosed {X:TopSpace} {A:Ens X} :
	Closed A -> Closure A = A.
Proof.
	intros. apply Ext.
	firstorder.
Qed.

Lemma ClosureMonotone {X:TopSpace} {A B:Ens X} :
	A c= B -> Closure A c= Closure B.
Proof.
 	firstorder.
Qed.

Lemma ClosureIsClosed {X:TopSpace} (A:Ens X) :
	Closed (Closure A).
Proof.
	unfold Closure, Closed.
	rewrite ComplInterEqUnion.
	apply OpenUnion. intros E [OpenA ASub].
	now rewrite ComplInvol in OpenA.
Qed.

(*
	INTERIEUR
*)

Definition Interior {X:TopSpace} (A:Ens X) : Ens X :=
	FamUnion (fun E:Ens X => Open E /\ E c= A).

Lemma InteriorSub {X:TopSpace} (A:Ens X) :
	Interior A c= A.
Proof.
	firstorder.
Qed. 

Lemma InteriorBiggest {X:TopSpace} {A E:Ens X} :
	Open E -> E c= A -> E c= (Interior A).
Proof.
	firstorder.
Qed.

Lemma InteriorMonotone {X:TopSpace} (A B:Ens X) :
	A c= B -> Interior A c= Interior B.
Proof.
	firstorder.
Qed.

Lemma InteriorOfOpen {X:TopSpace} {A:Ens X} :
	Open A <-> Interior A = A.
Proof.
	split.
		intros AOpen. apply SubAntisym.
			exact (InteriorSub A).
		now apply (InteriorBiggest AOpen).
	intros H. rewrite <- H. now apply OpenUnion.
Qed.

Lemma ClIntSub {X:TopSpace} {A:Ens X} :
	Closed A -> Closure (Interior A) c= A.
Proof.
	intros ? x ?. pose (G := fun E => Closed E /\ Interior A c= E).
	apply (@FamInterSubElem X G A) ; firstorder.
Qed.

(*
	VOISINAGES et LOCALITE
*)

Definition Nbhd {X:TopSpace} (x:X) : Ens (Ens X) :=
	fun A:Ens X => exists B:Ens X, x ∈ B /\ Open B /\ B c= A.

Definition NbhdBasis {X:TopSpace} (P:Ens X -> Prop) (B:Fam (Ens X)) (x:X) : Prop := 
	( forall E:Ens X, E ∈ B -> (P E /\ E ∈ Nbhd x) )
	/\ ( forall E:Ens X, E ∈ Nbhd x
		-> (exists E':Ens X, E' ∈ B /\ E' c= E) ).

Definition Locally (X:TopSpace) (P:Ens X -> Prop) : Prop :=
	forall x:X, exists B:Fam (Ens X), NbhdBasis P B x.

Notation "X 'Loc' P" := (Locally X P) (at level 70).

Lemma CaracOpen {X:TopSpace} {A:Ens X} :
	Open A <-> forall a:X, a ∈ A -> A ∈ Nbhd a.
Proof.
	split.
		firstorder.
	intros H. rewrite InteriorOfOpen.
	apply Ext. firstorder.
Qed.

Definition Apart {X:TopSpace} (x:X) (E:Ens X) :=
	Compl E ∈ Nbhd x.

Lemma ApartSub {X:TopSpace} {x:X} {A B:Ens X} :
	A c= B -> Apart x B -> Apart x A.
Proof.
	firstorder.
Qed.

Lemma ApartAll {X:TopSpace} (x:X) (F:Fam (Ens X)) :
	Fin F -> F c= (Apart x) -> Apart x (FamUnion F).
Proof.
	intros FinF FSub. induction FinF.
		exists Full. firstorder. apply OpenFull.
	destruct (IHFinF (SubTrans (UnionSubL F (Singl v)) FSub))
	as (B & xInB & BOpen & BSub).
	assert (tmp : Apart x v).
		now apply (SubTrans (UnionSubR F (Singl v)) FSub).
	destruct tmp as (C & xInC & COpen & CSub).
	exists (Inter B C). repeat split ; try assumption.
		now apply OpenInter.
	intros y [yInB yInC] (E & EInList & yInE).
	destruct EInList as [EInF | EEqv] ; apply (NoOneInEmpty y).
		rewrite <- (InterCompl (FamUnion F)). split.
			now apply (ElemSubFamUnion EInF).
		now apply BSub.
	rewrite <- (InterCompl v). split.
		now rewrite <- EEqv.
	now apply CSub.
Qed.


(*
	ADHERENCE
*)

Definition Adh {X:TopSpace} (A:Ens X) : Ens X :=
	fun x:X => forall V:Ens X, V ∈ Nbhd x -> Inter V A <> Empty.

Theorem AdhEqClosure {X:TopSpace} (A:Ens X) :
	Adh A = Closure A.
Proof.
	apply Ext. split.
		intros xInAdh E [ClosedE ASubE].
		destruct ( EM (x ∈ E) ) as [xInE | xNInE].
			assumption.
		absurd ( Inter (Compl E) A <> Empty ).
			intros InterNEmpty. apply InterNEmpty, Ext.
			firstorder.
		apply xInAdh. now exists (Compl E).
	intros xInCl V (B & xInB & OpenB & BSubV) InterEmpty.
	apply (xInCl (Compl B)).
		split.
			unfold Closed. now rewrite ComplInvol.
		intros y yInA yInB. apply (NoOneInEmpty y). 
		rewrite <- InterEmpty. split.
			now apply BSubV.
		assumption.
	assumption.
Qed.




(*
	DENSITE
*)

Definition Dense {X:TopSpace} (A:Ens X) : Prop :=
	Closure A = @Full X.

(* à regrouper *)

Theorem DensityWithOpens {X:TopSpace} {A:Ens X} :
	( forall U:Ens X, U <> Empty -> Open U -> (Inter U A <> Empty) ) -> Dense A.
Proof.
	intros H. apply Ext. split.
		easy.
	rewrite <- AdhEqClosure.
	intros _ V (B & xInB & BOpen & BSubV).
	assert (InterNEmpty : Inter B A <> Empty).
		apply H. rewrite InhEquivNEmpty.
			now exists x.
		assumption.
	intros InterEmpty. apply InterNEmpty, Ext.
	intros y. split.
		intros [yInB yInA]. rewrite <- InterEmpty.
		firstorder.
	easy.
Qed.

Theorem CaracDense {X:TopSpace} {A:Ens X} :
	Dense A -> ( forall U:Ens X, U <> Empty -> Open U -> (Inter U A <> Empty) ).
Proof.
	intros ADense U UNEmpty UOpen H.
	unfold Dense in ADense. rewrite <- AdhEqClosure in ADense.
	apply UNEmpty, Ext. split.
		intros xInU. assert ( xInAdh : x ∈ Adh A ).
			now rewrite ADense.
		exfalso. apply (xInAdh U).
			now exists U.
		assumption.
	easy.
Qed.

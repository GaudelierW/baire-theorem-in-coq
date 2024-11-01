From Baire Require Export BSet.



Definition Fam V : Type := Ens V.

(*
    UNION
*)

Definition FamUnion {V} (F:Fam (Ens V)) : Ens V :=
	fun x:V => exists E:(Ens V), (E ∈ F /\ x ∈ E).

Lemma EmptyUnionEqEmpty {V} :
	FamUnion (@Empty (Ens V)) = Empty .
Proof.
	apply Ext.
	firstorder.
Qed.

Lemma ElemSubFamUnion {V} {F:Fam (Ens V)} {E:Ens V} :
	E ∈ F -> E c= FamUnion F.
Proof.
	intros. now exists E.
Qed.

(*
    INTERSECTION
*)

Definition FamInter {V} (F : Fam (Ens V)) : Ens V :=
	fun x:V => forall E:Ens V, E ∈ F -> x ∈ E.

Lemma EmptyInterEqFull {V} :
	FamInter (@Empty (Ens V)) = Full.
Proof.
	now apply Ext.
Qed.

Lemma FamInterSubElem {V} {F:Fam (Ens V)} {E:Ens V} :
	E ∈ F -> (FamInter F) c= E.
Proof.
	firstorder.
Qed.

Lemma ComplInterEqUnion {V} (F:Fam (Ens V)) :
	Compl (FamInter F) = FamUnion (fun E:Ens V => Compl E ∈ F).
Proof.
	apply Ext. split.
		intros xInCompl.
		destruct (EM (FamInter F = Full)).
			now rewrite H, ComplFullEqEmpty in xInCompl.
		assert (tmp : exists E:Ens V, ~(E ∈ F -> x ∈ E)).
			apply NForallNEquivEx.
			intros H'. apply xInCompl.
			intros E. rewrite <- NNEquiv.
			exact (H' E).
		destruct tmp as [E H'].
		rewrite (@ImplEquiv (E ∈ F) (x ∈ E)),
		DeMorgan, NNEquiv in H'.
		destruct H' as [EInF xNInE].
		exists (Compl E). split.
			unfold InSet. now rewrite ComplInvol.
		easy.
	firstorder.
Qed.

(*
	LES FAMILLES FINIES
*)

Inductive Fin {V} : Ens V -> Prop :=
	EmptyFin : Fin Empty
	| UnionFin v F : Fin F -> Fin (Union F (Singl v)).

Lemma SubFinFam {V} {F:Fam V} :
	Fin F -> (forall E:Fam V, E c= F -> Fin E).
Proof.
	intros FinF. induction FinF.
		intros E ESubF. replace E with (@Empty V).
			exact EmptyFin.
		apply Ext. firstorder.
	intros E ESubF. destruct (EM (v ∈ E)).
		pose (E' := fun x => x ∈ E /\ x <> v).
		replace E with (Union E' (Singl v)).
			constructor. apply IHFinF. intros x [xInE xNeqv].
			exact (InUnionL (ESubF x xInE) xNeqv).
		apply Ext. split.
			intros [[xInE vNeqx] | xEqv].
				assumption.
			now rewrite xEqv.
		intros xInE. destruct (EM (x = v)) ; subst ; firstorder.
	apply IHFinF. intros x xInE.
	destruct (EM (x = v)).
		now subst.
	firstorder.
Qed.

(*
    FAMILLE DENOMBRABLE
*)

Definition DnbFam V : Type := nat -> V.

Definition DnbToFam {V} (F:DnbFam V) : Fam V :=
	fun v:V => exists n:nat, F n = v.

Lemma SubDnbInter {V} {F G:DnbFam (Ens V)} :
	(forall n:nat, F n c= G n) ->
	FamInter (DnbToFam F) c= FamInter (DnbToFam G).
Proof.
	intros Incl A AIF B [n GEqB].
	rewrite <- GEqB.
	apply (Incl n), (AIF (F n)).
	now exists n.
Qed.


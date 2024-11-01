From Baire Require Export BLogic.


(* Cette définition, ressemblant à l'axiome de compréhension,
nous convient car on sera en fait toujours dans le cas où V
est un espace topologique *)
Definition Ens V := V -> Prop.

(*
    APPARTENANCE
*)

Definition InSet {V:Type} (A:Ens V) (a:V) : Prop := A a.

Notation "a ∈ A" := (InSet A a) (at level 70).

Axiom Ext : forall V:Type, forall A B:Ens V,
	(forall x:V, x ∈ A <-> x ∈ B) -> A = B.

Lemma ExtEquiv {V} (A B:Ens V) :
	A = B <-> (forall x:V, x ∈ A <-> x ∈ B).
Proof.
	split.
		intros H. now rewrite H.
	apply Ext.
Qed.



(*
	INCLUSION
*)

Definition Sub {V} (A B:Ens V) : Prop :=
  forall x:V, x ∈ A -> x ∈ B.

Notation "A 'c=' B" := (Sub A B) (at level 70).

Lemma SubRefl {V} {A:Ens V} :
	A c= A.
Proof.
	easy.
Qed.

Lemma SubTrans {V} {A B C:Ens V} :
	A c= B -> B c= C -> A c= C.
Proof.
	firstorder.
Qed.

Lemma SubAntisym {V} {A B:Ens V} :
    A c= B -> B c= A -> A = B.
Proof.
	intros ASubB BSubA. apply Ext.
	firstorder.
Qed.



(*
	ENSEMBLE VIDE
*)

Definition Singl {V} (v:V) : Ens V :=
	fun x:V => x=v.

Definition Full {V} : Ens V := fun v:V => True.

Definition Empty {V} : Ens V := fun v:V => False.

Lemma NoOneInEmpty {V} (x:V) :
	~ ( x ∈ Empty ).
Proof.
	easy.
Qed.

Require Import Setoid. (* Pour pouvoir rewrite ExtEquiv *)

Lemma InhEquivNEmpty {V} (A:Ens V) :
	A <> Empty <-> (exists x:V, x ∈ A).
Proof.
    rewrite ExtEquiv, <- NForallNEquivEx.
	firstorder.
Qed.



(*
	UNION
*)

Definition Union {V} (A B:Ens V) : Ens V :=
    fun x:V => x ∈ A \/ x ∈ B.

Lemma InUnionL {V} {A B:Ens V} {x:V}:
	x ∈ Union A B -> ~(x ∈ B) -> x ∈ A.
Proof.
	firstorder.
Qed.

Lemma UnionSubL {V} (A B:Ens V) : 
	A c= Union A B.
Proof.
	firstorder.
Qed.

Lemma UnionSubR {V} (A B:Ens V) : 
	B c= Union A B.
Proof.
	firstorder.
Qed.

(*
    INTERSECTION
*)

Definition Inter {V} (A B:Ens V) : Ens V :=
    fun x:V => x ∈ A /\ x ∈ B.

Lemma InterSubL {V} (A B:Ens V) :
	Inter A B c= A.
Proof.
	firstorder.
Qed.

Lemma InterSubR {V} (A B:Ens V) :
	Inter A B c= B.
Proof.
	firstorder.
Qed.


(*
	COMPLEMENTAIRE
*)

Definition Compl {V} (A:Ens V) : Ens V := fun x:V => ~ (A x).

Lemma ComplInvol {V} (A:Ens V) :
    Compl (Compl A) = A.
Proof.
	apply Ext. split.
        apply NNEquiv.
    easy.
Qed.

Lemma ComplEmptyEqFull {V} :
    Compl (@Empty V) = Full.
Proof.
	now apply Ext.
Qed.

Lemma ComplFullEqEmpty {V} :
    Compl (@Full V) = Empty.
Proof.
    apply Ext. firstorder.
Qed.

Lemma ComplEquiv {V} {A B:Ens V} :
	A c= B <-> Compl B c= Compl A.
Proof.
	split.
		firstorder.
	rewrite <- (ComplInvol A), <- (ComplInvol B).
	firstorder.
Qed.

Lemma InterCompl {V} (A:Ens V) :
	Inter A (Compl A) = Empty.
Proof. 
	apply Ext.
    firstorder.
Qed.

Lemma Distinguish {V} {A:Ens V} {a b : V} :
	a ∈ A -> b ∈ Compl A -> a <> b.
Proof.
	intros ? ? ?. subst.
	apply (NoOneInEmpty b). now rewrite <- (InterCompl A).
Qed.

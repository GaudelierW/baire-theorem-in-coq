From Baire Require Export BFamily.

(*
    FAMILLES TOTALEMENT ORDONNEES
*)

From Coq Require Export Relation_Definitions.
Arguments reflexive {A}.
Arguments transitive {A}.

Definition LinOrd {V} (F:Ens V) (R:relation V) := 
	forall a b:V, a ∈ F -> b ∈ F -> R b a \/ R a b.

Lemma SubLin {V} {F E:(Ens V)} {R:relation V}:
	LinOrd F R -> E c= F -> LinOrd E R.
Proof.
	firstorder.
Qed.

Lemma MaxLin {V} {F:Ens V} {R:relation V} :
	Fin F -> LinOrd F R -> F <> Empty ->
	reflexive R -> transitive R ->
	exists a:V, a ∈ F /\ forall b:V, b ∈ F -> R b a.
Proof.
	intros FinF LinF FNEmpty RRefl RTrans. induction FinF.
		easy.
	clear FNEmpty. assert ( vInUn : v ∈ Union F (Singl v)).
		right. reflexivity.
	destruct ( EM (F = Empty) ) as [FEmpty | FNEmpty].
		subst. exists v. split.
			assumption.
		intros b [bInEmpty | bEqv].
			easy.
		now rewrite bEqv.
	destruct ( IHFinF (SubLin LinF (UnionSubL F (Singl v))) FNEmpty )
	as (a & aInF & aMax).
	pose ( aInUn := (UnionSubL F (Singl v)) a aInF ).
	destruct (LinF a v aInUn vInUn) as [vRa | aRv].
		exists a. split.
			assumption.
		intros b [bInF | bEqv].
			exact (aMax b bInF).
		now rewrite bEqv.
	exists v. split.
		assumption.
	intros b [bInF | bEqv].
		exact (RTrans b a v (aMax b bInF) aRv).
	now rewrite bEqv.
Qed.

Lemma UnionMax {V} {F:Fam (Ens V)} {A:Ens V}:
	Fin F -> A ∈ F -> (forall B:Ens V, B ∈ F -> B c= A)
	-> FamUnion F = A.
Proof.
	intros. apply Ext.
	firstorder.
Qed.

Lemma UnionMaxLin {V} {F:Fam (Ens V)} :
	Fin F -> LinOrd F Sub -> F <> Empty
	-> exists A:Ens V, A ∈ F /\ FamUnion F = A.
Proof.
	intros FinF LinF FNEmpty.
	destruct (MaxLin FinF LinF FNEmpty (@SubRefl V) (@SubTrans V))
	as (A & AInF & AMax).
	exists A. split.
		assumption.
	exact (UnionMax FinF AInF AMax).
Qed.

Lemma LocLinIsLin {V} {F:DnbFam V} {R:relation V} :
	reflexive R -> transitive R ->
	( forall n:nat, R (F n) (F (S n)) ) ->
	forall m n:nat, n <= m -> R (F n) (F m).
Proof.
	intros RRefl RTrans LocLin m. induction m ; intros n nLeq.
		induction n.
			exact (RRefl (F 0)).
		now exfalso.
	destruct ( EM (n = S m) ).
		now rewrite H.
	assert ( n <= m ).
		apply LtS, (LeqDiff nLeq H).
	exact (RTrans (F n) (F m) (F (S m)) (IHm n H0) (LocLin m)).
Qed.

Lemma LocLinRev {V} {F:DnbFam V} {R:relation V}:
	reflexive R -> transitive R ->
	( forall n:nat, R (F (S n)) (F n) ) ->
	forall m n:nat, n <= m -> R (F m) (F n).
Proof.
	pose ( R' := fun v w => R w v ). intros RRefl RTrans LocSub. 
	assert( R'Refl : reflexive R' ).
		assumption.
	assert ( R'Trans : transitive R' ).
		intros x y z R1 R2. now apply (RTrans z y x).
	exact (LocLinIsLin R'Refl R'Trans LocSub).
Qed.

Lemma LinDnb {V} {F:DnbFam V} {R:relation V} :
	reflexive R -> transitive R ->
	( forall n:nat, R (F n) (F (S n)) ) -> LinOrd (DnbToFam F) R.
Proof.
	intros RRefl RTrans LocLin A B [n AEqF] [m BEqF].
	rewrite <- AEqF, <- BEqF.
	destruct ( EM (n <= m) ).
		right. exact (LocLinIsLin RRefl RTrans LocLin m n H).
	apply PeanoNat.Nat.nle_gt, PeanoNat.Nat.lt_le_incl in H.
	left. exact (LocLinIsLin RRefl RTrans LocLin n m H).
Qed.
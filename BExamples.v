From Baire Require Export Baire.

(*
	UN EXEMPLE NON TRIVIAL : LA TOPOLOGIE COFINIE
*)

Definition Cof {V} (E:Ens V):=
	exists F:(Ens V), Fin F /\ Compl E = F.

Definition ZarOpen := fun E:(Ens nat) => Cof E \/ E = Empty.

(* On prouve d'abord des lemmes *)

Lemma UnionAssoc {V} (A B C:Ens V):
	(Union (Union A B) C) = (Union A (Union B C)).
Proof.
	apply Ext. firstorder.
Qed.

Lemma FinUnion {V} {A B:Ens V} :
	Fin A -> Fin B -> Fin (Union A B).
Proof.
	intros FinA FinB. induction FinB.
		replace (Union A Empty) with A.
			assumption.
		apply Ext. firstorder.
	rewrite <- (UnionAssoc A F (Singl v)).
	now apply UnionFin.
Qed.

Lemma ComplInter {V} {A B:Ens V} :
	Compl (Inter A B) = Union (Compl A) (Compl B).
Proof.
	apply Ext. split.
	intros xInCompl.
		destruct (EM (x ∈ A)).
			right. firstorder.
		now left.
	firstorder.
Qed.

Lemma InterCof {V} {A B:Ens V} :
	Cof A -> Cof B -> Cof (Inter A B).
Proof.
	intros (X & ? & ?) (Y & ? & ?).
	exists (Union X Y). split.
		now apply FinUnion.
	subst. exact ComplInter.
Qed.

Lemma SupCof {V} {A B:Ens V} :
	Cof A -> A c= B -> Cof B.
Proof.
	intros (C & FinC & ?) ASubB. subst.
	rewrite ComplEquiv in ASubB.
	pose (SubFinFam FinC (Compl B) ASubB).
	now exists (Compl B).
Qed.

Lemma NZarFull :
	ZarOpen (@Full nat).
Proof.
	left. exists Empty. split.
		exact EmptyFin.
	exact ComplFullEqEmpty.
Qed.

Lemma NZarInter {A B:Ens nat} :
	ZarOpen A -> ZarOpen B -> ZarOpen (Inter A B).
Proof.
	intros [CofA | AEmpty] ZOB ; subst.
		destruct ZOB as [CofB | BEmpty]; subst.
			left. exact (InterCof CofA CofB).
		replace (Inter A Empty) with (@Empty nat).
			now right.
		apply Ext. firstorder.
	replace (Inter Empty B) with (@Empty nat).
		now right.
	apply Ext. firstorder.
Qed.

Lemma NZarUnion {R:Fam (Ens nat)} :
	(forall E:Ens nat, E ∈ R -> ZarOpen E) -> ZarOpen (FamUnion R).
Proof.
	intros H. destruct (EM (R = Empty)) ; subst.
		right. exact EmptyUnionEqEmpty.
	apply InhEquivNEmpty in H0. destruct H0 as [E EInR].
	destruct (H E EInR).
		left. exact (SupCof H0 (ElemSubFamUnion EInR)).
	subst. pose (S := fun E => E ∈ R /\ Empty <> E).
	destruct (EM (S = Empty)).
		assert ( R = Singl Empty ).
			apply Ext. intros F. split.
				intros FInR. replace F with (@Empty nat).
					reflexivity.
				apply NNEquiv. intros EmptyNeq.
				apply (NoOneInEmpty F). now rewrite <- H0.
			intros FEq. now rewrite FEq.
		replace (FamUnion R) with (@Empty nat).
			now right.
		rewrite H1. apply Ext. split.
			easy.
		intros (E & EEmpty & xInE). now rewrite EEmpty in xInE.
	apply InhEquivNEmpty in H0.
	destruct H0 as (F & FInR & FNEmpty).
	left. destruct (H F FInR).
		exact (SupCof H0 (ElemSubFamUnion FInR)).
	now subst.
Qed.
	
(* La topologie cofinie *)
Definition NZariski := {| 
	Point := nat ;
	Open := ZarOpen;
	
	OpenFull := NZarFull ;
	OpenInter := @NZarInter ;
	OpenUnion := @NZarUnion
|}.

(* On va maintenant montrer que cet espace est compact et non hausdorff *)

(* Quelques lemmes avant : *)
Lemma FinSingl {V} (v:V):
	Fin (Singl v).
Proof.
	replace (Singl v) with (Union (@Empty V) (Singl v)).
		apply (UnionFin). exact EmptyFin.
	apply Ext. firstorder.
Qed.

Lemma CoverSub {X:TopSpace} {A B:Ens X} {R:Fam (Ens X)}:
	OpenCover B R -> A c= B -> OpenCover A R.
Proof.
	intros [CoverR ?] ASubB. split.
		exact (SubTrans ASubB CoverR).
	assumption.
Qed.

Theorem FinCpct {X:TopSpace} {K:Ens X} :
	Fin K -> Compact K.
Proof.
	intros FinK. induction FinK.
	intros R (RCover & OpenR). exists (@Empty (Ens X)).
	repeat split ; try easy.
		exact EmptyFin.
	intros R OCR.
	destruct (IHFinK R (CoverSub OCR (UnionSubL F (Singl v))))
	as (R' & [FSub OpenR'] & R'Sub & FinR').
	destruct OCR as [UnSub OpenR].
	assert ( vInUn : v ∈ Union F (Singl v) ).
		now right.
	destruct (UnSub v vInUn) as (E & EInR & vInE).
	exists ( Union R' (Singl E) ). repeat split.
				intros x [xInF | xEqv].
					destruct (FSub x xInF) as (G & GInR' & xInG).
					exists G. split.
						now left.
					assumption.
				exists E. split.
					now right.
				now rewrite xEqv.
			intros G [GInR' | GEqE].
				exact (OpenR' G GInR').
			rewrite GEqE. exact (OpenR E EInR).
		intros A [AInR' | AEqE].
			now apply R'Sub.
		now rewrite AEqE.
	now apply UnionFin.
Qed.

(* Compact *)
Theorem NZarCpct : (@Compact NZariski Full).
Proof.
	intros R [FullSub OpenR].
	assert ( @Full NZariski <> Empty ).
		intros H. apply (@NoOneInEmpty NZariski 0).
		now rewrite <- H.
	pose ( S := fun E => E ∈ R /\ E <> Empty ).	
	assert( SEqR : FamUnion S = FamUnion R ).
		apply Ext. intros n. split.
			intros (F & FInS & nInF). exists F. firstorder.
		intros (F & FInR & nInF). exists F.
		repeat split ; try assumption.
		apply InhEquivNEmpty. now exists n.
	assert ( CoverS : OpenCover Full S ).
		split.
			now rewrite SEqR.
		intros E [EInR ENEmpty]. exact (OpenR E EInR).
	assert ( tmp : S <> Empty ).
		exact (NEmptyCover H CoverS).
	clear H. apply InhEquivNEmpty in tmp.
	destruct tmp as (E & EInR & ENEmpty).
	assert ( tmp : Cof E ).
		now destruct (OpenR E EInR).
	destruct tmp as (F & FinF & ComplF). subst.
	destruct ( FinCpct FinF S ) as (S' & [ComplSub OpenS'] & S'Sub & FinS').
		now apply (CoverSub CoverS).
	exists (Union S' (Singl E)). repeat split.
				intros x _. destruct (EM (x ∈ E)).
					exists E. split.
						now right.
					assumption.
				destruct (ComplSub x H) as (A & AInS' & xInS').
				exists A. split.
					now left.
				assumption.
			intros A [AInS' | AEqE].
				exact (OpenS' A AInS').
			rewrite AEqE. exact (OpenR E EInR).
		intros A [AInS' | AEqE].
			apply S'Sub in AInS'. now destruct AInS' as [AInR _].
		now rewrite AEqE.
	now apply UnionFin.
Qed.

(* Quelques lemmes *)
Lemma natInfinite : ~(Fin (@Full nat)).
Proof.
	intros FinF. inversion FinF.
		apply (NoOneInEmpty 0). now rewrite H0.
	pose (G := Union F (Singl v)).
	assert ( LinG : LinOrd G le ).
		intros a b aInF bInF. exact (Nat.le_ge_cases b a).
	assert ( FinG : Fin G ).
		now apply UnionFin.
	assert ( GNEmpty : G <> Empty).
		apply InhEquivNEmpty. exists v. now right.
	destruct (MaxLin FinG LinG GNEmpty Nat.le_refl Nat.le_trans)
	as (a & aInG & aMax).
	apply (n_Sn a), Nat.le_antisymm.
		firstorder.
	apply (aMax (S a)). unfold G. now rewrite H.
Qed.

Lemma CofNEmpty {A:Ens NZariski} :
	Cof A -> A <> Empty.
Proof.
	intros (? & ? & ?) ?.
	apply natInfinite. rewrite <- ComplInvol, ComplFullEqEmpty.
	now subst.
Qed.

(* Non Hausdorff *)
Theorem NZarNHaus : ~(Hausdorff NZariski).
Proof.
	intros ZT2. destruct (ZT2 0 1 (n_Sn 0))
	as (A & B & OpenA & OpenB & OInA & SInB & InterAB).
	destruct OpenA.
		destruct OpenB.
		pose ( ICof := InterCof H H0 ).
				now apply (CofNEmpty ICof).
			now subst.
		now subst.
Qed.


		
	 








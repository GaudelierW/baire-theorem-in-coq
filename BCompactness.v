From Baire Require Export BTopSpace.

(*
	RECOUVREMENT
*)

Definition OpenCover {X:TopSpace} (A:Ens X) (R:Fam (Ens X)) : Prop :=
	A c= FamUnion R /\ (forall E:Ens X, E ∈ R -> Open E).

Lemma NEmptyCover {X:TopSpace} {R:Fam (Ens X)} {A:Ens X} : 
	A <> Empty -> OpenCover A R -> R <> Empty.
Proof.
	intros ANEmpty [RCover _] ?. subst.
	apply ANEmpty. rewrite EmptyUnionEqEmpty in RCover.
	now apply SubAntisym.
Qed.

(*
    COMPACITE
*)

Definition Compact {X:TopSpace} (K:Ens X) : Prop :=
	forall R:Fam (Ens X), OpenCover K R ->
	exists R':Fam (Ens X), OpenCover K R' /\ R' c= R /\ Fin R'.

Print Fin.

Theorem ClosedInCompact {X:TopSpace} {A K:Ens X} :
	Closed A -> Compact K -> A c= K -> Compact A.
Proof.
	intros AClosed Cpct ASubK R [RCover ROpen].
	pose (Q := Union R (Singl (Compl A)) ).
	assert (OpenCompl : Open (Compl A)).
		easy.
	assert (tmp : OpenCover A Q).
		split.
			firstorder.
		intros E [H1 | H2].
			exact (ROpen E H1).
		now rewrite H2.
	destruct tmp as [ACover QOpen].
	assert ( OpenCover K Q ).
		split.
			intros x xInK.
			destruct ( EM (x ∈ A) ).
				now apply ACover.
			exists (Compl A). firstorder.
		exact QOpen.
	destruct (Cpct Q H) as (Q' & [CovQ' OpenQ'] & Q'SubQ & FinQ').
	pose (R' := fun E:Ens X => E ∈ Q' /\ E <> Compl A).
	exists R'. repeat split.
				intros x xInA.
				assert (xInQ' : x ∈ FamUnion Q').
					now apply CovQ', ASubK.
				destruct xInQ' as (E & EInQ' & xInE).
				exists E. repeat split ; try assumption.
				intros EEqCompl. now rewrite EEqCompl in xInE.
			firstorder.
		intros E [EInQ' ENeqCompl].
		apply (InUnionL (Q'SubQ E EInQ') ENeqCompl).
	assert ( R' c= Q' ).
		firstorder.
	exact (SubFinFam FinQ' R' H0).
Qed.

Definition Hausdorff (X:TopSpace) : Prop :=
	forall x y:X, x <> y -> ( exists A B:Ens X,
	Open A /\ Open B /\ x ∈ A /\ y ∈ B /\ Inter A B = Empty ).

Theorem CpctT2Closed {X:TopSpace} :
	Hausdorff X -> ( forall K:Ens X, Compact K -> Closed K ).
Proof.
	intros T2 K Cpct. unfold Closed.
	destruct ( EM (K = Empty) ) as [KEmpty | KNEmpty].
		subst. rewrite ComplEmptyEqFull. apply OpenFull.
	destruct ( EM (K = Full) ) as [KFull | KNFull].
		subst. rewrite ComplFullEqEmpty. apply EmptyOpen.
	apply CaracOpen. intros a aInCompl.
	pose ( F := fun E:Ens X =>
		Open E /\ Inter E K <> Empty /\ Apart a E ).
	assert ( SubCover : exists F':Fam (Ens X),
	OpenCover K F' /\ F' c= F /\ Fin F' ).
		apply (Cpct F). split.
			intros x xInK.
			destruct ( T2 x a (Distinguish xInK aInCompl) )
			as (A & B & AOpen & BOpen & xInA & aInB & InterEmpty).
			exists A. repeat split ; try assumption.
				intros tmp. apply (NoOneInEmpty x).
				now rewrite <- tmp.
			exists B. repeat split ; try assumption.
			intros y yInB yInA. apply (NoOneInEmpty y).
			now rewrite <- InterEmpty.
		firstorder.
	destruct SubCover as (F' & [F'Cover FOpen] & F'SubF & FinF').
	apply (ApartSub F'Cover), (ApartAll a F' FinF').	
	intros V VInF'. apply F'SubF in VInF'.
	now destruct VInF' as (_ & _ & ApartV).
Qed.

Theorem InterDnbCompact {X:TopSpace} {K:DnbFam (Ens X)} :
	Hausdorff X
	-> ( forall n:nat, Compact (K n) )
	-> ( forall n:nat, K (S n) c= K n )
	-> ( forall n:nat, K n <> Empty )
	-> FamInter (DnbToFam K) <> Empty.
Proof.
	intros T2 Cpct Dec NEmpty InterEmpty.
	assert ( forall n:nat, Closed (K n) ).
		intros n. exact (CpctT2Closed T2 (K n) (Cpct n)).
	pose ( Q := fun n:nat => Compl (K n) ).
	pose ( R := (DnbToFam Q) ).
	assert ( REqFam : R = (fun E:Ens X => Compl E ∈ DnbToFam K) ).
		apply Ext. intros E.
		split ; intros [n tmp] ; subst ; exists n ; unfold Q.
			now rewrite ComplInvol.
		rewrite <- (ComplInvol E). now f_equal.
	assert ( CoversK : OpenCover (K 0) R ).
		split. 
			intros x xInK0. rewrite REqFam.
			rewrite <- ComplInterEqUnion. now rewrite InterEmpty.
		intros E EInR. rewrite <- ComplInvol.
		assert ( tmp : exists n:nat, K n = (Compl E) ).
			now rewrite REqFam in EInR.
		destruct tmp as [n ComplEKn].
		assert ( ComplClosed : Closed (Compl E) ).
			now rewrite <- ComplEKn.
		easy.
	destruct (Cpct 0 R CoversK) as (R' & SubCover & R'Sub & FinR').
	assert ( LinR : LinOrd R Sub ).
		apply LinDnb.
				easy.
			exact (@SubTrans X).
		intros n. unfold Q. now rewrite <- ComplEquiv.
	assert (LinR' : LinOrd R' Sub).
		exact (SubLin LinR R'Sub).
	clear LinR. pose ( H0 := NEmptyCover (NEmpty 0) SubCover).
	destruct (UnionMaxLin FinR' LinR' H0) as (A & AInR' & ?).
	subst. apply R'Sub in AInR'. destruct AInR' as [n QEqA].
	unfold Q in QEqA.
	apply (NEmpty n), Ext. split.
		intros xInKn.
		rewrite <- (InterCompl (K n)). split.
			assumption.
		apply (LocLinRev (@SubRefl X) (@SubTrans X) Dec n 0 (PeanoNat.Nat.le_0_l n)),
		SubCover in xInKn.
		now rewrite QEqA.
	easy.
Qed.



(*
	COMPACITE LOCALE
*)

Definition CpctClosureInNbhd (X:TopSpace) : Prop :=
	forall x:X, forall N:Ens X,
	N ∈ Nbhd x -> ( exists N':Ens X, N' ∈ Nbhd x 
		/\ Closure N' c= N
		/\ Compact (Closure N') ).

Theorem LocCpctCarac {X:TopSpace} :
	Hausdorff X -> X Loc Compact -> CpctClosureInNbhd X.
Proof.
	intros T2 LocCpct x N NNbhd.
	destruct (LocCpct x) as (B & H1 & H2).
	destruct (H2 N NNbhd) as (N' & N'InB & N'SubN).
	destruct (H1 N' N'InB) as (N'Cpct & (U & xInU & UOpen & USubN')).
	assert (ClosedN' : Closed N').
		apply (CpctT2Closed T2 N' N'Cpct).
	exists (Interior N'). repeat split.
			exists (Interior N'). repeat split.
					apply (InteriorMonotone U N' USubN').
					assert (IntEq : Interior U = U).
						now apply InteriorOfOpen.
					now rewrite IntEq.
				now apply OpenUnion.
			easy.
		intros y yInClInt. apply N'SubN.
		rewrite <- (ClosureOfClosed ClosedN').
		apply (ClosureMonotone (InteriorSub N') y yInClInt).
	pose ( ClosedCl := ClosureIsClosed (Interior N') ).
	apply (ClosedInCompact ClosedCl N'Cpct (ClIntSub ClosedN')).
Qed.
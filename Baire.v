From Baire Require Export BCompactness.

Definition Baire (X:TopSpace) : Prop :=
	forall F:DnbFam (Ens X),
	( forall n:nat, Open (F n) )
	-> ( forall n:nat, Dense (F n) )
	-> Dense (FamInter (DnbToFam F)).

(*
	AXIOME DU CHOIX DEPENDANT (ACD)
*)

Require Import Coq.Logic.ChoiceFacts.
Axiom FDC : forall A:Type, (FunctionalDependentChoice_on A).

(*
Definition FunctionalDependentChoice_on :=
  forall (R:A->A->Prop),
	(forall x, exists y, R x y) -> forall x0,
	(exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).
*)

(* L'inductif suivant va nous servir à utiliser l'ACD
on pourra construire la suite Kn que l'on veut car
les hypothèses dont on aura besoin sont dans Rel
*)
Inductive Rel {X:TopSpace} (F:DnbFam (Ens X)) (V:Ens X) : Type := 
	rel (n: nat) (Kn: Ens X) : 
		Compact Kn -> (exists x:X, Kn ∈ (Nbhd x)) -> 
		Kn c= F n -> Kn c= V -> Rel F V.

Definition RelToPair {X:TopSpace} (F:DnbFam (Ens X)) (V:Ens X) :
	Rel F V -> nat*(Ens X).
Proof.
	intros. destruct X0. exact (n, Kn).
Defined.

(*
	LE THEOREME DE BAIRE (VERSION LOCALEMENT COMPACT)
*)

Theorem BaireII (X:TopSpace) :
	Hausdorff X -> X Loc Compact -> Baire X.
Proof.
	intros T2 LocCpct F FOpen FDense. 
	apply DensityWithOpens.
	intros V VNEmpty VOpen InterEmpty.
	(* On définit une relation pour utiliser l'axiome du choix dépendant (ACD) *)
	pose ( R := fun (R1 R2 : Rel F V) =>
		forall n Kn Sn KSn, 
		((n, Kn), (Sn, KSn)) = (RelToPair F V R1, RelToPair F V R2)
		-> Sn = S n /\ KSn c= Kn /\ Compact KSn /\
		(exists x:X, KSn ∈ (Nbhd x)) /\ KSn c= F (S n) /\ Kn c= V
	).
	(* On prouve l'hypothèse nécessaire à l'ACD *)
	assert ( HACD : forall x, exists y, R x y ).
		intros [n Kn CpctKn (x & U & xInU & OpenU & USubKn) KnSub1 KnSub2].
		pose ( J := Inter U (F (S n)) ).
		assert( JOpen : Open J ).
			now apply OpenInter.
		assert ( JNEmpty : J <> Empty ).
			apply (CaracDense (FDense (S n)) U).
				intros ?. now subst.
			assumption.
		apply InhEquivNEmpty in JNEmpty.
		destruct JNEmpty as [y yInJ].
		assert ( JNbhd : J ∈ Nbhd y ).
			now exists J.
		destruct (LocCpctCarac T2 LocCpct y J JNbhd)
		as (J' & (B & yInB & OpenB & BSubJ') & KSnSubJ & CpctKSn).
		pose ( KSn := Closure J' ).
		assert ( KSnNbhd : exists a:X, KSn ∈ (Nbhd a) ).
			exists y, B. repeat split ; try assumption.
			exact (SubTrans BSubJ' (ClosureBigger J')).
		assert ( KSnSubFSn : KSn c= F (S n) ).
			exact (SubTrans KSnSubJ (InterSubR U (F (S n)))).
		assert ( KSnSubV : KSn c= V ).
			intros b ?.
			now apply KnSub2, USubKn, (InterSubL U (F (S n))), KSnSubJ.
		exists (rel F V (S n) KSn CpctKSn KSnNbhd KSnSubFSn KSnSubV).
		repeat split ; inversion H ; subst ; try assumption.
			reflexivity.
		intros b ?. now apply USubKn, (InterSubL U (F (S n))), KSnSubJ.
	(* On construit K0, le premier terme de la suite *)
	pose ( V0 := Inter V (F 0) ).
	assert ( tmp : exists x:X, x ∈ V0 ).
		now apply InhEquivNEmpty, (CaracDense (FDense 0)).
	destruct tmp as [pt ptInV0].
	assert ( V0Open : Open V0 ).
		now apply OpenInter.
	assert ( V0Nbhd : V0 ∈ Nbhd pt ).
		now exists V0.
	destruct (LocCpctCarac T2 LocCpct pt V0 V0Nbhd)
	as (N & (B & xInB & OpenB & BSubN) & K0SubV0 & CpctK0).
	pose ( K0 := Closure N ).
	(* On montre que K0 vérifie les conditions voulues*)
	assert ( K0Nbhd : exists x:X, K0 ∈ Nbhd x ).
		exists pt, B. repeat split ; try assumption.
		exact (SubTrans BSubN (ClosureBigger N)).
	assert ( K0SubF0 : K0 c= F 0 ).
		exact (SubTrans K0SubV0 (InterSubR V (F 0))).
	assert ( K0SubV : K0 c= V ).
		exact (SubTrans K0SubV0 (InterSubL V (F 0))).
	pose ( RK0 := rel F V 0 K0 CpctK0 K0Nbhd K0SubF0 K0SubV ).
	(* On applique l'axiome du choix dépendant 
		pour pouvoir définir la suite K toute entière *)
	destruct (FDC (Rel F V) R HACD RK0) as (f & f0Eq & fProp).
	pose ( K := fun n:nat => snd (RelToPair F V (f n)) ).
	(* On montre que K est une suite décroissante de cpct non vides*)
	assert ( H : forall n:nat, (n, K n) = RelToPair F V (f n) ).
		intros n. induction n. 
			unfold K. now rewrite f0Eq.
		unfold K. destruct (RelToPair F V (f (S n))) eqn : E.
		destruct (fProp n n (K n) (n0) e) as (a & _).
			now rewrite IHn, E.
		now rewrite a.
	assert ( KDec : forall n:nat, K (S n) c= K n ).
		intros n. destruct (fProp n n (K n) (S n) (K (S n)) ) as (_ & a & _).
			now rewrite (H n), (H (S n)).
		assumption.
	assert ( KCpct : forall n:nat, Compact (K n) ).
		intros n. unfold K. now destruct (f n).
	assert ( KNEmpty : forall n:nat, K n <> Empty ).
		intros n. unfold K. destruct (f n),
		e as (y & A & yInA & OpenA & ASubKn).
		simpl. intros KnEmpty. subst.
		now apply ASubKn in yInA.
	(* On applique le théorème d'intersection des compacts *)
	pose ( InterNEmpty := InterDnbCompact T2 KCpct KDec KNEmpty ).
	apply InhEquivNEmpty in InterNEmpty.
	destruct InterNEmpty as (a & aInInter). 
	(* On montre finalement que a est dans Inter V (FamInter (DnbToFam F)) *)
	assert ( KSubV : forall n:nat, K n c= V ).
		intros n. unfold K. now destruct (f n).
	assert ( KSubFn : forall n:nat, K n c= F n ).
		intros n. induction n.
			unfold K. now rewrite f0Eq.
		destruct (fProp n n (K n) (S n) (K (S n))) as (_ & _ & _ & _ & ? & _).
			now rewrite (H n), (H (S n)).
		assumption.
	apply (NoOneInEmpty a). 
	rewrite <- InterEmpty. split.
		apply (KSubV 0), aInInter.
		now exists 0.
	intros E [n EEqFn]. subst. apply (KSubFn n). 
	apply aInInter. now exists n.
Qed.

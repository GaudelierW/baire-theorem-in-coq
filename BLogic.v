From Coq Require Export Arith.

(* 
	LOGIQUE PROPOSITIONNELLE
*)

Axiom EM : forall P:Prop, P \/ ~ P.

Lemma NNEquiv {P : Prop} : ~ ~ P <-> P.
Proof.
    split.
        now destruct (EM P).
    easy.
Qed.

Lemma DeMorgan {A B:Prop} :
	~ (A \/ B) <-> ~A /\ ~B.
Proof.
	firstorder.
Qed.

Lemma ImplEquiv {A B:Prop} :
	(A -> B) <-> (~A \/ B).
Proof.
	destruct (EM A) ; firstorder.
Qed.

(*
	ENTIERS
*)

Lemma LeqDiff {n m:nat} :
	n <= m -> n <> m -> n < m.
Proof.
	intros nLeqm ?.
	now destruct (Lt.le_lt_or_eq _ _ nLeqm).
Qed.

Lemma LtS {n m:nat} :
	n < S m -> n <= m.
Proof.
	intros nLtSm. (* unfold lt in nLtSm. *)
	now apply le_S_n.
Qed.

(*
	LOGIQUE DU PREMIER ORDRE
*)

Lemma NForallNEquivEx {V} (P:V->Prop) :
	~ (forall x:V, ~ (P x)) <-> (exists x:V, (P x)).
Proof.
	split.
        intros H. apply NNEquiv.
        firstorder.
    firstorder.
Qed.
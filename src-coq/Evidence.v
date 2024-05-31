Require Import Translator.
Require Import DatalogAST.
Require Import MatrixAST.
Require Import Interpreter.
Require Import MatrixInterpreter.

Require Import Coq.Maps.Map.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sets.Set.

Require Import Coq.NArith.Nat.

Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Peano.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqNative.
Require Import Coq.Logic.Equivalences.
Require Import Coq.Logic.Seq.

Module SemanticsEvidence.

Definition evaluateMatrixAtom (atom : MatrixAtom) (db : Database) (subs : Substitution) : MatrixOp :=
  let matrix := MatrixAST.fromMatrixAST (atom.matrix) in
  let matrixDimensions := MatrixAST.shape matrix in
  let matrixValues := MatrixAST.matrixData matrix in
  let matrixSize := List.fold_left (fun acc dim => acc * dim) 1 matrixDimensions in
  let matrixValues' := List.map (fun x => List.map (evaluateAtom x db subs) matrixDimensions) matrixValues in
  let matrix' := MatrixAST.mkMatrix matrixDimensions matrixValues' in
  MatrixOp.MatrixConst (Matrix.mkMatrix matrixDimensions matrixValues').

Definition MatrixOp.one : MatrixOp A := MatrixConst (mkMatrix [1] [1]).

Definition MatrixOp.get (m : MatrixOp) (position : list nat) : A :=
  match m with
  | MatrixConst (mkMatrix dims matrixContent) =>
    let flatIndex := fold_left (fun acc (i, dim) => acc * dim + i) 0 (zip position dims) in
    nth flatIndex matrixContent default
  | _ => error "MatrixOp.get is not supported for this MatrixOp"
  end.

Lemma setMatrixValue_correct : forall (m : MatrixOp) (position : list nat) (value : A),
    m = setMatrixValue m position value ->
    let new_m := setMatrixValue m position value in
    (position * value) * MatrixOp.one = MatrixOp.get m position ->
    new_m = setMatrixValue m position value.
Proof.
  intros m position value Hm.
  unfold setMatrixValue in Hm.
  destruct m as [matrixContent dims | ]; try discriminate.
  simpl in Hm.
  injection Hm as HmatrixContent.
  clear Hm.
  unfold MatrixOp.get.
  simpl.
  rewrite HmatrixContent.
  f_equal.
  apply map_ext.
  intros i Hi.
  unfold enumFromTo.
  rewrite <- Hi.
  reflexivity.
Qed.

Lemma translateAtomsToMatrices_semantics_preservation :
  forall (atoms : list Atom) (db : Database) (subs : Substitution),
    (forall atom, In atom atoms -> evaluateAtom atom db subs = evaluateMatrixAtom (translateAtomsToMatrices atoms) db subs).
Proof.
  intros atoms db subs.
  induction atoms as [| atom atoms'].
  - intros atom' Hin. inversion Hin.
  - intros atom' Hin.
    destruct Hin as [Heq | Hin'].
    + subst atom'. rewrite translateAtomsToMatrices_cons.
      unfold evaluateMatrixAtom. rewrite Map.find_insert.
      unfold fillMatrix. rewrite setMatrixValue_correct.
      reflexivity.
    + apply IHatoms'. assumption.
Qed.

End SemanticsEvidence.

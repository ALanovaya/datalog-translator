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

Definition getDomainMapValue (domainMap : Map.Map string (list nat)) (predicate : string) : list nat :=
  Map.find_with_default [] predicate domainMap.

Definition evaluateAtomWithDomainMap (atom : Atom) (domainMap : Map.Map string (list nat)) : option (list nat) :=
  let dims := getDomainMapValue domainMap (predicate atom) in
  if dims = [] then None
  else Some (MatrixAST.matrixData (MatrixAST.fromMatrixAST (atom.matrix) dims)).

Lemma initializeMatrixForPredicate_correct : forall (domainMap : Map.Map string (list nat)) (atom : Atom),
  let dims := getDomainMapValue domainMap (predicate atom) in
  let numberOfCells := fold_left (fun acc x => acc * x) 1 dims in
  let cells := replicate numberOfCells 0 in
  MatrixAST.Matrix dims cells = initializeMatrixForPredicate domainMap atom.
Proof.
  intros domainMap atom.
  unfold initializeMatrixForPredicate.
  simpl.
  reflexivity.
Qed.

Lemma buildDomainMap_correct : forall (program : DatalogProgram),
  let domainMap := buildDomainMap program in
  forall (atom : Atom), In atom program ->
  let dims := getDomainMapValue domainMap (predicate atom) in
  dims <> [].
Proof.
  intros program domainMap atom Hin.
  induction program as [| clause program'].
  - contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst clause.
      unfold buildDomainMap in domainMap.
      simpl in domainMap.
      unfold updateDomainMap.
      simpl.
      destruct clause as [| atom'].
      * contradiction.
      * simpl.
        unfold countUniqueTerms.
        simpl.
        unfold getDomainMapValue.
        simpl.
        reflexivity.
    + apply IHprogram'.
      assumption.
Qed.

Theorem initializeMatrixForPredicate_preserves_semantics : forall (program : DatalogProgram) (atom : Atom),
  In atom program ->
  let domainMap := buildDomainMap program in
  let matrix := initializeMatrixForPredicate domainMap atom in
  evaluateAtomWithDomainMap atom domainMap = Some (MatrixAST.matrixData matrix).
Proof.
  intros program atom Hin.
  let domainMap := buildDomainMap program in
  let matrix := initializeMatrixForPredicate domainMap atom in
  apply initializeMatrixForPredicate_correct.
  apply buildDomainMap_correct.
  assumption.
Qed.

Definition getMatrixData (matrixOp : MatrixOp nat) : Matrix.t :=
  MatrixAST.matrixData (MatrixAST.fromMatrixAST matrixOp (getDimensions matrixOp)).

Definition evaluateMatrixOpWithTerms (matrixOp : MatrixOp nat) (terms : list Term) : option (list nat) :=
  let matrixData := getMatrixData matrixOp in
  let termValues := map (fun term => evalTerm term matrixData) terms in
  if exists (fun x => x = 0) termValues then None
  else Some (map (fun x => x * (List.nth termValues (List.nth (getDimensions matrixOp) 1))) (List.nth matrixData 0)).

Theorem multiplyMatricesAdjusted_semantics_preserving : forall (matrixA matrixB : MatrixOp nat) (termsA : list Term),
  let (updatedDimsA, matrixA') := adjustDimensions matrixB matrixA in
  let (updatedDimsB, matrixB') := adjustDimensions matrixA matrixB in
  let updatedTermsA := adjustTerms termsA updatedDimsA in
  let updatedTermsB := adjustTerms termsA updatedDimsB in
  let resultA := Multiply (replicate (length updatedTermsA) 0) (replicate (length updatedTermsB) 0) matrixA matrixB in
  let resultB := Multiply (replicate (length termsA) 0) (replicate (length termsA) 0) matrixA' matrixB' in
  evaluateMatrixOpWithTerms resultA termsA = Some (List.nth (getMatrixData resultB) 0) <->
  evaluateMatrixOpWithTerms matrixA termsA = Some (List.nth (getMatrixData resultB) 0).
Proof.
  intros matrixA matrixB termsA Hcorrect Hback.
  unfold evaluateMatrixOpWithTerms, getMatrixData, adjustDimensions, adjustTerms, Multiply.
  simpl.
  destruct (getDimensions matrixA) as [da db].
  destruct (getDimensions matrixB) as [dc dd].
  simpl.
  destruct (getDimensions matrixA') as [da' db'].
  destruct (getDimensions matrixB') as [dc' dd'].
  simpl.
  assert (da = da').
  {
    simpl.
    unfold replicate.
    simpl.
    reflexivity.
  }
  assert (db = db').
  {
    simpl.
    unfold replicate.
    simpl.
    reflexivity.
  }
  assert (dc = dc').
  {
    simpl.
    unfold replicate.
    simpl.
    reflexivity.
  }
  assert (dd = dd').
  {
    simpl.
    unfold replicate.
    simpl.
    reflexivity.
  }
  assert (da * db = da' * db').
  {
    simpl.
    reflexivity.
  }
  assert (db * dc = db' * dc').
  {
    simpl.
    reflexivity.
  }
  assert (da * db * dc = da' * db' * dc).
  {
    simpl.
    reflexivity.
  }
  assert (List.length termsA = da * db).
  {
    simpl.
    reflexivity.
  }
  assert (List.length termsA = List.length updatedTermsA).
  {
    simpl.
    reflexivity.
  }
  assert (List.length termsA = List.length updatedTermsB).
  {
    simpl.
    reflexivity.
  }
  assert (List.length termsA = List.length (List.nth (getMatrixData resultB) 0)).
  {
    simpl.
    reflexivity.
  }
  assert (List.length termsA = List.length (List.nth (getMatrixData resultB) 1)).
  {
    simpl.
    reflexivity.
  }
  rewrite Hback.
  reflexivity.
Qed.

End SemanticsEvidence.

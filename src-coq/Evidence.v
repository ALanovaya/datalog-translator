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

Theorem translateRule_semantics_preserving : forall (domainMap : Map.Map string (list nat)) (rule : Rule) (inputMatrix : MatrixOp nat),
  let (inputTerms, _) := termsList (body rule) in
  let (inputMatrix', _) := translateRule domainMap rule inputMatrix in
  let (_, inputMatrixDimensions) := getDimensions inputMatrix' in
  let (outputTerms, _) := termsList (head rule) in
  let outputMatrix := evaluateMatrixOpWithTerms inputMatrix' outputTerms in
  outputMatrix = Some (evaluateRule rule inputMatrix).
Proof.
  intros domainMap rule inputMatrix.
  unfold translateRule, termsList, getDimensions, evaluateMatrixOpWithTerms, evaluateRule.
  simpl.

  (* Step 1: Show that the dimensions of the input matrix and the output matrix are the same *)
  assert (inputMatrixDimensions = getDimensions inputMatrix).
  {
    simpl.
    reflexivity.
  }

  (* Step 2: Show that the terms in the body of the rule are the same as the terms in the input matrix *)
  assert (inputTerms = map terms (body rule)).
  {
    simpl.
    reflexivity.
  }

  (* Step 3: Show that the matrices in the body of the rule are the same as the matrices in the input matrix *)
  assert (filledMatrices = translateAtomsToMatrices (body rule)).
  {
    simpl.
    reflexivity.
  }

  (* Step 4: Show that the multiplied matrix is the same as the result of evaluating the rule *)
  assert (multipliedMatrix = fold_left1 (fun acc matrixTerms => let (accMatrix, _) := acc in let (matrix, terms) := matrixTerms in let (da, db) := findRepeatingTermIndices terms (snd acc) in (Multiply da db accMatrix matrix, terms)) matricesWithTerms).
  {
    simpl.
    reflexivity.
  }

  (* Step 5: Show that the output matrix is the same as the result of evaluating the rule *)
  rewrite H4.
  rewrite H3.
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Qed.

Fixpoint eval_datalog (p : DatalogProgram) (q : Query) : list Atom :=
  match p with
  | DatalogProgram clauses =>
    let facts := [fact | ClauseFact fact <- clauses] in
    let rules := [rule | ClauseRule rule <- clauses] in
    let derived_facts := eval_rules rules facts in
    let result := filter (fun fact => predicate fact = query_atom q) (facts ++ derived_facts) in
    result
  end

with eval_rules (rules : list Rule) (facts : list Atom) : list Atom :=
  match rules with
  | nil => facts
  | rule :: rules' =>
    let head_pred := predicate (Rule_head rule) in
    let body_atoms := Rule_body rule in
    let matching_facts := [fact | fact <- facts; predicate fact = head_pred; terms fact = terms (Rule_head rule)] in
    let derived_facts := [fact | fact <- matching_facts; body_atoms = terms fact] in
    eval_rules rules' (facts ++ derived_facts)
  end.

Fixpoint eval_matrix (ops : list MatrixOp) : Matrix :=
  match ops with
  | nil => Matrix_empty
  | op :: ops' =>
    let matrix := eval_matrix ops' in
    match op with
    | MatrixConst m => m
    | Multiply n m op1 op2 => Matrix_multiply n m (eval_matrix [op1]) (eval_matrix [op2])
    | Extend op dims => Matrix_extend (eval_matrix [op]) dims
    | Add op1 op2 => Matrix_add (eval_matrix [op1]) (eval_matrix [op2])
    end
  end.

Theorem translateDatalogProgram_correct :
  forall p q, eval_datalog p q = eval_matrix (translateDatalogProgram p) q.
Proof.
  intros p q.
  unfold eval_datalog, eval_matrix.
  rewrite <- (computeFixpoint_unfold (fun matrixMap => fold_left (processClause matrixMap) Map.empty (clauses p)) Map.empty).
  rewrite <- (Map.elements_correct (computeFixpoint (fun matrixMap => fold_left (processClause matrixMap) Map.empty (clauses p)) Map.empty)).
  rewrite <- (translateDatalogProgram_unfold p).
  induction p as [| c p'].
  - (* base case: empty program *)
    simpl. reflexivity.
  - (* inductive case: program with one more clause *)
    simpl.
    destruct c as [fact | rule].
    + (* fact clause *)
      simpl.
      let fact_matrix := hd (translateAtomsToMatrices [fact]) in
      let fact_pred := predicate fact in
      let matrix_map := buildDomainMap p' in
      let process_clause := processClause matrix_map c in
      rewrite <- (Map.insert_with_commute _ _ _ _ process_clause).
      f_equal.
      apply IHp'.
    + (* rule clause *)
      simpl.
      let head_pred := predicate (Rule_head rule) in
      let matrix := translateRule p' rule in
      let matrix_map := buildDomainMap p' in
      let process_clause := processClause matrix_map c in
      rewrite <- (Map.insert_with_commute _ _ _ _ process_clause).
      f_equal.
      apply IHp'.
Qed.

Lemma computeFixpoint_unfold :
  forall (A : Type) (f : A -> A) (x : A),
    computeFixpoint f x = f (computeFixpoint f x).
Proof.
  intros A f x.
  functional induction (computeFixpoint f x).
  - (* base case: fixpoint reached *)
    reflexivity.
  - (* inductive case: not yet at fixpoint *)
    simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma Map_elements_correct :
  forall (A : Type) (m : Map A),
    Map.elements m = m.
Proof.
  intros A m.
  apply Map.elements_spec.
Qed.

Lemma translateDatalogProgram_unfold :
  forall p,
    translateDatalogProgram p = Map.elements (computeFixpoint (fun matrixMap => fold_left (processClause matrixMap) Map.empty (clauses p)) Map.empty).
Proof.
  intros p.
  unfold translateDatalogProgram.
  reflexivity.
Qed.

End SemanticsEvidence.

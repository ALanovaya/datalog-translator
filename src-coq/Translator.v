Require Import Coq.Maps.Map.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Setoids.SetoidArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.NArith.Nat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Sets.Set.
Require Import DatalogAST.
Require Import MatrixAST.

Module Translator.

(* Function to transpose and nub a list of lists *)
Fixpoint transposeAndNub (ts : list (list Term)) : list (list Term) :=
  map nub (transpose ts).

(* Function to transform the predicate map *)
Definition transformPredicateMap (m : Map.Map string (list (list Term))) : Map.Map string (list (list Term)) :=
  Map.map transposeAndNub m.

(* Function to get the sizes of each predicate *)
Definition predicateSizesMap (m : Map.Map string (list (list Term))) : Map.Map string (list nat) :=
  Map.map (map length) m.

(* Function to create a predicate map *)
Definition createPredicateMap (atoms : list Atom) : Map.Map string (list (list Term)) :=
  Map.fromListWith (zipWith (++) % map nub) [(predicate a, map (fun t => [t]) (terms a)) | a <- atoms].

(* Function to translate a list of atoms to a list of matrices *)
Definition translateAtomsToMatrices (atoms : list Atom) : list MatrixOp :=
  let predicateMap := createPredicateMap atoms in
  let predicateMap' := transformPredicateMap predicateMap in
  let emptyMatrices := Map.mapWithKey (fun _ dims => MatrixConst (mkMatrix dims (repeat 0 (product dims)))) (predicateSizesMap predicateMap') in
  let filledMatrices := Map.foldlWithKey (fun m k v => fillMatrix m k v) emptyMatrices predicateMap' in
  Map.elems filledMatrices.

(* Helper function to replace each element in a list with its position *)
Fixpoint replaceWithPositions (ts : list (list A)) : list (list nat) :=
  map (fun xs => enumFromTo 0 (length xs - 1)) ts.

(* Helper function to set a value at a given position in a MatrixAST.Matrix *)
Definition setMatrixValue (m : MatrixOp) (position : list nat) (value : A) : MatrixOp :=
  match m with
  | MatrixConst (mkMatrix dims matrixContent) =>
    let flatIndex := fold_left (fun acc (i, dim) => acc * dim + i) 0 (zip position dims) in
    MatrixConst (mkMatrix dims (take flatIndex matrixContent ++ [value] ++ drop (flatIndex + 1) matrixContent))
  | _ => error "setMatrixValue is not supported for this MatrixOp"
  end.

(* Rewritten fillMatrix function *)
Definition fillMatrix (emptyMatrices : Map.Map string MatrixOp) (predName : string) (ts : list (list Term)) : Map.Map string MatrixOp :=
  let indices := transpose (replaceWithPositions ts) in
  let matrix := Map.findWithDefault (error "Predicate not found") predName emptyMatrices in
  let updatedMatrix := fold_left (fun m idx => setMatrixValue m idx 1) matrix indices in
  Map.insert predName updatedMatrix emptyMatrices.

Definition buildDomainMap (program : DatalogProgram) : Map.Map string (list nat) :=
  fold_left (fun acc clause => updateDomainMap acc clause) Map.empty program.

Definition updateDomainMap (acc : Map.Map string (list nat)) (clause : Clause) :=
  match clause with
  | ClauseFact atom =>
    let termCounts := countUniqueTerms (terms atom) in
    let newDomainMap := Map.insert_with (zip_with max) (predicate atom) termCounts acc in
    Map.adjust (map (fun x => max 0 x)) (predicate atom) newDomainMap
  | _ => acc
  end.

Definition countUniqueTerms (ts : list Term) : list nat :=
  map (fun x => length (Set.toList (Set.fromList x))) (transpose (ts :: nil)).

Definition initializeMatrixForPredicate (domainMap : Map.Map string (list nat)) (atom : Atom) : MatrixAST.Matrix nat :=
  let dims := Map.find_with_default [] (predicate atom) domainMap in
  let numberOfCells := fold_left (fun acc x => acc * x) 1 dims in
  let cells := replicate numberOfCells 0 in
  MatrixAST.Matrix dims cells.

Definition translateRule (domainMap : Map.Map string (list nat)) (rule : Rule) : MatrixOp nat :=
  let termsList := map terms (body rule) in
  let filledMatrices := translateAtomsToMatrices (body rule) in
  let matricesWithTerms := combine filledMatrices termsList in
  let multipliedMatrix :=
    fold_left1
      (fun acc matrixTerms =>
         let (accMatrix, _) := acc in
         let (matrix, terms) := matrixTerms in
         let (da, db) := findRepeatingTermIndices terms (snd acc) in
         (Multiply da db accMatrix matrix, terms))
      matricesWithTerms
  in
  let headMatrixDimensions := Map.find_with_default [] (predicate (head rule)) domainMap in
  Extend (fst multipliedMatrix) headMatrixDimensions.

Definition findRepeatingTermIndices (listA listB : list Term) : (nat, nat) :=
  let duplicates := filter (fun x => In x listB) listA in
  let indexA := nth 0 (elem_indices (nth 0 duplicates) listA) 0 in
  let indexB := nth 0 (elem_indices (nth 0 duplicates) listB) 0 in
  (indexA, indexB).

Definition getDimensions (matrixOp : MatrixOp nat) : list nat :=
  match matrixOp with
  | MatrixConst matrix => dimensions matrix
  | _ => error "Unsupported operation"
  end.

Definition adjustDimensions (largerMatrixOp smallerMatrixOp : MatrixOp nat) : (list nat, MatrixOp nat) :=
  let largerDimensions := getDimensions largerMatrixOp in
  let smallerDimensions := getDimensions smallerMatrixOp in
  let updatedSmallerDims :=
    if length largerDimensions <> length smallerDimensions
      then smallerDimensions ++ replicate (length largerDimensions - length smallerDimensions) (last smallerDimensions)
      else smallerDimensions
  in
  let extendedSmallerMatrix := Extend smallerMatrixOp updatedSmallerDims in
  (updatedSmallerDims, extendedSmallerMatrix).

Definition adjustTerms (termsA : list Term) (updatedDimsA : list nat) : list Term :=
  let diff := length updatedDimsA - length termsA in
  termsA ++ replicate diff (Constant "0").

Definition multiplyMatricesAdjusted (matrixA matrixB : MatrixOp nat) (termsA termsB : list Term) : MatrixOp nat :=
  let (updatedDimsA, matrixA') := adjustDimensions matrixB matrixA in
  let (updatedDimsB, matrixB') := adjustDimensions matrixA matrixB in
  let updatedTermsA := adjustTerms termsA updatedDimsA in
  let updatedTermsB := adjustTerms termsB updatedDimsB in
  let (da, db) := findRepeatingTermIndices updatedTermsA updatedTermsB in
  Multiply da db matrixA' matrixB'.

Variable A : Type.

Fixpoint computeFixpoint (f : A -> A) (x : A) : A :=
  match f x with
  | y => if y = x then x else computeFixpoint f y
  end.

Fixpoint translateDatalogProgram (p : DatalogProgram) : list MatrixOp :=
  let domainMap := buildDomainMap p in
  let processClause (acc : Map string MatrixOp) (c : Clause) : Map string MatrixOp :=
    match c with
    | ClauseFact fact =>
      let factMatrix := hd (translateAtomsToMatrices [fact]) in
      let factPred := predicate fact in
      Map.insert_with (fun _ _ acc' => Add acc' (Extend (MatrixConst factMatrix) (getDimensions acc'))) factPred factMatrix acc
    | ClauseRule rule =>
      let headPred := predicate (Rule_head rule) in
      let matrix := translateRule p rule in
      Map.insert_with (fun _ _ acc' => Add acc' (Extend (MatrixConst matrix) (getDimensions acc'))) headPred matrix acc
    end
  in
  Map.elements (computeFixpoint (fun matrixMap => fold_left (processClause matrixMap) Map.empty (clauses p)) Map.empty).

End Translator.


Require Import Coq.Maps.Map.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Setoids.SetoidArith.
Require Import Coq.Setoids.Setoid.
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

End Translator.


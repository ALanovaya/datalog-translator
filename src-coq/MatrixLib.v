Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Peano.
Require Import Coq.Init.NaturalNumber.
Require Import Coq.Init.BinNumbers.
Require Import Coq.Init.Generics.
Require Import Coq.Init.Prelude.

Module MatrixLib.

Inductive Matrix (A : Type) : Type :=
| Leaf : A -> Matrix A
| Matrix : list nat -> list (Matrix A) -> Matrix A.

Arguments Leaf {_} _.
Arguments Matrix {_} _ _.

Fixpoint addMatrices {A} (a b : Matrix A) : Matrix A :=
  match a, b with
  | Leaf a, Leaf b => Leaf (a + b)
  | Matrix dimsA subMatricesA, Matrix dimsB subMatricesB =>
    if dimsA =? dimsB then
      Matrix dimsA (map2 addMatrices subMatricesA subMatricesB)
    else
      error "Matrices must have the same dimensions"
  | _, _ => error "Incompatible matrix shapes for addition"
  end.

Fixpoint slice {A} (starts stops : list nat) (m : Matrix A) : Matrix A :=
  match m with
  | Matrix dims ms =>
    if length starts =? length stops then
      if length starts =? length dims then
        let newDims := map2 (fun x y => y - x) starts stops in
        Matrix newDims (map (slice (tl starts) (tl stops)) (firstn (hd stops - hd starts) (skipn (hd starts) ms)))
      else
        error "Dimension mismatch"
    else
      error "Start and stop lists must be of equal length"
  | Leaf _ => m
  end.

Fixpoint increaseDimensions {A} (n : nat) (m : Matrix A) : Matrix A :=
  match m with
  | Matrix dims ms =>
    if n <=? 0 then m else
      Matrix (repeat 1 n ++ dims) [m]
  | Leaf a =>
    if n <=? 0 then Leaf a else
      Matrix (repeat 1 n) [Leaf a]
  end.

Fixpoint shape {A} (m : Matrix A) : list nat :=
  match m with
  | Leaf _ => []
  | Matrix dims _ => dims
  end.

Fixpoint index {A} (m : Matrix A) (idx : list nat) : A :=
  match m, idx with
  | Leaf a, [] => a
  | Matrix _ ms, i :: is => index (nth i ms) is
  | _, _ => error "Invalid index"
  end.

Fixpoint set {A} (m : Matrix A) (idx : list nat) (val : A) : Matrix A :=
  match m, idx with
  | Leaf _, [] => Leaf val
  | Matrix dims ms, i :: is =>
    Matrix dims (firstn i ms ++ [set (nth i ms) is val] ++ skipn (i + 1) ms)
  | _, _ => error "Invalid index"
  end.

Fixpoint removeIdx {A} (idx : nat) (xs : list A) : list A :=
  firstn (idx - 1) xs ++ skipn idx xs.

Fixpoint replace {A} (idx : nat) (newVal : A) (list : list A) : list A :=
  firstn (idx - 1) list ++ newVal :: skipn idx list.

Fixpoint multidimensionalMatrixMultiply {A} (da db : nat) (a b : Matrix A) : Matrix A :=
  let (da', db') := if da >? db then (db, da) else (da, db) in
  let aDims := shape a in
  let bDims := shape b in
  let otherADims := removeIdx db' (removeIdx da' aDims) in
  let otherBDims := removeIdx db' (removeIdx da' bDims) in
  let resultDims := replace db' (nth (db' - 1) bDims) aDims in
  let result := createZeroMatrix resultDims in
  let sharedDim := nth (db' - 1) aDims in
  if nth (da' - 1) bDims =? sharedDim && otherADims =? otherBDims then
    fold_left
      (updateResult a b da' db' sharedDim)
      result
      (allIndices resultDims)
  else
    error "Incompatible dimensions for multiplication".

Fixpoint allIndices (dims : list nat) : list (list nat) :=
  mapM (fun x => seq 0 (x - 1)) dims.

Fixpoint updateResult {a : Type} (aMatrix bMatrix da db sharedDim : nat)
                      (result : Matrix a) (idx : list nat) : Matrix a :=
  match aMatrix, bMatrix with
  | Leaf _, Leaf _ => Leaf _
  | Matrix _ ms1, Matrix _ ms2 =>
    let sumProduct :=
          Nat.fold_left
            (fun sum x => sum + (index result (replace (db + 1) x idx) *
                                 index bMatrix (replace (da + 1) x idx)))
            0 sharedDim
    in set result idx sumProduct
  | _, _ => Leaf _
  end.

End MatrixLib.

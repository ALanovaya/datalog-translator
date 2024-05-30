Require Import Coq.Lists.List.

Section MatrixDefinition.

Variable A : Type.

(* Matrix data type with dimension information *)
Record Matrix : Type := mkMatrix {
  dimensions : list nat;
  matrixData : list A
}.

(* AST for matrix operations *)
Inductive MatrixOp : Type :=
  | MatrixConst : Matrix -> MatrixOp            (* A constant matrix *)
  | Multiply : nat -> nat -> MatrixOp -> MatrixOp -> MatrixOp (* Matrix multiplication *)
  | Extend : MatrixOp -> list nat -> MatrixOp   (* Matrix extensions *)
  | Add : MatrixOp -> MatrixOp -> MatrixOp.     (* Matrix addition *)

End MatrixDefinition

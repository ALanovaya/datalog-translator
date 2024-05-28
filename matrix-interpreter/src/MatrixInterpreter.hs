module MatrixInterpreter where

import MatrixAST
import Matrix

-- Convert MatrixAST to Matrix
fromMatrixAST :: MatrixOp a -> Matrix.Matrix a
fromMatrixAST (MatrixConst matrixAST) = convert matrixAST
  where
    convert :: MatrixAST.Matrix a -> Matrix.Matrix a
    convert (MatrixAST.Matrix [] _) = error "Empty dimensions list"
    convert (MatrixAST.Matrix [_] [val]) = Matrix.Leaf val -- Single value case, Leaf node
    convert (MatrixAST.Matrix (d:ds) vals)
      | null ds = if length vals == d -- Base case for the last dimension
                    then Matrix.Matrix [d] (map Matrix.Leaf vals)
                    else error "Dimension values mismatch"
      | otherwise =
        let subMatrixSize = product ds
            subMatrices = map (convert . MatrixAST.Matrix ds) (takeChunks subMatrixSize vals)
        in Matrix.Matrix (d:ds) subMatrices
fromMatrixAST _ = error "Unsupported MatrixOp type"

takeChunks :: Int -> [a] -> [[a]]
takeChunks _ [] = []
takeChunks n xs = take n xs : takeChunks n (drop n xs)

extendMatrix :: [Int] -> Matrix.Matrix Int -> Matrix.Matrix Int
extendMatrix matrixDimensions matrix =
  let currentDimensions = shape matrix
      dimensionDiff = length matrixDimensions - length currentDimensions
   in case compare dimensionDiff 0 of
        GT -> increaseDimensions dimensionDiff matrix
        LT ->
          let sliceStarts = replicate (length currentDimensions) 0
              sliceEnds =
                matrixDimensions
                  ++ drop (length matrixDimensions) currentDimensions
           in slice sliceStarts sliceEnds matrix
        EQ -> matrix

evalMatrixOp :: MatrixOp Int -> Matrix.Matrix Int
evalMatrixOp (MatrixConst matrix) = fromMatrixAST (MatrixConst matrix)
evalMatrixOp (Multiply n m opA opB) =
  multidimensionalMatrixMultiply n m (evalMatrixOp opA) (evalMatrixOp opB)
evalMatrixOp (Add opA opB) =
  addMatrices (evalMatrixOp opA) (evalMatrixOp opB)
evalMatrixOp (Extend op dims) =
  extendMatrix dims (evalMatrixOp op)
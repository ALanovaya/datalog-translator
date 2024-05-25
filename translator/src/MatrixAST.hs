module MatrixAST where

-- Matrix data type with dimension information
data Matrix a = Matrix
  { dimensions :: [Int]
  , matrixData :: [a]
  } deriving (Show, Eq)

-- AST for matrix operations
data MatrixOp a
  = MatrixConst (Matrix a)                      -- A constant matrix
  | Multiply Int Int (MatrixOp a) (MatrixOp a)  -- Matrix multiplication
  | Extend (MatrixOp a) [Int]                   -- Matrix extensions
  | Add (MatrixOp a) (MatrixOp a)               -- Matrix addition
  deriving (Show, Eq)
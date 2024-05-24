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
  | Transpose (MatrixOp a) Int Int              -- Matrix transpose
  | Extend (MatrixOp a) [Int]                   -- Matrix extensions
  | Diagonalize (MatrixOp a) [Int] [Int]        -- Matrix diagonalization
  | Add (MatrixOp a) (MatrixOp a)               -- Matrix addition
  | Delete (MatrixOp a) Int                     -- Matrix deletion of dimension
  deriving (Show, Eq)
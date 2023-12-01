{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Matrix where

import Data.List.Split (chunksOf)
import Data.List (foldl')
import Language.Haskell.TH

-- Define the data type for n-dimensional matrices
data Matrix a = Matrix [Int] [Matrix a] | Leaf a
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- Generate a function to create an n-dimensional matrix
mkMatrix :: Int -> Q Exp
mkMatrix n
  | n <= 0 = fail "Invalid matrix dimension"
  | n == 1 = [| \x -> Matrix [1] [Leaf x] |]
  | otherwise = do
      inner <- mkMatrix (n - 1)
      let innerExp = lamE [varP (mkName "x")] (appE (return inner) (varE (mkName "x")))
      [| \x -> Matrix (n : map length x) (map $innerExp x) |]

flatten :: Matrix a -> [a]
flatten (Leaf a) = [a]
flatten (Matrix _ ms) = concatMap flatten ms

reshape :: [Int] -> [a] -> Matrix a
reshape [] _ = error "Invalid dimensions"
reshape [n] xs 
  | length xs == n = Matrix [n] $ map Leaf xs
  | otherwise = error "Dimension size does not match number of elements"
reshape (n:ns) xs 
  | mod (length xs) productNs == 0 = Matrix (n:ns) (map (reshape ns . take productNs) (chunksOf productNs xs))
  | otherwise = error "Dimension size does not match number of elements"
  where productNs = product ns

slice :: Int -> Int -> Matrix a -> Matrix a
slice start stop (Matrix dims ms) = Matrix (take (stop - start) $ drop start dims) (take (stop - start) $ drop start ms)
slice _ _ leaf@(Leaf _) = leaf

sliceN :: Int -> Q Dec
sliceN n = do
  let name = mkName $ "slice" ++ show n
  funD name [clause [varP (mkName "start"), varP (mkName "stop"), varP (mkName "m")]
                    (normalB [|slice start stop m|])
                    []]

increaseDimensions :: Int -> Matrix a -> Matrix a
increaseDimensions n mat@(Matrix dims _) = Matrix (replicate n 1 ++ dims) (replicate n mat)
increaseDimensions _ (Leaf _) = error "Cannot increase dimensions on a leaf node"

shape :: Matrix a -> [Int]
shape (Leaf _) = []
shape (Matrix dims _) = dims

index :: Matrix a -> [Int] -> a
index (Leaf a) [] = a
index (Matrix _ ms) (i:is) = index (ms !! i) is
index _ _ = error "Invalid index"

set :: Matrix a -> [Int] -> a -> Matrix a
set (Leaf _) [] val = Leaf val
set (Matrix dims ms) (i:is) val = Matrix dims (take i ms ++ [set (ms !! i) is val] ++ drop (i + 1) ms)
set _ _ _ = error "Invalid index"

createZeroMatrix :: Num a => [Int] -> Matrix a
createZeroMatrix dims = reshape dims (repeat 0)

removeIdx :: Int -> [a] -> [a]
removeIdx idx xs = take (idx - 1) xs ++ drop idx xs

replace :: Int -> a -> [a] -> [a]
replace idx newVal list = take (idx - 1) list ++ [newVal] ++ drop idx list

multidimensionalMatrixMultiply :: Num a => Int -> Int -> Matrix a -> Matrix a -> Matrix a
multidimensionalMatrixMultiply da db a b = 
  let (da', db') = if da > db then (db, da) else (da, db)
      aDims = shape a
      bDims = shape b
      otherADims = removeIdx db' $ removeIdx da' aDims
      otherBDims = removeIdx db' $ removeIdx da' bDims
      resultDims = replace db' (bDims !! (db' - 1)) aDims
      result = createZeroMatrix resultDims
      sharedDim = aDims !! (db' - 1)
  in if bDims !! (da' - 1) /= sharedDim || otherADims /= otherBDims
     then error "Incompatible dimensions for multiplication"
     else foldl' (updateResult a b da' db' sharedDim) result (allIndices resultDims)

-- Helper to generate all possible indices for a given shape
allIndices :: [Int] -> [[Int]]
allIndices dims = sequence (map (\x -> [0..x-1]) dims)

-- Helper to update the result matrix
updateResult :: Num a => Matrix a -> Matrix a -> Int -> Int -> Int -> Matrix a -> [Int] -> Matrix a
updateResult a b da db sharedDim result idx = 
  let sumProduct = sum [index a (updateIndex idx db x) * index b (updateIndex idx da x) | x <- [0..sharedDim-1]]
  in set result idx sumProduct

-- Helper to replace the element at the specified index
updateIndex :: [Int] -> Int -> Int -> [Int]
updateIndex idx pos val = take pos idx ++ [val] ++ drop (pos + 1) idx
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Matrix where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- Define the data type for n-dimensional matrices
data Matrix a = Matrix [Matrix a] | Leaf a

-- Generate a function to create an n-dimensional matrix
mkMatrix :: Int -> Q Exp
mkMatrix n
  | n <= 0 = fail "Invalid matrix dimension"
  | n == 1 = [| Leaf |]
  | otherwise = [| Matrix |] `appE` [| replicateM |] `appE` [| n |] `appE` mkMatrix (n-1)

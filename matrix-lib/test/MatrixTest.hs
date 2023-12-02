module Main where

import Matrix
import System.Exit as Exit
import Test.HUnit

-- Test case for 'generateMatrix'
testGenerateMatrix =
  TestCase $ do
    let expected = Matrix [2] [Leaf 1, Leaf 1]
    assertEqual "generateMatrix 1 [2]" expected (generateMatrix 1 [2])

-- Test case for 'flatten'
testFlatten =
  TestCase $ do
    let matrix = Matrix [2] [Leaf 1, Leaf 2]
    assertEqual "flatten Matrix" [1, 2] (flatten matrix)

-- Test case for 'reshape'
testReshape =
  TestCase $ do
    let list = [1, 2, 3, 4]
    let expected =
          Matrix
            [2, 2]
            [Matrix [2] [Leaf 1, Leaf 2], Matrix [2] [Leaf 3, Leaf 4]]
    assertEqual "reshape [2, 2] list" expected (reshape [2, 2] list)

-- Test case for 'slice'
testSlice =
  TestCase $ do
    let matrix = Matrix [3] [Leaf 1, Leaf 2, Leaf 3]
    let expected = Matrix [2] [Leaf 2, Leaf 3]
    assertEqual "slice [1] [3] matrix" expected (slice [1] [3] matrix)

-- Test case for 'increaseDimensions'
testIncreaseDimensions =
  TestCase $ do
    let matrix = Matrix [2] [Leaf 1, Leaf 2]
    let expected = Matrix [1, 1, 2] [Matrix [1, 2] [Leaf 1, Leaf 2]]
    assertEqual
      "increaseDimensions 2 matrix"
      expected
      (increaseDimensions 2 matrix)

-- Test case for 'shape'
testShape =
  TestCase $ do
    let matrix = Matrix [2, 2] []
    assertEqual "shape matrix" [2, 2] (shape matrix)

-- Test case for 'index'
testIndex =
  TestCase $ do
    let matrix = Matrix [2] [Leaf 1, Leaf 2]
    assertEqual "index matrix [1]" 2 (index matrix [1])

-- Test case for 'set'
testSet =
  TestCase $ do
    let matrix = Matrix [2] [Leaf 1, Leaf 2]
    let expected = Matrix [2] [Leaf 1, Leaf 5]
    assertEqual "set matrix [1] 5" expected (set matrix [1] 5)

-- Test case for 'createZeroMatrix'
testCreateZeroMatrix =
  TestCase $ do
    let expected =
          Matrix
            [2, 2]
            [Matrix [2] [Leaf 0, Leaf 0], Matrix [2] [Leaf 0, Leaf 0]]
    assertEqual "createZeroMatrix [2, 2]" expected (createZeroMatrix [2, 2])

-- Test case for 'multidimensionalMatrixMultiply'
testMultidimensionalMatrixMultiply =
  TestCase $ do
    let matrixA =
          Matrix
            [2, 2]
            [Matrix [2] [Leaf 1, Leaf 2], Matrix [2] [Leaf 3, Leaf 4]]
    let matrixB =
          Matrix
            [2, 2]
            [Matrix [2] [Leaf 5, Leaf 6], Matrix [2] [Leaf 7, Leaf 8]]
    let expected =
          Matrix
            [2, 2]
            [Matrix [2] [Leaf 19, Leaf 22], Matrix [2] [Leaf 43, Leaf 50]]
    assertEqual
      "multidimensionalMatrixMultiply 2 2 matrixA matrixB"
      expected
      (multidimensionalMatrixMultiply 2 2 matrixA matrixB)

tests :: Test
tests =
  TestList
    [ TestLabel "testGenerateMatrix" testGenerateMatrix
    , TestLabel "testFlatten" testFlatten
    , TestLabel "testReshape" testReshape
    , TestLabel "testSlice" testSlice
    , TestLabel "testIncreaseDimensions" testIncreaseDimensions
    , TestLabel "testShape" testShape
    , TestLabel "testIndex" testIndex
    , TestLabel "testSet" testSet
    , TestLabel "testCreateZeroMatrix" testCreateZeroMatrix
    , TestLabel
        "testMultidimensionalMatrixMultiply"
        testMultidimensionalMatrixMultiply
    ]

main :: IO ()
main = do
  result <- runTestTT tests
  if failures result > 0
    then Exit.exitFailure
    else Exit.exitSuccess

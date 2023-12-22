module Translator where

import Data.List (elemIndices, foldl', foldl1', transpose)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DatalogAST
import Matrix

-- Function to build a domain map for variables 
buildDomainMap :: DatalogProgram -> Map.Map String [Int]
buildDomainMap (DatalogProgram clauses) =
  foldl' updateDomainMap Map.empty clauses
  where
    updateDomainMap acc (ClauseFact (Atom predicateName ts)) =
      let termCounts = countUniqueTerms ts
          newDomainMap =
            Map.insertWith (zipWith max) predicateName termCounts acc
       in Map.adjust (zipWith max (repeat 0)) predicateName newDomainMap
    updateDomainMap acc _ = acc

countUniqueTerms :: [Term] -> [Int]
countUniqueTerms ts = length . Set.toList . Set.fromList <$> transpose [ts]

-- A function that creates a matrix for a given predicate based on the terms it involves
initializeMatrixForPredicate :: Map.Map String [Int] -> Atom -> Matrix Int
initializeMatrixForPredicate domainMap (Atom predicateName _) =
  let dimensions = Map.findWithDefault [] predicateName domainMap
   in createZeroMatrix dimensions

translateRule :: Map.Map String [Int] -> Rule -> Matrix Int
translateRule domainMap (Rule headAtom bodyAtoms) =
  let termsList = map terms bodyAtoms -- Extract terms from each bodyAtom
      bodyMatrices = map (initializeMatrixForPredicate domainMap) bodyAtoms
      matricesWithTerms = zip bodyMatrices termsList -- Pair each matrix with its terms
      multipliedMatrix =
        foldl1'
          (\acc (matrix, bodyTerms) ->
             let (accMatrix, _) = acc -- Extract the Matrix Int part from the tuple
              in ( multiplyMatricesAdjusted accMatrix matrix bodyTerms bodyTerms
                 , bodyTerms))
          matricesWithTerms
      headMatrixDimensions =
        Map.findWithDefault [] (predicate headAtom) domainMap
   in adjustFinalMatrix headMatrixDimensions (fst multipliedMatrix)

findRepeatingTermIndices :: [Term] -> [Term] -> (Int, Int)
findRepeatingTermIndices listA listB =
  let duplicates = filter (`elem` listB) listA
      indexA = Prelude.head $ elemIndices (Prelude.head duplicates) listA
      indexB = Prelude.head $ elemIndices (Prelude.head duplicates) listB
   in (indexA, indexB)

adjustDimensions :: Matrix Int -> Matrix Int -> ([Int], Matrix Int)
adjustDimensions largerMatrix smallerMatrix =
  let largerDimensions = shape largerMatrix
      smallerDimensions = shape smallerMatrix
      updatedSmallerDims =
        if length largerDimensions /= length smallerDimensions
          then take (length largerDimensions)
                 $ smallerDimensions ++ repeat (Prelude.head largerDimensions)
          else smallerDimensions
      flattenedSmallerMatrix = flatten smallerMatrix
      reshapedSmallerMatrix = reshape updatedSmallerDims flattenedSmallerMatrix
   in (updatedSmallerDims, reshapedSmallerMatrix)

adjustTerms :: [Term] -> [Int] -> [Term]
adjustTerms termsA updatedDimsA =
  let diff = length updatedDimsA - length termsA
   in replicate diff (Constant "0") ++ termsA

multiplyMatricesAdjusted ::
     Matrix Int -> Matrix Int -> [Term] -> [Term] -> Matrix Int
multiplyMatricesAdjusted matrixA matrixB termsA termsB =
  let (updatedDimsA, matrixA') = adjustDimensions matrixB matrixA -- assuming matrixB is larger
      (updatedDimsB, matrixB') = adjustDimensions matrixA matrixB -- assuming matrixA is larger
      updatedTermsA = adjustTerms termsA updatedDimsA -- fix it later
      updatedTermsB = adjustTerms termsB updatedDimsB
      (da, db) = findRepeatingTermIndices updatedTermsA updatedTermsB
   in multidimensionalMatrixMultiply da db matrixA' matrixB'

adjustFinalMatrix :: [Int] -> Matrix Int -> Matrix Int
adjustFinalMatrix headMatrixDimensions matrix =
  let currentDimensions = shape matrix
      dimensionDiff = length headMatrixDimensions - length currentDimensions
   in case compare dimensionDiff 0 of
        GT -> increaseDimensions dimensionDiff matrix
        LT ->
          let sliceStarts = replicate (length currentDimensions) 0
              sliceEnds =
                headMatrixDimensions
                  ++ drop (length headMatrixDimensions) currentDimensions
           in slice sliceStarts sliceEnds matrix
        EQ -> matrix

-- The main translation function that translates a DatalogProgram to a list of matrices
translateDatalogProgram :: DatalogProgram -> [Matrix Int]
translateDatalogProgram (DatalogProgram clauses) =
  let domainMap = buildDomainMap (DatalogProgram clauses)
      processClause acc (ClauseFact _) = acc
      processClause acc (ClauseRule rule) =
        let headPred = predicate (DatalogAST.head rule)
            matrix = translateRule domainMap rule
            updatedMatrix =
              Map.insertWith addAdjustedMatrices headPred matrix acc
         in updatedMatrix
      addAdjustedMatrices newMatrix oldMatrix =
        let adjustedMatrix = adjustFinalMatrix (shape oldMatrix) newMatrix
            adjustedMatrixOld = adjustFinalMatrix (shape newMatrix) oldMatrix
         in addMatrices adjustedMatrix adjustedMatrixOld
      initialMatrixMap = Map.empty
      finalMatrixMap = foldl' processClause initialMatrixMap clauses
   in Map.elems finalMatrixMap

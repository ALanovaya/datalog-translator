module Translator where

import Data.List (elemIndices, foldl', foldl1', transpose, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DatalogAST
import MatrixAST

-- Function to transpose and nub a list of lists
transposeAndNub :: [[Term]] -> [[Term]]
transposeAndNub = map nub . transpose

-- Function to transform the predicate map
transformPredicateMap :: Map.Map String [[Term]] -> Map.Map String [[Term]]
transformPredicateMap = Map.map transposeAndNub

-- Function to get the sizes of each predicate
predicateSizesMap :: Map.Map String [[Term]] -> Map.Map String [Int]
predicateSizesMap = Map.map (map length)

-- Function to create a predicate map
createPredicateMap :: [Atom] -> Map.Map String [[Term]]
createPredicateMap atoms = Map.fromListWith (zipWith (++) . map nub) [(predicate atom, map (:[]) $ terms atom) | atom <- atoms]

-- Function to translate a list of atoms to a list of matrices
translateAtomsToMatrices :: [Atom] -> [MatrixOp Int]
translateAtomsToMatrices atoms =
  let predicateMap = createPredicateMap atoms
      predicateMap' = transformPredicateMap predicateMap
      emptyMatrices = Map.mapWithKey (\_ dims -> MatrixConst (MatrixAST.Matrix dims (replicate (product dims) 0))) (predicateSizesMap predicateMap')
      filledMatrices = Map.foldlWithKey' fillMatrix emptyMatrices predicateMap'
  in Map.elems filledMatrices

-- Helper function to replace each element in a list with its position
replaceWithPositions :: [[a]] -> [[Int]]
replaceWithPositions = map (\xs -> enumFromTo 0 (length xs - 1))

-- Helper function to set a value at a given position in a MatrixAST.Matrix
setMatrixValue :: MatrixOp Int -> [Int] -> Int -> MatrixOp Int
setMatrixValue (MatrixConst (MatrixAST.Matrix dims matrixContent)) position value =
  let flatIndex = foldl' (\acc (i, dim) -> acc * dim + i) 0 (zip position dims)
  in MatrixConst (MatrixAST.Matrix dims (take flatIndex matrixContent ++ [value] ++ drop (flatIndex + 1) matrixContent))
setMatrixValue _ _ _ = error "setMatrixValue is not supported for this MatrixOp"

-- Rewritten fillMatrix function
fillMatrix :: Map.Map String (MatrixOp Int) -> String -> [[Term]] -> Map.Map String (MatrixOp Int)
fillMatrix emptyMatrices predName ts =
  let indices = transpose . replaceWithPositions $ ts
      matrix = Map.findWithDefault (error "Predicate not found") predName emptyMatrices
      updatedMatrix = foldl' (\m idx -> setMatrixValue m idx 1) matrix indices
  in Map.insert predName updatedMatrix emptyMatrices

-- Function to build a domain map for variables 
buildDomainMap :: DatalogProgram -> Map.Map String [Int]
buildDomainMap (DatalogProgram clauses) =
  foldl' updateDomainMap Map.empty clauses
  where
    updateDomainMap acc (ClauseFact (Atom predicateName ts)) =
      let termCounts = countUniqueTerms ts
          newDomainMap =
            Map.insertWith (zipWith max) predicateName termCounts acc
       in Map.adjust (map (max 0)) predicateName newDomainMap
    updateDomainMap acc _ = acc

-- Function to count the number of unique terms
countUniqueTerms :: [Term] -> [Int]
countUniqueTerms ts = length . Set.toList . Set.fromList <$> transpose [ts]

-- A function that creates a matrix for a given predicate based on the terms it involves
initializeMatrixForPredicate :: Map.Map String [Int] -> Atom -> MatrixAST.Matrix Int
initializeMatrixForPredicate domainMap (Atom predicateName _) =
  let dims = Map.findWithDefault [] predicateName domainMap
      numberOfCells = product dims
      cells = replicate numberOfCells 0
  in MatrixAST.Matrix dims cells                  

-- Function to translate a rule
translateRule :: Map.Map String [Int] -> Rule -> MatrixOp Int
translateRule domainMap (Rule headAtom bodyAtoms) =
  let termsList = map terms bodyAtoms -- Extract terms from each bodyAtom
      filledMatrices = translateAtomsToMatrices bodyAtoms
      matricesWithTerms = zip filledMatrices termsList -- Pair each matrix with its terms
      multipliedMatrix =
        foldl1'
          (\acc (matrix, bodyTerms) ->
             let (accMatrix, _) = acc -- Extract the MatrixAST.Matrix Int part from the tuple
              in ( multiplyMatricesAdjusted accMatrix matrix bodyTerms bodyTerms
                 , bodyTerms))
          matricesWithTerms
      headMatrixDimensions =
        Map.findWithDefault [] (predicate headAtom) domainMap
  in Extend (fst multipliedMatrix) headMatrixDimensions

-- Function to find the indices of the repeating terms
findRepeatingTermIndices :: [Term] -> [Term] -> (Int, Int)
findRepeatingTermIndices listA listB =
  let duplicates = filter (`elem` listB) listA
      indexA = Prelude.head $ elemIndices (Prelude.head duplicates) listA
      indexB = Prelude.head $ elemIndices (Prelude.head duplicates) listB
   in (indexA, indexB)

-- Function to get the dimensions of a matrix
getDimensions :: MatrixOp a -> [Int]
getDimensions matrixOp = case matrixOp of
  MatrixConst matrix -> dimensions matrix
  _ -> error "Unsupported operation"

-- Function to adjust the dimensions of a matrix
adjustDimensions :: MatrixOp Int -> MatrixOp Int -> ([Int], MatrixOp Int)
adjustDimensions largerMatrixOp smallerMatrixOp =
  let largerDimensions = getDimensions largerMatrixOp
      smallerDimensions = getDimensions smallerMatrixOp
      updatedSmallerDims =
        if length largerDimensions /= length smallerDimensions
          then take (length largerDimensions)
                 $ smallerDimensions ++ repeat (Prelude.head largerDimensions)
          else smallerDimensions
      extendedSmallerMatrix = Extend smallerMatrixOp updatedSmallerDims
   in (updatedSmallerDims, extendedSmallerMatrix)

-- Function to adjust the dimensions of a term
adjustTerms :: [Term] -> [Int] -> [Term]
adjustTerms termsA updatedDimsA =
  let diff = length updatedDimsA - length termsA
   in replicate diff (Constant "0") ++ termsA

-- Function to multiply two matrices
multiplyMatricesAdjusted ::
     MatrixOp Int -> MatrixOp Int -> [Term] -> [Term] -> MatrixOp Int
multiplyMatricesAdjusted matrixA matrixB termsA termsB =
  let (updatedDimsA, matrixA') = adjustDimensions matrixB matrixA -- assuming matrixB is larger
      (updatedDimsB, matrixB') = adjustDimensions matrixA matrixB -- assuming matrixA is larger
      updatedTermsA = adjustTerms termsA updatedDimsA
      updatedTermsB = adjustTerms termsB updatedDimsB
      (da, db) = findRepeatingTermIndices updatedTermsA updatedTermsB
   in Multiply da db matrixA' matrixB'

-- Function to compute the fixpoint of a function
computeFixpoint :: Eq a => (a -> a) -> a -> a
computeFixpoint f x
  | x == next = x
  | otherwise = computeFixpoint f next
  where next = f x

-- The main translation function that translates a DatalogProgram to a list of matrices
translateDatalogProgram :: DatalogProgram -> [MatrixOp Int]
translateDatalogProgram (DatalogProgram clauses) =
  let domainMap = buildDomainMap (DatalogProgram clauses)
      processClause acc (ClauseFact fact) =
        let factMatrix = Prelude.head (translateAtomsToMatrices [fact])
            factPred = predicate fact
            updatedMatrix =
              Map.insertWith addAdjustedMatrices factPred factMatrix acc
         in updatedMatrix
      processClause acc (ClauseRule rule) =
        let headPred = predicate (DatalogAST.head rule)
            matrix = translateRule domainMap rule
            updatedMatrix =
              Map.insertWith addAdjustedMatrices headPred matrix acc
         in updatedMatrix
      addAdjustedMatrices newMatrix oldMatrix =
        let adjustedMatrix = Extend newMatrix (getDimensions oldMatrix) 
            adjustedMatrixOld = Extend oldMatrix (getDimensions newMatrix)
         in Add adjustedMatrix adjustedMatrixOld
      initialMatrixMap = Map.empty
      finalMatrixMap = computeFixpoint (\matrixMap -> foldl' processClause matrixMap clauses) initialMatrixMap
   in Map.elems finalMatrixMap


module Main where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import DatalogAST
import Translator
import Interpreter
import Matrix
import System.Exit (exitFailure)

genTerm :: Gen Term
genTerm = Gen.choice [ Variable <$> Gen.string (Range.linear 1 10) Gen.alphaNum
                     , Constant <$> Gen.string (Range.linear 1 10) Gen.alphaNum
                     ]

genAtom :: Gen Atom
genAtom = Atom <$> Gen.string (Range.linear 1 10) Gen.alphaNum <*> Gen.list (Range.linear 1 5) genTerm

genRule :: Gen Rule
genRule = Rule <$> genAtom <*> Gen.list (Range.linear 1 5) genAtom

genFact :: Gen Fact
genFact = genAtom

genClause :: Gen Clause
genClause = Gen.choice [ ClauseFact <$> genFact
                       , ClauseRule <$> genRule
                       ]

genDatalogProgram :: Gen DatalogProgram
genDatalogProgram = DatalogProgram <$> Gen.list (Range.linear 1 10) genClause

genQuery :: Gen Query
genQuery = Query <$> genAtom

compareResults :: Eq a => [Matrix a] -> [Matrix a] -> Bool
compareResults translatedInterpretedResult translatedResult =
    length translatedInterpretedResult == length translatedResult &&
    and (zipWith (==) translatedInterpretedResult translatedResult)

testTranslateInterpretAST :: Property
testTranslateInterpretAST = property $ do
  program <- forAll genDatalogProgram
  let translatedResult = translateDatalogProgram program
  let interpretedResult = executeProgram program
  let translatedInterpretedResult = translateAtomsToMatrices (interpretedResult)
  assert $ compareResults translatedInterpretedResult translatedResult

main :: IO ()
main = do
  result <- check testTranslateInterpretAST
  if result
    then putStrLn "All tests passed!"
    else exitFailure

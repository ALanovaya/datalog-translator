import Test.HUnit
import Interpreter
import DatalogAST
import qualified Data.Map as Map

-- Test for applySubstTerm function
testApplySubstTermVariable :: Test
testApplySubstTermVariable = TestCase $ do
  let subst = Map.fromList [("x", "1"), ("y", "2")]
  let term = Variable "x"
  let expected = Constant "1"
  assertEqual "applySubstTerm should substitute variable with its constant value"
    expected (applySubstTerm subst term)

testApplySubstTermConstant :: Test
testApplySubstTermConstant = TestCase $ do
  let subst = Map.fromList [("x", "1"), ("y", "2")]
  let term = Constant "3"
  assertEqual "applySubstTerm with constant should leave term unchanged"
    term (applySubstTerm subst term)

-- Test for isFact function
testIsFactTrue :: Test
testIsFactTrue = TestCase $ do
  let atom = Atom "pred" [Constant "1", Constant "2"]
  assertBool "isFact should return True for an atom with only constants" (isFact atom)

testIsFactFalse :: Test
testIsFactFalse = TestCase $ do
  let atom = Atom "pred" [Variable "x", Constant "2"]
  assertBool "isFact should return False for an atom with variables" (not $ isFact atom)

-- More tests for applySubstAtom function
testApplySubstAtom :: Test
testApplySubstAtom = TestCase $ do
  let subst = Map.fromList [("x", "1"), ("y", "2")]
  let atom = Atom "pred" [Variable "x", Variable "y", Constant "3"]
  let expected = Atom "pred" [Constant "1", Constant "2", Constant "3"]
  assertEqual "applySubstAtom should apply substitution to all terms in the atom"
    expected (applySubstAtom subst atom)

-- Assuming there is a 'generateDatabase' function that creates a simple Database for testing
generateDatabase :: Database
generateDatabase = [Atom "pred" [Constant "1", Constant "2"],
                    Atom "pred" [Constant "3", Constant "4"]]

-- Tests for evaluateQuery function with the Query type from your Datalog AST
testEvaluateQueryMatch :: Test
testEvaluateQueryMatch = TestCase $ do
  let db = generateDatabase
  let query = Query (Atom "pred" [Variable "x", Constant "2"])
  let expected = [Map.fromList [("x", "1")]] -- Expected substitution that makes query a fact in the db
  assertEqual "evaluateQuery should return correct substitutions for matching queries"
    expected (evaluateQuery db query)

testEvaluateQueryNoMatch :: Test
testEvaluateQueryNoMatch = TestCase $ do
  let db = generateDatabase
  let query = Query (Atom "pred" [Variable "x", Constant "5"]) -- This value does not exist in the db
  let expected = [] -- No substitutions should be returned
  assertEqual "evaluateQuery should return empty list when no matches found"
    expected (evaluateQuery db query)

testApplyRule :: Test
testApplyRule = TestCase $ do
  -- Create a simple database with some facts
  let database = [Atom "parent" [Constant "Alice", Constant "Bob"],
                  Atom "parent" [Constant "Bob", Constant "Charlie"]]
  -- Create a rule: grandparent(X, Y) :- parent(X, Z), parent(Z, Y).
  let rule = Rule (Atom "grandparent" [Variable "X", Variable "Y"])
                  [Atom "parent" [Variable "X", Variable "Z"],
                   Atom "parent" [Variable "Z", Variable "Y"]]
  let expected = [Atom "grandparent" [Constant "Alice", Constant "Charlie"]]
  let result = applyRule database rule
  assertEqual "applyRule should produce the correct grandparent relationship"
    expected result

-- Update the extendedTests group to include the fixed tests
extendedTests :: Test
extendedTests = TestList [TestLabel "testApplySubstTermVariable" testApplySubstTermVariable,
                          TestLabel "testApplySubstTermConstant" testApplySubstTermConstant,
                          TestLabel "testIsFactTrue" testIsFactTrue,
                          TestLabel "testIsFactFalse" testIsFactFalse,
                          TestLabel "testApplySubstAtom" testApplySubstAtom,
                          TestLabel "testEvaluateQueryMatch" testEvaluateQueryMatch,
                          TestLabel "testEvaluateQueryNoMatch" testEvaluateQueryNoMatch,
                          TestLabel "testApplyRule" testApplyRule]

-- Main function to run the extended tests
main :: IO Counts
main = runTestTT extendedTests
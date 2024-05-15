module Interpreter where

import Control.Monad (foldM)
import Data.List (delete, nub, (\\))
import qualified Data.Map as Map
import qualified Data.Set as Set
import DatalogAST

-- A Database is a set of facts
type Database = Set.Set Fact

-- A Substitution is a mapping from variable names to constants
type Substitution = Map.Map String Term

-- Evaluate an Atom
evaluateAtom :: Atom -> Database -> Substitution -> [Substitution]
evaluateAtom (Atom pr ts) db subs =
  let matchedFacts = matchPredicate (Atom pr ts) db
      unifiedSubstitutions = concatMap (unifyWithFact ts) matchedFacts
   in concatMap (composeSubstitutions subs) unifiedSubstitutions

-- Unify a list of terms with a fact to produce a substitution
unifyWithFact :: [Term] -> Fact -> [Substitution]
unifyWithFact queryTerms (Atom _ factTerms) =
  foldM unifyPairs Map.empty (zip queryTerms factTerms)

-- Try to unify two terms and update the substitution
unifyPairs :: Substitution -> (Term, Term) -> [Substitution]
unifyPairs subs (Variable var, term) =
  case Map.lookup var subs of
    Just term' -> ([subs | term == term'])
    Nothing -> [Map.insert var term subs]
unifyPairs subs (term, Variable var) = unifyPairs subs (Variable var, term)
unifyPairs subs (Constant const1, Constant const2) = [subs | const1 == const2]

-- Filter the database for facts that match the given predicate atom
matchPredicate :: Atom -> Database -> Set.Set Fact
matchPredicate (Atom name ts) = Set.filter matchFact
  where
    matchFact (Atom factName factTerms) =
      name == factName && length ts == length factTerms

-- Compose two substitutions together
composeSubstitutions :: Substitution -> Substitution -> [Substitution]
composeSubstitutions sub1 sub2
  | hasConflicts sub1 sub2 = [sub1, sub2]
  | otherwise =
      let sub1AppliedToSub2 = Map.map (recursiveApply sub1) sub2
          combinedSubs = Map.union sub1AppliedToSub2 sub1
       in [Map.map (recursiveApply combinedSubs) combinedSubs]

-- Check for conflicts between the two substitutions
hasConflicts :: Substitution -> Substitution -> Bool
hasConflicts sub1 sub2 =
  allKeysInAnotherMap && noConflictingValues && noVariableAsKey
  where
    allKeysInAnotherMap =
      Map.keysSet sub1 `Set.isSubsetOf` Map.keysSet sub2
        || Map.keysSet sub2 `Set.isSubsetOf` Map.keysSet sub1
    noConflictingValues =
      any conflicts (Map.keysSet sub1 `Set.union` Map.keysSet sub2)
    conflicts key =
      case (Map.lookup key sub1, Map.lookup key sub2) of
        (Just (Constant val1), Just (Constant val2)) -> val1 /= val2
        (Just (Variable _), Just _) -> True
        (Just _, Just (Variable _)) -> True
        _ -> False
    noVariableAsKey =
      let allVars = [v | Variable v <- Map.elems sub1 ++ Map.elems sub2]
       in not $
            any (`Map.member` sub1) allVars || any (`Map.member` sub2) allVars

-- Recursive function to apply substitutions until a constant is found or no further substitutions can be made
recursiveApply :: Substitution -> Term -> Term
recursiveApply subs term@(Variable var) =
  case Map.lookup var subs of
    Just nextTerm@(Variable _) -> recursiveApply subs nextTerm
    Just constant@(Constant _) -> constant
    Nothing -> term
recursiveApply _ term@(Constant _) = term

-- Apply a substitution to a term
applySubstitution :: Substitution -> Term -> Term
applySubstitution subs term@(Variable var) = Map.findWithDefault term var subs
applySubstitution _ term@(Constant _) = term

-- Apply a substitution to an atom
applySubstitutionToAtom :: Substitution -> Atom -> Atom
applySubstitutionToAtom subs (Atom predName ts) =
  Atom predName (map (applySubstitution subs) ts)

-- Evaluate a Rule
evaluateRule :: Database -> Substitution -> Rule -> Bool
evaluateRule db subs (Rule {DatalogAST.head = headAtom, body = bodyAtoms}) =
  all (\atom -> not (null (evaluateAtom atom db subs))) bodyAtoms
    && isHeadSatisfied
  where
    substitutedHead = applySubstitutionToAtom subs headAtom
    isHeadSatisfied = Set.member substitutedHead db

-- Check if the first substitution is a subset of the second
isSubsetOf :: Substitution -> Substitution -> Bool
isSubsetOf sub1 sub2 =
  all (`Map.member` sub2) (Map.keys sub1)
    && all (\k -> Map.lookup k sub1 == Map.lookup k sub2) (Map.keys sub1)

-- Evaluate the body of a rule
evaluateBody :: Database -> Substitution -> [Atom] -> [Substitution]
evaluateBody db initialSubs atoms =
  let allVars = Set.fromList $ concatMap getVarsFromAtom atoms
      uniqueVarCount = Set.size allVars
      subs =
        concatMap
          (\atom -> evaluateAtom atom db initialSubs)
          atoms
      filteredSubs =
        filter
          (\sub -> not $ any (sub `isSubsetOf`) (delete sub subs))
          subs
      composedSubs = composeAllSubs filteredSubs
      consistentSubs = filter isConsistent composedSubs
      correctSizeSubs =
        filter (\sub -> Map.size sub == uniqueVarCount) consistentSubs
   in nub correctSizeSubs
  where
    composeAllSubs subs =
      let pairs = [(x, y) | x <- subs, y <- subs, x /= y]
          composedPairs = nub $ concatMap (uncurry composeSubstitutions) pairs
          newSubs = nub (subs ++ composedPairs)
       in if null (newSubs \\ subs)
            then subs
            else composeAllSubs newSubs
    isConsistent sub =
      let constants = Map.elems sub
       in length constants == length (nub constants)

getVarsFromAtom :: Atom -> [String]
getVarsFromAtom (Atom _ ts) = concatMap getVarsFromTerm ts

getVarsFromTerm :: Term -> [String]
getVarsFromTerm (Variable var) = [var]
getVarsFromTerm (Constant _) = []

-- Apply a Rule to a Database
applyRule :: Rule -> Database -> Database
applyRule rule db =
  let bodySubstitutions = evaluateBody db Map.empty (body rule)
      newFacts =
        filter (not . (`Set.member` db)) $
          map
            (\subs -> applySubstitutionToAtom subs (DatalogAST.head rule))
            bodySubstitutions
   in foldr Set.insert db newFacts

-- Evaluate a query
evaluateQuery :: Query -> Database -> [Substitution]
evaluateQuery (Query atom) db = evaluateAtom atom db Map.empty

-- Fixpoint algorithm
evaluateProgram :: DatalogProgram -> Database -> Database
evaluateProgram program = fixpoint (map applyRule (rules program))
  where
    -- Extract rules from the program
    rules (DatalogProgram clauses) = [r | ClauseRule r <- clauses]
    -- Fixpoint function to apply the rules until no changes occur
    fixpoint rs database
      | database' == database = database
      | otherwise = fixpoint rs database'
      where
        database' = foldr ($) database rs

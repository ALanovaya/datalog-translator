module Interpreter where

import qualified Data.Map as Map
import Data.Maybe
import DatalogAST

-- A Substitution is a mapping from variable names to constants
type Substitution = Map.Map String String

-- Apply a substitution to a term
applySubstTerm :: Substitution -> Term -> Term
applySubstTerm subst (Variable v) = maybe (Variable v) Constant (Map.lookup v subst)
applySubstTerm _ term@(Constant _) = term

-- Apply a substitution to an atom
applySubstAtom :: Substitution -> Atom -> Atom
applySubstAtom subst (Atom pr ts) = Atom pr (map (applySubstTerm subst) ts)

-- Check if an atom is a fact (no variables)
isFact :: Atom -> Bool
isFact (Atom _ ts) = all isConstant ts
  where
    isConstant (Constant _) = True
    isConstant _            = False

-- A simple database of facts
type Database = [Fact]

-- Evaluate a query against the database
evaluateQuery :: Database -> Query -> [Substitution]
evaluateQuery db (Query atom) = mapMaybe (matchFact atom) db

-- Match an atom with a fact, returning a possible substitution
matchFact :: Atom -> Fact -> Maybe Substitution
matchFact (Atom qPred qTerms) (Atom fPred fTerms)
  | qPred == fPred = foldr addBinding (Just Map.empty) (zip qTerms fTerms)
  | otherwise = Nothing
  where
    addBinding (_, Constant c) (Just subst) = Just subst
    addBinding (Variable v, Constant c) (Just subst) = Just (Map.insert v c subst)
    addBinding _ _ = Nothing

-- A function to execute a Datalog program and return the resulting database
executeProgram :: DatalogProgram -> Database
executeProgram (DatalogProgram clauses) = foldl processClause [] clauses
  where
    processClause db (ClauseFact fact) = fact : db
    processClause db (ClauseRule rule) = applyRule db rule ++ db

applyRule :: Database -> Rule -> Database
applyRule db (Rule headAtom bodyAtoms) = 
  -- Find all the substitutions that satisfy the body of the rule
  let possibleSubstitutions = map (evaluateBody db) bodyAtoms
      -- Calculate the cross product of all possible substitutions
      combinedSubstitutions = sequenceA possibleSubstitutions
      -- Apply each combined substitution to the head atom
      newFacts = map (`applySubstAtom` headAtom) (concatMap catMaybes combinedSubstitutions)
  in filter isFact newFacts  -- Filter out any non-facts (i.e., atoms with variables)

-- Helper function to handle the evaluation of the body atoms of a rule
evaluateBody :: Database -> Atom -> [Maybe Substitution]
evaluateBody db atom = map (matchFact atom) db
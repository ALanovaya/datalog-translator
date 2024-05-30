Module Interpreter.

Require Import Coq.Maps.Map.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Setoids.SetoidArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Sets.Set.
Require Import DatalogAST.

(* Define a type for a database *)
Definition Database := Set Fact.

(* Define a type for a substitution *)
Definition Substitution := Map string Term.

(* Evaluate an Atom *)
Definition evaluateAtom (atom : Atom) (db : Database) (subs : Substitution) : list Substitution :=
  let matchedFacts := matchPredicate atom db in
  concatMap (fun fact => unifyWithFact (terms atom) fact) (Set.elements matchedFacts) >>= fun unifiedSubs =>
  concatMap (composeSubstitutions subs) unifiedSubs.

(* Unify a list of terms with a fact to produce a substitution *)
Definition unifyWithFact (queryTerms : list Term) (fact : Fact) : list Substitution :=
  foldM (unifyPairs queryTerms) Map.empty (zip queryTerms (terms fact)).

(* Try to unify two terms and update the substitution *)
Definition unifyPairs (queryTerms : list Term) (subs : Substitution) (pair : Term * Term) : list Substitution :=
  match pair with
  | (Variable var, term) =>
    let subs' :=
      match Map.lookup var subs with
      | Some term' => if term == term' then [subs] else []
      | None => [Map.insert var term subs]
      end in
    subs'
  | (term, Variable var) => unifyPairs queryTerms subs (Variable var, term)
  | (Constant const1, Constant const2) => if const1 == const2 then [subs] else []
  end.

(* Filter the database for facts that match the given predicate atom *)
Definition matchPredicate (atom : Atom) (db : Database) : Database :=
  Set.filter (fun fact => predicate atom == predicate fact && length (terms atom) == length (terms fact)) db.

(* Compose two substitutions together *)
Definition composeSubstitutions (sub1 sub2 : Substitution) : list Substitution :=
  if hasConflicts sub1 sub2 then [sub1; sub2] else
    let sub1AppliedToSub2 := Map.map (recursiveApply sub1) sub2 in
    let combinedSubs := Map.union sub1AppliedToSub2 sub1 in
    [Map.map (recursiveApply combinedSubs) combinedSubs].

(* Check if two substitutions have conflicts *)
Definition hasConflicts (sub1 sub2 : Substitution) : bool :=
  let allKeysInAnotherMap :=
    Set.is_subset (Map.keysSet sub1) (Map.keysSet sub2) ||
    Set.is_subset (Map.keysSet sub2) (Map.keysSet sub1) in
  let noConflictingValues :=
    Map.for_all
      (fun key =>
         match (Map.lookup key sub1, Map.lookup key sub2) with
         | (Some (Constant val1), Some (Constant val2)) => val1 == val2
         | (Some (Variable _), Some _) => true
         | (Some _, Some (Variable _)) => true
         | _ => false
         end)
      (Map.union (Map.keysSet sub1) (Map.keysSet sub2)) in
  let allVars := [v | Variable v <- Map.values sub1 ++ Map.values sub2] in
  let noVariableAsKey :=
    negb (existsb (fun v => Map.mem v sub1 || Map.mem v sub2) allVars) in
  allKeysInAnotherMap && noConflictingValues && noVariableAsKey.

(* Recursively apply a substitution to a term *)
Definition recursiveApply (subs : Substitution) (term : Term) : Term :=
  match term with
  | Variable var =>
    match Map.lookup var subs with
    | Some term' => recursiveApply subs term'
    | None => term
    end
  | Constant _ => term
  end.

(* Apply a substitution to a term *)
Definition applySubstitution (subs : Substitution) (term : Term) : Term :=
  match term with
  | Variable var =>
    match Map.lookup var subs with
    | Some term' => term'
    | None => term
    end
  | Constant _ => term
  end.

(* Apply a substitution to an atom *)
Definition applySubstitutionToAtom (subs : Substitution) (atom : Atom) : Atom :=
  let (predName, ts) := atom in
  Atom predName (List.map (applySubstitution subs) ts).

(* Check if the first substitution is a subset of the second *)
Definition isSubsetOf (sub1 sub2 : Substitution) : bool :=
  Map.for_all (fun _ v => Map.mem v sub2) sub1.

Definition evaluateRule (db : list Fact) (subs : Substitution) (rule : Rule) : bool := 
  let headAtom := head rule in let bodyAtoms := body rule in 
  let substitutedHead := applySubstitutionToAtom subs headAtom in 
  (forallb (fun atom => not (null (evaluateAtom atom db subs))) bodyAtoms) && Set.mem substitutedHead db.

Definition evaluateBody (db : Database) (initialSubs : Substitution) (atoms : list Atom) : list Substitution :=
  let allVars := Set.from_list (concat_map getVarsFromAtom atoms) in
  let uniqueVarCount := Set.cardinal allVars in
  let subs := concat_map (fun atom => evaluateAtom atom db initialSubs) atoms in
  let filteredSubs := filter (fun sub => not (any (fun sub' => isSubsetOf sub sub') (remove sub subs))) subs in
  let composedSubs := composeAllSubs filteredSubs in
  let consistentSubs := filter isConsistent composedSubs in
  let correctSizeSubs := filter (fun sub => Map.cardinal sub =? uniqueVarCount) consistentSubs in
  nub correctSizeSubs.

Fixpoint composeAllSubs (subs : list Substitution) : list Substitution :=
  let pairs := combine subs subs in
  let composedPairs := nub (concat_map (uncurry composeSubstitutions) pairs) in
  let newSubs := nub (subs ++ composedPairs) in
  if null (newSubs \\ subs) then subs else composeAllSubs newSubs.

Definition isConsistent (sub : Substitution) : bool :=
  let constants := Map.values sub in
  length constants =? length (nub constants).

Definition getVarsFromAtom (atom : Atom) : list string :=
  concat_map getVarsFromTerm (terms atom).

Definition getVarsFromTerm (term : Term) : list string :=
  match term with
  | Variable var => [var]
  | Constant _ => []
  end.

Definition applyRule (rule : Rule) (db : Database) : Database :=
  let bodySubstitutions := evaluateBody db Map.empty (body rule) in
  let newFacts := filter (fun fact => not (Set.mem fact db)) (map (fun subs => applySubstitutionToAtom subs (head rule)) bodySubstitutions) in
  fold_right Set.add db newFacts.

Definition evaluateQuery (query : Query) (db : Database) : list Substitution :=
  evaluateAtom (atom query) db Map.empty.

Fixpoint evaluateProgram (program : DatalogProgram) (db : Database) : Database :=
  fixpoint (map (fun rule => applyRule rule) (rules program)) db
  where
    rules (DatalogProgram clauses) := [r | ClauseRule r <- clauses].
    fixpoint rs database :=
      match database' with
      | database => database
      | _ => fixpoint rs database'
      end
      where
        database' := fold_right (fun f db => f db) database rs.

End Interpreter.

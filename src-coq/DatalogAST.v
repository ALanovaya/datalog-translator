Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Module DatalogAST.

(* Define a type for a variable or constant *)
Inductive Term : Set :=
  | Variable : string -> Term
  | Constant : string -> Term.

(* Define a type for an atom (a predicate with its arguments) *)
Record Atom : Set := mkAtom {
  predicate : string;
  terms : list Term
}.

(* Define a type for a rule (a head atom and a list of body atoms) *)
Record Rule : Set := mkRule {
  head : Atom;
  body : list Atom
}.

(* In Coq, Fact is essentially an Atom, so we can use type synonym *)
Definition Fact := Atom.

(* Define a type for a Clause, which can be either a Fact or a Rule *)
Inductive Clause : Set :=
  | ClauseFact : Fact -> Clause
  | ClauseRule : Rule -> Clause.

(* Define a type for a DatalogProgram which holds a list of Clauses *)
Record DatalogProgram : Set := mkDatalogProgram {
  clauses : list Clause
}.

(* Define a type for a query (an atom representing the query to be evaluated) *)
Record Query : Set := mkQuery {
  query_atom : Atom
}.

End DatalogAST.

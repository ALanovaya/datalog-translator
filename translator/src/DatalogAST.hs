module DatalogAST where 

-- Define a type for a variable or constant
data Term = Variable String | Constant String deriving (Show, Eq, Ord)

-- Define a type for an atom (a predicate with its arguments)
data Atom = Atom {
    predicate :: String,
    terms :: [Term]
} deriving (Show, Eq)

-- Define a type for a rule (a head atom and a list of body atoms)
data Rule = Rule {
    head :: Atom,
    body :: [Atom]
} deriving (Show, Eq)

-- Define a type for a Fact, which is essentially an Atom
type Fact = Atom

-- Define a type for a Clause, which can be either a Fact or a Rule
data Clause = ClauseFact Fact | ClauseRule Rule deriving (Show, Eq)

-- Modify the DatalogProgram type to hold a list of Clauses
data DatalogProgram = DatalogProgram [Clause] deriving (Show, Eq)

-- Define a type for a query (an atom representing the query to be evaluated)
data Query = Query Atom deriving (Show, Eq)
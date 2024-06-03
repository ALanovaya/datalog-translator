# Datalog-translator
<a href="https://github.com/ALanovaya/datalog-translator/actions"><img alt="Actions Status" src="https://github.com/ALanovaya/datalog-translator/actions/workflows/haskell.yml/badge.svg"></a>
## Multidimensional Matrix Library
The Multidimensional Matrix Operations library provides a number of functions for creating, transforming, and manipulating matrices. Key operations include generating matrices, changing their shape, accessing and modifying elements, and obtaining submatrices. These operations are the basis for implementing more complex algorithms, such as matrix multiplication, which is used to compose relationships in Datalog.

## Translator of Datalog to linear algebra
The process of translating Datalog into matrix operations is a method of executing logical queries, thereby taking advantage of optimized computing libraries and hardware acceleration available for matrix operations. The translation process provides the basis for creating high-performance query processing systems that can handle large amounts of data and complex queries typical of modern applications in the field of big data and artificial intelligence.

## Automated proof of translator correctness
We consider a translator that takes a Datalog program as input, represented as a type DatalogProgram, which extends the chain rule for predicates of arbitrary arity, and produces a matrix representation of the program as output, encoded as an abstract syntax tree of matrix operations MatrixOp. The components of the program have been rewritten in Coq, and the correctness proof has been automated. Notably, the proof is step-by-step, consisting of several key steps that establish important properties of the translation process. The steps are organized into three main sections:
+ Translating atoms to matrices
+ Translating rules to matrix operations
+ Translating the entire Datalog program to a matrix representation
```coq
Record DatalogProgram : Set := mkDatalogProgram {
  clauses : list Clause;
  chain_rule_extension : forall c : Clause, 
    match c with
    | ClauseFact _ => True
    | ClauseRule r => 
        let head_pred := r.(head).(predicate) in
        let head_terms := r.(head).(terms) in
        let body_atoms := r.(body) in
        exists t : Term, 
          (In t head_terms /\ 
           forall b : Atom, 
             In b body_atoms -> 
             exists p : string, 
               b.(predicate) = p /\ 
               exists ts : list Term, 
                 b.(terms) = ts /\ 
                 In t ts)
    end
}.
```

Details are provided in ./docs directory.

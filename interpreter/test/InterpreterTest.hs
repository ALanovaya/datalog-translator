module Main where

import qualified Data.Map as Map
import qualified Data.Set as Set
import DatalogAST
import Interpreter
import Test.Hspec

main :: IO ()
main =
  hspec $ do
    -- Test case for the evaluateAtom function
    describe "evaluateAtom" $ do
      it "handles complex substitutions" $ do
        let db = Set.fromList [Atom "parent" [Constant "Alice", Constant "Bob"]]
            atom = Atom "parent" [Variable "x", Variable "y"]
            subs = Map.fromList [("x", Constant "Alice")]
        evaluateAtom atom db subs `shouldBe` [Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob")]]

      it "matches no facts in the database" $ do
        let db = Set.fromList [Atom "friend" [Constant "Alice", Constant "Bob"]]
            atom = Atom "friend" [Constant "Dan", Variable "y"]
            subs = Map.empty
        evaluateAtom atom db subs `shouldBe` []

      it "contains both variables and constants" $ do
        let db = Set.fromList [Atom "likes" [Constant "Alice", Constant "IceCream"]]
            atom = Atom "likes" [Variable "x", Constant "IceCream"]
            subs = Map.empty
        evaluateAtom atom db subs `shouldBe` [Map.fromList [("x", Constant "Alice")]]

      it "requires recursive substitutions" $ do
        let db =
              Set.fromList
                [ Atom "parent" [Constant "Alice", Constant "Bob"],
                  Atom "parent" [Constant "Bob", Constant "Charlie"]
                ]
            atom = Atom "parent" [Variable "x", Variable "z"]
            subs = Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob"), ("z", Variable "y")]
        evaluateAtom atom db subs
          `shouldMatchList` [ Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob"), ("z", Constant "Bob")],
                              Map.fromList [("x", Constant "Bob"), ("y", Constant "Bob"), ("z", Constant "Charlie")]
                            ]

      it "partially matches the terms in the atom" $ do
        let db =
              Set.fromList
                [ Atom "teaches" [Constant "DrSmith", Constant "Math101"],
                  Atom "teaches" [Constant "DrJones", Constant "Eng201"]
                ]
            atom = Atom "teaches" [Variable "x", Constant "Math101"]
            subs = Map.fromList [("x", Constant "DrSmith")]
        evaluateAtom atom db subs `shouldBe` [Map.fromList [("x", Constant "DrSmith")]]

      it "matches multiple facts in the database" $ do
        let db =
              Set.fromList
                [ Atom "friend" [Constant "Alice", Constant "Bob"],
                  Atom "friend" [Constant "Alice", Constant "Charlie"]
                ]
            atom = Atom "friend" [Variable "x", Variable "y"]
            subs = Map.empty
        evaluateAtom atom db subs
          `shouldMatchList` [ Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob")],
                              Map.fromList [("x", Constant "Alice"), ("y", Constant "Charlie")]
                            ]

    -- Test cases for composeSubstitutions function
    describe "composeSubstitutions" $ do
      it "composes two non-conflicting substitutions" $ do
        let sub1 = Map.singleton "X" (Constant "John")
            sub2 = Map.singleton "Y" (Constant "Mary")
            expected =
              [Map.fromList [("X", Constant "John"), ("Y", Constant "Mary")]]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "applies the first substitution to the second one during composition" $ do
        let sub1 = Map.singleton "X" (Constant "Steve")
            sub2 = Map.singleton "X" (Constant "John")
            expected =
              [ Map.singleton "X" (Constant "Steve"),
                Map.singleton "X" (Constant "John")
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "respects order of application - sub1 is applied to sub2" $ do
        let sub1 = Map.singleton "X" (Variable "Z")
            sub2 = Map.singleton "X" (Constant "John")
            expected =
              [ Map.singleton "X" (Variable "Z"),
                Map.singleton "X" (Constant "John")
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "applies sub1 to every element in sub2" $ do
        let sub1 = Map.singleton "Y" (Constant "Alice")
            sub2 = Map.fromList [("X", Variable "Y"), ("Z", Constant "Bob")]
            expected =
              [ Map.fromList
                  [ ("X", Constant "Alice"),
                    ("Y", Constant "Alice"),
                    ("Z", Constant "Bob")
                  ]
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "deals with complex substitutions involving multiple variables" $ do
        let sub1 = Map.fromList [("X", Variable "Y"), ("Y", Constant "Alice")]
            sub2 = Map.fromList [("Z", Variable "X"), ("W", Variable "Y")]
            expected =
              [ Map.fromList
                  [ ("X", Constant "Alice"),
                    ("Y", Constant "Alice"),
                    ("Z", Constant "Alice"),
                    ("W", Constant "Alice")
                  ]
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "should handle independent substitutions without invalidation" $ do
        let sub1 = Map.fromList [("X", Constant "Alice"), ("Y", Variable "Z")]
            sub2 =
              Map.fromList [("Z", Constant "Bob"), ("Y", Constant "Charlie")]
            expected =
              [ Map.fromList
                  [ ("X", Constant "Alice"),
                    ("Y", Constant "Charlie"),
                    ("Z", Constant "Bob")
                  ]
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "should handle different length to return sub2" $ do
        let sub1 = Map.singleton "X" (Constant "Alice")
            sub2 =
              Map.fromList [("X", Constant "Alice"), ("Y", Constant "Charlie")]
            expected =
              [ Map.fromList
                  [("X", Constant "Alice"), ("Y", Constant "Charlie")]
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

      it "should handle different length to return union of subs" $ do
        let sub1 = Map.singleton "X" (Constant "Alice")
            sub2 =
              Map.fromList [("X", Constant "Bob"), ("Y", Constant "Charlie")]
            expected =
              [ Map.singleton "X" (Constant "Alice"),
                Map.fromList [("X", Constant "Bob"), ("Y", Constant "Charlie")]
              ]
        composeSubstitutions sub1 sub2 `shouldBe` expected

    -- Test case for applySubstitution function
    describe "applySubstitution" $ do
      it "applies a substitution to a variable term" $ do
        let subs = Map.singleton "X" (Constant "John")
            term = Variable "X"
        applySubstitution subs term `shouldBe` Constant "John"
      it "leaves a constant term unchanged after applying a substitution" $ do
        let subs = Map.singleton "X" (Constant "John")
            term = Constant "Mary"
        applySubstitution subs term `shouldBe` term

    -- Test case for evaluateBody function
    describe "evaluateBody" $ do
      it "succeeds with a simple body and a single substitution" $ do
        let db = Set.fromList [Atom "knows" [Constant "Alice", Constant "Bob"]]
            initialSubs = Map.empty
            atoms = [Atom "knows" [Variable "x", Variable "y"]]
            expectedSubs = [Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob")]]
        evaluateBody db initialSubs atoms `shouldBe` expectedSubs

      it "fails when no substitutions satisfy the body atoms" $ do
        let db = Set.fromList [Atom "knows" [Constant "Alice", Constant "Bob"]]
            initialSubs = Map.empty
            atoms = [Atom "knows" [Variable "x", Constant "Charlie"]] -- Charlie is not known by Alice here
            expectedSubs = []
        evaluateBody db initialSubs atoms `shouldBe` expectedSubs

      it "handles multiple atoms with multiple substitutions" $ do
        let db = Set.fromList [Atom "parent" [Constant "Alice", Constant "Bob"], Atom "parent" [Constant "Bob", Constant "Charlie"]]
            initialSubs = Map.empty
            atoms = [Atom "parent" [Variable "x", Variable "y"], Atom "parent" [Variable "y", Variable "z"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob"), ("z", Constant "Charlie")]]

      it "handles overlapping variables with correct composition of substitutions" $ do
        let db = Set.fromList [Atom "connected" [Constant "A", Constant "B"], Atom "connected" [Constant "B", Constant "C"]]
            initialSubs = Map.empty
            atoms = [Atom "connected" [Variable "x", Variable "y"], Atom "connected" [Variable "y", Variable "z"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("x", Constant "A"), ("y", Constant "B"), ("z", Constant "C")]]

      it "filters out inconsistent substitutions" $ do
        let db = Set.fromList [Atom "friend" [Constant "Alice", Constant "Bob"], Atom "friend" [Constant "Alice", Constant "Charlie"]]
            initialSubs = Map.empty
            atoms = [Atom "friend" [Variable "x", Variable "y"], Atom "friend" [Variable "x", Variable "z"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("x", Constant "Alice"), ("y", Constant "Bob"), ("z", Constant "Charlie")], Map.fromList [("x", Constant "Alice"), ("y", Constant "Charlie"), ("z", Constant "Bob")]]

      it "removes redundant substitutions where some are subsets of others" $ do
        let db = Set.fromList [Atom "likes" [Constant "Alice", Constant "IceCream"], Atom "likes" [Constant "Bob", Constant "IceCream"]]
            initialSubs = Map.empty
            atoms = [Atom "likes" [Variable "x", Constant "IceCream"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("x", Constant "Alice")], Map.fromList [("x", Constant "Bob")]]

      it "produces multiple consistent and unique substitutions of the correct size" $ do
        let db = Set.fromList [Atom "likes" [Constant "Alice", Constant "IceCream"], Atom "likes" [Constant "Bob", Constant "Chocolate"]]
            initialSubs = Map.empty
            atoms = [Atom "likes" [Variable "x", Variable "y"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("x", Constant "Alice"), ("y", Constant "IceCream")], Map.fromList [("x", Constant "Bob"), ("y", Constant "Chocolate")]]

      it "handles constants within atoms correctly" $ do
        let db = Set.fromList [Atom "enjoys" [Constant "Charlie", Constant "Skating"]]
            initialSubs = Map.empty
            atoms = [Atom "enjoys" [Constant "Charlie", Variable "z"]]
        evaluateBody db initialSubs atoms `shouldBe` [Map.fromList [("z", Constant "Skating")]]

    -- Test cases for the applyRule function
    describe "applyRule" $ do
      it "applies a rule with multiple body atoms that share variables" $ do
        let db =
              Set.fromList
                [ Atom "parent" [Constant "Alice", Constant "Bob"],
                  Atom "parent" [Constant "Bob", Constant "Charlie"]
                ]
            rule =
              Rule
                (Atom "grandparent" [Variable "X", Variable "Z"])
                [ Atom "parent" [Variable "X", Variable "Y"],
                  Atom "parent" [Variable "Y", Variable "Z"]
                ]
            expectedDb = Set.insert (Atom "grandparent" [Constant "Alice", Constant "Charlie"]) db
        applyRule rule db `shouldBe` expectedDb

      it "applies a rule that introduces new facts to the database" $ do
        let db = Set.fromList [Atom "likes" [Constant "Alice", Constant "Gardening"]]
            rule =
              Rule
                (Atom "hobbyist" [Variable "X"])
                [Atom "likes" [Variable "X", Constant "Gardening"]]
            expectedDb = Set.insert (Atom "hobbyist" [Constant "Alice"]) db
        applyRule rule db `shouldBe` expectedDb

      it "applies a rule that doesn't introduce any new facts because they exist" $ do
        let db =
              Set.fromList
                [ Atom "friend" [Constant "Alice", Constant "Bob"],
                  Atom "trusts" [Constant "Alice", Constant "Bob"]
                ]
            rule =
              Rule
                (Atom "ally" [Variable "X", Variable "Y"])
                [ Atom "friend" [Variable "X", Variable "Y"],
                  Atom "trusts" [Variable "X", Variable "Y"]
                ]
            expectedDb = db -- No new Atom is introduced
        applyRule rule db `shouldBe` expectedDb

      it "applies a rule with body atoms that have no satisfying facts in the db" $ do
        let db = Set.fromList [Atom "likes" [Constant "Alice", Constant "Reading"]]
            rule =
              Rule
                (Atom "bookworm" [Variable "X"])
                [Atom "likes" [Variable "X", Constant "Books"]]
            expectedDb = db -- No change since there's no matching facts
        applyRule rule db `shouldBe` expectedDb

      it "applies a rule that results in complex substitutions" $ do
        let db =
              Set.fromList
                [ Atom "teaches" [Constant "ProfA", Constant "Math101"],
                  Atom "enrolled" [Constant "StudentB", Constant "Math101"]
                ]
            rule =
              Rule
                (Atom "taughtBy" [Variable "S", Variable "P"])
                [ Atom "teaches" [Variable "P", Variable "C"],
                  Atom "enrolled" [Variable "S", Variable "C"]
                ]
            expectedDb = Set.insert (Atom "taughtBy" [Constant "StudentB", Constant "ProfA"]) db
        applyRule rule db `shouldBe` expectedDb

    -- Test cases for the evaluateProgram function
    describe "evaluateProgram" $ do
      it "correctly evaluates a program with simple facts" $ do
        let facts = [ClauseFact (Atom "parent" [Constant "Alice", Constant "Bob"])]
            program = DatalogProgram facts
            expectedDB = Set.fromList [Atom "parent" [Constant "Alice", Constant "Bob"]]
        evaluateProgram program (Set.fromList (map (\(ClauseFact fact) -> fact) facts)) `shouldBe` expectedDB

      it "correctly applies rules with no dependencies" $ do
        let rules =
              [ ClauseRule $
                  Rule
                    (Atom "grandparent" [Variable "X", Variable "Z"])
                    [ Atom "parent" [Variable "X", Variable "Y"],
                      Atom "parent" [Variable "Y", Variable "Z"]
                    ]
              ]
            facts =
              [ ClauseFact $ Atom "parent" [Constant "Alice", Constant "Bob"],
                ClauseFact $ Atom "parent" [Constant "Bob", Constant "Charlie"]
              ]
            program = DatalogProgram $ facts ++ rules
            expectedDB =
              Set.fromList
                [ Atom "parent" [Constant "Alice", Constant "Bob"],
                  Atom "parent" [Constant "Bob", Constant "Charlie"],
                  Atom "grandparent" [Constant "Alice", Constant "Charlie"]
                ]
        evaluateProgram program (Set.fromList (map (\(ClauseFact fact) -> fact) facts)) `shouldBe` expectedDB

      it "correctly evaluates a program with empty database" $ do
        let program = DatalogProgram []
        evaluateProgram program Set.empty `shouldBe` Set.empty

      it "does not add duplicate facts to the database" $ do
        let facts =
              [ ClauseFact $ Atom "likes" [Constant "Alice", Constant "IceCream"],
                ClauseFact $ Atom "likes" [Constant "Alice", Constant "IceCream"]
              ]
            program = DatalogProgram facts
            expectedDB = Set.fromList [Atom "likes" [Constant "Alice", Constant "IceCream"]]
        evaluateProgram program (Set.fromList (map (\(ClauseFact fact) -> fact) facts)) `shouldBe` expectedDB

      it "correctly evaluates a program with no rules" $ do
        let facts = [ClauseFact $ Atom "likes" [Constant "Alice", Constant "IceCream"]]
            program = DatalogProgram facts
            expectedDB = Set.fromList [Atom "likes" [Constant "Alice", Constant "IceCream"]]
        evaluateProgram program (Set.fromList (map (\(ClauseFact fact) -> fact) facts)) `shouldBe` expectedDB

      it "handles recursive rules and reaches a fixpoint" $ do
        let rule =
              [ ClauseRule $
                  Rule
                    (Atom "ancestor" [Variable "X", Variable "Z"])
                    [ Atom "parent" [Variable "X", Variable "Y"],
                      Atom "parent" [Variable "Y", Variable "Z"]
                    ],
                ClauseRule $
                  Rule
                    (Atom "ancestor" [Variable "Z", Variable "X"])
                    [ Atom "parent" [Variable "Y", Variable "X"],
                      Atom "ancestor" [Variable "Y", Variable "Z"]
                    ]
              ]
            facts =
              [ ClauseFact $ Atom "parent" [Constant "Alice", Constant "Bob"],
                ClauseFact $ Atom "parent" [Constant "Bob", Constant "Charlie"]
              ]
            program = DatalogProgram $ facts ++ rule
            expectedDB =
              Set.fromList
                [ Atom "parent" [Constant "Alice", Constant "Bob"],
                  Atom "parent" [Constant "Bob", Constant "Charlie"],
                  Atom "ancestor" [Constant "Alice", Constant "Charlie"],
                  Atom "ancestor" [Constant "Charlie", Constant "Bob"]
                ]
        evaluateProgram program (Set.fromList (map (\(ClauseFact fact) -> fact) facts)) `shouldBe` expectedDB

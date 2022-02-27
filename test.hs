{-# LANGUAGE NoMonomorphismRestriction #-}

module Testing where

import NormalFroms
import Data.List
import Data.Maybe

-- === Common ===

-- Generate all True/False sequences with length n
genAllBinarySequences :: Int -> [[Value]]
genAllBinarySequences 0 = [[]]
genAllBinarySequences n = gen (n - 1) [[False], [True]] where
    gen :: Int -> [[Value]] -> [[Value]]
    gen 0 list = list
    gen n list = gen (n - 1) (map (False :) list ++ map (True :) list)

assertEq :: (Eq a, Show a) => a -> a -> Bool
assertEq expected actual = if (expected == actual) then
        True
    else
        error ("Assertion failed!\nExpected " ++ show expected ++ ", but found " ++ show actual)

-- Function to check if expressions are equivalent.
-- Generates all possible interpretations and checks
-- if expressions evaluate into same Value
infixl 4 ~~
(~~) :: Expr -> Expr -> Bool
a ~~ b = let vars = union (variableList a) (variableList b)
             vals = genAllBinarySequences (length vars) in
             all (eqEvals vars) vals where
                 eqEvals :: [Name] -> [Value] -> Bool
                 eqEvals vars vals = let interp = zip vars vals in
                                         eval interp a == eval interp b

-- Function to check if expression is satisfyable.
-- Generates all possible interpretations and checks
-- if expression evaluates to truth
checkSat :: Expr -> Maybe [(Name, Value)]
checkSat e = let vars = variableList e
                 vals = genAllBinarySequences (length vars) in
                 checkInterp vars vals where
                     checkInterp :: [Name] -> [[Value]] -> Maybe [(Name, Value)]
                     checkInterp vars [] = Nothing
                     checkInterp vars (vals : t) = let interp = zip vars vals in
                                                       if (eval interp e == True) then
                                                           Just interp
                                                       else
                                                           checkInterp vars t

-- Function to check if expressions are equisatisfyable
infixl 4 `eqSat`
eqSat :: Expr -> Expr -> Bool
ini `eqSat` ext = isJust (checkSat ini) == isJust (checkSat ext) where

-- Function to invoke list of unit-tests
invokeTests :: [Bool] -> [Bool]
invokeTests [] = []
invokeTests (a : t) = let result = a in seq a a : invokeTests t

-- Function to invoke test group
runTestGroup runGroup = do
    let res = runGroup
    putStrLn $ show res
    putStrLn ("All " ++ show (length res) ++ " tests passed!\n")

-- Main function. Invokes all tests
runTests = do
    putStrLn "\n===================================================================================\n"
    putStrLn "Testing (~~)"
    runTestGroup testEq
    putStrLn "Testing checkSat"
    runTestGroup testCheckSat
    putStrLn "Testing eqSat"
    runTestGroup testEqSat
    putStrLn "Testing variableList"
    runTestGroup testVariableList
    putStrLn "Testing eval"
    runTestGroup testEval
    putStrLn "Testing reduceOperators"
    runTestGroup testReduceOperators
    putStrLn "Testing toNNF"
    runTestGroup testToNNF
    putStrLn "Testing toDNF"
    runTestGroup testToDNF
    putStrLn "Testing toCNF"
    runTestGroup testToCNF
    putStrLn "All test groups passed!\n"

-- List of unit-tests below

-- === test (~~) ===

testEq = invokeTests [testEq1, testEq2, testEq3, testEq4, testEq5, testEq6, testEq7, testEq8]

testEq1 = let a = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "b"))
              b = Xor (Var "a") (Var "b") in
              assertEq True (a ~~ b)

testEq2 = let a = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "c"))
              b = Xor (Var "a") (Var "b") in
              assertEq False (a ~~ b)

testEq3 = let a = Xor (Impl (Var "x") (Var "y")) (RImpl (Var "x") (Var "y"))
              b = Xor (Var "x") (Var "y") in
              assertEq True (a ~~ b)

testEq4 = let a = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "b") (Var "a"))
              b = Bot in
              assertEq True (a ~~ b)

testEq5 = let a = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
              b = Or (Or (Var "a") (And (Var "a") (Var "c"))) (And (Var "a") (Var "b")) in
              assertEq False (a ~~ b)

testEq6 = let a = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
              b = Or (Or (Or (Var "a") (And (Var "a") (Var "c"))) (And (Var "a") (Var "b"))) (And (Var "b") (Var "c")) in
              assertEq True (a ~~ b)

testEq7 = let a = Impl (Var "a") (Or (Var "a") (Var "b"))
              b = Top in
              assertEq True (a ~~ b)

testEq8 = let a = And Top Bot
              b = Top in
              assertEq False (a ~~ b)

-- === test checkSat ===

testCheckSat = invokeTests [testCheckSat1, testCheckSat2, testCheckSat3, testCheckSat4, testCheckSat5, testCheckSat6, testCheckSat7, testCheckSat8, testCheckSat9, testCheckSat10, testCheckSat11, testCheckSat12]

testCheckSat1 = let f = Impl (Or (And (Var "a") (Var "b")) (Xor (Var "a") (Var "c"))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat2 = let f = Var "a"
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat3 = let f = Or (Not (Var "a")) (Var "a")
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat4 = let f = And (Var "a") (Not (Var "a"))
                    res = checkSat f in
                    assertEq True (res == Nothing)

testCheckSat5 = let f = Xor (Not Bot) Top
                    res = checkSat f in
                    assertEq True (res == Nothing)

testCheckSat6 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat7 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat8 = let f = Iff (Var "a") (Iff (Var "b") (Iff (Var "c") (Iff (Var "d") (Iff (Var "e") (Not (Var "a"))))))
                    res = checkSat f in
                    assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat9 = let f = Bot
                    res = checkSat f in
                    assertEq True (res == Nothing)

testCheckSat10 = let f = Top
                     res = checkSat f in
                     assertEq True (res /= Nothing && eval (fromJust res) f == True)

testCheckSat11 = let f = Iff (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))) (Not (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))))
                     res = checkSat f in
                     assertEq True (res == Nothing)

testCheckSat12 = let f = And (And (Iff (Var "a") (Var "b")) (Iff (Var "b") (Var "c"))) (And (Iff (Var "c") (Var "d")) (Iff (Var "d") (Not (Var "a"))))
                     res = checkSat f in
                     assertEq True (res == Nothing)

-- === test eqSat ===

testEqSat = invokeTests [testEqSat1, testEqSat2, testEqSat3, testEqSat4, testEqSat5, testEqSat6, testEqSat7, testEqSat8]

testEqSat1 = let a = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "b"))
                 b = Xor (Var "a") (Var "b") in
                 assertEq True (a `eqSat` b)

testEqSat2 = let a = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "b"))
                 b = And (Var "x") (Not (Var "x")) in
                 assertEq False (a `eqSat` b)

testEqSat3 = let a = Xor (Var "a") (Var "b")
                 b = Or (And (Var "a") (Not (Var "b"))) (And (Not (Var "a")) (Var "b")) in
                 assertEq True (a `eqSat` b)

testEqSat4 = let a = Iff (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))) (Not (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))))
                 b = Var "a" in
                 assertEq False (a `eqSat` b)

testEqSat5 = let a = Iff (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))) (Not (Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))))
                 b = Bot in
                 assertEq True (a `eqSat` b)

testEqSat6 = let a = Impl (Var "a") (Var "b")
                 b = Or (Not (Var "a")) (Var "b") in
                 assertEq True (a `eqSat` b)

testEqSat7 = let a = Var "a"
                 b = Not (Var "b") in
                 assertEq True (a `eqSat` b)

testEqSat8 = let a = Xor (Not Bot) Top
                 b = Not (Var "b") in
                 assertEq False (a `eqSat` b)

-- === testVariableList ===

testVariableList = invokeTests [testVariableList1, testVariableList2, testVariableList3, testVariableList4, testVariableList5]

testVariableList1 = let f = Impl (Or (And (Var "a") (Var "b")) (Xor (Var "a") (Var "c"))) (Iff (Var "d") (RImpl (Var "a") (Var "b"))) in
                        assertEq ["a", "b", "c", "d"] (variableList f)

testVariableList2 = let f = Not Bot in
                        assertEq [] (variableList f)

testVariableList3 = let f = Top in
                        assertEq [] (variableList f)

testVariableList4 = let f = Xor (Var "a") (Var "kek") in
                        assertEq ["a", "kek"] (variableList f)

testVariableList5 = let f = Or (Var "a") (Not (Var "a")) in
                        assertEq ["a"] (variableList f)

-- === testEval ===

testEval = invokeTests [testEval1, testEval2, testEval3, testEval4, testEval5, testEval6, testEval7, testEval8, testEval9]

testEval1 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                i = [("a", False), ("b", False), ("c", False), ("d", False)] in
                assertEq False (eval i f)

testEval2 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                i = [("a", True), ("b", False), ("c", False), ("d", False)] in
                assertEq True (eval i f)

testEval3 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                i = [("a", False), ("b", False), ("c", False), ("d", True)] in
                assertEq True (eval i f)

testEval4 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                i = [("a", False), ("b", False), ("c", True), ("d", False)] in
                assertEq True (eval i f)

testEval5 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                i = [("a", True), ("b", True), ("c", True), ("d", True)] in
                assertEq True (eval i f)

testEval6 = let f = Xor (Not Bot) Top
                i = [] in
                assertEq False (eval i f)

testEval7 = let f = Xor (Not Bot) Top
                i = [("a", True), ("b", True), ("c", False)] in
                assertEq False (eval i f)

testEval8 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                i = [("a", False), ("b", True)] in
                assertEq False (eval i f)

testEval9 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                i = [("a", True), ("b", True)] in
                assertEq True (eval i f)

-- === testReduceOperators ===

-- Check if expression is reduced
-- (consists of only Not, Or, And, Top and Bot nodes)
isReduced :: Expr -> Bool
isReduced Top = True
isReduced Bot = True
isReduced (Var x) = True
isReduced (Not e) = isReduced e
isReduced (Or a b) = isReduced a && isReduced b
isReduced (And a b) = isReduced a && isReduced b
isReduced _ = False

testReduceOperators = invokeTests [testReduceOperators1, testReduceOperators2, testReduceOperators3, testReduceOperators4, testReduceOperators5, testReduceOperators6, testReduceOperators7]

testReduceOperators1 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators2 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators3 = let f = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "c"))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators4 = let f = Xor (Not Bot) Top
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators5 = let f = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators6 = let f = Not (Not (Var "x"))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

testReduceOperators7 = let f = And (And (Iff (Var "a") (Var "b")) (Iff (Var "b") (Var "c"))) (And (Iff (Var "c") (Var "d")) (Iff (Var "d") (Not (Var "a"))))
                           g = reduceOperators f in
                           assertEq True (isReduced g && f ~~ g)

-- === testToNNF ===

-- Check if expression is in NNF
isInNNF :: Expr -> Bool
isInNNF Top = True
isInNNF Bot = True
isInNNF (Var x) = True
isInNNF (Not (Var x)) = True
isInNNF (Not _) = False
isInNNF (Or a b) = isInNNF a && isInNNF b
isInNNF (And a b) = isInNNF a && isInNNF b
isInNNF _ = False

testToNNF = invokeTests [testToNNF1, testToNNF2, testToNNF3, testToNNF4, testToNNF5, testToNNF6, testToNNF7, testToNNF8, testToNNF9, testToNNF10, testToNNF11, testToNNF12]

testToNNF1 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF2 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF3 = let f = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "c"))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF4 = let f = Xor (Not Bot) Top
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF5 = let f = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF6 = let f = Not (Xor (Var "a") (Var "b"))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF7 = let f = Not (Xor (Not (Var "a")) (Not (Var "b")))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF8 = let f = Not (Impl (And (Not (Var "a")) (Var "b")) (RImpl (Not (Var "c")) (Var "d")))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF9 = let f = Not (Impl (And (Var "a") (Var "b")) (RImpl (Var "c") (Var "d")))
                 g = toNNF f in
                 assertEq True (isInNNF g && f ~~ g)

testToNNF10 = let f = Not Top
                  g = toNNF f in
                  assertEq True (isInNNF g && f ~~ g)

testToNNF11 = let f = And (Or (And (Var "a") (Var "b")) (Or (Var "a") (Var "c"))) (And (Var "d") (Or (Var "a") (Var "b")))
                  g = toNNF f in
                  assertEq True (isInNNF g && f ~~ g)

testToNNF12 = let f = And (Or (And (Not (Var "a")) (Var "b")) (Or (Var "a") (Not (Var "c")))) (And (Not (Var "d")) (Or (Var "a") (Var "b")))
                  g = toNNF f in
                  assertEq True (isInNNF g && f ~~ g)

-- === testToDNF ===

-- Check if expression is in DNF
isInDNF :: Expr -> Bool
isInDNF = helper False where
    helper :: Bool -> Expr -> Bool
    helper _ Top = True
    helper _ Bot = True
    helper _ (Var x) = True
    helper _ (Not (Var x)) = True
    helper _ (Not _) = False
    helper False (Or a b) = helper False a && helper False b
    helper True (Or a b) = False
    helper _ (And a b) = helper True a && helper True b
    helper _ _ = False

testToDNF = invokeTests [testToDNF1, testToDNF2, testToDNF3, testToDNF4, testToDNF5, testToDNF6, testToDNF7, testToDNF8, testToDNF9, testToDNF10, testToDNF11, testToDNF12, testToDNF13, testToDNF14, testToDNF15, testToDNF16, testToDNF17]

testToDNF1 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF2 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF3 = let f = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "c"))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF4 = let f = Xor (Not Bot) Top
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF5 = let f = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF6 = let f = Not (Xor (Var "a") (Var "b"))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF7 = let f = Not (Xor (Not (Var "a")) (Not (Var "b")))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF8 = let f = Not (Impl (And (Not (Var "a")) (Var "b")) (RImpl (Not (Var "c")) (Var "d")))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF9 = let f = Not (Impl (And (Var "a") (Var "b")) (RImpl (Var "c") (Var "d")))
                 g = toDNF f in
                 assertEq True (isInDNF g && f ~~ g)

testToDNF10 = let f = Not Top
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF11 = let f = And (Or (And (Var "a") (Var "b")) (Or (Var "a") (Var "c"))) (And (Var "d") (Or (Var "a") (Var "b")))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF12 = let f = And (Or (And (Not (Var "a")) (Var "b")) (Or (Var "a") (Not (Var "c")))) (And (Not (Var "d")) (Or (Var "a") (Var "b")))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF13 = let f = Iff (Impl (Var "a") (Impl (Var "b") (Impl (Var "a") (Var "b")))) (Or (Xor (Var "x") (Var "y")) (And (Var "a") (Var "b")))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF14 = let f = Iff (Var "a") (Iff (Var "b") (Iff (Var "c") (Iff (Var "d") (Iff (Var "e") (Not (Var "a"))))))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF15 = let f = Not (Iff (Not (Impl (Var "a") (Impl (Var "b") (Not (Impl (Var "a") (Var "b")))))) (Or (Xor (Not (Var "x")) (Var "y")) (And (Var "a") (Not (Var "b")))))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF16 = let f = Iff (Or (Var "a") (Not (Var "a"))) Top
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

testToDNF17 = let f = And (And (Iff (Var "a") (Var "b")) (Iff (Var "b") (Var "c"))) (And (Iff (Var "c") (Var "d")) (Iff (Var "d") (Not (Var "a"))))
                  g = toDNF f in
                  assertEq True (isInDNF g && f ~~ g)

-- === testToCNF ===

-- Check if expression is in CNF
isInCNF :: Expr -> Bool
isInCNF = helper False where
    helper :: Bool -> Expr -> Bool
    helper _ Top = True
    helper _ Bot = True
    helper _ (Var x) = True
    helper _ (Not (Var x)) = True
    helper _ (Not _) = False
    helper _ (Or a b) = helper True a && helper True b
    helper False (And a b) = helper False a && helper False b
    helper True (And a b) = False
    helper _ _ = False

testToCNF = invokeTests [testToCNF1, testToCNF2, testToCNF3, testToCNF4, testToCNF5, testToCNF6, testToCNF7, testToCNF8, testToCNF9, testToCNF10, testToCNF11, testToCNF12, testToCNF13, testToCNF14, testToCNF15, testToCNF16, testToCNF17]

testToCNF1 = let f = Impl (Or (And (Var "a") (Var "b")) (Not (Xor (Var "a") (Var "c")))) (Iff (Var "d") (RImpl (Var "a") (Var "b")))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF2 = let f = Xor (Impl (Var "a") (Not (Var "b"))) (RImpl (Var "b") (Var "a"))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF3 = let f = Xor (Impl (Var "a") (Var "b")) (RImpl (Var "a") (Var "c"))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF4 = let f = Xor (Not Bot) Top
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF5 = let f = And (Or (Var "a") (Var "b")) (Or (Var "a") (Var "c"))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF6 = let f = Not (Xor (Var "a") (Var "b"))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF7 = let f = Not (Xor (Not (Var "a")) (Not (Var "b")))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF8 = let f = Not (Impl (And (Not (Var "a")) (Var "b")) (RImpl (Not (Var "c")) (Var "d")))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF9 = let f = Not (Impl (And (Var "a") (Var "b")) (RImpl (Var "c") (Var "d")))
                 g = toCNF f in
                 assertEq True (isInCNF g && f `eqSat` g)

testToCNF10 = let f = Not Top
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF11 = let f = And (Or (And (Var "a") (Var "b")) (Or (Var "a") (Var "c"))) (And (Var "d") (Or (Var "a") (Var "b")))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF12 = let f = And (Or (And (Not (Var "a")) (Var "b")) (Or (Var "a") (Not (Var "c")))) (And (Not (Var "d")) (Or (Var "a") (Var "b")))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF13 = let f = Iff (Impl (Var "a") (Impl (Var "b") (Impl (Var "a") (Var "b")))) (Or (Xor (Var "x") (Var "y")) (And (Var "a") (Var "b")))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF14 = let f = Iff (Var "a") (Iff (Var "b") (Iff (Var "c") (Iff (Var "d") (Iff (Var "e") (Not (Var "a"))))))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF15 = let f = Not (Iff (Not (Impl (Var "a") (Impl (Var "b") (Not (Impl (Var "a") (Var "b")))))) (Or (Xor (Not (Var "x")) (Var "y")) (And (Var "a") (Not (Var "b")))))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF16 = let f = Iff (Or (Var "a") (Not (Var "a"))) Top
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

testToCNF17 = let f = And (And (Iff (Var "a") (Var "b")) (Iff (Var "b") (Var "c"))) (And (Iff (Var "c") (Var "d")) (Iff (Var "d") (Not (Var "a"))))
                  g = toCNF f in
                  assertEq True (isInCNF g && f `eqSat` g)

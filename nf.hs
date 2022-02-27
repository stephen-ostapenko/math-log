{-# LANGUAGE NoMonomorphismRestriction #-}

module NormalFroms (Name,
                    Value,
                    Expr (Top, Bot, Var, Not, Or, And, Xor, Iff, Impl, RImpl),
                    variableList,
                    eval,
                    reduceOperators,
                    toNNF,
                    toDNF,
                    toCNF) where

import Data.List (union, nub)
import Data.Maybe (fromJust)
import Control.Monad.State (State, get, modify, evalState)

type Name = String
type Value = Bool

-- Class for expression and operator priorities
data Expr = Top
          | Bot
          | Var Name        -- priority
          | Not Expr        --     6
          | Or Expr Expr    --     3
          | And Expr Expr   --     5
          | Xor Expr Expr   --     4
          | Iff Expr Expr   --     2
          | Impl Expr Expr  --     1
          | RImpl Expr Expr --     1
          deriving (Eq)

instance Show Expr where
    showsPrec _ Top = showString "Top"
    showsPrec _ Bot = showString "Bot"
    showsPrec _ (Var x) = showString x
    showsPrec contextPrec (Not e) = let curPrec = 6 in showParen (contextPrec > curPrec) $ showString "~" . showsPrec curPrec e
    showsPrec contextPrec (Or a b) = let curPrec = 3 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " | " . showsPrec curPrec b
    showsPrec contextPrec (And a b) = let curPrec = 5 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " & " . showsPrec curPrec b
    showsPrec contextPrec (Xor a b) = let curPrec = 4 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " ^ " . showsPrec curPrec b
    showsPrec contextPrec (Iff a b) = let curPrec = 2 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " == " . showsPrec curPrec b
    showsPrec contextPrec (Impl a b) = let curPrec = 1 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " -> " . showsPrec curPrec b
    showsPrec contextPrec (RImpl a b) = let curPrec = 1 in showParen (contextPrec > curPrec) $ showsPrec curPrec a . showString " <- " . showsPrec curPrec b

-- Extract list of variable names from expression
variableList :: Expr -> [Name]
variableList Top = []
variableList Bot = []
variableList (Var x) = [x]
variableList (Not e) = variableList e
variableList (Or a b) = union (variableList a) (variableList b)
variableList (And a b) = union (variableList a) (variableList b)
variableList (Xor a b) = union (variableList a) (variableList b)
variableList (Iff a b) = union (variableList a) (variableList b)
variableList (Impl a b) = union (variableList a) (variableList b)
variableList (RImpl a b) = union (variableList a) (variableList b)

-- Evaluate expression using specified interpretation
eval :: [(Name, Value)] -> Expr -> Value
eval _ Top = True
eval _ Bot = False
eval interp (Var x) = let res = lookup x interp in
                                if (res == Nothing) then
                                    error ("Variable " ++ show x ++ " is not in interpretation list")
                                else
                                    fromJust res
eval interp (Not e) = not (eval interp e)
eval interp (Or a b) = eval interp a || eval interp b
eval interp (And a b) = eval interp a && eval interp b
eval interp (Xor a b) = eval interp a /= eval interp b
eval interp (Iff a b) = eval interp a == eval interp b
eval interp (Impl a b) = not (eval interp a) || eval interp b
eval interp (RImpl a b) = eval interp a || not (eval interp b)

-- Transform expression into equivalent, but
-- with only Not, Or, And, Top and Bot nodes
-- (rewrite Xor, Iff, ... with Not, Or, And)
reduceOperators :: Expr -> Expr
reduceOperators Top = Top
reduceOperators Bot = Bot
reduceOperators (Var x) = Var x
reduceOperators (Not e) = Not (reduceOperators e)
reduceOperators (Or a b) = Or (reduceOperators a) (reduceOperators b)
reduceOperators (And a b) = And (reduceOperators a) (reduceOperators b)
reduceOperators (Xor a b) = let x = reduceOperators a
                                y = reduceOperators b in Or (And x (Not y)) (And (Not x) y)
reduceOperators (Iff a b) = let x = reduceOperators a
                                y = reduceOperators b in Or (And x y) (And (Not x) (Not y))
reduceOperators (Impl a b) = let x = reduceOperators a
                                 y = reduceOperators b in Or (Not x) y
reduceOperators (RImpl a b) = let x = reduceOperators a
                                  y = reduceOperators b in Or x (Not y)

-- Transform expression to NNF form
toNNF :: Expr -> Expr
toNNF e = convertToNNF False (reduceOperators e) where
    convertToNNF :: Bool -> Expr -> Expr
    convertToNNF invert Top = if (invert) then Bot else Top
    convertToNNF invert Bot = if (invert) then Top else Bot
    convertToNNF invert (Var x) = if (invert) then Not (Var x) else Var x
    convertToNNF invert (Not e) = convertToNNF (not invert) e
    convertToNNF invert (Or a b) = if (invert) then And (convertToNNF True a) (convertToNNF True b) else Or (convertToNNF False a) (convertToNNF False b)
    convertToNNF invert (And a b) = if (invert) then Or (convertToNNF True a) (convertToNNF True b) else And (convertToNNF False a) (convertToNNF False b)
    convertToNNF invert _ = error "There must be only literals, or, and, not"

-- Function to build clauses like
-- Or (Or (Var "a") (Var "b")) (Or (Var "c") (Var "d")) or like
-- And (And (Var "a") (Var "b")) (And (Var "c") (Var "d"))
buildClauseFromListOfLiterals :: (Expr -> Expr -> Expr) -> [Expr] -> Expr
buildClauseFromListOfLiterals _ [] = error "List of variables can't be empty"
buildClauseFromListOfLiterals _ [Top] = Top
buildClauseFromListOfLiterals _ [Bot] = Bot
buildClauseFromListOfLiterals _ [Var x] = Var x
buildClauseFromListOfLiterals _ [Not (Var x)] = Not (Var x)
buildClauseFromListOfLiterals _ [_] = error "There can be only literals in clause list"
buildClauseFromListOfLiterals operation (Top : t) = operation Top (buildClauseFromListOfLiterals operation t)
buildClauseFromListOfLiterals operation (Bot : t) = operation Bot (buildClauseFromListOfLiterals operation t)
buildClauseFromListOfLiterals operation ((Var x) : t) = operation (Var x) (buildClauseFromListOfLiterals operation t)
buildClauseFromListOfLiterals operation ((Not (Var x)) : t) = operation (Not (Var x)) (buildClauseFromListOfLiterals operation t)
buildClauseFromListOfLiterals _ (_ : t) = error "There can be only literals in clause list"

-- Transform expression to DNF form
toDNF :: Expr -> Expr
toDNF e = buildDNFFromClauses (getClausesForDNF (toNNF e)) where
    getClausesForDNF :: Expr -> [[Expr]]
    getClausesForDNF Top = [[Top]]
    getClausesForDNF Bot = [[Bot]]
    getClausesForDNF (Var x) = [[Var x]]
    getClausesForDNF (Not (Var x)) = [[Not (Var x)]]
    getClausesForDNF (Not _) = error "Expr must be in NNF"
    getClausesForDNF (Or a b) = getClausesForDNF a ++ getClausesForDNF b
    getClausesForDNF (And a b) = (++) <$> getClausesForDNF a <*> getClausesForDNF b
    getClausesForDNF _ = error "There must be only literals, or, and, not"

    buildDNFFromClauses :: [[Expr]] -> Expr
    buildDNFFromClauses list = helper (nub (map nub list)) where -- removing duplicates
        helper :: [[Expr]] -> Expr
        helper [] = error "List of clauses can't be empty"
        helper [clause] = buildClauseFromListOfLiterals And clause
        helper (clause : t) = Or (buildClauseFromListOfLiterals And clause) (helper t)

-- Transform expression to NNF form
toCNF :: Expr -> Expr
toCNF e = buildCNFFromClauses (getClausesForCNF e) where
    -- Using State monad to create new temp variables
    getNewTmpVar :: State Int Expr
    getNewTmpVar = do
        modify (+ 1)
        n <- get
        return (Var ("_" ++ show n))

    -- Doing Tseitin transformation of an expression
    tseitinTransformation :: Expr -> State Int ([Expr], Expr)
    tseitinTransformation Top = do
        newVar <- getNewTmpVar
        return ([Iff newVar Top], newVar)
    tseitinTransformation Bot = do
        newVar <- getNewTmpVar
        return ([Iff newVar Bot], newVar)
    tseitinTransformation (Var x) = do
        return ([], Var x)
    tseitinTransformation (Not e) = do
        newVar <- getNewTmpVar
        (list, lastVar) <- tseitinTransformation e
        return ((Iff newVar (Not lastVar)) : list, newVar)
    tseitinTransformation (Or a b) = templateTseitinTransformation Or a b
    tseitinTransformation (And a b) = templateTseitinTransformation And a b
    tseitinTransformation (Xor a b) = templateTseitinTransformation Xor a b
    tseitinTransformation (Iff a b) = templateTseitinTransformation Iff a b
    tseitinTransformation (Impl a b) = templateTseitinTransformation Impl a b
    tseitinTransformation (RImpl a b) = templateTseitinTransformation RImpl a b

    -- Since transformations for all binary operators look very similar
    -- we can create a template for them
    templateTseitinTransformation :: (Expr -> Expr -> Expr) -> Expr -> Expr -> State Int ([Expr], Expr)
    templateTseitinTransformation operation a b = do
        newVar <- getNewTmpVar
        (listA, lastVarA) <- tseitinTransformation a
        (listB, lastVarB) <- tseitinTransformation b
        return ([Iff newVar (operation lastVarA lastVarB)] ++ listA ++ listB, newVar)

    -- After Tseitin transformation we have a list of formulas like
    -- x == (a -> b)
    -- x == ~y
    -- y == z | t
    -- ...
    -- Each formula has not more than 5 variables,
    -- so CNFs for all this formulas can be precalculated.
    -- Here there are hardcoded CNFs for all possible formulas
    getClausesForSimpleCNF :: Expr -> [[Expr]]
    getClausesForSimpleCNF (Iff (Var x) Top) = [[Var x]]
    getClausesForSimpleCNF (Iff (Var x) Bot) = [[Not (Var x)]]
    getClausesForSimpleCNF (Iff (Var x) (Var y)) = [[Not (Var x), Var y], [Var x, Not (Var y)]]
    getClausesForSimpleCNF (Iff (Var x) (Not (Var y))) = [[Var x, Var y], [Not (Var x), Not (Var y)]]
    getClausesForSimpleCNF (Iff (Var x) (Or (Var a) (Var b))) = [[Var x, Var a, Not (Var b)], [Var x, Not (Var a), Var b], [Var x, Not (Var a), Not (Var b)], [Not (Var x), Var a, Var b]]
    getClausesForSimpleCNF (Iff (Var x) (And (Var a) (Var b))) = [[Var x, Not (Var a), Not (Var b)], [Not (Var x), Var a, Var b], [Not (Var x), Var a, Not (Var b)], [Not (Var x), Not (Var a), Var b]]
    getClausesForSimpleCNF (Iff (Var x) (Xor (Var a) (Var b))) = [[Var x, Var a, Not (Var b)], [Var x, Not (Var a), Var b], [Not (Var x), Var a, Var b], [Not (Var x), Not (Var a), Not (Var b)]]
    getClausesForSimpleCNF (Iff (Var x) (Iff (Var a) (Var b))) = [[Var x, Var a, Var b], [Var x, Not (Var a), Not (Var b)], [Not (Var x), Var a, Not (Var b)], [Not (Var x), Not (Var a), Var b]]
    getClausesForSimpleCNF (Iff (Var x) (Impl (Var a) (Var b))) = [[Var x, Var a, Var b], [Var x, Var a, Not (Var b)], [Var x, Not (Var a), Not (Var b)], [Not (Var x), Not (Var a), Var b]]
    getClausesForSimpleCNF (Iff (Var x) (RImpl (Var a) (Var b))) = [[Var x, Var a, Var b], [Var x, Not (Var a), Var b], [Var x, Not (Var a), Not (Var b)], [Not (Var x), Var a, Not (Var b)]]
    getClausesForSimpleCNF _ = error "Invalid result of Tseitin transformation"

    getClausesForCNF :: Expr -> [[Expr]]
    getClausesForCNF (Var x) = [[Var x]]
    getClausesForCNF e = let (list, initVar) = evalState (tseitinTransformation e) 0 in
        [initVar] : concat (map getClausesForSimpleCNF list)

    buildCNFFromClauses :: [[Expr]] -> Expr
    buildCNFFromClauses list = helper (nub (map nub list)) where
        helper :: [[Expr]] -> Expr
        helper [] = error "List of clauses can't be empty"
        helper [clause] = buildClauseFromListOfLiterals Or clause
        helper (clause : t) = And (buildClauseFromListOfLiterals Or clause) (helper t)

{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Formula where

import System.IO
import Data.List
import Control.Monad
import Data.Containers.ListUtils
import Text.Parsec
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Test.QuickCheck hiding (Fun, (===))

import Utils

-- Variable names are just strings
type VarName = String
type FunName = String
type RelName = String

data GenTerm a = Var a | Fun FunName [GenTerm a] deriving (Eq, Show, Ord)

type Term = GenTerm VarName

variables :: Term -> [VarName]
variables (Var x) = [x]
variables (Fun _ ts) = nubOrd $ concatMap variables ts

type FunInt a = FunName -> [a] -> a
type Env a = VarName -> a

evalTerm :: FunInt a -> Env a -> Term -> a
evalTerm _ rho (Var x) = rho x
evalTerm int rho (Fun f ts) = int f $ map (evalTerm int rho) ts

-- our inductive type for first-order logic formulas
data Formula =
      F
    | T
    | Rel RelName [Term]
    | Not Formula
    | Or Formula Formula
    | And Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    | Exists VarName Formula
    | Forall VarName Formula deriving (Eq, Show, Ord)

type Substitution = Env Term
type SATSolver = Formula -> Bool
type FOProver = Formula -> Bool

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nubOrd $ concatMap varsT ts

-- find all free variables
fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = varsT (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nubOrd $ fv phi ++ fv psi
fv (Or phi psi) = nubOrd $ fv phi ++ fv psi
fv (Implies phi psi) = nubOrd $ fv phi ++ fv psi
fv (Iff phi psi) = nubOrd $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

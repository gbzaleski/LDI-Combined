{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Eta reduce" #-}

module PropositionalLogic where
import Data.List
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe
import Utils
import Data.Containers.ListUtils ( nubOrd )

-- Variable names are just strings
type PropName = String

-- generation of fresh variable names
fresh :: [PropName] -> PropName
fresh vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

data Formula =
    T
  | F
  | Prop PropName -- atomic formulas
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  deriving (Eq)

instance Show Formula where
    show T = "True"
    show F = "False"
    show (Prop name) = name
    show (Not f) = "(~" ++ show f ++ ")"
    show (And f1 f2) = "(" ++ show f1 ++ " ^ " ++ show f2 ++ ")"
    show (Or f1 f2) = "(" ++ show f1 ++ " V " ++ show f2 ++ ")"
    show (Implies f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
    show (Iff f1 f2) = "(" ++ show f1 ++ " <=> " ++ show f2 ++ ")"

type Valuation = PropName -> Bool

eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ro = ro p
eval (Not phi) ro = not (eval phi ro)
eval (And phi psi) ro = (eval phi ro) && (eval psi ro)
eval (Or phi psi) ro = (eval phi ro) || (eval psi ro)
eval (Implies phi psi) ro = not (eval phi ro) || eval psi ro
eval (Iff phi psi) ro = eval phi ro == eval psi ro

variables :: Formula -> [PropName]
variables = nubOrd . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ro x True, update ro x False] | ro <- valuations xs]

type SATSolver = Formula -> Bool

satisfiable :: SATSolver
satisfiable phi = or [eval phi ro | ro <- valuations (variables phi)]

tautology :: Formula -> Bool
tautology phi = and [eval phi ro | ro <- valuations (variables phi)]

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf r@(Prop p) = r
nnf (Not phi) = case nnf phi of
  T -> F
  F -> T
  Not phi' -> phi'
  Or phi' psi' -> And (nnf (Not phi')) (nnf (Not psi'))
  And phi' psi' -> Or (nnf (Not phi')) (nnf (Not psi'))
  phi' -> Not phi'
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = Or (nnf (And phi psi)) (nnf (And (Not phi) (Not psi)))

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type CNFClause = [Literal]
type CNF = [CNFClause]

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

positive_literals :: CNFClause -> [PropName]
positive_literals ls = nubOrd [p | Pos p <- ls]

negative_literals :: CNFClause -> [PropName]
negative_literals ls = nubOrd [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nubOrd $ positive_literals ls ++ negative_literals ls

cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (phi `And` psi) = go phi ++ go psi
  go (phi `Or` psi) = [as ++ bs | as <- go phi, bs <- go psi]
  go _ = error "Not possible to get there"

equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable phi psi = satisfiable phi == satisfiable psi

-- Assuming no variable starts with "p$v_" in the original formula.
-- Alternatively we can start with finding the longest PropName v and then using v + "_".
newVar :: Int -> PropName
newVar n = "p$v_" ++ show n

-- Representative is either Prop p | Not (Prop p) | T | F
-- -> (Repr, CNF clauses)
ecnf' :: Formula -> Int -> (Formula, CNF)
ecnf' T n = (T, [])
ecnf' F n = (F, [])
ecnf' (Prop p) n = (Prop p, [])
ecnf' (Not f) n = let (v1, cnf1) = ecnf' f (2*n) in (Not v1, cnf1)
ecnf' (And phi psi) n = ecnf_bin And phi psi n
ecnf' (Or phi psi) n = ecnf_bin Or phi psi n
ecnf' (Implies phi psi) n = ecnf_bin Implies phi psi n
ecnf' (Iff phi psi) n = ecnf_bin Iff phi psi n

ecnf_bin :: (Formula -> Formula -> Formula) -> Formula -> Formula -> Int -> (Formula, CNF)
ecnf_bin bin_op phi psi n = let (v1, cnf1) = ecnf' phi (2*n)
                                (v2, cnf2) = ecnf' psi (2*n+1)
                                v0 = newVar n
                    in (Prop v0, cnf1 ++ cnf2 ++ cnf (Iff (Prop v0) (bin_op v1 v2)))

ecnf :: Formula -> CNF
ecnf phi = let (v, cnf1) = ecnf' phi 1 in cnf v ++ cnf1

remove_tautologies :: CNF -> CNF
remove_tautologies phi = filter (not . is_tautology) phi where
  is_tautology :: CNFClause -> Bool
  is_tautology [] = False
  is_tautology ((Pos p):tail) = elem (Neg p) tail || is_tautology tail
  is_tautology ((Neg p):tail) = elem (Pos p) tail || is_tautology tail

one_literal :: CNF -> CNF
one_literal phi = let iterated_phi = one_literal_util phi in 
  if phi == iterated_phi 
    then phi
    else one_literal iterated_phi where 
  one_literal_util :: CNF -> CNF
  one_literal_util phi = let single_vars = concat $ filter (\c -> length c == 1) $ map nubOrd phi in foldl reduce_ol phi single_vars
  reduce_ol :: CNF -> Literal -> CNF
  reduce_ol clause lit = map (filter (\elem -> elem /= opposite lit)) $ filter (notElem lit) clause

affirmative_negative :: CNF -> CNF
affirmative_negative phi = let single_variables = filter (\lit -> opposite lit `notElem` concat phi) (concat phi) in
  if single_variables /= [] then affirmative_negative $ reduce_an (head single_variables) phi else phi where
  opposite (Pos p) = Neg p
  opposite (Neg p) = Pos p
  reduce_an p phi = filter (notElem p) phi

-- Davis-Putnam algorithm
dp :: CNF -> Bool
dp psi = let cleared_psi = affirmative_negative $ one_literal $ remove_tautologies psi in
  if psi == cleared_psi then
    if psi == []
      then True
    else
      if elem [] psi then False
      else
        let lit = head (head cleared_psi) in
        dp (flag lit cleared_psi) || dp (flag (opposite_lit lit) cleared_psi) -- resolution
  else dp cleared_psi where
    opposite_lit :: Literal -> Literal
    opposite_lit (Pos x) = Neg x
    opposite_lit (Neg x) = Pos x
    flag :: Literal -> CNF -> CNF
    flag lit phi = filter (notElem lit) (map (filter (/= opposite_lit lit)) phi)

sat_DP :: SATSolver
sat_DP form = dp cnf where
  cnf = ecnf form




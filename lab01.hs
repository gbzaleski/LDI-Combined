{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

-- Grzegorz B. Zaleski (418494)

import Data.List
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe

-- updating a function
update :: Eq a => (a -> b) -> a -> b -> a -> b
update ro x v = \y -> if x == y then v else ro y

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

todo :: a
todo = undefined

-- propositional variable names are just strings
type PropName = String

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And -- input with "\and"

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

satisfiable_formulas = [
    p ∧ q ∧ s ∧ p,
    T,
    p,
    Not p,
    (p ∨ q ∧ r) ∧ (Not p ∨ Not r),
    (p ∨ q) ∧ (Not p ∨ Not q)
  ]

unsatisfiable_formulas = [
    p ∧ q ∧ s ∧ Not p,
    T ∧ F,
    F,
    (p ∨ q ∧ r) ∧ Not p ∧ Not r,
    (p ⇔ q) ∧ (q ⇔ r) ∧ (r ⇔ s) ∧ (s ⇔ Not p)
  ]

instance Arbitrary Formula where
    arbitrary = sized f where

      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- truth valuations
type Valuation = PropName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ro = ro p
eval (Not phi) ro = not (eval phi ro)
eval (And phi psi) ro = eval phi ro && eval psi ro
eval (Or phi psi) ro = eval phi ro || eval psi ro
eval (Implies phi psi) ro = not (eval phi ro) || eval psi ro
eval (Iff phi psi) ro = eval phi ro == eval psi ro

ro0 :: b -> Bool
ro0 = const True
ro1 :: b -> Bool
ro1 = const False
ro2 :: String -> Bool
ro2 = update ro0 "p" False

test_eval :: Bool
test_eval =
  eval (p ∧ Not p) ro0 == False &&
  eval (p ∧ Not p) ro1 == False &&
  eval (p ∨ q) ro2 == True

-- quickCheck test_eval

-- check that the eval function is efficient
-- ifformula 3 == Iff (Iff (Iff T T) T) T
ifformula :: Int -> Formula
ifformula 0 = T
ifformula n = Iff (ifformula (n-1)) T

-- this should evaluate within a fraction of second
test_eval2 :: Bool
test_eval2 = eval (ifformula 23) (const True) == True

t1 = quickCheck test_eval2

variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi
 -- go _ = error "not a propositional formula"

-- the list of all valuations on a given list of variables
valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ro x True, update ro x False] | ro <- valuations xs]

satisfiable :: Formula -> Bool
satisfiable phi = or [eval phi ro | ro <- valuations (variables phi)]

tautology :: Formula -> Bool
tautology phi = and [eval phi ro | ro <- valuations (variables phi)]

run_v :: Formula -> [Bool]
run_v phi = [eval phi ro | ro <- valuations (variables phi)]

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Prop _) = True
is_nnf (Not (Prop _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False
--is_nnf _ = error "not a propositional formula"

t3 = quickCheck $ is_nnf (Not p ∧ (q ∨ (r ∧ s))) && not (is_nnf $ Not (p ∨ q))

nnf :: Formula -> Formula
nnf phi = nnify2 $ nnify1 phi where
  nnify1 :: Formula -> Formula
  nnify1 (Implies phi psi) = Or (Not (nnify1 phi)) (nnify1 psi)
  nnify1 (Iff phi psi) = And (Or (Not (nnify1 phi)) (nnify1 psi)) (Or (nnify1 phi) (Not (nnify1 psi)))
  nnify1 T = T
  nnify1 F = F
  nnify1 (Prop p) = Prop p
  nnify1 (Not phi) = Not (nnify1 phi)
  nnify1 (And phi psi) = And (nnify1 phi) (nnify1 psi)
  nnify1 (Or phi psi) = Or (nnify1 phi) (nnify1 psi)

  nnify2 :: Formula -> Formula
  nnify2 (Not (Not psi)) = nnify2 psi
  nnify2 (Not (And phi psi)) = Or (nnify2 (Not phi)) (nnify2 (Not psi))
  nnify2 (Not (Or phi psi)) = And (nnify2 (Not phi)) (nnify2 (Not psi))
  nnify2 (Not T) = F
  nnify2 (Not F) = T
  nnify2 T = T
  nnify2 F = F
  nnify2 (Prop p) = Prop p
  nnify2 (Not (Prop p)) = Not (Prop p)
  nnify2 (And phi psi) = And (nnify2 phi) (nnify2 psi)
  nnify2 (Or phi psi) = Or (nnify2 phi) (nnify2 psi)
  nnify2 (Iff phi psi) = error "Not possible to get there"
  nnify2 (Implies phi psi) = error "Not possible to get there"
  nnify2 (Not (Iff phi psi)) = error "Not possible to get there"
  nnify2 (Not (Implies phi psi)) = error "Not possible to get there"


prop_nnf :: Formula -> Bool
prop_nnf phi = let psi = nnf phi in is_nnf psi && tautology (phi ⇔ psi)

t4 = quickCheck prop_nnf

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

type DNFClause = [Literal]
type DNF = [DNFClause]

dnf2formula :: DNF -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

toDNF :: Formula -> DNF 
toDNF F = []
toDNF T = [[]]
toDNF (Prop p) = [[Pos p]] 
toDNF (Not (Prop p)) = [[Neg p]]
toDNF (Or phi psi) = nub $ toDNF phi ++ toDNF psi 
toDNF (And phi psi) = let phi2 = toDNF phi 
                          psi2 = toDNF psi 
                     in if psi2 == [] || phi2 == [] 
                        then [] 
                        else [nub (el1 ++ el2) | el1 <- psi2, el2 <- phi2]
toDNF _ = error "Not possible to get there"

dnf :: Formula -> DNF
dnf psi = toDNF $ nnf psi

test_dnf :: Formula -> Bool
test_dnf phi = tautology $ phi ⇔ dnf2formula (dnf phi)

t5 = quickCheckWith (stdArgs {maxSize = 20}) test_dnf

type SATSolver = Formula -> Bool

sat_dnf :: SATSolver
sat_dnf phi = let psi = dnf phi in any check_clause psi where
    check_clause :: DNFClause -> Bool
    check_clause [] = True
    check_clause ((Pos p):tail) = notElem (Neg p) tail && check_clause tail
    check_clause ((Neg p):tail) = notElem (Pos p) tail && check_clause tail

prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi

t6 = quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf

test_solver :: SATSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

t7 = quickCheck (test_solver sat_dnf)

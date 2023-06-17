{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

------------------------------------------
------ Grzegorz B. Zaleski (418494) ------
------------------------------------------

module Main where

import Data.List
import System.IO
import Data.Containers.ListUtils
import Formula
import Utils
import Parser hiding (one)
import FirstOrderLogic
import qualified PropositionalLogic as PL
import Data.Map (Map, fromList, (!))

-- First order logic prover
prover :: Formula -> Bool
prover phi
  | free_vars == [] = not $ satFormula substituted 0
  | all (\(_, arity) -> arity == 0) signatures = not $ satFormula substituted (length herbranded)
  | otherwise = not (isAntitautology phi) && not (satIter substituted 0) where
    cleared = clear_qf phi
    negated = Not cleared
    skolemised = skolemise negated
    prefixless = remove_universal_qf_prefix skolemised
    free_vars = fv prefixless
    signatures = sig prefixless
    herbranded = herbrandTuples (length free_vars) signatures
    substituted = [(`subst` prefixless) (sigma terms free_vars) | terms <- herbranded]


-- Antitautology checker (instant answer case)
isAntitautology :: Formula -> Bool
isAntitautology (Exists _ phi) = isAntitautology phi
isAntitautology (Forall _ phi) = isAntitautology phi
isAntitautology (Rel _ _) = True
isAntitautology (Not(Rel _ _)) = True
isAntitautology _ = False

-- Removes uneesenary quantifiers
clear_qf :: Formula -> Formula
clear_qf phi = filterFormula phi (usedVars phi) where

  usedVars :: Formula -> [VarName]
  usedVars T = []
  usedVars F = []
  usedVars (Rel _ ts) = nubOrd $ concatMap goRel ts
  usedVars (Not phi) = usedVars phi
  usedVars (And phi psi) = nubOrd $ usedVars phi ++ usedVars psi
  usedVars (Or phi psi) = nubOrd $ usedVars phi ++ usedVars psi
  usedVars (Implies phi psi) = nubOrd $ usedVars phi ++ usedVars psi
  usedVars (Iff phi psi) = nubOrd $ usedVars phi ++ usedVars psi
  usedVars (Exists x phi) = usedVars phi
  usedVars (Forall x phi) = usedVars phi

  goRel :: Term -> [VarName]
  goRel (Var tag) = [tag]
  goRel (Fun _ ts) = nubOrd $ concatMap goRel ts

  filterFormula :: Formula -> [VarName] -> Formula
  filterFormula T lst = T
  filterFormula F lst = F
  filterFormula phi@(Rel _ _) lst = phi
  filterFormula (Not phi) lst = Not $ filterFormula phi lst
  filterFormula (And phi psi) lst = And (filterFormula phi lst) (filterFormula psi lst)
  filterFormula (Or phi psi) lst = Or (filterFormula phi lst) (filterFormula psi lst)
  filterFormula (Implies phi psi) lst = Implies (filterFormula phi lst) (filterFormula psi lst)
  filterFormula (Iff phi psi) lst = Iff (filterFormula phi lst) (filterFormula psi lst)
  filterFormula (Exists x phi) lst = if x `elem` lst then Exists x (filterFormula phi lst) else phi
  filterFormula (Forall x phi) lst = if x `elem` lst then Forall x (filterFormula phi lst) else phi

-- Position matching of free variables
sigma :: [Term] -> [VarName] -> VarName -> Term
sigma terms free_vars = rho where
    rho :: VarName -> Term
    rho v = case v `elemIndex` free_vars of
            Just i -> terms !! i
            Nothing -> Var v

-- Going over possible valuations to find contradiction
-- Abandoned idea for timout cutoff to find contradiction
satIter :: [Formula] -> Int -> Bool
satIter forms k = satFormula forms k && satIter forms (k + 1)

-- DP Prover for propositional logic
satFormula :: [Formula] -> Int -> Bool
satFormula forms k = PL.sat_DP psi where
    phi = if k > 0 then foldl1 And (take k forms) else head forms
    psi = convert phi

-- Herbrand algorithm
herbrandTuples :: Int -> Signature -> [[Term]]
herbrandTuples m sig =
  if funs == []
    then groundTuples cons funs m 0
    else concatMap (reverse . groundTuples cons funs m) [0..] where

  groundTerms :: [Term] -> [(FunName, Int)] -> Int -> [Term]
  groundTerms cons funs n =
    if n == 0
      then cons
      else concatMap (\(ftag, arity) -> Fun ftag <$> groundTuples cons funs arity (n - 1)) funs

  groundTuples :: [Term] -> [(FunName, Int)] -> Int -> Int -> [[Term]]
  groundTuples cons funs m n =
    if m == 0
      then [[] | n == 0]
      else [h:t | k <- [0..n], h <- groundTerms cons funs k, t <- groundTuples cons funs (m - 1) (n - k)]

  funs = filter (\(_, arity) -> arity /= 0) sig
  c = constants sig
  cons = if c == [] then [Fun dummyVariableName []] else c -- Add dummy const to make set nonempty

-- Converting first order formula to the propositional logic
convert :: Formula -> PL.Formula
convert phi = convertFormula phi (mapRelations (atomicFormulas phi)) where

  mapRelations :: [Formula] -> Map Formula PL.Formula
  mapRelations forms = fromList $ zipWith (\ phi i -> (phi, PL.Prop (show i))) forms [0..]

  convertFormula :: Formula -> Map Formula PL.Formula -> PL.Formula
  convertFormula T _ = PL.T
  convertFormula F _ = PL.F
  convertFormula phi@(Rel _ _) map = map ! phi
  convertFormula (Not phi) map = PL.Not (convertFormula phi map)
  convertFormula (And phi psi) map = PL.And (convertFormula phi map) (convertFormula psi map)
  convertFormula (Or phi psi) map = PL.Or (convertFormula phi map) (convertFormula psi map)
  convertFormula (Implies phi psi) map = PL.Implies (convertFormula phi map) (convertFormula psi map)
  convertFormula (Iff phi psi) map = PL.Iff (convertFormula phi map) (convertFormula psi map)
  convertFormula _ _ = error "Not possible to get there"

-- Main function
main :: IO ()
main = do
  eof <- hIsEOF stdin
  if eof
      then return ()
      else do
        line <- getLine -- read the input
        let phi = parseString line -- call the parser 
        if prover phi -- call the prover
          then putStrLn "1" -- write 1 if the formula is a tautology
          else putStrLn "0" -- write 0 if the formula is not a tautology
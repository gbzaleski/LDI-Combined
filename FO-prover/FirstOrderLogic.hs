{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
-- Grzegorz B. Zaleski (418494)

module FirstOrderLogic where

import Formula
import Utils
import Data.List
import Control.Monad
import Control.Monad.State
import Data.Containers.ListUtils
import GHC.Num (Num(negate))

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges [] = []
merges (as:ass) = merge as (merges ass)

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nubOrd $ vars phi ++ vars psi
vars (Or phi psi) = nubOrd $ vars phi ++ vars psi
vars (Implies phi psi) = nubOrd $ vars phi ++ vars psi
vars (Iff phi psi) = nubOrd $ vars phi ++ vars psi
vars (Exists x phi) = nubOrd $ x : vars phi
vars (Forall x phi) = nubOrd $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = x `notElem` vars phi

-- enumerate variants of a variable name
variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

substT :: Substitution -> Term -> Term
substT par (Var x) = par x
substT par (Fun f ts) = Fun f (map (substT par) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst par (Rel r ts) = Rel r $ map (substT par) ts
subst par (Not phi) = Not $ subst par phi
subst par (And phi psi) = And (subst par phi) (subst par psi)
subst par (Or phi psi) = Or (subst par phi) (subst par psi)
subst par (Implies phi psi) = Implies (subst par phi) (subst par psi)
subst par (Iff phi psi) = Iff (subst par phi) (subst par psi)
subst par (Exists x phi) = Exists x (subst (update par x (Var x)) phi)
subst par (Forall x phi) = Forall x (subst (update par x (Var x)) phi)

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, y `notElem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf phi@(Rel tag terms) = phi
nnf (Not pphi) = case nnf pphi of
  T -> F
  F -> T
  phi@(Rel _ _) -> Not phi
  Not phi@(Rel _ _) -> phi
  And phi psi -> Or (nnf (Not phi)) (nnf (Not psi))
  Or phi psi -> And (nnf (Not phi)) (nnf (Not psi))
  Exists tag for -> Forall tag (nnf (Not for))
  Forall tag for -> Exists tag (nnf (Not for))
  phi -> error $ "Impossibe to get here " ++ show phi
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = Or (nnf (And phi psi)) (nnf (And (Not phi) (Not psi)))
nnf (Exists tag phi) = Exists tag (nnf phi)
nnf (Forall tag phi) = Forall tag (nnf phi)

-- prenex normal form (all quantifiers in front)
pnf :: Formula -> Formula
pnf psi = pnfUtil (nnf psi) where
  pnfUtil :: Formula -> Formula
  pnfUtil T = T
  pnfUtil F = F
  pnfUtil phi@(Rel _ _) = phi
  pnfUtil phi@(Not (Rel _ _)) = phi
  pnfUtil (Exists tag phi) = Exists tag (pnfUtil phi)
  pnfUtil (Forall tag phi) = Forall tag (pnfUtil phi)
  pnfUtil (And phi psi) = pnfUtil_bin And (pnfUtil phi) (pnfUtil psi)
  pnfUtil (Or phi psi)  = pnfUtil_bin Or (pnfUtil phi) (pnfUtil psi)
  pnfUtil phi = error $ "Impossibe to get here " ++ show phi

  pnfUtil_bin :: (Formula -> Formula -> Formula) -> Formula -> Formula -> Formula
  pnfUtil_bin bin_op (Forall tag phi) psi = extract_qf Forall tag bin_op phi psi
  pnfUtil_bin bin_op (Exists tag phi) psi = extract_qf Exists tag bin_op phi psi
  pnfUtil_bin bin_op phi (Forall tag psi) = extract_qf Forall tag bin_op psi phi
  pnfUtil_bin bin_op phi (Exists tag psi) = extract_qf Exists tag bin_op psi phi
  pnfUtil_bin bin_op phi psi = bin_op phi psi

  extract_qf :: (VarName -> Formula -> Formula) -> VarName -> (Formula -> Formula -> Formula) -> Formula -> Formula -> Formula
  extract_qf existential tag bin_op phi psi =
    if tag `freshIn` psi
      then existential tag (pnfUtil_bin bin_op phi psi)
      else let new_tag = freshVariant tag (bin_op phi psi) in
        existential new_tag (pnfUtil_bin bin_op (rename tag new_tag phi) psi)

close_formula :: Formula -> Formula
close_formula phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Exists x $ go xs

miniscope :: Formula -> Formula
miniscope phi = phi

skolem_replace :: Formula -> Formula
skolem_replace phi = go Var [] phi where
  go :: Substitution -> [Term] -> Formula -> Formula
  go _ _ T = T
  go _ _ F = F
  go par names (Rel r ts) = Rel r $ map (substT par) ts
  go par names (Not phi) = Not $ go par names phi
  go par names (And phi psi) = And (go par names phi) (go par names psi)
  go par names (Or phi psi) = Or (go par names phi) (go par names psi)
  go par names (Implies phi psi) = Implies (go par names phi) (go par names psi)
  go par names (Iff phi psi) = Iff (go par names phi) (go par names psi)
  go par names (Exists x phi) = go (update par x (Fun x names)) names phi
  go par names (Forall x phi) = Forall x (go par (Var x:names) phi)

skolemise :: Formula -> Formula
skolemise phi = skolemise_result where
                  closed = close_formula phi -- Step 1 - Close
                  nnfed = nnf closed -- Step 2 - NNF
                  freshened_nnf = fresh nnfed -- Step 3 - Fresh
                  miniscoped = miniscope freshened_nnf -- Step 4 - Miniscope (optional, currently ignored)
                  skolem_replaced = skolem_replace miniscoped -- Step 5 - Skolem-replace
                  skolemise_result = pnf skolem_replaced -- Step 6 - PNF
-- It's important to note that the Skolem form of a formula is not equivalent to the original formula, 
--    but a set of formulas is satisfiable if and only if the Skolem form of the set of formulas is satisfiable

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nubOrd $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nubOrd $ sig phi ++ sig psi
sig (Or phi psi) = nubOrd $ sig phi ++ sig psi
sig (Implies phi psi) = nubOrd $ sig phi ++ sig psi
sig (Iff phi psi) = nubOrd $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = [Fun c [] | (c, 0) <- s]

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances phi ts = map (`subst` phi) (functions (fv phi) ts)

atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ ts) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = nubOrd $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nubOrd $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nubOrd $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nubOrd $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

remove_universal_qf_prefix :: Formula -> Formula
remove_universal_qf_prefix (Forall v phi) = remove_universal_qf_prefix phi
remove_universal_qf_prefix phi = phi

dummyVariableName:: String
dummyVariableName = "dv"

{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
-- Grzegorz B. Zaleski (418494)

import Data.List
import Control.Monad
import Control.Monad.State
import Test.QuickCheck hiding (Fun, (==>))
import GHC.Num (Num(negate))

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x | x == a = b
               | otherwise = f x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

-- all possible ways to split n into the sum of stricly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

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

type VarName = String
type FunName = String
type RelName = String

-- enumerate variants of a variable name
variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

-- instance {-# OVERLAPPING #-} Arbitrary VarName where
--   arbitrary = elements ["x", "y", "z", "t"]

-- instance {-# OVERLAPPING #-} Arbitrary FunName where
--   arbitrary = elements ["f", "g", "h", "i"]

instance {-# OVERLAPPING #-} Arbitrary RelName where
  arbitrary = elements ["R", "S", "T", "U"]

data Term = Var VarName | Fun FunName [Term] deriving (Eq, Ord, Show)

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

instance Arbitrary Term where
  arbitrary = resize 8 $ sized f where
    f size | size == 0 || size == 1 = do x <- arbitrary
                                         return $ Var x
           | otherwise = frequency [ (1, go sizes) | sizes <- catalan size]
              where go sizes = do ts <- sequence $ map f sizes
                                  return $ Fun "f" ts

data Formula =
    T |
    F |
    Rel RelName [Term] |
    Not Formula |
    And Formula Formula |
    Or Formula Formula |
    Implies Formula Formula |
    Iff Formula Formula |
    Exists VarName Formula |
    Forall VarName Formula deriving (Eq, Ord, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"

instance Arbitrary Formula where
  arbitrary = resize 30 $ sized f where
    f 0 = do ts <- arbitrary
             return $ Rel "R" ts
    f size = frequency [
      (1, liftM Not (f (size - 1))),
      (4, do
            size' <- choose (0, size - 1)
            conn <- oneof $ map return [And, Or, Implies, Iff]
            left <- f $ size'
            right <- f $ size - size' - 1
            return $ conn left right),
      (5, do
            conn <- oneof $ map return [Exists, Forall]
            phi <- f $ size - 1
            x <- arbitrary
            return $ conn x phi)
      ]

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = x `notElem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = varsT (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nub $ fv phi ++ fv psi
fv (Or phi psi) = nub $ fv phi ++ fv psi
fv (Implies phi psi) = nub $ fv phi ++ fv psi
fv (Iff phi psi) = nub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

prop_fv = fv (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == ["y", "z"]
-- >>> quickCheck prop_fv

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

-- par variable
type Substitution = VarName -> Term

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

prop_generalise = generalise (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) 
  == Forall "y" (Forall "z" (Exists "x" (Rel "R" [Fun "f" [Var "x",Var "y"],Var "z"])))

-- >>> quickCheck prop_generalise

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
             let y = head [y | y <- variants x, not $ y `elem` xs]
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

prop_skolemise = skolemise (Forall "x" $ Exists "y" $ Rel "P" [Var "x", Var "y"] /\ Rel "Q" [Var "y"])
  == Forall "x" (And (Rel "P" [Var "x", Fun "y" [Var "x"]]) (Rel "Q" [Fun "y" [Var "x"]]))
-- >>> quickCheck prop_skolemise

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
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
atomicFormulas (And phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- functions atoms [True, False]]
  where atoms = atomicFormulas phi
        ev :: (Formula -> Bool) -> Formula -> Bool
        ev int T = True
        ev int F = False
        ev int atom@(Rel _ _) = int atom
        ev int (Not phi) = not (ev int phi)
        ev int (Or phi psi) = ev int phi || ev int psi
        ev int (And phi psi) = ev int phi && ev int psi
        ev _ phi = error $ "unexpected formula: " ++ show phi

remove_universal_qf_prefix :: Formula -> Formula
remove_universal_qf_prefix (Forall v phi) = remove_universal_qf_prefix phi
remove_universal_qf_prefix phi = phi

dummyVariableName:: String
dummyVariableName = "dv"
checkIfEmpty :: Formula -> [Term] -> [Term]
checkIfEmpty phi term_list = if term_list == [] then [Var $ freshVariant dummyVariableName phi] else term_list

aedecide :: Formula -> Bool
aedecide phi = answer where
                closed = close_formula phi -- Step 1 - Close
                negated = Not closed -- Step 2 - Negate
                skolemised = skolemise negated -- Step 3 - Skolemise 
                prefixless = remove_universal_qf_prefix skolemised -- Step 4 - Remove prefix
                consts_list = checkIfEmpty prefixless $ constants $ sig prefixless -- Check empty
                ground_instances = groundInstances prefixless consts_list -- Step 5 - Ground
                answer = not $ sat (foldl And T ground_instances) -- Step 6 - Check unsatisfability
                
forallImpliesExists = Forall "x" (Rel "r" [Var "x"]) ==> Exists "x" (Rel "r" [Var "x"])
-- >>> aedecide forallImpliesExists

t x y = Rel "t" [Var x, Var y]
lem = Forall "x" $ Forall "y" $ t "x" "y" ∨ (Not $ t "x" "y")
-- >>> aedecide lem

swap = Exists "x" (Forall "y" $ t "x" "y") ==> Forall "y" (Exists "x" $ t "x" "y")
-- >>> aedecide swap

prop_aedecide = aedecide forallImpliesExists && aedecide lem && aedecide swap

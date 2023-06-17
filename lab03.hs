{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

import Data.List
import Control.Monad
import Test.QuickCheck hiding (Fun)

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

-- all possible ways to split n into the sum of stricly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

todo = undefined

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

infixr 5 \/, ∨
-- , ==>
(\/) = Or
(∨) = Or -- input with "\or"
-- (==>) = Implies

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
        (5, do conn <- oneof $ map return [Exists, Forall]
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
x `freshIn` phi = not $ x `elem` vars phi

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

d x = Rel "d" [Var x]
drinker = Exists "x" (d "x" `Implies` Forall "y" (d "y"))

t x y = Rel "t" [Var x, Var y]
lem = Forall "x" $ Forall "y" $ t "x" "y" ∨ (Not $ t "x" "y")

flip = Exists "x" (Forall "y" $ t "x" "y") `Implies` Forall "y" (Exists "x" $ t "x" "y")

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Rel _ _) = True
is_nnf (Not (Rel _ _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False
is_nnf (Exists _ phi) = is_nnf phi
is_nnf (Forall _ phi) = is_nnf phi

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


nnfProp :: Formula -> Bool
nnfProp phi = is_nnf (nnf phi)

-- >>> quickCheck nnfProp

is_pnf :: Formula -> Bool
is_pnf (Forall _ phi) = is_pnf phi
is_pnf (Exists _ phi) = is_pnf phi
is_pnf phi = qf phi where
  -- check whether the formula is quantifier-free
  qf :: Formula -> Bool
  qf (Rel _ _) = True
  qf (Not phi) = qf phi
  qf (And phi psi) = qf phi && qf psi
  qf (Or phi psi) = qf phi && qf psi
  qf (Implies phi psi) = qf phi && qf psi
  qf (Iff phi psi) = qf phi && qf psi
  qf _ = False

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

pnfProp :: Formula -> Bool
pnfProp = is_pnf . pnf

-- >>> quickCheck pnfProp



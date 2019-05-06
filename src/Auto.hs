{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  DataKinds, PolyKinds, AllowAmbiguousTypes #-}
module Auto where

import Theory
import Control.Lens hiding (rewrite)
import Data.Type.Bool



-- | The main combinator to expand out any polynomial into canonical form with terms sorted

canonical :: (Dist a b, Absorb b c, RightAssoc c d, SortTerm d e) => a ~~ e
canonical = dist . absorb . rightAssoc . sortTerm

rewrite :: forall a' a b c d e e' d' c' b'. (Dist a b, Absorb b c, RightAssoc c d,
                 SortTerm d e, e ~ e', Dist a' b',
                Absorb b' c', RightAssoc c' d', SortTerm d' e') => a ~~ a'
rewrite = canonical . (rev canonical)



-- | AUTOMATING DISTRIBUTION

class RDist a b | a -> b where
    rdist' :: Iso' a b

instance RDist a a' => RDist (a * I) (a' * I) where
    rdist' = firsting rdist'
instance RDist a a' => RDist (a * O) (a' * O) where
    rdist' = firsting rdist'
instance RDist a a' => RDist (a * (V b)) (a' * (V b)) where
    rdist' = firsting rdist'

instance (RDist (a * b) ab, RDist (a * c) ac) => RDist (a * (b + c)) (ab + ac) where
    rdist' = rdist . (bimapping rdist' rdist')
instance (RDist a a', RDist (b * c) bc) => RDist (a * (b * c)) (a' * bc) where
    rdist' = (bimapping rdist' rdist')
instance (RDist a a', RDist b b') => RDist (a + b) (a' + b') where
    rdist' = bimapping rdist' rdist'

instance RDist O O where
    rdist' = id
instance RDist I I where
    rdist' = id
instance RDist (V a) (V a) where
    rdist' = id

-- can derive ldist from swapped . rdist' . swapped?

class LDist a b | a -> b where
    ldist' :: Iso' a b
instance (LDist (b * a) ab, LDist (c * a) ac) => LDist ((b + c) * a) (ab + ac) where
    ldist' = ldist . (bimapping ldist' ldist')
instance (LDist (b * c) bc, LDist a a') => LDist ((b * c) * a) (bc * a') where
    ldist' = bimapping ldist' ldist'
instance LDist a a' => LDist (I * a) (I * a') where
    ldist' = seconding ldist'
instance LDist a a' => LDist (O * a) (O * a') where
    ldist' = seconding ldist'
instance LDist a a' => LDist ((V b) * a) ((V b) * a') where
    ldist' = seconding ldist'

instance (LDist a a', LDist b b') => LDist (a + b) (a' + b') where
    ldist' = bimapping ldist' ldist'

instance LDist O O where
    ldist' = id
instance LDist I I where
    ldist' = id
instance LDist (V a) (V a) where
    ldist' = id

type family HasPlus a where
    HasPlus (a + b) = 'True
    HasPlus (a * b) = (HasPlus a) || (HasPlus b)
    HasPlus I = 'False
    HasPlus O = 'False
    HasPlus (V _) = 'False

class Dist' f a b | f a -> b where
    dist' :: a ~~ b
instance (f ~ HasPlus ab', LDist (a * b) ab, 
          RDist ab ab', Dist' f ab' ab'') => Dist' 'True (a * b) ab'' where
    dist' = ldist' . rdist' . (dist' @f)
instance Dist' 'False (a * b) (a * b) where
    dist' = id
instance (HasPlus a ~ fa, HasPlus b ~ fb, 
          Dist' fa a a', Dist' fb b b') => Dist' x (a + b) (a' + b') where
    dist' = bimapping (dist' @fa) (dist' @fb)
    -- is that enough though? only dist if 
instance Dist' x I I where
    dist' = id
instance Dist' x O O where
    dist' = id
instance Dist' x (V a) (V a) where
    dist' = id

class Dist a b | a -> b where
    dist :: a ~~ b
-- dist' should distributed out all multiplications
instance (f ~ HasPlus a, Dist' f a b) => Dist a b where
    dist = dist' @f


-- | AUTOMATING ABSORBTION OF CONSTANTS



-- RAbsorb matches only on the right hand side of binary operators
-- matching on both sides is ungainly to write
class RAbsorb a b | a -> b where
    rabsorb :: a ~~ b
-- obvious absorptions
instance RAbsorb x x' => RAbsorb (x + O) x' where
    rabsorb = id_plus . rabsorb
instance RAbsorb x x' => RAbsorb (x + I) (x' + I) where
    rabsorb = firsting rabsorb
instance RAbsorb x x' => RAbsorb (x * I) x' where
    rabsorb = id_mul . rabsorb
instance RAbsorb (x * O) O where
    rabsorb = mul_zero
instance RAbsorb x x' => RAbsorb (x * (V a)) (x' * (V a)) where
    rabsorb = firsting rabsorb
instance RAbsorb x x' => RAbsorb (x + (V a)) (x' + (V a)) where
    rabsorb = lefting rabsorb
-- recursion steps
instance (RAbsorb (y * z) yz, RAbsorb x x') => RAbsorb (x * (y * z)) (x' * yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y + z) yz, RAbsorb x x') => RAbsorb (x * (y + z)) (x' * yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y + z) yz, RAbsorb x x') => RAbsorb (x + (y + z)) (x' + yz) where
    rabsorb = bimapping rabsorb rabsorb
instance (RAbsorb (y * z) yz, RAbsorb x x') => RAbsorb (x + (y * z)) (x' + yz) where
    rabsorb = bimapping rabsorb rabsorb
-- base cases
instance RAbsorb O O where
    rabsorb = id
instance RAbsorb I I where
    rabsorb = id
instance RAbsorb (V a) (V a) where
    rabsorb = id


-- mirror of RAbsorb    
class LAbsorb a b | a -> b where
    labsorb :: a ~~ b
instance LAbsorb x x' => LAbsorb (O + x) x' where
    labsorb = comm_plus . id_plus . labsorb
instance LAbsorb x x' => LAbsorb (I + x) (I + x') where
    labsorb = righting labsorb
instance LAbsorb x x' => LAbsorb (I * x) x' where
    labsorb = comm_mul . id_mul . labsorb
instance LAbsorb (O * x) O where
    labsorb = comm_mul . mul_zero
instance LAbsorb x x' => LAbsorb ((V a) + x) ((V a) + x') where
    labsorb = righting labsorb
instance LAbsorb x x' => LAbsorb ((V a) * x) ((V a) * x') where
    labsorb = seconding labsorb

instance (LAbsorb (y * z) yz, LAbsorb x x') => LAbsorb ((y * z) * x) (yz * x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y + z) yz, LAbsorb x x') => LAbsorb ((y + z) * x) (yz * x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y + z) yz, LAbsorb x x') => LAbsorb ((y + z) + x) (yz + x') where
    labsorb = bimapping labsorb labsorb
instance (LAbsorb (y * z) yz, LAbsorb x x') => LAbsorb ((y * z) + x) (yz + x') where
    labsorb = bimapping labsorb labsorb

instance LAbsorb O O where
    labsorb = id
instance LAbsorb I I where
    labsorb = id
instance LAbsorb (V a) (V a) where
    labsorb = id
    
-- labsorb :: (Swapped p, RAbsorb (p b a) (p b' a')) => (p a b) ~~ (p a' b')
-- labsorb = swapped . rabsorb . swapped   

-- a test function to see if an expression is properly absorbed
type family Absorbed a where
    Absorbed (O + a) = 'False
    Absorbed (a + O) = 'False
    Absorbed (a * I) = 'False
    Absorbed (I * a) = 'False
    Absorbed (a * O) = 'False
    Absorbed (O * a) = 'False
    Absorbed (a + b) = (Absorbed a) && (Absorbed b)
    Absorbed (a * b) = (Absorbed a) && (Absorbed b)
    Absorbed I = 'True
    Absorbed O = 'True
    Absorbed (V a) = 'True

-- iteratively rabsorbs and leftabsorbs until tree is properly absorbed.
class Absorb' f a b | f a -> b where
    absorb' :: a ~~ b
instance Absorb' 'True a a where
    absorb' = id
instance (LAbsorb a a', RAbsorb a' a'',
          f ~ Absorbed a'', Absorb' f a'' a''') => Absorb' 'False a a''' where
    absorb' = labsorb . rabsorb . (absorb' @f)

-- wrapper class to avoid the flag.
class Absorb a b | a -> b where
    absorb :: a ~~ b
instance (f ~ Absorbed a, Absorb' f a b) => Absorb a b where
    absorb = absorb' @f


-- | NORMALIZING ASSOCIATION


class LeftAssoc a b | a -> b where
    leftAssoc :: Iso' a b

instance LeftAssoc a a' => LeftAssoc (a + I) (a' + I) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a + O) (a' + O) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * I) (a' * I) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * O) (a' * O) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a * (V b)) (a' * (V b)) where
    leftAssoc = firsting leftAssoc 
instance LeftAssoc a a' => LeftAssoc (a + (V b)) (a' + (V b)) where
    leftAssoc = firsting leftAssoc 

instance (LeftAssoc ((a + b) + c) abc') => LeftAssoc (a + (b + c)) abc' where
    leftAssoc = plus_assoc . leftAssoc 
instance (LeftAssoc ((a * b) * c) abc') => LeftAssoc (a * (b * c)) abc' where
    leftAssoc = mul_assoc . leftAssoc 


instance (LeftAssoc (b * c) bc, LeftAssoc a a') => LeftAssoc (a + (b * c)) (a' + bc) where
    leftAssoc = bimapping leftAssoc leftAssoc
-- a * (b + c) ->  a * b + a * c 
-- This case won't happen if we've already distribute out.
instance (LeftAssoc (b + c) bc, LeftAssoc a a') => LeftAssoc (a * (b + c)) (a' * bc) where
    leftAssoc = bimapping leftAssoc leftAssoc

instance LeftAssoc O O where
    leftAssoc = id
instance LeftAssoc I I where
    leftAssoc = id
instance LeftAssoc (V a) (V a) where
    leftAssoc = id




-- right assoc will completely associate strings of + or -. Mixed terms are not associated.
-- cases  on left hand side of binary expression
-- always makes progress by either reassociating or recursing
class RightAssoc a b | a -> b where
    rightAssoc :: Iso' a b
instance (RightAssoc (a + (b + c)) abc') => RightAssoc ((a + b) + c) abc' where
    rightAssoc = (rev plus_assoc) . rightAssoc 
instance (RightAssoc (a * (b * c)) abc') => RightAssoc ((a * b) * c) abc' where
    rightAssoc = (rev mul_assoc) . rightAssoc 
instance RightAssoc a a' => RightAssoc (I + a) (I + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (O + a) (O + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (I * a) (I * a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc (O * a) (O * a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc ((V b) + a) ((V b) + a') where
    rightAssoc = seconding rightAssoc 
instance RightAssoc a a' => RightAssoc ((V b) * a) ((V b) * a') where
    rightAssoc = seconding rightAssoc 


instance (RightAssoc (b * c) bc, RightAssoc a a') => RightAssoc ((b * c) + a) (bc + a') where
    rightAssoc = bimapping rightAssoc rightAssoc
instance (RightAssoc (b + c) bc, RightAssoc a a') => RightAssoc ((b + c) * a) (bc * a') where
    rightAssoc = bimapping rightAssoc rightAssoc

instance RightAssoc O O where
    rightAssoc = id
instance RightAssoc I I where
    rightAssoc = id
instance RightAssoc (V a) (V a) where
    rightAssoc = id



-- | SORTING TERMS BY POWER

type family (a :: k) == (b :: k) :: Bool where
    f a == g b = f == g && a == b
    a == a = 'True
    _ == _ = 'False

type family SortedTerm a :: Bool where
    SortedTerm (a + (b + c)) = (((CmpTerm a b) == 'EQ) || ((CmpTerm a b) == 'GT)) && (SortedTerm (b + c))
    SortedTerm (a + b) = ((CmpTerm a b) == 'EQ) || ((CmpTerm a b) == 'GT)
    --SortedTerm a = 'True 
    SortedTerm I = 'True 
    SortedTerm O = 'True 
    SortedTerm (V a) = 'True 

-- higher powers of V are bigger.
-- CmpTerm compares TimesLists.    
type family CmpTerm a b where
    CmpTerm ((V a) * b) ((V a) * c) = CmpTerm b c
    CmpTerm ((V a) * b) (V a) = 'GT
    CmpTerm (V a) ((V a) * b)  = 'LT
    CmpTerm I ((V a) * b) = 'LT
    CmpTerm ((V a) * b) I = 'GT
    CmpTerm (V a) (V a) = 'EQ
    CmpTerm I (V a) = 'LT
    CmpTerm (V a) I = 'GT
    CmpTerm I I = 'EQ


-- Maybe this is all uneccessary since we'll expand out and abosrb to a*a + a*a + a + a + a + a


-- type a == b = TEq.(==) a b


-- Head and Tail of PlusLists
type family PlusHead a where
    PlusHead (x + y) = x
    PlusHead x = x
type family PlusTail a where
    PlusTail (x + y) = y



-- bubble assume a plusList of multiplicative terms. I.E. fully distributed, fully rightassociated , fully absorbed  
-- does one pass of a bubble sort
class Bubble f a b | f a -> b where
    bubble :: a ~~ b
-- more to go
instance (f ~ CmpTerm b (PlusHead c), Bubble f (b + c) bc) => Bubble 'EQ (a + (b + c)) (a + bc) where
    bubble = righting (bubble @f)
instance (f ~ CmpTerm b (PlusHead c), Bubble f (b + c) bc) => Bubble 'GT (a + (b + c)) (a + bc) where
    bubble = righting (bubble @f)
instance (f ~ CmpTerm a (PlusHead c), Bubble f (a + c) ac) => Bubble 'LT (a + (b + c)) (b + ac) where
    bubble = plus_assoc . (lefting comm_plus) . (rev plus_assoc) . righting (bubble @f)


-- The times, or constants shows that we're at the end of our + list.
instance Bubble 'EQ (a + (b * c)) (a + (b * c)) where
    bubble = id
instance Bubble 'GT (a + (b * c)) (a + (b * c)) where
    bubble = id
instance Bubble 'LT (a + (b * c)) ((b * c) + a) where
    bubble = comm_plus

instance Bubble 'EQ (a + I) (a + I) where
    bubble = id
instance Bubble 'GT (a + I) (a + I) where
    bubble = id
instance Bubble 'LT (a + I) (I + a) where
    bubble = comm_plus

instance Bubble 'EQ (a + O) (a + O) where
    bubble = id
instance Bubble 'GT (a + O) (a + O) where
    bubble = id
instance Bubble 'LT (a + O) (O + a) where -- shouldn't happen
    bubble = comm_plus

instance Bubble 'EQ (a + (V b)) (a + (V b)) where
    bubble = id
instance Bubble 'GT (a + (V b)) (a + (V b)) where
    bubble = id
instance Bubble 'LT (a + (V b)) ((V b) + a) where
    bubble = comm_plus
-- goofy base cases in case bubble gets called on a single element
instance Bubble x O O where
    bubble = id
instance Bubble x I I where
    bubble = id
instance Bubble x (V a) (V a) where
    bubble = id


-- sort term assumes rightassociated, fully distributed, fully I O absorbed expressions
class SortTerm' f a b | f a -> b where -- f is flag whether PlusList is sorted.
    sortTerm' :: a ~~ b
instance SortTerm' 'True a a where
    sortTerm' = id
-- a single term with no plus shouldn't get here. That is why PlusTail is ok.
instance (f ~ CmpTerm (PlusHead a) (PlusHead (PlusTail a)), Bubble f a a',
          f' ~ SortedTerm a', SortTerm' f' a' b) => SortTerm' 'False a b where
    sortTerm' = (bubble @f) . (sortTerm' @f')
class SortTerm a b | a -> b where -- f is flag whether PlusList is sorted.
    sortTerm :: a ~~ b
instance (f ~ SortedTerm a, SortTerm' f a a') => SortTerm a a' where
    sortTerm = sortTerm' @f


-- | DeepSwap. Completely flips the entire syntax tree left to right. Sometimes useful

class DeepSwap a b | a -> b where
    deepswap :: a ~~ b
-- could combined these cases with swapping combinator
instance (DeepSwap a a', DeepSwap b b') => DeepSwap (a*b) (b' * a') where
    deepswap = comm_mul . (bimapping deepswap deepswap)
instance (DeepSwap a a', DeepSwap b b') => DeepSwap (a + b) (b' + a') where
    deepswap = comm_plus . (bimapping deepswap deepswap)
instance DeepSwap I I where
    deepswap = id
instance DeepSwap O O where
    deepswap = id
instance DeepSwap (V a) (V a) where
    deepswap = id


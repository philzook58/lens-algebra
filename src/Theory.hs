{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  DataKinds, PolyKinds, AllowAmbiguousTypes #-}
module Theory where


-- | This module (in combination with a bit from Lens) holds the axiomatic lego blocks
-- | for manipulating algebraic types, proving equivalences and inequalities.

import  Control.Lens hiding (rewrite)
import Control.Arrow
import Data.Void


-- I'm a Naughty boy. Needs NoStarIsType to compile this
type a * b = (a,b)
type a + b = Either a b
type b ^ a = a -> b
type O = Void
type I = ()






-- http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.TypeNats.html#%2A
-- check out typelits for more on how to get this to work good
infixl 6 + -- ((a + b) + c)
infixl 7 *
infixr 8 ^


-- derived definitions
type Succ a = I + a
type Two = Succ I
type Three = Succ Two
type Four = Succ Three

-- alternative hierarchy
type One = Succ O


type family Binary a where
    Binary (a ': b) = a + Two * (Binary b)
    Binary '[] = O


type a ~~ b = Iso' a b
infix 5 ~~




{-
Isomorphisms have an identity and compose. They form a category
id :: Iso' a a
(.) :: Iso' b c -> Iso' a b -> Iso' a c

Other combinators:
-}

refl ::  a ~~ a
refl = id

compose :: (a ~~ b) -> (b ~~ c) -> (a ~~ c)
compose = (.)

-- isomorphisms can also be reversed. from is the name of this combinator from Control.Lens.Iso
rev ::  a ~~ b -> b ~~ a
rev = from



-- now we start to state our axioms
-- interestingly, I believe the Iso and Lens laws to follow actually follow via parametricity.

-- associativity + a identity object make mul and plus a monoid
plus_assoc :: Iso' (a + (b + c)) (a + b + c)
plus_assoc =  iso assoc unassoc  where
                   assoc (Left a) = Left (Left a)
                   assoc (Right (Left b)) = Left (Right b)
                   assoc (Right (Right c)) = Right c
                   unassoc (Left (Left a)) = Left a
                   unassoc (Left (Right b)) = Right (Left b)
                   unassoc (Right c) = (Right (Right c))

mul_assoc :: Iso' (a * (b * c)) (a * b * c)
mul_assoc =  iso (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))


-- could also use `absurd` from Data.Void for empty case/. Could also use EmptyCase syntax
id_plus :: Iso' (a + O) a
id_plus = iso (\case Left x -> x
                     Right x -> absurd x) Left

id_mul :: Iso' (a * I) a
id_mul = iso (\(x,_) -> x) (\x -> (x,()))


-- they are also commutative
-- specialized version of swapped from Control.Lens.Iso for future clarity
comm_plus :: Iso' (a + b) (b + a)
comm_plus = swapped
comm_mul :: Iso' (a * b) (b * a)
comm_mul = swapped


-- comm = swapped


--type Test a b c = (a * b + a * c)
-- The distributive property and the zero*x=zero property make the type algebra a semiring.

-- I don't see this one in Lens. Maybe it is there though?
-- distributive property
rdist :: Iso' (a * (b + c)) (a * b + a * c)
rdist = iso (\(a,bc) -> (a,) +++ (a,) $ bc) (\case Left (a,b) -> (a, Left b)
                                                   Right (a,c) -> (a, Right c))   

mul_zero :: Iso' (a,O) O
mul_zero = iso (\(_,y) -> absurd y) absurd

-- Those are our basic laws.


-- a specialized version of firsting and seconding for clarity
lefting :: (a ~~ b) -> (a + c) ~~ (b + c)
lefting = firsting

righting :: (a ~~ b) -> (c + a) ~~ (c + b)
righting = seconding

-- ldist can be derived from what we've already given.
ldist ::   ((b + c) * a) ~~ (b * a + c * a)
ldist = comm_mul . rdist . (lefting comm_mul) . (righting comm_mul)




{-
Prism = inequality
Lens = divisibility
-}

type a >= b = Prism' a b
type a .| b = Lens' a b

{-

the core combinators from the lens library for manipulating these are

_1 :: (a,b) .| a
_2 :: (a,b) .| b

_Left :: (a + b) >= a
_Right :: (a + b) >= b


-}

-- once again, these are true via parametricity, more or less
one_div :: a .| I 
one_div = lens (const ()) const

zero_lte :: a >= O
zero_lte = prism' absurd (const Nothing)

zero_div :: O .| a
zero_div = lens absurd const



-- For working with Variables

-- (lefting dist) . _
-- a newtype to mark variable position
newtype V a = V a

-- typical usage, bind the V in a unification predicate to keep expression clean
-- (V a' ~ a, V b' ~ b) => (a + b) * b 

-- multinomials.
-- a phantom labelled newtype for variable ordering. 
newtype VL l a = VL a
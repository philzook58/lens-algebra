{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  DataKinds, PolyKinds, AllowAmbiguousTypes,
NoImplicitPrelude, GADTs #-}

module Iso where

import Control.Category
import Data.Void
import Data.Coerce
import Prelude hiding (id, (.))
import Data.Functor.Yoneda
import Data.Functor.Coyoneda
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Rep -- adjunctions package representable functors
import Data.Functor.Adjunction
import Data.Bifunctor
-- hide this constructor. 
-- is the main point of this module to rebuild Lens. Iso using the simpler form of Iso that can be hidden?
-- mostly. NatIso at the bottom is interesting though.
data Iso a b = Iso {to :: a -> b, from :: b -> a}


type a * b = (a,b)
type a + b = Either a b
type b ^ a = a -> b
type O = Void
type I = ()

-- Iso p a b = Iso {to :: p a b, from :: p b a} ? Just a thought 
instance Category Iso where
    id = Iso id id
    (Iso t f) . (Iso t' f') = Iso (t . t') (f' . f)

rev :: Iso a b -> Iso b a
rev (Iso t f) = Iso f t
{-

-- These are axioms stating . We can derive comap and mapiso from promap using Star.
-- These are axioms about the nature of lawful profunctors.
-- we can guarantee a profunctor is lawful if we build it piecemeal.
    -- check out 2.2 of Reason isomorphically

mapiso :: Functor f => (Iso a b) -> Iso (f a) (f b)
comapiso :: Contravariant f => (Iso a b) -> Iso (f a) (f b)
promapiso :: Profunctor f => (Iso a b) -> Iso (p a a) (p b b)

-- if we write our function using recursion schemes
cataiso :: (Algebra f a ~~ Algebra f b) -> (Fix f ~~ Fix g)


bimapping :: Binfunctor f => Iso a a' -> Iso b b' -> Iso (f a b) (f a' b')
bimapping (Iso t f) (Iso t' f')= Iso (bimap t t') (bimap f f')
seconding
-}
bimapping :: Bifunctor f => Iso a a' -> Iso b b' -> Iso (f a b) (f a' b')
bimapping (Iso t f) (Iso t' f')= Iso (bimap t t') (bimap f f')
firsting f = bimapping f id
seconding f = bimapping id f

-- swapped

{-

I hsould probably just use the Lens library names
dimapping for promap
contramapping
etc
all of these combinators are in there.
-}

mapiso :: Functor f => Iso a b -> Iso (f a) (f b)
mapiso (Iso t f) = Iso (fmap t) (fmap f)

contramapiso :: Contravariant f => Iso a b -> Iso (f b) (f a) -- what is the better ordering?
contramapiso (Iso t f) = Iso (contramap t) (contramap f)

-- the phantom function is interesting. Could also be done through coercion probably.
phantomiso :: (Contravariant f, Functor f) => Iso (f a) (f b)
phantomiso = Iso phantom phantom

data Finite a where
    Prod :: Finite a -> Finite b -> Finite (a * b)
    LSum :: Finite a -> Finite (a + b)
    RSum :: Finite b -> Finite (a + b)
    Unit :: Finite ()

-- the forall, sum / product analogy
-- Iso (Forall1 Finite) Nat

fabsurd :: Finite Void -> a
fabsurd = undefined


-- newtype Forall0 = forall a. Forall {runforall0 :: a}
newtype Forall1 f = Forall1 {runforall1 :: forall a. f a}
newtype Forall2 f b = Forall2 {runforall2 :: forall a. f a b}
-- rotten bananas, kmett's article mentions this 
-- http://hackage.haskell.org/package/exists-0.2/docs/Data-Exists.html
-- Using this newtype instead of raw forall means we can grab forall in a typeclass constructor
-- Although the intended use is to hide type variables, really this constructor is not an exists. It is a rankNtype
-- newtype Exists f = Exists {runExists :: }

{-

Hmm. Maybe it is an exists
Forall0 :: (forall a. a) -> Forall
matchforall :: forall r. Forall0 -> (forall a. a. -> r) -> r 

but then is it even possible to reify forall?
(forall a. a -> a)

-}
-- If a is isomorhpic to Unit, it is uniquely inhabited.
type Unique a = Iso a ()
type Impossible a = Iso a Void
-- if a is isomorphic to Void is is impossible to construct

-- Lens calls this coerced
coerceiso :: (Coercible a b, Coercible b a) => Iso a b
coerceiso = Iso coerce coerce



-- convertIso' :: Iso' a b -> Iso a b
--isoIso :: Iso (Iso' a b) (Iso a b)
--isoIso = Iso  (\i -> Iso (to i) (from i))  (\(Iso t f) -> iso t f) 

-- alternativel plus_assoc = (to isoIso) TH.plus_assoc
plus_assoc :: Iso (a + (b + c)) (a + b + c)
plus_assoc =  Iso assoc unassoc  where
                   assoc (Left a) = Left (Left a)
                   assoc (Right (Left b)) = Left (Right b)
                   assoc (Right (Right c)) = Right c
                   unassoc (Left (Left a)) = Left a
                   unassoc (Left (Right b)) = Right (Left b)
                   unassoc (Right c) = (Right (Right c))

mul_assoc :: Iso (a * (b * c)) (a * b * c)
mul_assoc =  Iso (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))


{-

promatch :: Profuctor p => MyGadt a -> p Int Int -> p Bool Bool -> p a a



pointful reaosning
forall x. Iso x a -> Iso x b ~~ Iso a b 


class   => FreeThereom (Forall f) where

instance FreeTheorem (a -> b)
    theorem :: profunctor p => Comp p (a -> b) <= Comp (a -> b) p
-- instanceiate profunctor p to (->) for 
Do we have a notion of profunctor inequality?

The idea is that Profunctors are "relations" kind of. They aren't a good signature for actual data types of relations, but maybe they are 
Then we can make a function that instatiates p to (->) and removes the existentail type put in there by 
-}
newtype CPS a r = CPS {runCPS :: ((a -> r) -> r)}
type CPS' a = Forall1 (CPS a)
-- an expeirment. CPS should be a speical case of something else.
cpsiso :: Iso (CPS' a) a
cpsiso = Iso (\f -> (runCPS $ runforall1 f) (\x -> x)) (\a -> (Forall1 (CPS (\f -> f a))))

-- cpsiso' :: Iso (CPS' a) a
-- cpsiso' = Iso (\f -> (coerce f) (\x -> x)) (\a -> (Forall1 (CPS (\f -> f a))))

--yonedaiso :: Iso (Yoneda f) f 

-- from Data.Functor.Yoneda from kan-extensions library
{-
runYoneda :: forall b. (a -> b) -> f b


-}

type Hom a b = a -> b
type Nat f g = forall a. f a -> g a
-- yonedaiso :: Iso (Nat (Hom a) f) (f a)   
yonedaiso :: Functor f => Iso (Yoneda f a) (f a)
yonedaiso = Iso lowerYoneda liftYoneda 

coyonedaiso :: Functor f => Iso (Coyoneda f a) (f a)
coyonedaiso = Iso lowerCoyoneda liftCoyoneda 




{-


-}

--kaniso ::


-- Iso1 is a natural isomorphism, roughly. SHould we inlcude a Funcftor constraint?
-- Functor equality.
-- Call NatIso?
-- Iso1 f g = Iso1 {to1 :: forall a. f a -> g a, from :: forall a. g a -> f a}
data NatIso f g = NatIso {natto :: forall a. f a -> g a, natfrom :: forall a. g a -> f a}
-- NatIso = NatIso forall a. Iso (f a) (g a) ? Is this the same thing? The from and to might be force to be connected now.
instance Category NatIso where -- wow. It is super sirpring this worked. Polykinds for the win I think.
   id = NatIso id id
   (NatIso t f) . (NatIso t' f') = NatIso (t . t') (f' . f)
-- This is horizonal composition of natural trans.
composeiso :: (Functor f, Functor f') => NatIso f f' -> NatIso g g' -> NatIso (Compose f g) (Compose f' g')
composeiso (NatIso t f) (NatIso t' f') = NatIso (Compose . t . (fmap t') . getCompose) (Compose . f . (fmap f') . getCompose)

-- derived notions, functor f actually isn't necessary for the outer
outeriso :: (Functor f, Functor f') => NatIso f f' -> NatIso (Compose f g) (Compose f' g) 
outeriso f = composeiso f id
inneriso :: (Functor f) => NatIso g g' -> NatIso (Compose f g) (Compose f g') 
inneriso f = composeiso id f


idiso :: NatIso (Compose Identity g) g
idiso = NatIso coerce coerce -- NatIso (runIdentity . runCompose) (Compose . Identity) 

-- Idnetity is the 1 for composition
idisoright :: Functor g => NatIso (Compose g Identity) g
idisoright = NatIso ((fmap runIdentity) . getCompose ) (Compose . fmap Identity)


-- Const is kind of like a compilicated Void. It is the 0 for composition.
isoConst :: NatIso (Compose (Const a) g) (Const a)
isoConst = NatIso coerce coerce


repiso :: Representable f => NatIso ((->) (Rep f)) f
repiso = NatIso tabulate index

-- hmm this is actually polymorphic in both arguments. Should be a pro Iso
-- two functors are adjoint if the homsets are isomorphic to each other in just the right wya.
-- adjunctiso :: Adjunction f u => NatIso ((->) (f)
-- adjunctIso = ProIso leftAdjunct rightAdjunct

-- curry is the classic adjunction example. Runar gave a good talk

-- yoiso :: IsoNat 

-- right Const. Doesn't work actually
-- isoConst :: NatIso (Compose g (Const a)) (g a)
-- isoConst = NatIso coerce coerce
{-



natisoinstance :: NatIso f g -> Nat (f a) (g a)
natisoinstnace (Iso1 t f) = (Iso t f)






prodiso :: NatIso f f' -> NatIso g g' -> NatIso (Compose f g) (Compose f' g')
sumiso


-}
{-
-- dinatural transformation?
data ProIso = ProIso {  p a a -> q a a, q a a -> p a a }
or 
data ProIso p q = ProIso { forall a b.  p a b -> q a b, q a a -> p a a }
-}

-- Functor composition
{-

Const
Id
Compose
Sum
Prod


-}

{-
Clown joker combinators?
-}
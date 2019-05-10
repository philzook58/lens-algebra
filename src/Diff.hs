{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  DataKinds, PolyKinds, AllowAmbiguousTypes #-}
module Diff where

import Theory
import qualified GHC.TypeLits as TL
import Control.Lens

type family Pow x n where
    Pow x 0 = I
    Pow x 1 = x
    Pow x n = x * (Pow x (n TL.- 1))

-- The derivative of a type
type family Diff a where
    Diff O = O
    Diff I = O
    Diff (V a) = I
    Diff (a + b) = (Diff a) + (Diff b)
    Diff (a * b) = (Diff a) * b + a * (Diff b)
    -- Diff (a ^ b) -- going to need logarithms of types -> Representable functors
    -- hmmm. Chain rule isn't coming out good.
    -- I suppose since we don't have a literal compose combinator we don't need it?
    -- Diff (Compose f g) = (Compose (Diff (f) g)) :*: (Diff g) 
    -- Diff (f (g a)) = Diff (f (V a)) ()

-- But really I should want a Diff relation similar to how I have Lens and Iso

type family Apply' f x where
    Apply' (V a) x = x
    -- Apply' (VL l a) xs = Lookup l xs -- multivariate. For another day
    Apply' (a + b) x = (Apply' a x) + (Apply' b x)
    Apply' (a * b) x = (Apply' a x) * (Apply' b x)
    Apply' I _ = I
    Apply' O _ = O


-- Pretty ugly stuff. Changing style to use Functor compose does appeal.
type family Compose' f g where
    Compose' f g = Apply' f g
    --Compose (V a) g = g


{-

Galois Connection

class GaloisPlus f g a b where
    gplus :: (f a) >= b)) ~~ (a >= (g b))

class Division a b d r | a b -> d r where
    divmod :: a ~~ b * d + r
instance Division I I I O where
    divmod = rewrite
instance Division O I O O where
    divmod = rewrite
instance Division (I + a)

-- this is the form of subtraction that can always go though. Like the divmod formula but for subtraction
-- Feels more like a*b ~~ c*d of fraction equaivalence.
-- c and d are the two smallest numbers that can make this statement true.
class Subtract a b c d | a b -> c d where
    subtract :: a + c ~~ b + d
-- these two overlap. That is so annoying
instance Subtract a O O a where -- a + 0 ~ O + a
    subtract = rewrite
instance Subtract O a a O where -- 0 + a ~ a + 0
    subtract = rewrite
instance Subtract I I O O where -- 1 + 0 ~ 1 + 0
    subtract = rewrite
instance Subtract a b c d => Subtract (I + a) (I + b) (I + c) (I + d) where -- 
    subtract = rewrite

-- Subtract a b c d,  => Subtract' 'GT 
-- Subtract' 'EQ 
-- Subtract' 'LT a b 


-- This is a type that can store pairs of numbers, like how a power series stores it's coefficients
-- The polymorphisms
-- The pair of a and b, such that the only meaning is (a - b), analog of the pair formulation of fractions.
type Negative a b c d = (a + c) ~~ (b + d)

What I'm trying to channel is that negative numbers are an equivlaence class of (a,b) such that (a,b) ~~ (c,d) if a + d ~~ b + c
    can we cut out the middle man of the tuple, since tuples are hard to come by here. 

-- Can they be added and subtracted?
nadd :: N a b -> N c d -> N (a + c) (b + d)
nadd f g = bimapping f g . _ -- then we need to reduce the two. We have for terms on each side. we need the subthereom

existsplus :: forall d c. (forall a b. (a + b ~~ c)) -> (d ~~ c)
existsplus f = (rev id_plus) . f -- unifies b ~ O, a ~ d hopefully 
forall d c. (forall a b. (a + b ~~ c)) ~~ (d ~~ c) ? We can always just add zero, or unify d with b + c
(forall d. d ~~ c) -> (b + a ~~ c) -- just unify d with b + a. Given that we have something that unifies forll d. 
onedirectin f = f --?
There is something prety fishy about all this

nsub :: N a c -> N c d -> N (a + d) (b + c)  
nsub f g = bimapping f (rev g)


type Hmmmmmm a b c = a * b + c
type Fraction a b c d = (a * c) ~ (b * d)
type Fraction a b = forall c d. (a * c) ~~ (b * d)
newtype Fraction a b = Fraction forall c d. (a * c) ~~ (b * d)

gives question to isomorphism of isomorphisms? When is one isomorphism isomorphic to another? Well, when we can



-}
-- Oh. This doesn't make any sense at all.
{-
newtype N a b = N { unN :: forall c d. (a + c) ~~ (b + d) }
nadd :: N a b -> N c d -> N (a + c) (b + d)
nadd (N f) (N g) = (bimapping f g) . _
-}

-- is this even right? shouldn't the forall d wrap... No this is right.
existsplus'' :: forall c d. (forall a b. a + b ~~ c) -> d ~~ c
existsplus'' f = (rev id_plus) . f
existsplus' :: forall c a b. (forall d. d ~~ c) ->  a + b ~~ c
existsplus' f = f
-- Have to bend over backward to get this one to compile. Nasty. Impredicative polymorphism problems
existsplus :: forall c. (LeftSide c) ~~ (RightSide c)
existsplus = iso (\x -> (RightSide (existsplus'' (runLeft x)))) (\x -> LeftSide (existsplus' (runRight x)))
-- existsplus2 :: forall c. (forall a b. a + b ~~ c) ~~ (forall d. d ~~ c)
-- existsplus2 = iso (existsplus'' :: (forall a b. a + b ~~ c) -> (forall d. d ~~ c )) existsplus'

newtype LeftSide c = LeftSide {runLeft :: (forall a b. a + b ~~ c) }

--isoleft :: (LeftSide c) ~~ (forall a b. a + b ~~ c)
--isoleft = iso runLeft LeftSide

newtype RightSide c = RightSide {runRight :: forall d. d ~~ c}
type a ~~~ b = ReifiedIso' a b


{-


-- when we've already used up tuple to mean *, it isn't clear how to build a true tuple of nats.
data Diff a b = Diff a b
type DiffIso (Diff a b) (Diff c d) = Iso' (a + d) (b + d)  
a ~~ a', b ~~ b', 


Division is proof procedure for Lens
Subtraction is proof procedure for Prism



-- this reflection is gonna make my grabbing of + *  miserable

type Family ReflectTypeLit a where
    ReflectTypeLit I = 1
    ReflectTypeLit O = 0
    ReflectTypeLit (a + b) = (ReflectTypeLit a) TL.+ (ReflectTypeLit b) 
    ReflectTypeLit (a * b) = (ReflectTypeLit a) TL.* (ReflectTypeLit b) 
    -- ReflectTypeLit (Div a b) = 

type family ReflectAlgebra where
    ReflectAlgebra 1 = I
    ReflectAlgebra 0 = O
    ReflectAlgebra n = I + (ReflectAlgebra (n TL.- 1))

class ReflectSingleton n where
    reflect :: SNat (Reflection n)
    reflect :: Eq n n' -> Iso' (Reify n) (Reify n') -- I suppose Reify and Reflect are something like adjunctions. Destroys structure. but only once 
    reflect :: Iso' n n' -> Eq (Reflect n) (Reflect n')
    weeewooowawa :: (Eq n n') ~~ (n ~~ n') = iso reflect reflect'
-- obviously i'm trying to channel a weirdo HOTT for some reason.
-- Pretty sure I can't construct these. Not without just generating the proofs for both sides.
-- could unsafe coerce them and I think I'd be fine.
-- can I reflect singleton proofs over? Maybe it would be easier to port the free semiring. Well, yeah


-- htis is just a DSL for exactly my combinators.
data EqSemiRing n n' where
    RDist :: IsoSemiRing (a * (b + c)) ()
    IdMul ::
    Comp :: 
    Dup
    Par






Is it cheating to get strong hints from GHC? Nah. Especially if we can just use them to construct an actual proof.
My canonical form work isn't wasted, since GHC is not going to give us proofs of how to turn one form into another.


CollectTerms -- Collect up the terms of the same variable power. Like so. (1 + 1 + 1) * (V a) + (1 + 1)

type family search

-- open type family
type family HasInstance c '[arguments]
-- directly reflect instances into type family for easier programming.
-- Allows us to do legit search for instances by trying possibilities in turn.

type hasInstance Factor c 

type family FindFactor n x where
    FindFactor x x = x
    FindFactor n x = ITE (HasInstance Factor n x) n (FindFactor (n + 1) x)

type family FindFactor' x where
    FindFactor x = FindFactor 2 x

type family PossibleTransformations
   PossibleTransformations x = '[ 1, 2 , 3, 4]

type family SearchTransformations x where
    SearchTransformations '[] =  



Is there any way that equivalences of equivlaences doesn't give garbage?
(ReifiedIso a b) ~~ (ReifiedIso c d)

ReifiedIso () () ~~ ReifiedIso () ()
 = id
considered modulo isomorphisms, seems like a ReifiedIso is unique.



-- It's like a DSL for logic formula
-- Or a DSL for a simple boolean programming language
data BDD a b a' b' where
    Root :: a b () 
    End :: a b a' (AllVals b)
    Share :: BDD a b (a',a') a'
    Decide :: BDD a b a' (a',a')
    Compose :: 
    // Fst, Snd, shouldn't be necessary
    Assoc :: -- assoc seems stupid. Just make associative by default

-- Yeah if I was gonna build a point free programming language with sharing
-- And it has canonical forms? Like all the fusion rules are so...

-- BDDs are a programming language. for finite types... where the variables have to be inspected in a particular order.
-- And then completing fusion gives a canonical form?


env = '[]

data 
   ITE (a : )
   Skip (b : bs) bs
 

-- case takes something off the input stack and puts it on the world's tree?
Case :: (b : bs) ws bs (ws ++ ws)
-- Skip takes off the stack but doesn't add to worlds
Skip :: (b : bs) 
-- join fuses worlds.
Join :: l (() : () : ws) l (() : w')

-- return has empty input stack and can reduce the worlds
Return :: '[] (() : w2) '[] w2

Join :: (a,b) () -- we can join any two arbitrary world sets into a single world. 
-- That is sligthly more efficient we only have to get all the worlds together under a signle heading. 
Join :: Proxy n -> Proxy m -> BDD ws (Fuse n m ws)

-- less fancy types what I've built is this implicit form. I'm indexing into the worlds I've built.
-- this is not canonical unless the joins are sorted or something, or happen as early as they can.
-- or as late as they can. right before the node they are casing
data BDD = Case BDD | Skip BDD | Join Int Int BDD
type JoinList = [(Int,Int)]
data BDD = Case JoinList BDD | Skip BDD | Final resullt JoinList

Curry?

-- we also need world manipulation swap, assoc. Which is trash.
we don't really want a worlds stack or tree. we want to just be able to freely grab worlds.
The non canonical form of the world manipulations will suck


Then the total type we desire is BDD '[b,b,b,b,b] () '[] ()
worlds tracks the total number of lines we have at each spot.

We've replaced pointerful sharing with implcit sequential mutation or something. It's goofy.


-}
{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoStarIsType, TupleSections, 
LambdaCase, EmptyCase, MultiParamTypeClasses, FunctionalDependencies, TypeApplications, 
ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,  UndecidableInstances,  
DataKinds, PolyKinds, AllowAmbiguousTypes, PartialTypeSignatures #-}
module Main where

import Theory
import Auto
import Control.Lens hiding (rewrite)

main :: IO ()
main = print "hey there buddo"

-- exmaple usage of Binary. least significant bit is first
type NineTeen = Binary '[I,I,O,O,I]    

-- a very simple proof. holds basically by definition
oneonetwo :: Iso' (I + I) Two
oneonetwo = id

-- a more complicated proof
twotwofour :: Iso' (Two + Two) Four
twotwofour = rev plus_assoc

-- very painful. Using holes _ and error messages absolutely essential
factorexample ::  ((a + I) * (a + I)) ~~ (a * a + Two * a + I)
factorexample = rdist .  -- distribute out the right side 
               (lefting (comm_mul . rdist)) . -- in the left sum term distribute out
               (righting (comm_mul . rdist)) . -- in the right sum term distribute out
                plus_assoc . -- reassociate plus to the left
               (lefting (lefting (righting comm_mul))) . -- turn a * I term to I * a
                (lefting (rev plus_assoc)) . -- associate the two a*I terms together into an (a * I + a * I) term 
                 (lefting (righting (rev ldist))) . -- factor together that subterm into Two * a
                  (righting id_mul) -- convert last I * I term into I

twodiv4 :: (Two * Two) .| Two
twodiv4 = _1

onelesstwo :: Two >= I
onelesstwo = _Left

-- Iso can be composed with Lens and Prism and stay a Lens or Prism.
-- This corresponds with you can compose isomorphisms with either inequalities or divisiblity
factorexample'' ::  (a * a + Two * a + I) .| (a + I)
factorexample'' = (rev factorexample) . _1 


-- examples using automation 

exampledist :: ((I + (O + I)) * (I + O)) ~~ _
exampledist = dist
exampledist2 :: (I + Two * Two * Two) ~~ _
exampledist2 = dist
exampledist3 :: NineTeen ~~ _
exampledist3 = dist


ex4 :: ((O + I + O) + O) ~~ _
ex4 = absorb
ex5 :: (Two * (Two + O + Two * O + O * Two)) ~~ _
ex5 = absorb
ex6 :: NineTeen ~~ _
ex6 = absorb

ex7 :: NineTeen ~~ _
ex7 = dist' . absorb

ex8 :: NineTeen ~~ _ 
ex8 = ex7 . rightAssoc

ex9 :: (a ~ V a') => ((a + I) * (I + a)) ~~ (a * a + Two * a + I)
ex9 = rewrite -- canonical . (rev canonical)

ex10 :: (a ~ V a') => ((a + I) * (I + a) * (Two + a)) ~~  (a * a * a + a * a * Four + Two + Four * a + a)
ex10 = rewrite -- canonical . (rev canonical)

ex11 :: NineTeen ~~ _
ex11 = canonical
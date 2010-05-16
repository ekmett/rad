{-# LANGUAGE Rank2Types, TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Numeric.RAD
-- Copyright   :  (c) Edward Kmett 2010
-- License     :  BSD3
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  GHC only 
--
-- Reverse Mode Automatic Differentiation via overloading to perform
-- nonstandard interpretation that replaces original numeric type with
-- a bundle that contains a value of the original type and the tape that
-- will be used to recover the value of the sensitivity.
-- 
-- This package uses StableNames internally to recover sharing information from 
-- the tape to avoid combinatorial explosion, and thus runs asymptotically faster
-- than it could without such sharing information, but the use of side-effects
-- contained herein is benign.
--
-- The API has been built to be close to the design of 'Numeric.FAD' from the 'fad' package
-- by Barak Pearlmutter and Jeffrey Mark Siskind and contains portions of that code, with minor liberties taken.
-- 
-----------------------------------------------------------------------------

module Numeric.RAD 
    ( 
    -- * First-Order Reverse Mode Automatic Differentiation
      RAD
    , lift
    -- * First-Order Differentiation Operators
    , diffUU
    , diffUF
    , diff2UU
    , diff2UF
    -- * Common access patterns 
    , diff
    , diff2
    , jacobian
    , jacobian2
    , grad
    , grad2
    -- * Optimization Routines 
    , zeroNewton
    , inverseNewton
    , fixedPointNewton
    , extremumNewton
    , argminNaiveGradient
    ) where

import Control.Applicative (Applicative(..),(<$>))
import Control.Monad (forM_)
import Control.Monad.ST
import Data.List (foldl')
import Data.Array.ST
import Data.Array
import Data.Ix
import Data.Map (Map)
import Text.Show
import qualified Data.Map as Map
import Data.Graph (graphFromEdges', topSort, Vertex)
import Data.Reify (reifyGraph, MuRef(..))
import qualified Data.Reify.Graph as Reified
import System.IO.Unsafe (unsafePerformIO)

newtype RAD s a = RAD (Tape a (RAD s a))

data Tape a t
    = C a 
    | V a Int
    | B a a a t t
    | U a a t 

instance Show a => Show (RAD s a) where
    showsPrec d = disc1 (showsPrec d)

-- | The 'lift' function injects a primal number into the RAD data type with a 0 derivative.
-- If reverse-mode AD numbers formed a monad, then 'lift' would be 'return'.
lift :: a -> RAD s a 
lift = RAD . C 
{-# INLINE lift #-}

primal :: RAD s a -> a
primal (RAD (C y)) = y
primal (RAD (V y _)) = y
primal (RAD (B y _ _ _ _)) = y
primal (RAD (U y _ _)) = y
{-# INLINE primal #-}

var :: a -> Int -> RAD s a 
var a v = RAD (V a v)

-- TODO: A higher-order data-reify
-- mapDeRef :: (Applicative f) => (forall a . Num a => RAD s a -> f (u a)) -> a -> f (Tape a (u a))
instance MuRef (RAD s a) where
    type DeRef (RAD s a) = Tape a
    mapDeRef f (RAD (C a)) = pure (C a)
    mapDeRef f (RAD (V a v)) = pure (V a v)
    mapDeRef f (RAD (B a jb jc x1 x2)) = B a jb jc <$> f x1 <*> f x2
    mapDeRef f (RAD (U a j x)) = U a j <$> f x

on :: (a -> a -> c) -> (b -> a) -> b -> b -> c
on f g a b = f (g a) (g b)

instance Eq a =>  Eq (RAD s a) where
    (==) = (==) `on` primal

instance Ord a => Ord (RAD s a) where
    compare = compare `on` primal

instance Bounded a => Bounded (RAD s a) where
    maxBound = lift maxBound
    minBound = lift minBound

unary_ :: (a -> a) -> a -> RAD s a -> RAD s a
unary_ f _ (RAD (C b)) = RAD (C (f b))
unary_ f g b = RAD (U (disc1 f b) g b)
{-# INLINE unary_ #-}

unary :: (a -> a) -> (a -> a) -> RAD s a -> RAD s a
unary f _ (RAD (C b)) = RAD (C (f b))
unary f g b = RAD (U (disc1 f b) (disc1 g b) b)
{-# INLINE unary #-}

binary_ :: (a -> a -> a) -> a -> a -> RAD s a -> RAD s a -> RAD s a
binary_ f _ _ (RAD (C b)) (RAD (C c)) = RAD (C (f b c))
binary_ f gb gc b c = RAD (B (f vb vc) gb gc b c)
    where vb = primal b; vc = primal c
{-# INLINE binary_ #-}

-- binary_ with partials
binary :: (a -> a -> a) -> (a -> a) -> (a -> a) -> RAD s a -> RAD s a -> RAD s a
binary f _ _ (RAD (C b)) (RAD (C c)) = RAD (C (f b c))
binary f gb gc b c = RAD (B (f vb vc) (gb vc) (gc vb) b c)
    where vb = primal b; vc = primal c
{-# INLINE binary #-}

disc1 :: (a -> b) -> RAD s a -> b
disc1 f x = f (primal x)
{-# INLINE disc1 #-}

disc2 :: (a -> b -> c) -> RAD s a -> RAD s b -> c
disc2 f x y = f (primal x) (primal y)
{-# INLINE disc2 #-}

disc3 :: (a -> b -> c -> d) -> RAD s a -> RAD s b -> RAD s c -> d
disc3 f x y z = f (primal x) (primal y) (primal z)
{-# INLINE disc3 #-}

from :: Num a => RAD s a -> a -> RAD s a
from (RAD (C a)) x = RAD (C x)
from a x = RAD (U x 1 a)

fromBy :: Num a => RAD s a -> RAD s a -> Int -> a -> RAD s a 
fromBy (RAD (C a)) _ _ x = RAD (C x)
fromBy a delta n x = RAD (B x 1 (fromIntegral n) a delta)

instance (Num a, Enum a) => Enum (RAD s a) where
    succ = unary_ succ 1
    pred = unary_ pred 1
    toEnum   = lift . toEnum
    fromEnum = disc1 fromEnum
    -- the enumerated results vary with the lower bound and so their derivatives reflect that
    enumFrom a           = from a <$> disc1 enumFrom a
    enumFromTo a b       = from a <$> disc2 enumFromTo a b
    -- these results vary with respect to both the lower bound and the delta between that and the second argument
    enumFromThen a b     = zipWith (fromBy a delta) [0..] $ disc2 enumFromThen a b where delta = b - a
    enumFromThenTo a b c = zipWith (fromBy a delta) [0..] $ disc3 enumFromThenTo a b c where delta = b - a

instance Num a => Num (RAD s a) where
    fromInteger = lift . fromInteger
    (+) = binary_ (+) 1 1 
    (-) = binary_ (-) 1 (-1)
    negate = unary_ negate (-1)
    (*) = binary (*) id id
    -- incorrect if the argument is complex
    abs = unary abs signum
    signum = lift . signum . primal

-- notComplex :: Num a => a -> Bool
-- notComplex x = s == 0 || s == 1 || s == -1
--     where s = signum x 

instance Real a => Real (RAD s a) where
    toRational = disc1 toRational

instance RealFloat a => RealFloat (RAD s a) where
    floatRadix = disc1 floatRadix
    floatDigits = disc1 floatDigits
    floatRange = disc1 floatRange

    decodeFloat = disc1 decodeFloat
    encodeFloat m e = lift (encodeFloat m e)

    scaleFloat n = unary_ (scaleFloat n) (scaleFloat n 1) 
    isNaN = disc1 isNaN
    isInfinite = disc1 isInfinite
    isDenormalized = disc1 isDenormalized
    isNegativeZero = disc1 isNegativeZero
    isIEEE = disc1 isIEEE

    exponent x
        | m == 0 = 0 
        | otherwise = n + floatDigits x
        where (m,n) = decodeFloat x 

    significand x =  unary_ significand (scaleFloat (- floatDigits x) 1) x

    atan2 (RAD (C x)) (RAD (C y)) = RAD (C (atan2 x y))
    atan2 x y = RAD (B (atan2 vx vy) (vy*r) (-vx*r) x y)
        where vx = primal x
              vy = primal y
              r = recip (vx^2 + vy^2)

instance RealFrac a => RealFrac (RAD s a) where
    properFraction (RAD (C a)) = (w, RAD (C p))
        where (w, p) = properFraction a
    properFraction a = (w, RAD (U p 1 a))
        where (w, p) = properFraction (primal a)
    truncate = disc1 truncate
    round = disc1 truncate
    ceiling = disc1 truncate
    floor = disc1 truncate

instance Fractional a => Fractional (RAD s a) where
    (/) = binary (/) recip id
--   recip = unary recip  (const . negate . (^2))
    fromRational r = lift $ fromRational r

instance Floating a => Floating (RAD s a) where
    pi      = lift pi
    exp     = unary exp id
    log     = unary log recip
    sqrt    = unary sqrt (recip . (2*) . sqrt)
    RAD (C x) ** RAD (C y) = lift (x ** y)
    x ** y  = RAD (B (vx ** vy) (vy/vx) (log (vx)) x y)
        where vx = primal x
              vy = primal y
    sin     = unary sin cos
    cos     = unary cos (negate . sin)
    asin    = unary asin (recip . sqrt . (1-) . (^2))
    acos    = unary acos (negate . recip . sqrt . (1-) . (^2))
    atan    = unary atan (recip . (1+) . (^2))
    sinh    = unary sinh cosh
    cosh    = unary cosh sinh
    asinh   = unary asinh (recip . sqrt . (1+) . (^2))
    acosh   = unary acosh (recip . sqrt . (-1+) . (^2))
    atanh   = unary atanh (recip . (1-) . (^2))

-- back propagate sensitivities along the tape.
backprop :: (Ix t, Ord t, Num a) => (Vertex -> (Tape a t, t, [t])) -> STArray s t a -> Vertex -> ST s ()
backprop vmap ss v = do
        case node of
            U _ g b -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + g*da)
            B _ gb gc b c -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + gb*da)
                dc <- readArray ss c
                writeArray ss c (dc + gc*da)
            _ -> return ()
    where 
        (node, i, _) = vmap v


runTape :: Num a => (Int, Int) -> Reified.Graph (Tape a) -> Array Int a
runTape vbounds (Reified.Graph xs start) = accumArray (+) 0 vbounds [ (id, sensitivities ! ix) | (ix, V _ id) <- xs ]
    where
        (g, vmap) = graphFromEdges' (edgeSet <$> filter nonConst xs)
        sensitivities = runSTArray $ do
            ss <- newArray (sbounds xs) 0
            writeArray ss start 1
            forM_ (topSort g) $ 
                backprop vmap ss
            return ss
        sbounds ((a,_):as) = foldl' (\(lo,hi) (b,_) -> (min lo b, max hi b)) (a,a) as
        edgeSet (i, t) = (t, i, successors t)
        nonConst (_, C{}) = False
        nonConst _ = True
        successors (U _ _ b)   = [b]
        successors (B _ _ _ b c) = [b,c]
        successors _ = []

tape :: RAD s a -> Reified.Graph (Tape a) 
tape = unsafePerformIO . reifyGraph

d :: Num a => RAD s a -> a
d r = runTape (0,0) (tape r) ! 0 

d2 :: Num a => RAD s a -> (a,a)
d2 r = (primal r, d r)

diffUU :: Num a => (forall s. RAD s a -> RAD s a) -> a -> a
diffUU f a = d $ f (var a 0)

diffUF :: (Functor f, Num a) => (forall s. RAD s a -> f (RAD s a)) -> a -> f a
diffUF f a = d <$> f (var a 0)

-- diffMU :: Num a => (forall s. [RAD s a] -> RAD s a) -> [a] -> [a] -> a
-- TODO: finish up diffMU and their ilk

diff2UU :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2UU f a = d2 $ f (var a 0)

diff2UF :: (Functor f, Num a) => (forall s. RAD s a -> f (RAD s a)) -> a -> f (a, a)
diff2UF f a = d2 <$> f (var a 0)

diff :: Num a => (forall s. RAD s a -> RAD s a) -> a -> a
diff = diffUU 

diff2 :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2 = diff2UU

-- requires the input list to be finite in length
grad :: Num a => (forall s. [RAD s a] -> RAD s a) -> [a] -> [a]
grad f as = elems $ runTape (1, length as) $ tape $ f $ zipWith var as [1..]

-- compute the primal and gradient
grad2 :: Num a => (forall s. [RAD s a] -> RAD s a) -> [a] -> (a, [a])
grad2 f as = (primal r, elems $ runTape (1, length as) (tape r))
    where r = f (zipWith var as [1..])

-- | The 'jacobian' function calcualtes the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. When the output dimensionality is
-- significantly greater than the input dimensionality you should use Numeric.FAD.jacobian instead.
jacobian :: (Functor f, Num a) => (forall s. [RAD s a] -> f (RAD s a)) -> [a] -> f [a]
jacobian f as = row <$> f (zipWith var as [1..])
    where bounds = (1, length as)
          row a = elems . runTape bounds . tape

-- | The 'jacobian2' function calcualtes both the result and the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. 
-- 'fmap snd' on the result will recover the result of 'jacobian'
jacobian2 :: (Functor f, Num a) => (forall s. [RAD s a] -> f (RAD s a)) -> [a] -> f (a, [a])
jacobian2 f as = row <$> f (zipWith var as [1..])
    where bounds = (1, length as)
          row a = (primal a, elems (runTape bounds (tape a)))

-- | The 'zeroNewton' function finds a zero of a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--  @take 10 $ zeroNewton (\\x->x^2-4) 1  -- converge to 2.0@
--
-- TEST CASE
--  :module Data.Complex Numeric.FAD
--  @take 10 $ zeroNewton ((+1).(^2)) (1 :+ 1)  -- converge to (0 :+ 1)@
--
zeroNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> [a]
zeroNewton f x0 = iterate (\x -> let (y,y') = diff2UU f x in x - y/y') x0

-- | The 'inverseNewton' function inverts a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--   @take 10 $ inverseNewton sqrt 1 (sqrt 10)  -- converge to 10@
--
inverseNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> a -> [a]
inverseNewton f x0 y = zeroNewton (\x -> f x - lift y) x0

-- | The 'fixedPointNewton' function find a fixedpoint of a scalar
-- function using Newton's method; its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)
fixedPointNewton :: Fractional a => (forall s. RAD s a -> RAD s a) -> a -> [a]
fixedPointNewton f = zeroNewton (\x -> f x - x)

-- | The 'extremumNewton' function finds an extremum of a scalar
-- function using Newton's method; produces a stream of increasingly
-- accurate results.  (Modulo the usual caveats.)
extremumNewton :: Fractional a => (forall s t. RAD t (RAD s a) -> RAD t (RAD s a)) -> a -> [a]
extremumNewton f x0 = zeroNewton (diffUU f) x0

-- | The 'argminNaiveGradient' function performs a multivariate
-- optimization, based on the naive-gradient-descent in the file
-- @stalingrad\/examples\/flow-tests\/pre-saddle-1a.vlad@ from the
-- VLAD compiler Stalingrad sources.  Its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)  
-- This is /O(n)/ faster than Numeric.FAD.argminNaiveGradient
argminNaiveGradient :: (Fractional a, Ord a) => (forall s. [RAD s a] -> RAD s a) -> [a] -> [[a]]
argminNaiveGradient f x0 =
    let
        gf = grad f
        loop x fx gx eta i =
            -- should check gx = 0 here
            let
                x1 = zipWith (+) x (map ((-eta)*) gx)
                fx1 = lowerFU f x1
                gx1 = gf x1
            in
              if eta == 0 then []
              else if (fx1 > fx) then loop x fx gx (eta/2) 0
                   else if all (==0) gx then []
                        -- else if fx1 == fx then loop x1 fx1 gx1 eta (i+1)
                        else x1:(if (i==10)
                                 then loop x1 fx1 gx1 (eta*2) 0
                                 else loop x1 fx1 gx1 eta (i+1))
    in
      loop x0 (lowerFU f x0) (gf x0) 0.1 0

{-
lowerUU :: (forall s. RAD s a -> RAD s b) -> a -> b
lowerUU f = primal . f . lift

lowerUF :: Functor f => (forall s. RAD s a -> f (RAD s b)) -> a -> f b
lowerUF f = fmap primal . f . lift

lowerFF :: (Functor f, Functor g) => (forall s. f (RAD s a) -> g (RAD s b)) -> f a -> g b
lowerFF f = fmap primal . f . fmap lift
-}

lowerFU :: Functor f => (forall s. f (RAD s a) -> RAD s b) -> f a -> b
lowerFU f = primal . f . fmap lift

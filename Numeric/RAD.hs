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

import Prelude hiding (mapM)
import Control.Applicative (Applicative(..),(<$>))
import Control.Monad.ST
import Control.Monad (forM_)
import Data.List (foldl')
import Data.Array.ST
import Data.Array
import Data.Ix
import Text.Show
import Data.Graph (graphFromEdges', topSort, Vertex)
import Data.Reify (reifyGraph, MuRef(..))
import qualified Data.Reify.Graph as Reified
import Data.Traversable (Traversable, mapM)
import System.IO.Unsafe (unsafePerformIO)

newtype RAD s a = RAD (Tape a (RAD s a))

data Tape a t
    = Literal a 
    | Var a Int
    | Binary a a a t t
    | Unary a a t 

instance Show a => Show (RAD s a) where
    showsPrec d = disc1 (showsPrec d)

-- | The 'lift' function injects a primal number into the RAD data type with a 0 derivative.
-- If reverse-mode AD numbers formed a monad, then 'lift' would be 'return'.
lift :: a -> RAD s a 
lift = RAD . Literal 
{-# INLINE lift #-}

primal :: RAD s a -> a
primal (RAD (Literal y)) = y
primal (RAD (Var y _)) = y
primal (RAD (Binary y _ _ _ _)) = y
primal (RAD (Unary y _ _)) = y
{-# INLINE primal #-}

var :: a -> Int -> RAD s a 
var a v = RAD (Var a v)

-- TODO: A higher-order data-reify
-- mapDeRef :: (Applicative f) => (forall a . Num a => RAD s a -> f (u a)) -> a -> f (Tape a (u a))
instance MuRef (RAD s a) where
    type DeRef (RAD s a) = Tape a
    mapDeRef f (RAD (Literal a)) = pure (Literal a)
    mapDeRef f (RAD (Var a v)) = pure (Var a v)
    mapDeRef f (RAD (Binary a jb jc x1 x2)) = Binary a jb jc <$> f x1 <*> f x2
    mapDeRef f (RAD (Unary a j x)) = Unary a j <$> f x

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
unary_ f _ (RAD (Literal b)) = RAD (Literal (f b))
unary_ f g b = RAD (Unary (disc1 f b) g b)
{-# INLINE unary_ #-}

unary :: (a -> a) -> (a -> a) -> RAD s a -> RAD s a
unary f _ (RAD (Literal b)) = RAD (Literal (f b))
unary f g b = RAD (Unary (disc1 f b) (disc1 g b) b)
{-# INLINE unary #-}

binary_ :: (a -> a -> a) -> a -> a -> RAD s a -> RAD s a -> RAD s a
binary_ f _ _ (RAD (Literal b)) (RAD (Literal c)) = RAD (Literal (f b c))
binary_ f gb gc b c = RAD (Binary (f vb vc) gb gc b c)
    where vb = primal b; vc = primal c
{-# INLINE binary_ #-}

-- binary_ with partials
binary :: (a -> a -> a) -> (a -> a) -> (a -> a) -> RAD s a -> RAD s a -> RAD s a
binary f _ _ (RAD (Literal b)) (RAD (Literal c)) = RAD (Literal (f b c))
binary f gb gc b c = RAD (Binary (f vb vc) (gb vc) (gc vb) b c)
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
from (RAD (Literal a)) x = RAD (Literal x)
from a x = RAD (Unary x 1 a)

fromBy :: Num a => RAD s a -> RAD s a -> Int -> a -> RAD s a 
fromBy (RAD (Literal a)) _ _ x = RAD (Literal x)
fromBy a delta n x = RAD (Binary x 1 (fromIntegral n) a delta)

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

    atan2 (RAD (Literal x)) (RAD (Literal y)) = RAD (Literal (atan2 x y))
    atan2 x y = RAD (Binary (atan2 vx vy) (vy*r) (-vx*r) x y)
        where vx = primal x
              vy = primal y
              r = recip (vx^2 + vy^2)

instance RealFrac a => RealFrac (RAD s a) where
    properFraction (RAD (Literal a)) = (w, RAD (Literal p))
        where (w, p) = properFraction a
    properFraction a = (w, RAD (Unary p 1 a))
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
    exp     = unary exp exp
    log     = unary log recip
    sqrt    = unary sqrt (recip . (2*) . sqrt)
    RAD (Literal x) ** RAD (Literal y) = lift (x ** y)
    x ** y  = RAD (Binary vz (vy*vz/vx) (vz*log vx) x y)
        where vx = primal x
              vy = primal y
              vz = vx ** vy
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
            Unary _ g b -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + g*da)
            Binary _ gb gc b c -> do
                da <- readArray ss i
                db <- readArray ss b
                writeArray ss b (db + gb*da)
                dc <- readArray ss c
                writeArray ss c (dc + gc*da)
            _ -> return ()
    where 
        (node, i, _) = vmap v

runTape :: Num a => (Int, Int) -> RAD s a -> Array Int a 
runTape vbounds tape = accumArray (+) 0 vbounds [ (id, sensitivities ! ix) | (ix, Var _ id) <- xs ]
    where
        Reified.Graph xs start = unsafePerformIO $ reifyGraph tape
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
        successors (Unary _ _ b) = [b]
        successors (Binary _ _ _ b c) = [b,c]
        successors _ = []    

        -- this isn't _quite_ right, as it should allow negative zeros to multiply through
        -- but then we have to know what an isNegativeZero looks like, and that rather limits
        -- our underlying data types we can permit.
        -- this approach however, allows for the occasional cycles to be resolved in the 
        -- dependency graph by breaking the cycle on 0 edges.

        -- test x = y where y = y * 0 + x

        -- successors (Unary _ db b) = edge db b []
        -- successors (Binary _ db dc b c) = edge db b (edge dc c [])
        -- successors _ = []    

        -- edge 0 x xs = xs
        -- edge _ x xs = x : xs

d :: Num a => RAD s a -> a
d r = runTape (0,0) r ! 0 

d2 :: Num a => RAD s a -> (a,a)
d2 r = (primal r, d r)


-- | The 'diffUU' function calculates the first derivative of a
-- scalar-to-scalar function.
diffUU :: Num a => (forall s. RAD s a -> RAD s a) -> a -> a
diffUU f a = d $ f (var a 0)


-- | The 'diffUF' function calculates the first derivative of
-- scalar-to-nonscalar function.
diffUF :: (Functor f, Num a) => (forall s. RAD s a -> f (RAD s a)) -> a -> f a
diffUF f a = d <$> f (var a 0)

-- diffMU :: Num a => (forall s. [RAD s a] -> RAD s a) -> [a] -> [a] -> a
-- TODO: finish up diffMU and their ilk

-- avoid dependency on MTL
newtype S a = S { runS :: Int -> (a,Int) } 

instance Monad S where
    return a = S (\s -> (a,s))
    S g >>= f = S (\s -> let (a,s') = g s in runS (f a) s')
    
bind :: Traversable f => f a -> (f (RAD s a), (Int,Int))
bind xs = (r,(0,s)) 
    where 
        (r,s) = runS (mapM freshVar xs) 0
        freshVar a = S (\s -> let s' = s + 1 in s' `seq` (RAD (Var a s), s'))

unbind :: Functor f => f (RAD s b) -> Array Int a -> f a 
unbind xs ys = fmap (\(RAD (Var _ i)) -> ys ! i) xs

-- | The 'diff2UU' function calculates the value and derivative, as a
-- pair, of a scalar-to-scalar function.
diff2UU :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2UU f a = d2 $ f (var a 0)

-- | Note that the signature differs from that used in Numeric.FAD, because while you can always
-- 'unzip' an arbitrary functor, not all functors can be zipped.
diff2UF :: (Functor f, Num a) => (forall s. RAD s a -> f (RAD s a)) -> a -> f (a, a)
diff2UF f a = d2 <$> f (var a 0)

-- | The 'diff' function is a synonym for 'diffUU'.
diff :: Num a => (forall s. RAD s a -> RAD s a) -> a -> a
diff = diffUU 

-- | The 'diff2' function is a synonym for 'diff2UU'.
diff2 :: Num a => (forall s. RAD s a -> RAD s a) -> a -> (a, a)
diff2 = diff2UU

-- requires the input list to be finite in length
grad :: (Traversable f, Num a) => (forall s. f (RAD s a) -> RAD s a) -> f a -> f a
grad f as = unbind s (runTape bounds $ f s)
    where (s,bounds) = bind as

-- compute the primal and gradient
grad2 :: (Traversable f, Num a) => (forall s. f (RAD s a) -> RAD s a) -> f a -> (a, f a)
grad2 f as = (primal r, unbind s (runTape bounds r))
    where (s,bounds) = bind as
          r = f s

-- | The 'jacobian' function calcualtes the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. When the output dimensionality is
-- significantly greater than the input dimensionality you should use 'Numeric.FAD.jacobian' instead.
jacobian :: (Traversable f, Functor g, Num a) => (forall s. f (RAD s a) -> g (RAD s a)) -> f a -> g (f a)
jacobian f as = unbind s . runTape bounds <$> f s
    where (s, bounds) = bind as

-- | The 'jacobian2' function calcualtes both the result and the Jacobian of a
-- nonscalar-to-nonscalar function, using m invocations of reverse AD,
-- where m is the output dimensionality. 
-- 'fmap snd' on the result will recover the result of 'jacobian'
jacobian2 :: (Traversable f, Functor g, Num a) => (forall s. f (RAD s a) -> g (RAD s a)) -> f a -> g (a, f a)
jacobian2 f as = row <$> f s
    where (s, bounds) = bind as
          row a = (primal a, unbind s (runTape bounds a))

-- | The 'zeroNewton' function finds a zero of a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--  @take 10 $ zeroNewton (\\x->x^2-4) 1  -- converge to 2.0@
--
-- TEST CASE
--  :module Data.Complex Numeric.RAD
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
-- This is /O(n)/ faster than 'Numeric.FAD.argminNaiveGradient'
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
      loop x0 (lowerFUnary f x0) (gf x0) 0.1 0

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

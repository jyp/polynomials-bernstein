{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RebindableSyntax #-}

module Algebra.Polynomials.Bernstein.Maintainable where

import Prelude hiding (Num(..),(/),mod,fromRational)
import Prelude (abs)
import Algebra.Classes
import Algebra.Linear hiding (index)
import Data.Foldable
import Test.QuickCheck
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MUV
import Control.Monad (replicateM)

-- | The type for Bernstein polynomials. The number of variables is
-- given by the functor f.
data BernsteinP f a = BernsteinP { degree :: f Int,  coefs :: UV.Vector a }

mapCoefs :: (MUV.Unbox a, MUV.Unbox b) => (a -> b) -> BernsteinP f a -> BernsteinP f b
mapCoefs f (BernsteinP d c) = BernsteinP d (UV.map f c)

deriving instance (UV.Unbox a, Show (f Int), Show a) => Show (BernsteinP f a)

ex :: BernsteinP V2' Double
ex = BernsteinP d (UV.replicate (rangeSize d) 1)
  where d = (V2' 4 4)

instance Arbitrary (BernsteinP V2' Double) where
  arbitrary = do
    m <- choose (0,5)
    n <- choose (0,5)
    c <- replicateM (n*m) arbitrary
    return $ BernsteinP (V2' m n) (UV.fromList c)

similarBP :: BernsteinP V2' Double -> BernsteinP V2' Double ->  Property
similarBP x y = forAll (choose (0::Double,1)) $ \t ->
                forAll (choose (0::Double,1)) $ \u ->
                let v = V2' t u
                in abs (deCasteljauN v x - deCasteljauN v y) < 0.01

prop_refl :: BernsteinP V2' Double -> Property
prop_refl x = similarBP x x

lerp :: Module scalar a => scalar -> a -> a -> a
lerp t a b = t *^ b + (one - t) *^ a

deCasteljau1 :: (Module a v) => a -> [v] -> v
deCasteljau1 _ [] = error "deCasteljau1: empty input"
deCasteljau1 _ [b] = b
deCasteljau1 t c = deCasteljau1 t (zipWith (lerp t) c (tail c))

deCasteljau :: MUV.Unbox a => Field a => Finite f => f a -> BernsteinP f a -> a
deCasteljau = deCasteljauN
 
bernstein :: (UV.Unbox a, Finite f) =>
  f Int -> (f Int -> a) -> BernsteinP f a
bernstein d f = BernsteinP d $ UV.create $ do
  v <- MUV.new (rangeSize d)
  forM_ (range d) $ \i -> MUV.write v (index d i) (f i)
  return v

(?) :: UV.Unbox e => Finite f => BernsteinP f e -> f Int -> e
BernsteinP d p ? i = p UV.! (index d i)

-- >>> index (V2' 1 1) (V2' 0 0)
-- 0

class (Foldable f,Applicative f) => Finite f where
  deCasteljauN :: (Field v,UV.Unbox v, Module a v) => f a -> BernsteinP f v -> v
  index :: f Int -> f Int -> Int
  rangeSize :: f Int -> Int
  range :: f Int -> [f Int]

instance Finite VZero where
  deCasteljauN VZero p = p ? VZero
  index _ _ = 0
  rangeSize _ = 1
  range _ = [VZero]

instance Finite f => Finite (VNext f) where
  range (VNext xs x) = [VNext zs z | z <- [0..x-1], zs <- range xs]
  rangeSize (VNext xs x) = rangeSize xs * x
  index (VNext xs _) (VNext zs z) = rangeSize xs*z + index xs zs
  deCasteljauN (VNext _ _) (BernsteinP (VNext _ 0) _) = 0
  deCasteljauN (VNext ts t) (BernsteinP (VNext ds d) c) =
    deCasteljauN ts (deCasteljau1 t [BernsteinP ds (UV.slice (i*s) s c) | i <- [0..d-1]])
    where s = rangeSize ds

instance (Field v,Finite f,UV.Unbox v,Module a v) => Module a (BernsteinP f v) where
  x *^ p  = mapCoefs (x *^) p

-- | binomials n generates binomial coefficients up to n.
-- (chose i j) is given by binomials (n-1) (i*n+j); if i,j <= n
binomials::(Ring a, MUV.Unbox a)=>Int-> Int -> Int -> a
binomials m i0 j0 = c UV.! (j0*(m+1)+i0) where
  c = UV.create $ do
    v<-MUV.replicate ((m+1)*(m+1)) 0
    MUV.write v 0 1
    let fill i
          | i>=(m+1)*(m+1) = return v
          | i`mod`(m+1) == 0 = do
            MUV.write v i 1
            fill (i+1)
          | otherwise = do
            a<-MUV.read v (i-m-1)
            b<-MUV.read v (i-m-2)
            MUV.write v i (a+b)
            fill (i+1)
    fill (m+1)

-- binomials :: forall a. Ring a => Int -> Int -> Int -> a
-- binomials n = b
--   where a :: Array (Int,Int) a
--         a = array bnds [((i,j), b' i j) | (i,j) <- range bnds]
--         b i j = a!(i,j)
--         b' _ 0 = zero
--         b' 0 _ = zero
--         b' i j | i > j  = zero
--         b' 1 _ = one
--         b' i j | i == j = one
--                | otherwise = b i (j-1) + b (i-1) (j-1)
--         bnds = ((0,0),(n,n))

-- >>> [binomials 10 i j  :: Int | j <- [0..5], i <- [0..5]]
-- [1,0,0,0,0,0,1,1,0,0,0,0,1,2,1,0,0,0,1,3,3,1,0,0,1,4,6,4,1,0,1,5,10,10,5,1]


-- | @elevateTo d p@ increases the degree of p to d without changing
-- its value; but won't lower the degree of p.
elevateTo :: forall f b. (Field b, UV.Unbox b,  Finite f) => f Int -> BernsteinP f b -> BernsteinP f b
elevateTo d p@(BernsteinP d0 _) = elevate ((-) <$> d <*> d0) p

prop_elevate :: BernsteinP (VNext V1') Double -> Property
prop_elevate p = forAll (choose (0,3)) $ \n ->
                 forAll (choose (0,3)) $ \m ->
                 elevate (V2' n m) p `similarBP` p

-- | @elevate r p@ increases the degree of p by r without changing its value.
elevate :: forall f b. (Field b,UV.Unbox b, Finite f) => f Int -> BernsteinP f b -> BernsteinP f b
elevate r_ p@(BernsteinP n _) = bernstein n'r coef
  where r = max 0 <$> r_
        n'r = (+) <$> n <*> r
        bin = binomials (maximum $ subtract 1 <$> n'r)
        f ii jj nn rr = bin ii (nn-1) * bin (jj-ii) rr / bin jj (nn+rr-1)
        coef j = add [ p?i * multiply (f <$> i <*> j <*> n <*> r)
                     | i <- range (min <$> n <*> ((+1) <$> j))]

-- | Add one more (constant) variable in last position
promote1 :: BernsteinP f b -> BernsteinP (VNext f) b
promote1 (BernsteinP d c) = BernsteinP (VNext d 1) c

-- | Add one more (constant) variable in butlast position
promote2 :: BernsteinP (VNext f) b -> BernsteinP (VNext (VNext f)) b
promote2 (BernsteinP (d `VNext` n) c) = BernsteinP (d `VNext` 1 `VNext` n) c

instance (Finite f,UV.Unbox b,Field b) => AbelianAdditive (BernsteinP f b)
instance (Finite f,UV.Unbox b,Field b) => Additive (BernsteinP f b) where
  zero = bernstein (pure zero) (error "BernsteinP: zero: panic: no index")
  x + y = BernsteinP dmax (UV.zipWith (+) cx cy)
    where dmax = max <$> degree x <*> degree y
          BernsteinP _ cx = elevateTo dmax x
          BernsteinP _ cy = elevateTo dmax y

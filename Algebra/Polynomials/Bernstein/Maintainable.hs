{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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
import qualified Prelude
import Prelude (abs)
import Algebra.Classes
import Algebra.Linear hiding (index)
import Data.Foldable
import Test.QuickCheck
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as MUV
import Control.Monad (replicateM)
import Control.Monad.ST

-- | An f-dimensional box (with Finite f)
type Box f a = (f a, f a)

-- | The type for Bernstein polynomials. The number of variables is
-- given by the functor f.
data BernsteinP f a = BernsteinP { degree :: f Int,  coefs :: UV.Vector a }
deriving instance (UV.Unbox a, Show (f Int), Show a) => Show (BernsteinP f a)

-- | Apply a function on the coefficients
mapCoefs :: (MUV.Unbox a, MUV.Unbox b) => (a -> b) -> BernsteinP f a -> BernsteinP f b
mapCoefs f (BernsteinP d c) = BernsteinP d (UV.map f c)

-- ex :: BernsteinP V2' Double
-- ex = BernsteinP d (UV.replicate (rangeSize d) 1)
--   where d = (V2' 4 4)

instance Arbitrary (BernsteinP V2' Double) where
  arbitrary = do
    m <- choose (0,5)
    n <- choose (0,5)
    c <- replicateM (n*m) arbitrary
    return $ BernsteinP (V2' m n) (UV.fromList c)

genPoint :: Gen (V2' Double)
genPoint = V2' <$> choose (0::Double,1) <*> choose (0::Double,1)

-- | Are the two polynomials within 0.01 ?
similarBP :: BernsteinP V2' Double -> BernsteinP V2' Double ->  Property
similarBP x y = forAll genPoint $ \v -> deCasteljauN v x `similar` deCasteljauN v y

-- | Are two points similar within 0.01 ?
similar :: (Ord a, Prelude.Num a, Field a) => a -> a -> Bool
similar x y = abs (x-y) < 0.01

genBox :: Gen (V2' Double, V2' Double)
genBox = do
  p <- genPoint
  q <- genPoint
  let a = min <$> p <*> q
  let b = max <$> p <*> q
  return (a,b)

prop_refl :: BernsteinP V2' Double -> Property
prop_refl x = similarBP x x

-- | Linear interpolation
{-# INLINE lerp #-}
lerp :: Module scalar a => scalar -> a -> a -> a
lerp t a b = (one - t) *^ a + t *^ b 

-- | One pass of deCasteljau algorithm
deCasteljau1 :: (Module a v) => a -> [v] -> v
deCasteljau1 _ [] = error "deCasteljau1: empty input"
deCasteljau1 _ [b] = b
deCasteljau1 t c = deCasteljau1 t (zipWith (lerp t) c (tail c))


deCasteljau :: MUV.Unbox a => Field a => Finite f => f a -> BernsteinP f a -> a
deCasteljau = deCasteljauN

-- | Construct a bernstein polynomial
bernstein :: (UV.Unbox a, Finite f) =>
  f Int -> (f Int -> a) -> BernsteinP f a
bernstein d f = BernsteinP d $ UV.create $ do
  v <- MUV.new (rangeSize d)
  forM_ (range d) $ \i -> MUV.write v (index d i) (f i)
  return v

-- | Query a coefficient
(?) :: UV.Unbox e => Finite f => BernsteinP f e -> f Int -> e
BernsteinP d p ? i = p UV.! (index d i)

-- >>> index (V2' 1 1) (V2' 0 0)
-- 0

class (Foldable f,Applicative f) => Finite f where
  index :: f Int -> f Int -> Int
  rangeSize :: f Int -> Int
  range :: f Int -> [f Int]
  cut :: (Field a,Ord a) => Int -> (f a,f a) -> [(f a,f a)]
  deCasteljauN :: (Field v,UV.Unbox v, Module a v) => f a -> BernsteinP f v -> v
  restrictN :: (Field a, UV.Unbox a) => Int -> f Int -> Box f a -> MUV.MVector s a -> ST s ()

prop_restrict :: BernsteinP V2' Double -> Property
prop_restrict p =
  forAll genBox $ \b@(lo,hi) ->
  forAll genPoint $ \t ->
  let t' = (+) <$> lo <*> ((*) <$> ((-) <$> hi <*> lo) <*> t)
  in deCasteljau t (restrict b p) `similar` deCasteljau t' p

-- | Restrict a polynomial to the given sub-box of the f-dimensional unit-box.
restrict :: (MUV.Unbox a, Finite f, Field a) => Box f a -> BernsteinP f a -> BernsteinP f a
restrict box (BernsteinP d p) = runST $ do
  pf <- UV.thaw p
  restrictN 1 d box pf
  pff <- UV.unsafeFreeze pf
  return (BernsteinP d pff)


instance Finite VZero where
  deCasteljauN VZero p = p ? VZero
  index _ _ = 0
  rangeSize _ = 1
  range _ = [VZero]
  cut _ _ = error "BernsteinP: attempt to cut in non-existing dimension"
  restrictN _ _ _ _ = return ()

boxSize :: (Ring a, Finite f) => Box f a -> a
boxSize (a,b) = multiply ((-) <$> b <*> a)

variables :: forall f. Finite f => Int
variables = length (pure () :: f ())

-- | Run a restriction pass (to the interval [u,v]) on Berstein
-- coefficients pf, in-place. The dimension to act on is given by the
-- stride of the combined "smaller" dimensions (aft), the size of the
-- current dimension (nv) and the size of the combined larger
-- dimensions (bef).

-- This is done by running "nv-1" passes over the data, each
-- performing a local linear interpolation between neighboring points
-- in the specified dimension.  Each pass is split into two parts, one
-- interpolating towards u, one towards v.
restrict1 :: (MUV.Unbox a, Field a) => MUV.MVector s a -> Int -> Int -> Int -> a -> a -> ST s ()
restrict1 pf bef nv aft u v = go 0 0 1 0
  where
    idx i j k=(i*nv+j)*aft + k -- index in space (bef,nv,aft)
    v'=(v-u)/(1-u) -- scale 2nd part to account for 1st part restriction.
    go i k s j -- s is the pass number.
      | i>=bef = return ()
      | k>=aft= go (i+1) 0 1 0
      | s>=nv = go i (k+1) 1 0
      | j>=nv = go i k (s+1) 0
      | otherwise= do
          if s+j<nv
            then do
                 pfi0<-MUV.read pf (idx i j k)
                 pfi1<-MUV.read pf (idx i (j+1) k)
                 MUV.write pf (idx i j k) $ lerp u pfi0 pfi1
            else do
                 pfi0<-MUV.read pf (idx i (j-1) k)
                 pfi1<-MUV.read pf (idx i j k)
                 MUV.write pf (idx i j k) $ lerp v' pfi0 pfi1
          go i k s (j+1)

instance Finite f => Finite (VNext f) where
  range (VNext xs x) = [VNext zs z | z <- [0..x-1], zs <- range xs]
  rangeSize (VNext xs x) = rangeSize xs * x
  index (VNext xs _) (VNext zs z) = rangeSize xs*z + index xs zs
  cut 0 x@(VNext as a,VNext bs b) = if a<m && m<b then
                                      [(VNext as a,VNext bs m),(VNext as m,VNext bs b)]
                                    else
                                      [x]
    where m=(a+b)/2
  cut n (VNext as a,VNext bs b) = [(VNext l a, VNext h b) | (l,h) <- cut (n-1) (as,bs)]
  deCasteljauN (VNext _ _) (BernsteinP (VNext _ 0) _) = 0
  deCasteljauN (VNext ts t) (BernsteinP (VNext ds d) c) =
    deCasteljauN ts (deCasteljau1 t [BernsteinP ds (UV.slice (i*s) s c) | i <- [0..d-1]])
    where s = rangeSize ds
  restrictN bef (VNext ds d) (VNext as a, VNext bs b) pf = do
    restrictN (bef*d) ds (as,bs) pf
    restrict1 pf bef d (multiply ds) a b

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
instance (Finite f,UV.Unbox b,Field b) => Group (BernsteinP f b) where
  negate = mapCoefs negate

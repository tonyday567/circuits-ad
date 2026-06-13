{-# LANGUAGE RebindableSyntax #-}

-- | Small square-matrix toolbox for star-elimination over list channels.
--
-- This is the list-backed implementation used internally by
-- "Circuit.AD.Eliminate" and "Circuit.AD.Star".  The public,
-- typed-array version lives in "Harpie.NumHask.Matrix".
module Circuit.AD.Matrix
  ( Matrix (..),
    matPlus,
    matTimes,
    matVec,
    starMatrix,
  )
where

import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import Prelude (Bool (..), Eq, Int, Show, all, drop, foldr, fromInteger, length, replicate, take, zip, zipWith, (++))
import Prelude qualified as P

-- | Square matrix stored row-major.
newtype Matrix a = Matrix {unMatrix :: [[a]]}
  deriving (Eq, Show)

-- | Elementwise addition.
matPlus :: NHA.Additive a => Matrix a -> Matrix a -> Matrix a
matPlus (Matrix a) (Matrix b) =
  Matrix [zipWith (NHA.+) rowA rowB | (rowA, rowB) <- zip a b]

-- | Matrix–vector product.
matVec :: (NHA.Additive a, NHM.Multiplicative a) => Matrix a -> [a] -> [a]
matVec (Matrix m) v =
  [foldr (NHA.+) NHA.zero (zipWith (NHM.*) row v) | row <- m]

-- | Matrix multiplication.
matTimes ::
  (NHA.Additive a, NHM.Multiplicative a) =>
  Matrix a ->
  Matrix a ->
  Matrix a
matTimes (Matrix a) (Matrix b) =
  Matrix [[foldr (NHA.+) NHA.zero (zipWith (NHM.*) row col) | col <- transpose b] | row <- a]
  where
    transpose :: [[a]] -> [[a]]
    transpose [] = []
    transpose xss
      | all P.null xss = []
      | P.otherwise = [h | (h : _) <- xss] : transpose [t | (_ : t) <- xss]

-- | Partition a square matrix into four quadrants.
partition :: Matrix a -> (Matrix a, Matrix a, Matrix a, Matrix a)
partition (Matrix m) =
  let n = length m
      k = n `P.div` 2
      top = take k m
      bot = drop k m
      a = Matrix [take k row | row <- top]
      b = Matrix [drop k row | row <- top]
      c = Matrix [take k row | row <- bot]
      d = Matrix [drop k row | row <- bot]
   in (a, b, c, d)

-- | Combine four quadrants into a single matrix.
combine :: Matrix a -> Matrix a -> Matrix a -> Matrix a -> Matrix a
combine (Matrix a) (Matrix b) (Matrix c) (Matrix d) =
  Matrix
    ( [rowA ++ rowB | (rowA, rowB) <- zip a b]
        ++ [rowC ++ rowD | (rowC, rowD) <- zip c d]
    )

-- | Kleene star of a square matrix by 2×2 block recursion.
starMatrix :: NHR.StarSemiring a => Matrix a -> Matrix a
starMatrix (Matrix []) = Matrix []
starMatrix m =
  case unMatrix m of
    [[a]] -> Matrix [[NHR.star a]]
    _ ->
      let (a, b, c, d) = partition m
          dStar = starMatrix d
          f = matPlus a (matTimes b (matTimes dStar c))
          fStar = starMatrix f
          e = fStar
          fBlock = matTimes fStar (matTimes b dStar)
          g = matTimes dStar (matTimes c fStar)
          h = matPlus dStar (matTimes dStar (matTimes c (matTimes fStar (matTimes b dStar))))
       in combine e fBlock g h

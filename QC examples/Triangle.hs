module Triangle where

import Data.List (sort, deleteBy)
import Test.QuickCheck

data TriangleType = NotTriangle
  | Equilateral
  | Isosceles
  | Other
  deriving (Eq, Show)

triangleType a b c
  | a == b && b == c     = Equilateral
  | not (a' + b' > c')   = NotTriangle
  | a' == b' || b' == c' = Isosceles
  | otherwise            = Other
  where
  [a', b', c'] = sort [a, b, c]

data TriangleLengths = TriangleLengths Int Int Int
  deriving (Show)

instance Arbitrary TriangleLengths where
  arbitrary = do
    (Positive a) <- arbitrary
    (Positive b) <- arbitrary
    (Positive c) <- arbitrary
    return $ TriangleLengths a b c

perm l = aux n l
  where
  aux 0 [] = return []
  aux n l  = do
    i <- choose (0,n-1)
    let l'     = zip [0..] l
        Just x = lookup i l'
    xs <- aux (n-1) (map snd $ deleteBy (\x y -> fst x == fst y) (i,x) l')
    return $ x:xs
  n = length l

prop_perm (TriangleLengths a b c) = do
  [a', b', c'] <- perm [a, b, c]
  return $ triangleType a b c == triangleType a' b' c'

prop_notTriangle (TriangleLengths a b c) =
  let [a', b', c'] = sort [a, b, c] in
  c' > a' + b' ==> forAll (perm [a', b', c']) $ \[a'', b'', c''] ->
    triangleType a'' b'' c'' == NotTriangle


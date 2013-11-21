module Queue where

import Test.QuickCheck

data Queue = BQ [Int] [Int]
  deriving (Show)

bq :: [Int] -> [Int] -> Queue
bq [] r = BQ (reverse r) []
bq f  r = BQ f r

empty :: Queue
empty = BQ [] []

enqueue :: Int -> Queue -> Queue
enqueue x (BQ f r) = bq f (x:r)

dequeue :: Queue -> Queue
dequeue (BQ f r) = bq (tail f) r

isEmpty :: Queue -> Bool
isEmpty (BQ f r) = null f

front :: Queue -> Int
front (BQ f r) = last f

prop_front_singleton x = front (enqueue x empty) == x

prop_front_non_empty q x = not (isEmpty q) ==> front (enqueue x q) == front q

prop_front_deq q x = not (isEmpty q) ==> front (dequeue (enqueue x q)) == front (enqueue x (dequeue q))

invariant (BQ f r) = not (null f) || null r

instance Arbitrary Queue where
  arbitrary = do
    x <- arbitrary
    y <- arbitrary
    return $ bq x y

  shrink (BQ f r) =
    [ q | f' <- shrink f, let q = BQ f' r, invariant q ] ++
    [ q | r' <- shrink r, let q = BQ f r', invariant q ]

data Op = Enq Int | Deq | Front
  deriving Show

instance Arbitrary Op where
  arbitrary = oneof [fmap Enq arbitrary, return Deq, return Front]

  shrink (Enq x) = map Enq $ shrink x
  shrink _       = []

model :: [Op] -> [Maybe Int]
model l = aux [] l
  where
  aux s     []        = []
  aux s     (Enq x:l) = Nothing : aux (s++[x]) l
  aux []    (Deq:_)   = []
  aux (y:s) (Deq:l)   = Nothing : aux s        l
  aux []    (Front:_) = []
  aux (y:s) (Front:l) = Just y  : aux (y:s)    l

sut :: [Op] -> [Maybe Int]
sut l = aux empty l
  where
  aux s []        = []
  aux s (Enq x:l) = Nothing        : aux (enqueue x s) l
  aux s (Deq:l)   = Nothing        : aux (dequeue s)   l
  aux s (Front:l) = Just (front s) : aux s             l

prop_model :: [Op] -> Bool
prop_model l = m == sut (zipWith const l m)
  where
  m = model l

module Filter where

import Test.QuickCheck
import Test.QuickCheck.Function

prop_filter_1 :: Fun Int Bool -> [Int] -> Bool
prop_filter_1 (Fun _ p) l = all p $ filter p l

filter' :: [Int] -> [Int]
filter' l = filter (>2000) l

prop_filter' :: [Int] -> Bool
prop_filter' l = all (>2001) $ filter' l



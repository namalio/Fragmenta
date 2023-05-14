
module TheNil(The(..), Nil(..)) where

class The f where
   the ::  Eq a =>f a-> a

class Nil f where
   nil ::  f a
   isNil ::  Eq a =>f a-> Bool
   isSomething ::  Eq a =>f a-> Bool
   isNil f = not $ isSomething f
   isSomething f = not $ isNil f

--class Unique f where
--   unique :: Eq a =>f a ->Bool
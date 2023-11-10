
module TheNil(The(..), Nil(..)) where

class The f where
   the :: f a-> a

class Nil f where
   nil ::  f a
   isNil ::  f a-> Bool
   isSomething ::  f a-> Bool
   isNil f = not $ isSomething f
   isSomething f = not $ isNil f

--class Unique f where
--   unique :: Eq a =>f a ->Bool
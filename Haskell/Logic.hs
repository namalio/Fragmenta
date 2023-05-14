
module Logic(implies, iff) where

-- Implication
implies :: Bool -> Bool -> Bool
implies False _ = True
implies True True = True
implies True False = False

iff :: Bool -> Bool -> Bool
iff p q = p `implies` q && q`implies` p
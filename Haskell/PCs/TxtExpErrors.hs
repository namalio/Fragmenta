
module PCs.TxtExpErrors 
    (E
    , thenE
    , returnE
    , failE
    , catchE
    ) 
    where

type E a = Either a String

thenE :: E a -> (a -> E b) -> E b
m `thenE` k =
   case m of
       Left a     -> k a
       Right e    -> Right e

returnE :: a -> E a
returnE a = Left a

failE :: String -> E a
failE err = Right err

catchE :: E a -> (String -> E a) -> E a
catchE m k =
   case m of
      Left a    -> Left a
      Right e   -> k e
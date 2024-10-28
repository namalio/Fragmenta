module QUR(
    Pair,
    Quad,
    QuadURel(..)
    , qur
    , consQUR
    , nilQUR
    , qurOneTpl
    , singleQUR
    , join
    , gJoin
    , singleQURFrFst
    , singleQURFrSndTrpl
    , fstQUR
    , quad) where

import Relations
import Sets
import SimpleFuns ( combineQwUnion, makeQFrTFst )

type Pair a = (a, a)
type Trpl a = (a, a, a)
type Quad a = (a, a, a, a)
newtype QuadURel a = QuadURel (Quad (Rel a a))

instance Show a=>Show (QuadURel a) where
    show :: QuadURel a -> String
    show (QuadURel (x, y, z, w)) = "QUR (" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show w ++ ")" 

qur :: Quad (Rel a a) -> QuadURel a
qur = QuadURel

consQUR::Rel a a->Rel a a->Rel a a->Rel a a->QuadURel a
consQUR x y z w = qur (x, y, z, w)

-- Creates a QUR with emty sets
nilQUR :: QuadURel a
nilQUR = qur (EmptyS, EmptyS, EmptyS, EmptyS)

-- Gets 1st component of a QUR
fstQUR::QuadURel a->Rel a a
fstQUR (QuadURel (x, _, _, _)) = x

-- Gets quadruple a QUR
quad::QuadURel a->Quad(Rel a a)
quad (QuadURel q) = q

qurOneTpl::Rel a a->Trpl (Rel a a)->QuadURel a
qurOneTpl xs t = qur $ makeQFrTFst xs t

singleQUR::Quad(Pair a)->QuadURel a
singleQUR (x, y, z, w) = qur (singles x, singles y, singles z, singles w)

singleQURFrFst::Pair a->QuadURel a
singleQURFrFst x = qur (singles x, EmptyS, EmptyS, EmptyS)

singleQURFrSndTrpl::Trpl (Pair a)->QuadURel a
singleQURFrSndTrpl (y, z, w) = qur (EmptyS, singles y, singles z, singles w)

join::Eq a=>QuadURel a->QuadURel a->QuadURel a
(QuadURel q1) `join` (QuadURel q2) = QuadURel $ q1 `combineQwUnion` q2

gJoin::Eq a=>[QuadURel a]->QuadURel a
gJoin = foldl join nilQUR



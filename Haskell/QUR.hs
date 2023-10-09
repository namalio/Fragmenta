module QUR(
    QuadURel(..)
    , qur
    , nilQUR
    , qurOneTpl
    , singleQUR
    , join
    , gJoin
    , singleQURFrFst) where

import Relations
import Sets
import SimpleFuns

type Pair a = (a, a)
type Trpl a = (a, a, a)
type Quad a = (a, a, a, a)
newtype QuadURel a = QuadURel (Quad (Rel a a))

qur :: Quad (Rel a a) -> QuadURel a
qur = QuadURel

nilQUR :: QuadURel a
nilQUR = qur (EmptyS, EmptyS, EmptyS, EmptyS)

qurOneTpl::Rel a a->Trpl (Rel a a)->QuadURel a
qurOneTpl xs t = qur $ makeQFrTFst xs t

singleQUR::Quad(Pair a)->QuadURel a
singleQUR (x, y, z, w)= qur (singles x, singles y, singles z, singles w)

singleQURFrFst::Pair a->QuadURel a
singleQURFrFst x = qur $ makeQFrTFst (singles x) (EmptyS, EmptyS, EmptyS)

join::Eq a=>QuadURel a->QuadURel a->QuadURel a
(QuadURel q1) `join` (QuadURel q2) = QuadURel $ q1 `combineQwUnion` q2

gJoin::Eq a=>[QuadURel a]->QuadURel a
gJoin = foldl join nilQUR



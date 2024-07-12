module QUR(
    Pair,
    Quad,
    QuadURel(..)
    , qur
    , nilQUR
    , qurOneTpl
    , singleQUR
    , join
    , gJoin
    , singleQURFrFst
    , singleQURFrSndTrpl
    , fstQUR
    , quadQUR) where

import Relations
import Sets
import SimpleFuns ( combineQwUnion, makeQFrTFst )

type Pair a = (a, a)
type Trpl a = (a, a, a)
type Quad a = (a, a, a, a)
newtype QuadURel a = QuadURel (Quad (Rel a a))

qur :: Quad (Rel a a) -> QuadURel a
qur = QuadURel

-- Creates a QUR with emty sets
nilQUR :: QuadURel a
nilQUR = qur (EmptyS, EmptyS, EmptyS, EmptyS)

-- Gets 1st component of a QUR
fstQUR::QuadURel a->Rel a a
fstQUR (QuadURel (x, _, _, _)) = x

-- Gets quadruple a QUR
quadQUR::QuadURel a->Quad(Rel a a)
quadQUR (QuadURel q) = q

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




import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Relations (Rel, dom_of, ran_of, inv, id_on, dres, rres, dsub, rsub, img, functional, fun_bij, fun_pinj, appl, 
                  override, rcomp, injective, bcomp, reflexive, antireflexive, symmetric, transitive, pfun, trancl, 
                  rtrancl, rtrancl_on, acyclic, cross, eq_rel)
import FragmentaTests.Sets.SetsDefs
import Sets(Set(..), toList, set, intersec, power, card, zipS, sminus, intoSet, singles, union, disjoint)
import TheNil

testDom1::Assertion
testDom1 = assertEqual "Domain of empty relation" (dom_of (nil::Rel Int Int)) (nil::Set Int)

testDom2::Assertion
testDom2 = assertEqual "Domain of some relation" (dom_of . set $ [(2, 3), (3, 4)]) (set [2, 3])

propDomOf1::Eq a=>Rel a b->Bool
propDomOf1 r = all(\(x, _)-> x `elem` dom_of r) r

propDomOf2::Int->Bool
propDomOf2 k = dom_of (zipS a b) == a
             where a = set [0..k-1]
                   b = set [k..2*k]

testsDomOf :: TestTree
testsDomOf = testGroup "tests related to the domain relational operator" [
      testCase "Domain of empty relation" testDom1
      , testCase "Domain of some relation" testDom2
      , testProperty "Any x element of a relation is in the domain of the relation " (propDomOf1::Rel Int Int->Bool)
      , testProperty "The domain of the zip of two sets is the first set" propDomOf2
      ]

testRan1::Assertion
testRan1 = assertEqual "Range of empty relation" (ran_of (nil::Rel Int Int)) (nil::Set Int)

testRan2::Assertion
testRan2 = assertEqual "Range of some relation" (ran_of . set $ [(2, 3), (3, 4)]) (set [3, 4])

propRanOf1::Rel Int Int->Bool
propRanOf1 r = all(\(_, y)-> y `elem` ran_of r) r

propRanOf2::Int->Bool
propRanOf2 k = ran_of (zipS a b) == b
             where a = set [0..k-1]
                   b = set [k..(2*k)-1]

testsRanOf :: TestTree
testsRanOf = testGroup "tests related to the domain relational operator" [
      testCase "Range of empty relation" testRan1
      , testCase "Range of some relation" testRan2
      , testProperty "Any x element of a relation is in the domain of the relation " propRanOf1
      , testProperty "The domain of the zip of two sets is the first set" propRanOf2
      ]

testId1::Assertion
testId1 = assertEqual "Identity of empty set" (id_on (nil::Set Int)) (nil::Rel Int Int)

propId1::Eq a=>Set a->Bool
propId1 xs = all (\x->(x, x) `elem` rid) xs
            where rid = id_on xs

propId2::Eq a=>Set a->Bool
propId2 xs = dom_of rid == ran_of rid
            where rid = id_on xs

testsIdOf :: TestTree
testsIdOf = testGroup "tests related to the domain relational operator" [
      testCase "id_on ∅ = ∅ <-> ∅" testId1
      , testProperty "∀ x ∈ A. (x, x) ∈ id_on A" (propId1::Set Int->Bool)
      , testProperty "dom (id_on A) = ran (id_on A)" (propId2::Set Int->Bool)
      ]

testInv1::Assertion
testInv1 = assertEqual "Inversion of empty relation" (inv (nil::Rel Int Char)) (nil::Rel Char Int)

testInv2::Assertion
testInv2 = assertEqual "Inversion of singleton relation" (inv $ singles (2, 3)) (singles (3, 2))

propInv1::Int->Bool
propInv1 k = inv (zipS a b) == zipS b a
             where k' = abs k
                   a = set [0..k'-1]
                   b = set [k..(2*k')-1]

propInv2::(Eq a, Eq b)=>Rel a b->Bool
propInv2 r = all(\(x, y)-> (y, x) `elem` inv r) r

propInv3::(Eq a, Eq b)=>Rel a b->Bool
propInv3 r = r == (inv . inv $ r)

propDomOfInvEqRan::(Eq a, Eq b)=>Rel a b->Bool
propDomOfInvEqRan r = (dom_of . inv  $ r) == ran_of r

propRanOfInvEqDom::Eq a=>Rel a b->Bool
propRanOfInvEqDom r = (ran_of . inv  $ r) == dom_of r

propInvId::Eq a=>Set a->Bool
propInvId s = (inv . id_on $ s) == id_on s

testsInv :: TestTree
testsInv = testGroup "tests related to the inversion relational operator" [
      testCase "Inversion of empty relation" testInv1
      , testCase "Inversion of singleton relation" testInv2
      , testProperty "The inversion of a zip is the zip inverted" propInv1
      , testProperty "The domain of the zip of two sets is the first set" (propInv2::Rel Int Int->Bool)
      , testProperty "The inverse of the inverse of the relation is the relation itself" (propInv3::Rel Int Int->Bool)
      , testProperty "dom (inv R) = ran R" (propDomOfInvEqRan::Rel Int Int->Bool)
      , testProperty "ran (inv R) = dom R" (propDomOfInvEqRan::Rel Int Int->Bool)
      , testProperty "(id_on A)~ = id_on A" (propInvId::Set Int->Bool)
      ]


--propDomOf2::(Int, Int)->Rel Int Int->Property
--propDomOf2 p r = p `elem` r ==> fst p `elem` dom_of r

--propDomOfInvRanOf::Int->Rel Int Int->Property
--propDomOfInvRanOf x r = x `elem` dom_of r ==> x `elem` (ran_of . inv $ r)

--propRanOfInvDomOf::Int->Rel Int Int->Property
--propRanOfInvDomOf y r = y `elem` ran_of r ==> y `elem` (dom_of . inv $ r)

propDres1::Eq a=>Set a->Bool
propDres1 s = dres (nil::Rel a Int) s == nil

propDres2::(Eq a, Eq b)=>Rel a b->Bool
propDres2 r = dres r EmptyS == nil

propDres3::(Eq a, Eq b)=>Rel a b->Set a->Bool
propDres3 r a = dom_of (dres r a) <= a
      --(not . null) (a `intersec` dom_of r) ==> dom_of (dres r a) <= a

propDres4::(Eq a, Eq b)=>Rel a b->Property
propDres4 r = length r < 10 ==> all(\a->dom_of (dres r a) == a)(power $ dom_of r)

testsDRes :: TestTree
testsDRes = testGroup "Domain restriction" [
      testProperty "A ◁ ∅ = ∅" (propDres1::Set Int->Bool)
      , testProperty "∅ ◁ r = ∅" (propDres2::Rel Int Char->Bool)
      , testProperty "dom(A ◁ r) ⊆ A" (propDres3::Rel Int Char->Set Int->Bool)
      , testProperty "∀ A : dom r . dom(A ◁ r) = A" (propDres4::Rel Int Char->Property)
      ]

--propDres4::Rel Int Int->Set Int->Property
--propDres4 r a = null (a `intersec` dom_of r) ==> dom_of (dres r a) == nil

propRres1::Eq b=>Set b->Bool
propRres1 s = rres  (nil::Rel Int b) s == nil

propRres2::(Eq a, Eq b)=>Rel a b->Bool
propRres2 r = rres r EmptyS == nil

propRres3::(Eq a, Eq b)=>Rel a b->Set b->Bool
propRres3 r a = ran_of (rres r a) <= a
      --(not . null) (a `intersec` ran_of r) ==> ran_of (rres r a) <= a

--propRres4::Rel Int Int->Set Int->Property
--propRres4 r a = null (a `intersec` ran_of r) ==> ran_of (rres r a) == nil

propRres4::(Eq a, Eq b)=>Rel a b->Property
propRres4 r = length r < 10 ==> all(\a->ran_of (rres r a) == a)(power $ ran_of r)

propDresRres::(Eq a, Eq b)=>Rel a b->Set a->Set b->Bool
propDresRres r a b = dom_of rr <= a && ran_of rr <= b
                     where rr = rres (dres r a) b

--(not . null) (a `intersec` dom_of r) && (not . null) (b `intersec` ran_of r) 

testsRRes :: TestTree
testsRRes = testGroup "Range restriction" [
      testProperty "∅ ▷ A = ∅" (propRres1::Set Int->Bool)
      , testProperty "r ▷ ∅= ∅" (propDres2::Rel Int Int->Bool)
      , testProperty "ran(r ▷ A) ⊆ A" (propRres3::Rel Int Int->Set Int->Bool)
      , testProperty "∀ A : dom r . ran(r ▷ A) = A" (propRres4::Rel Int Int->Property)
      , testProperty "∀ A : dom r; B : ran r . dom(A ◁ r ▷B) ⊆ A ∧ ran(A ◁ r ▷B) ⊆ B" (propDresRres::Rel Int Int->Set Int->Set Int->Bool)
      ]

propDSub1::Eq a=>Set a->Bool
propDSub1 s = dsub (nil::Rel a Int) s == nil

propDsub2::(Eq a, Eq b)=>Rel a b->Bool
propDsub2 r = dsub r nil == r

propDsub3::(Eq a, Eq b)=>Rel a b->Set a->Property
propDsub3 r a = (not . null) (a `intersec` dom_of r) ==> null $ dom_of (dsub r a) `intersec` a

propDsub4::(Eq a, Eq b)=>Rel a b->Set a->Property
propDsub4 r a = null (a `intersec` dom_of r) ==> dsub r a == r

propDsub5::(Eq a, Eq b)=>Rel a b->Property
propDsub5 r = length r < 10 ==> all(\a->null $ dom_of (dsub r a) `intersec` a)(power $ dom_of r)

propDsub6::(Eq a, Eq b)=>Rel a b->Set a->Bool
propDsub6 r a = dsub r a == dres r (dom_of r `sminus` a)

testsDSub :: TestTree
testsDSub = testGroup "Domain subtraction" [
      testProperty "A ⩤ ∅ = ∅" (propDSub1::Set Int->Bool)
      , testProperty "(∅ ⩤ r) = r" (propDsub2::Rel Int Int->Bool)
      , testProperty "A ∩ dom r ≠ ∅ => dom (A ⩤ r) ∩ A = ∅" (propDsub3::Rel Int Int->Set Int->Property)
      , testProperty "A ∩ dom r = ∅ => A ⩤ r = r" (propDsub4::Rel Int Int->Set Int->Property)
      , testProperty "∀ A : 𝒫 dom r . dom (A ⩤ r) ∩ A = ∅" (propDsub5::Rel Int Int->Property)
      , testProperty "A ⩤ r = (dom r ∖ A) ◁ r" (propDsub6::Rel Int Int->Set Int->Bool)
      ]

propRSub1::Eq b=>Set b->Bool
propRSub1 b = rsub (nil::Rel Int b) b == nil

propRsub2::(Eq a, Eq b)=>Rel a b->Bool
propRsub2 r = rsub r nil == r

propRsub3::(Eq a, Eq b)=>Rel a b->Set b->Property
propRsub3 r a = (not . null) (a `intersec` ran_of r) ==> null $ ran_of (rsub r a) `intersec` a

propRsub4::(Eq a, Eq b)=>Rel a b->Set b->Property
propRsub4 r a = null (a `intersec` ran_of r) ==> rsub r a == r

propRsub5::(Eq a, Eq b)=>Rel a b->Property
propRsub5 r = length r < 10 ==> all(\a->null $ ran_of (rsub r a) `intersec` a)(power $ ran_of r)

propRsub6::(Eq a, Eq b)=>Rel a b->Set b->Bool
propRsub6 r a = rsub r a == rres r (ran_of r `sminus` a)

testsRSub :: TestTree
testsRSub = testGroup "Domain subtraction" [
      testProperty "A ⩥ ∅ = ∅" (propRSub1::Set Int->Bool)
      , testProperty "(r ⩥ ∅) = r" (propRsub2::Rel Int Int->Bool)
      , testProperty "A ∩ ran r ≠ ∅ => ran (r ⩥ A) ∩ A = ∅" (propRsub3::Rel Int Int->Set Int->Property)
      , testProperty "A ∩ ran r = ∅ => r ⩥ A = r" (propRsub4::Rel Int Int->Set Int->Property)
      , testProperty "∀ A : 𝒫 dom r . ran (r ⩥ A) ∩ A = ∅" (propRsub5::Rel Int Int->Property)
      , testProperty "r ⩥ A =  r ▷ (ran r ∖ A)" (propRsub6::Rel Int Int->Set Int->Bool)
      ]

propImg1::Eq a=>Set a->Bool
propImg1 s = img (nil::Rel a Int) s == nil

propImg2::(Eq a, Eq b)=>Rel a b->Bool
propImg2 r = img r EmptyS == nil

propImg3::(Eq a, Eq b)=>Rel a b->Set a->Bool
propImg3 r a = img r a == ran_of (dres r a)

propImg4::(Eq a, Eq b)=>Rel a b->Set a->Bool
propImg4 r a = img r a == dom_of (rres (inv r) a)

--propImg5::Rel a b->Bool
--propImg5 r = all (\x->card (img r' (singles x))==1) (dom_of r')
--              where r' = foldr (\(x, y) rn->if x `elem` dom_of rn then rn else (x,y) `intoSet` rn) nil r

propImg5::(Eq a, Eq b)=>Rel a b->Property
propImg5 r = functional r==>all (\x->card (img r (singles x))==1) (dom_of r)

propAppl1::(Eq a, Eq b)=>Rel a b->Property
propAppl1 r = functional r==>all (\(x, y)->appl r x==y) r           

propAppl2::(Eq a, Eq b)=>Rel a b->Bool
propAppl2 r = all (\x->(appl r x) `elem` img r (singles x)) (dom_of r) 

testsImgAppl :: TestTree
testsImgAppl = testGroup "Image and function application on relations" [
      testProperty "∅ ⦇ A ⦈ = ∅" (propImg1::Set Int->Bool)
      , testProperty "r ⦇ ∅ ⦈  = ∅" (propImg2::Rel Int Int->Bool)
      , testProperty "r ⦇ A ⦈ = ran (A ◁ r)" (propImg3::Rel Int Int->Set Int->Bool)
      , testProperty "r ⦇ A ⦈  = dom (r~  ▷ A)" (propImg4::Rel Int Int->Set Int->Bool)
      , testProperty "∀ x : dom r . #r ⦇ {x} ⦈ = 1" (propImg5::Rel Int Int->Property)
      , testProperty "r ∊ A ⇸ B ==> ∀ (x, y) : r . r (x) = y" (propAppl1::Rel Int Int->Property)
      , testProperty "∀ x : dom r . r (x) ∊ r ⦇ {x} ⦈" (propAppl2::Rel Int Int->Bool)
      ]

propOverride1::(Eq a, Eq b)=>Rel a b->Rel a b->Bool
propOverride1 r s = all (\(x, y)->if x `elem` dom_of s then (x, y) `elem` s else (x, y) `elem` r) (r `override` s)

propOverride2::(Eq a, Eq b)=>Rel a b->Rel a b->Bool
propOverride2 r s = r `override` s == dsub r (dom_of s) `union` s

propOverride3::Eq a=>Rel a a->Bool
propOverride3 r = r `override` (id_on . dom_of $ r) == (id_on . dom_of $ r)

propOverride4::(Eq a, Eq b)=>Rel a b->Rel a b->Property
propOverride4 r s = null (dom_of r `intersec` dom_of s) ==> r `override` s == r `union` s
--r `override` (id_on . dom_of $ r) == (id_on . dom_of $ r)

testsOverride :: TestTree
testsOverride = testGroup "Image and function application on relations" [
      testProperty "∀ (x, y) : r ⊕ s . x ∊ dom s ==> (x, y) ∊ s ∨ ¬x ∊ dom s ==> (x, y) ∊ r" (propOverride1::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ⊕ s  = (dom s ⩤ r) ∪ s" (propOverride2::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ⊕ (id_on (dom r)) = id_on (dom r)" (propOverride3::Rel Int Int->Bool)
      , testProperty "dom_of r ∩ dom_of s = ∅ ==> r ⊕ s = r ∪ s" (propOverride4::Rel Int Int->Rel Int Int->Property)
      ]

testrComp1::Assertion
testrComp1 = assertEqual "Relation composition of empty relations" ((nil::Rel Int Char) `rcomp` (nil::Rel Char Int)) (nil::Rel Int Int)

proprComp1::(Eq a, Eq b)=>Rel a b->Bool
proprComp1 r = r `rcomp` (nil::Rel b Int) == nil

proprComp2::(Eq a, Eq b)=>Rel a b->Bool
proprComp2 r = (nil::Rel Int a) `rcomp` r == nil

proprComp3::(Eq a, Eq b)=>Rel a b->Bool
proprComp3 r = r `rcomp` (id_on . ran_of $ r) == r

proprComp4::(Eq a, Eq b)=>Rel a b->Bool
proprComp4 r = (id_on . dom_of $ r) `rcomp` r   == r

proprComp5::(Eq a, Eq b)=>Rel a b->Property
proprComp5 r = functional r && injective r ==> r `rcomp` (inv r) == (id_on . dom_of $ r)

proprComp6::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Property
proprComp6 r s= null(ran_of r `intersec` dom_of s) ==> r `rcomp` s == nil

proprComp7::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Bool
proprComp7 r s= all(\(x, y)->any(\z->(x, z) `elem`r && (z, y) `elem`s) (ran_of r) ) (r `rcomp` s)

mkFunction ::(Foldable t, Eq a, Eq b)=> t(a, b) -> Rel a b
mkFunction = foldr (\p t->if fst p `elem` dom_of t then t else p `intoSet` t) nil

proprComp8::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Bool
proprComp8 r s = 
      functional r' && functional s' && functional (r' `rcomp` s')
      where r' = mkFunction r
            s' = mkFunction s
            --mkFunction = foldr (\p t->if fst p `elem` dom_of t then t else p `intoSet` t) nil

proprComp9::Int->Property
proprComp9 k = k>1 ==> (pfun f a b) && (pfun g b c) && (pfun (f `rcomp` g) a c)
      where a = set [0..k-1]
            b = set [k..2*k-1]
            c = set [2*k..3*k-1]
            f = (a `sminus` singles (k-1) )`zipS` (b `sminus` singles (2*k-1))
            g = (b `sminus` singles (2*k-1)) `zipS` (c `sminus` singles (3*k-1))

testsrComp :: TestTree
testsrComp = testGroup "Relation composition" [
      testCase "∅ ⨾ ∅ = ∅" testrComp1
      , testProperty "∅ ⨾ r = ∅" (proprComp1::Rel Int Int->Bool)
      , testProperty "r ⨾ ∅ = ∅" (proprComp2::Rel Int Int->Bool)
      , testProperty "r ⨾ id_on (ran r) = r" (proprComp3::Rel Int Int->Bool)
      , testProperty "id_on (dom r) ⨾ r = r" (proprComp4::Rel Int Int->Bool)
      , testProperty "r ∊ A ⤔ B ==> r ⨾ r~ = r" (proprComp5::Rel Int Int->Property)
      , testProperty "ran r ∩ dom s = ∅ ==> r ⨾ s = ∅" (proprComp6::Rel Int Int->Rel Int Int->Property)
      , testProperty "∀ (x, y) ∊ r ⨾ s. ∃ z ∊ ran r. (x, z) ∊ r ∧ (z, y) ∊ s" (proprComp7::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ∊ A ⇸ B; s ∊ B ⇸ C ==> r ⨾ s ∊ A ⇸ C" (proprComp8::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ∊ A ⇸ B; s ∊ B ⇸ C ==> r ⨾ s ∊ A ⇸ C" (proprComp9::Int->Property)
      ]

testbComp1::Assertion
testbComp1 = assertEqual "Backwards relation composition of empty relations" ((nil::Rel Int Char) `bcomp` (nil::Rel Char Int)) (nil::Rel Char Char)

propbComp1::(Eq a, Eq b)=>Rel a b->Bool
propbComp1 r = r `bcomp` (nil::Rel Int a) == (nil::Rel a b)

propbComp2::(Eq a, Eq b)=>Rel a b->Bool
propbComp2 r = (nil::Rel b Int) `bcomp` r == nil

propbComp3::(Eq a, Eq b)=>Rel a b->Bool
propbComp3 r = (id_on . ran_of $ r) `bcomp` r  == r

propbComp4::(Eq a, Eq b)=>Rel a b->Bool
propbComp4 r =  r `bcomp` (id_on . dom_of $ r)   == r

propbComp5::(Eq a, Eq b)=>Rel a b->Property
propbComp5 r = functional r && injective r ==> (inv r) `bcomp` r  == (id_on . dom_of $ r)

propbComp6::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Property
propbComp6 r s= null(ran_of r `intersec` dom_of s) ==> s `bcomp` r  == nil

propbComp7::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Bool
propbComp7 r s= all(\(x, y)->any(\z->(x, z) `elem`r && (z, y) `elem`s) (ran_of r) ) (s `bcomp` r)

propbComp8::(Eq a, Eq b, Eq c)=>Rel a b->Rel b c->Bool
propbComp8 r s = functional r' && functional s' && functional (s' `bcomp` r')
      where r' = mkFunction r
            s' = mkFunction s

propbComp9::Int->Property
propbComp9 k = k>1 ==> (pfun f a b) && (pfun g b c) && (pfun (g `bcomp` f) a c)
      where a = set [0..k-1]
            b = set [k..2*k-1]
            c = set [2*k..3*k-1]
            f = (a `sminus` singles (k-1) )`zipS` (b `sminus` singles (2*k-1))
            g = (b `sminus` singles (2*k-1)) `zipS` (c `sminus` singles (3*k-1))

testsbComp :: TestTree
testsbComp = testGroup "Backwards relation composition" [
      testCase "∅ ∘ ∅ = ∅" testbComp1
      , testProperty "r ∘ ∅ = ∅" (propbComp1::Rel Int Int->Bool)
      , testProperty "∅ ∘ r = ∅" (propbComp2::Rel Int Int->Bool)
      , testProperty "id_on (ran r) ∘ r = r" (propbComp3::Rel Int Int->Bool)
      , testProperty "r ∘ id_on (dom r) = r" (propbComp4::Rel Int Int->Bool)
      , testProperty "r ∊ A ⤔ B ==> r~ ∘ r = r" (propbComp5::Rel Int Int->Property)
      , testProperty "ran r ∩ dom s = ∅ ==> s ∘ r = ∅" (propbComp6::Rel Int Int->Rel Int Int->Property)
      , testProperty "∀ (x, y) ∊ s ∘ r. ∃ z ∊ ran r. (x, z) ∊ r ∧ (z, y) ∊ s" (propbComp7::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ∊ A ⇸ B; s ∊ B ⇸ C ==> s ∘ r ∊ A ⇸ C" (propbComp8::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ∊ A ⇸ B; s ∊ B ⇸ C ==> s ∘ r ∊ A ⇸ C" propbComp9
      ]

testAntiReflexive1::Assertion
testAntiReflexive1 = assertBool "Anti-reflexive Empty relation" (antireflexive (nil::Rel Int Int))

testAntiReflexive2::Assertion
testAntiReflexive2 = assertBool "Anti-reflexive singleton: {(2,3)}" (antireflexive (singles (2,3)))

testAntiReflexive3::Assertion
testAntiReflexive3 = assertBool "Not Anti-reflexive singleton: {(2,2)}" (not $ antireflexive (singles (2,2)))

propAntiReflexive::Eq a=>Rel a a->Property
propAntiReflexive r = antireflexive r ==> null $ r `intersec` (id_on . dom_of $ r)

testReflexive1::Assertion
testReflexive1 = assertBool "Reflexive Empty relation" (reflexive (nil::Rel Int Int))

testReflexive2::Assertion
testReflexive2 = assertBool "Reflexive singleton: {(2,2)}" (reflexive (singles (2, 2)))

testReflexive3::Assertion
testReflexive3 = assertBool "Not reflexive singleton: {(2,3)}" (not $ reflexive (singles (2, 3)))

propReflexive::Eq a=>Set a->Bool
propReflexive s = reflexive (id_on s)

propBijection::Int->Property
propBijection k = k > 1 ==> fun_bij (zipS a b) a b
                   where a = set [0..k]
                         b = set $ reverse [0..k]

propPInjection::Int->Property
propPInjection k = k > 1 ==> fun_pinj (zipS a' b') a b
                   where a = set [0..k]
                         a' = a `sminus` singles k
                         b = set $ reverse [0..k]
                         b' = b `sminus` singles 0

testSymmetric1::Assertion
testSymmetric1 = assertBool "Symmetric Empty relation" (symmetric (nil::Rel Int Int))

testSymmetric2::Assertion
testSymmetric2 = assertBool "Symmetric: {(2,3), (3,2)}" (symmetric (set [(2, 3), (3,2)]))

propSymmetric::Int->Property
propSymmetric k = k > 1 ==> symmetric (r `union` (inv r))
                where a = set [0..k]
                      b = set $ reverse [0..k]
                      r = zipS a b

testsPRels :: TestTree
testsPRels = testGroup "Properties of relations" [
      testCase "antireflexive ∅" testAntiReflexive1
      , testCase "antireflexive {(2, 3)}" testAntiReflexive2
      , testCase "¬ antireflexive {(2, 2)}" testAntiReflexive3
      , testProperty "r ∩ id_on (dom r) = ∅ ==> antireflexive r" (propAntiReflexive::Rel Int Int->Property)
      , testCase "reflexive ∅" testReflexive1
      , testCase "reflexive {(2, 2)}" testReflexive2
      , testCase "¬ reflexive {(2, 3)}" testReflexive3
      , testProperty "A bijection construction" propBijection
      , testProperty "A partial injection construction" propPInjection
      , testCase "symmetric ∅" testSymmetric1
      , testCase "symmetric: {(2,3), (3,2)}" testSymmetric2
      , testProperty "A symmetric construction" propSymmetric
      ]

testTranclEmptyR::Assertion
testTranclEmptyR = assertEqual "Transitive closure of empty relation" (trancl (nil::Rel Int Int)) (nil::Rel Int Int)

testTranclSingleton::Assertion
testTranclSingleton = assertEqual "Transitive closure of singleton {(2, 3)}" (trancl (singles (2, 3))) (singles (2, 3))

testTranclSet1::Assertion
testTranclSet1 = assertEqual "Transitive closure of set {(2, 3), (5, 10)}" (trancl (set [(2, 3), (5, 10)])) (set [(2, 3), (5, 10)])

testTranclSet2::Assertion
testTranclSet2 = assertEqual "Transitive closure of set {(2, 3), (3, 4)}" (trancl (set [(2, 3), (3, 4)])) (set [(2, 3), (3, 4), (2, 4)])

propTrancl1::Eq a=>Set a->Bool
propTrancl1 xs = trancl (id_on xs) == id_on xs

propTrancl2::Eq a=>Rel a a->Bool
propTrancl2 r = r <= trancl r

propTrancl3::Eq a=>Rel a a->Property
propTrancl3 r = null (dom_of r `intersec` ran_of r)  ==> r == trancl r 

propTrancl4::Eq a=>Rel a a->Bool
propTrancl4 r = all (\(x, y)->(x, y) `elem` r || any (\z->(x, z) `elem` r && (z, y) `elem` tc) (dom_of r)) tc  
            where tc = trancl r

propTrancl5::Eq a=>Rel a a->Rel a a->Bool
propTrancl5 r s = 
      --disjoint [dom_of r `union` ran_of r, dom_of s `union` ran_of s] ==> 
      trancl (r `union` s') == trancl r `union`  trancl s'
      where s' = rsub (dsub s rs) rs
            rs = dom_of r `union` ran_of r

propTrancl6::Eq a=>Rel a a->Property
propTrancl6 r = length r < 9 ==> transitive . trancl $ r 

propTrancl7::Eq a=>Rel a a->Property
propTrancl7 r = length r < 9 ==> (symmetric . trancl) $ r `union` (inv r)

testsTrancl :: TestTree
testsTrancl = testGroup "Properties of transitive closure" [
      testCase "(∅)+= ∅" testTranclEmptyR
      , testCase "{(2, 3)}+ = {(2,3)}" testTranclSingleton
      , testCase "{(2, 3), (5, 10)}+ = {(2, 3), (5, 10)}" testTranclSet1
      , testCase "{(2, 3), (3, 4)}+ = {(2, 3), (3, 4), (2, 4)}" testTranclSet2
      , testProperty "(id_on A)+ = id_on A" (propTrancl1::Rel Int Int->Bool)
      , testProperty "r ⊆ r+" (propTrancl2::Rel Int Int->Bool)
      , testProperty "dom r ∩ ran r = ∅ ==> r = r+" (propTrancl3::Rel Int Int->Property)
      , testProperty "∀ (x, y) ∊ r+. ∃ z ∊ dom r. (x, z) ∊ r ∧ (z, y) ∊ r+" (propTrancl4::Rel Int Int->Bool)
      , testProperty "(dom r ∪ ran r) ∩ (dom s ∪ ran s) = ∅ ==> (r ∪ s)+ = r+ ∪ s+" (propTrancl5::Rel Int Int->Rel Int Int->Bool)
      , testProperty "transitive(r+)" (propTrancl6::Rel Int Int->Property)
      , testProperty "symmetric ((r ∪ r~)+)" (propTrancl7::Rel Int Int->Property)
      ]

testRTrancl1::Assertion
testRTrancl1 = assertEqual "Reflexive transitive closure of empty relation" (rtrancl_on (nil::Rel Int Int) (set [0..5])) (id_on . set $ [0..5] )

testRTrancl2::Assertion
testRTrancl2 = assertEqual "Reflexive transitive closure of singleton {(2, 3)}" (rtrancl (singles (2, 3))) (set [(2, 3), (2,2), (3,3)])

propRtrancl1::Eq a=>Rel a a->Bool
propRtrancl1 r = reflexive . rtrancl $ r

propRtrancl2::Eq a=>Rel a a->Bool
propRtrancl2 r = r `union` (id_on $ dom_of r `union` ran_of r) <= rtrancl r

propRtrancl3::Eq a=>Rel a a->Bool
propRtrancl3 r = rtrancl r `sminus` (id_on $ dom_of r `union` ran_of r) <= trancl r

propRtrancl4::Eq a=>Rel a a->Rel a a->Bool
propRtrancl4 r s = rtrancl (r `union` s') == rtrancl r `union` rtrancl s'
      where s' = rsub (dsub s rs) rs
            rs = dom_of r `union` ran_of r
      --disjoint [dom_of r `union` ran_of r, dom_of s `union` ran_of s] ==> rtrancl (r `union` s) == rtrancl r `union`  rtrancl s

propRtrancl5::Eq a=>Rel a a->Property
propRtrancl5 r = (not . null $ r) ==> not . acyclic . rtrancl $ r

propRtrancl6::Eq a=>Rel a a->Property
propRtrancl6 r = length r < 9 ==> transitive . rtrancl $ r

propRtrancl7::Eq a=>Rel a a->Property
propRtrancl7 r = length r < 9 ==> (symmetric . trancl) $ r `union` inv r

propRtrancl8::Eq a=>Set a->Bool
propRtrancl8 s = rtrancl_on (nil::Rel a a) s == id_on s

testsRTrancl :: TestTree
testsRTrancl = testGroup "Properties of reflexive transitive closure" [
      testCase "(∅)*= ∅" testRTrancl1
      , testCase "{(2, 3)}*" testRTrancl2
      , testProperty "reflexive (r*)" (propRtrancl1::Rel Int Int->Bool)
      , testProperty "r ∪ (id_on (dom r ∪ ran r)) ⊆ r* " (propRtrancl2::Rel Int Int->Bool)
      , testProperty "r* ∖ (id_on (dom r ∪ ran r)) ⊆ r+ " (propRtrancl3::Rel Int Int->Bool)
      , testProperty "(dom r ∪ ran r) ∩ (dom s ∪ ran s) = ∅ ==> (r ∪ s)* = r* ∪ s*" (propRtrancl4::Rel Int Int->Rel Int Int->Bool)
      , testProperty "r ≠ ∅ ==> ¬acyclic (r*)" (propRtrancl5::Rel Int Int->Property)
      , testProperty "transitive (r*)" (propRtrancl6::Rel Int Int->Property)
      , testProperty "transitive (r*)" (propRtrancl7::Rel Int Int->Property)
      , testProperty "(∅)*= ∅" (propRtrancl8::Rel Int Int->Bool)
      ]

testAcyclic1::Assertion
testAcyclic1 = assertBool "Acyclic empty relation" (acyclic (nil::Rel Int Int))

testAcyclic2::Assertion
testAcyclic2 = assertBool "Acyclic {(2,3)}" (acyclic . singles $ (2, 3))

propAcyclic1::Eq a=>Rel a a->Property
propAcyclic1 r = acyclic r ==> antireflexive r

propAcyclic2::Eq a=>Rel a a->Property
propAcyclic2 r = null (trancl r `intersec` id_on (dom_of r `union` ran_of r)) ==> acyclic r

testsAcyclic :: TestTree
testsAcyclic = testGroup "Properties of acyclic" [
      testCase "acyclic {}" testAcyclic1
      , testCase "acyclic  {(2,3)}" testAcyclic2
      , testProperty "acyclic r ==> antireflexive r" (propAcyclic1::Rel Int Int->Property)
      , testProperty "r+ ∩ id_on (dom r ∪ ran r)  ==> acyclic r" (propAcyclic2::Rel Int Int->Property)
      ]

testEqRel::Assertion
testEqRel = assertBool "Acyclic empty relation" (reflexive er && symmetric er && transitive er)
            where er = eq_rel (nil::Rel Int Int)

propEqRel::Eq a=>Rel a a->Property
propEqRel r = length r < 9 ==> reflexive er && symmetric er && transitive er
             where er = eq_rel r

testsEqRel :: TestTree
testsEqRel = testGroup "Properties of equivalence relations" [
      testCase "eq_rel {} is reflexive, symmetric and transitive" testEqRel
      , testProperty "eq_rel r is reflexive, symmetric and transitive" (propEqRel::Rel Int Int->Property)
      ]

testCross1::Assertion
testCross1 = assertEqual "Cross product of empty sets" (cross (nil::Set Int) (nil::Set Int)) nil 

propCross1::Set Int->Property
propCross1 a = length a < 9 ==> (cross a (nil::Set Int)) == nil 

propCross2::Set Int->Property
propCross2 a = length a < 9 ==> (cross (nil::Set Int) a) == nil 

propCross3::Set Int->Property
propCross3 a = length a < 9 ==> zipS a a <= cross a a

testsCross :: TestTree
testsCross = testGroup "Properties of cross product" [
      testCase "{}x{}={}" testCross1
      , testProperty "Ax{}={}" propCross1
      , testProperty "{}xA={}" propCross2
      , testProperty "zip A A = A x A" propCross3
      ]


tests :: TestTree
tests =  testGroup "Overall tests" [
    testsDomOf
    , testsRanOf
    , testsIdOf
    , testsInv
    , testsDRes
    , testsRRes
    , testsDSub
    , testsRSub
    , testsImgAppl
    , testsOverride
    , testsrComp
    , testsbComp
    , testsPRels
    , testsTrancl
    , testsRTrancl
    , testsAcyclic
    , testsEqRel
    , testsCross
    ]

main :: IO ()
main = do
    defaultMain tests

--qcTests :: Testable prop => [prop]
--qcTests = [propDomOf1, propDomOf2]

--return []
--runTests :: IO Bool
--runTests = $quickCheckAll

--runQuickCheckOn p = quickCheck p

--main = $forAllProperties (quickCheckWithResult stdArgs { maxSuccess = 500 })
--main :: IO ()
--main = do
--   quickCheck propDomOf1
--   quickCheck propDomOf2
--   quickCheck propRanOf1
--   quickCheck propRanOf2
--   quickCheck propInv1
--   quickCheck propInv2
--   quickCheck propInv3
--   quickCheck propId1
--   quickCheck propId2
--   quickCheck propInvId
--   quickCheck propDomOfInv
--   quickCheck propRanOfInv
--   quickCheck propDomOfInvRanOf
--   quickCheck propRanOfInvDomOf
--   quickCheck propDres1
--   quickCheck propDres2
--   quickCheck propDres3
--   quickCheck propDres4
--   quickCheck propRres1
--   quickCheck propRres2
--   quickCheck propRres3
--   quickCheck propRres4
--   quickCheck propDresRres
--   quickCheck propDsub1
--   quickCheck propDsub2
--   quickCheck propDsub3
--   quickCheck propDsub4
--   quickCheck propDsub5
--   quickCheck propRsub1
--   quickCheck propRsub2
--   quickCheck propRsub3
--   quickCheck propRsub4
--   quickCheck propRsub5
--   quickCheck propImg1
--   quickCheck propImg2
--   quickCheck propImg3
--   quickCheck propImg4
--   quickCheck propImg5
--   quickCheck propImg6
--   quickCheck propAppl1
--   quickCheck propAppl2
--   quickCheck propOverride1
--   quickCheck propOverride2
--   quickCheck propOverride3
--   quickCheck proprComp1
--   quickCheck proprComp2
--   quickCheck proprComp3
--   quickCheck proprComp4
--   quickCheck proprComp5
--   quickCheck proprComp6
--   quickCheck propbComp1
--   quickCheck propbComp2
--   quickCheck propbComp3
--   quickCheck propbComp4
--   quickCheck propbComp5
--   quickCheck propbComp6
--   quickCheck propAntiReflexive
--   quickCheck propReflexive
--   quickCheck propBijection
--   quickCheck propPInjection
--   quickCheck propSymmetric
--   quickCheck propTrancl1
--   quickCheck propTrancl2
--   quickCheck propTrancl3
--   quickCheck propTrancl4
--   quickCheck propTrancl5
--   quickCheck propTrancl6
--   quickCheck propTrancl7
--   quickCheck propRtrancl1
--   quickCheck propRtrancl2
--   quickCheck propRtrancl3
--   quickCheck propRtrancl4
--   quickCheck propRtrancl5
--   quickCheck propRtrancl6
--   quickCheck propRtrancl7
--   quickCheck propRtranclOn
--   quickCheck propAcyclic
--   quickCheck propEqRel
--   quickCheck propCross1
--   quickCheck propCross2
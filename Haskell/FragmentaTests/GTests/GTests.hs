
import Gr_Cls
import Grs
import LoadCheckDraw ( loadG, loadM )
import FragmentaTests.GTests.GTestsCommon
import System.Exit ( exitFailure, exitSuccess )
import Sets ( set, singles )
import Relations ( dom_of, ran_of )
import TheNil
import Test.Tasty
import Test.Tasty.HUnit

testG1:: Assertion
testG1 = assertBool "Okay G1" (not $ okayG Nothing eg1)

testG2:: Assertion
testG2 = assertBool "Okay G2" (not $ okayG Nothing eg2)

testG3:: Assertion
testG3 = assertBool "Okay G3" (okayG Nothing eg3)

testG4:: Assertion
testG4 = assertBool "Okay G4" (okayG Nothing eg4)

testG5 :: IO()
testG5 = do
   (nm1, g1) <-loadG def_path "G_chain_4.g"
   assertBool ("WF " ++ nm1) (okayG Nothing g1)

testsWF :: TestTree
testsWF = testGroup "Well-formedness tests" [
   testCase "Okay G1" testG1
   , testCase "Okay G2" testG2
   , testCase "Okay G3" testG3
   , testCase "Okay G4" testG4
   , testCase "Okay G5: 'G_chain_4.g'" testG4
   ]

testG3Src:: Assertion
testG3Src = assertBool "G3's src function" (dom_of (src eg3) == es eg3 && ran_of (src eg3) <= ns eg3)

testG3Tgt:: Assertion
testG3Tgt = assertBool "G3's tgt function" (dom_of (tgt eg3) == es eg3 && ran_of (tgt eg3) <= ns eg3)

testG3Adjacent:: Assertion
testG3Adjacent = assertBool "G3's adjency" (adjacent eg3 "V1" "V2")

testG3AdjacentE:: Assertion
testG3AdjacentE = assertBool "G3's edge adjency" (adjacentE eg3 "EV1V2" "EV2V3")

testG3RelOf:: Assertion
testG3RelOf = assertBool "G3's node relation" (relOfG eg3 == set [("V1", "V2"), ("V2", "V3"), ("V3", "V4")])

testG3RelOfE:: Assertion
testG3RelOfE = assertBool "G3's edge relation" (relOfGE eg3 == set [("EV1V2", "EV2V3"), ("EV2V3", "EV3V4")])

testG4RelOf:: Assertion
testG4RelOf = assertBool "G4's node relation" (relOfG eg4 == set [("V1", "V1")])

testG4RelOfE:: Assertion
testG4RelOfE = assertBool "G4's edge relation" (relOfGE eg4 == set [("EV1V1", "EV1V1")])

testG3Ayclic:: Assertion
testG3Ayclic = assertBool "G3 Acyclic" (acyclicG eg3)

testG4NotAyclic:: Assertion
testG4NotAyclic = assertBool "G4 not acyclic" (not . acyclicG $ eg4)

testsWFGs :: TestTree
testsWFGs = testGroup "Properties of Well-formed graphs" [
   testCase "Domain and range of G3's src function" testG3Src
   , testCase "Domain and range of G3's tgt function" testG3Tgt
   , testCase "Node V1 adjacent to V2 in G3" testG3Adjacent
   , testCase "Edge 'EV1V2' adjacent to 'EV2V3' in G3" testG3Adjacent
   , testCase "Relation between nodes derived from G3" testG3RelOf
   , testCase "Relation betwen edges derived from G3" testG3RelOfE
   , testCase "Relation betwen nodes derived from G4" testG4RelOf
   , testCase "Relation betwen edges derived from G4" testG4RelOfE
   , testCase "G3 Acyclic" testG3Ayclic
   , testCase "G4 has a loop" testG4NotAyclic
   ]

testWFG1 :: IO()
testWFG1 = do
   (nm1, g1) <-loadG def_path "G_chain_4.g"
   assertBool ("WF " ++ nm1) (okayG Nothing g1)
   assertBool ("Incident edges of " ++ nm1 ++ " for '{V3}'") (esIncident g1 ["V3"] == set ["EV3_V4","EV2_V3"])
   assertBool ("Incident edges of " ++ nm1 ++ " for '{V2}'") (esIncident g1 ["V2"] == set ["EV1_V2","EV2_V3"])
   assertBool ("Connection edges of " ++ nm1 ++ " for '{V3}'") (esConnect g1 ["V3"] == nil)
   assertBool ("Connection edges of " ++ nm1 ++ " for '{V2}'") (esConnect g1 ["V2"] == nil)
   assertBool ("Connection edges of " ++ nm1 ++ " for '{V2, V3}'") (esConnect g1  ["V2", "V3"] == (singles "EV2_V3"))
   let sG = consG (set ["V1", "V2", "V4"]) (singles "EV1_V2") (singles ("EV1_V2","V1")) (singles ("EV1_V2","V2"))
   assertBool ("Node subtraction of " ++ nm1 ++ " for '{V3}'") (subtractNs g1 (singles "V3") == sG)
   assertBool ("WF subtracted " ++ nm1) (okayG Nothing sG)

testWFG2 :: IO()
testWFG2 = do
   (nm1, g1) <-loadG def_path "G_A_B.g"
   (nm2, g2) <-loadG def_path "G_C_D.g" 
   let g3 = g1 `unionG` g2
   assertBool ("WF " ++ nm1) (okayG Nothing g1)
   assertBool ("WF " ++ nm2) (okayG Nothing g2)
   assertBool ("WF Union of " ++ nm1 ++ " and " ++ nm2) (okayG Nothing g3)
   assertBool ("Relation of union graph") (relOfG g3 == set [("C","D"), ("A","B")])
   assertBool ("Incident edges of union graph for {'A'}") (esIncident g3 ["A"] == singles "EA_B")
   let g4 = subsumeG g3 (singles ("C", "A"))
   assertBool ("WF Subsumption of union graph") (okayG Nothing g4)
   assertBool ("Relation of subsummption graph") (relOfG g4 == set [("A","D"),("A","B")])
   assertBool ("Relation of inverted subsummption graph") ((relOfG . invertG $ g4) == set [("D","A"),("B","A")])

testMorphisms :: IO()
testMorphisms = do
   (nm1, g1) <-loadG def_path "G_A_B.g"
   (nm2, g2) <-loadG def_path "G_C_D.g"
   (nm_m1, m1)<-loadM def_path "m_A_B_C_D_1.gm"
   (nm_m2, m2)<-loadM def_path "m_A_B_C_D_2.gm"
   (nm_m3, m3)<-loadM def_path "m_A_B_C_D_3.gm"
   (nm_m4, m4)<-loadM def_path "m_A_B_C_D_4.gm"
   (nm_m5, m5)<-loadM def_path "m_A_B_C_D_5.gm"
   let g3 = g1 `unionG` g2
   assertBool ("Erroneous G1->G2" ++ nm_m1) (not $ okayGM Nothing (g1, m1, g2))
   assertBool ("Ok G1->G2:" ++ nm_m2) (okayGM Nothing (g1, m2, g2))
   assertBool ("Erroneous G1->G2:" ++ nm_m3) (not $ okayGM Nothing (g1, m3, g2))
   let g4 = subsumeG g3 (singles ("C", "A"))
   assertBool ("⊙ G_A_B_C_D -> ⊙ G_A_B_C_D (identity)") (okayGM Nothing (g4, gid g4, g4))
   assertBool ("G_A_B_C_D -> ⊙ G_A_B_C_D (identity morphism)") (okayGM Nothing (g4, gid g4, g4))
   assertBool ("G_A_B_C_D -> ⊙ G_A_B_C_D (" ++ nm_m4 ++ ")") (okayGM Nothing (g3, m4, g4)) 
   assertBool ("⊙ G_A_B_C_D -> G_A_B (" ++ nm_m5 ++ ")") (okayGM Nothing (g4, m5, g1)) 
   assertBool ("⊙ G_A_B_C -> G_A_B (composition with identity)") (okayGM Nothing (g4, gid g1 `ogm` m5, g1))
   assertBool ("⊙ G_A_B_C -> G_A_B_C (composition via g1)") (okayGM Nothing (g4, m2 `ogm` m5, g3))

testsBigWFGs :: TestTree
testsBigWFGs = testGroup "Big tests involving well-formed graphs and morphisms" [
   testCase "Tests for 'G_chain_4.g'" testWFG1
   , testCase "Tests for 'G_A_B.g' and 'G_C_D.g'" testWFG2
   , testCase "Tests for 'G_A_B.g' and 'G_C_D.g' and morphisms" testMorphisms
   ]





--testsIO :: TestTree
--testsIO = TestGroup $ fmap TestCase [testWFG1, testWFG2, testMorphisms]

--main:: IO()
--main = do
--   counts <- runTestTT (tests)
--   if (errors counts + failures counts == 0)
--      then exitSuccess
--      else exitFailure

tests :: TestTree
tests =  testGroup "Overall tests" [
   testsWF
   , testsWFGs
   , testsBigWFGs
   ]

main :: IO ()
main = do
    defaultMain tests
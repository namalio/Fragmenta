
import Grs
import Sets ( singles )
import LoadCheckDraw
import MyMaybe 
import CheckUtils
import Utils
import FragmentaTests.GTests.GrsTestsCommon

saveDrawings :: IO ()
saveDrawings = do
    (nm1, g1) <-loadG def_path "G_A_B.g"
    (nm2, g2) <-loadG def_path "G_C_D.g"
    (nm3, g3) <-loadG def_path "G_chain_4.g"
    draw_to_file img_path nm1 (wrapG g1)
    draw_to_file img_path nm2 (wrapG g2)
    draw_to_file img_path nm3 (wrapG g3)
    let g4 = g1 `unionG` g2
    draw_to_file img_path "G_A_B_C_D" (wrapG g4)
    let g5 = subsumeG g3 (singles ("C", "A"))
    draw_to_file img_path "G_A_B_C_1" (wrapG g5)
    let g6 = invertG g5
    draw_to_file img_path "G_A_B_C_2" (wrapG g6)


--confirms that 'g_1' and 'g_2' are malformed
test_gerrs :: IO ()
test_gerrs = do
    check_report_wf "G1" Nothing eg1 False
    check_report_wf "G2" Nothing eg2 False

do_test_1 :: IO ()
do_test_1 = do
    (nm1, g1) <-loadG def_path "G_chain_4.g"
    check_report_wf nm1 Nothing g1 True
    putStrLn $ "Incident edges of 'V3': " ++ (show $ esIncident g1 ["V3"])
    putStrLn $ "Incident edges of 'V2': " ++ (show $ esIncident g1 ["V2"])
    putStrLn $ "Connection edges of 'V3': " ++ (show $ esConnect g1 ["V3"])
    putStrLn $ "Connection edges of 'V2': " ++ (show $ esConnect g1 ["V2"])
    putStrLn $ "Connection edges of '{V2, V3}': " ++ (show $ esConnect g1 ["V2", "V3"])
    putStrLn $ "Subtracting 'V3': " ++  (show $ subtractNs g1 (singles "V3"))

-- Examples of the PCs paper
--confirms that 'G_A_B_C' is well-formed and does stuff with these graphs
test_G_A_B_C_D :: IO ()
test_G_A_B_C_D = do
    (nm1, g1) <-loadG def_path "G_A_B.g"
    (nm2, g2) <-loadG def_path "G_C_D.g" 
    (nm_m1, m1)<-loadM def_path "m_A_B_C_D_1.gm"
    (nm_m2, m2)<-loadM def_path "m_A_B_C_D_2.gm"
    (nm_m3, m3)<-loadM def_path "m_A_B_C_D_3.gm"
    (nm_m4, m4)<-loadM def_path "m_A_B_C_D_4.gm"
    (nm_m5, m5)<-loadM def_path "m_A_B_C_D_5.gm"
    check_report_wf nm1 Nothing g1 True
    check_report_wf nm2 Nothing g2 True
    let g3 = g1 `unionG` g2
    check_report_wf "G_A_B_C_1" Nothing g3 True
    -- shows relation derived from the graph
    putStrLn $ "Relation: " ++ (show $ relOfG g3)
    -- All incident edges of node 'A'
    putStrLn $ "Relation: " ++ (show $ esIncident g3 ["A"])
    -- Does the subsumption with PA replaced by A
    let g4 = subsumeG g3 (singles ("C", "A"))
    putStrLn $ "Relation of submsumption: " ++ (show $ relOfG g4)
    putStrLn $ "Relation of the inverse of submsumption: " ++ (show $ relOfG . invertG $ g4)
    check_report_wf "⊙ G_A_B_C" Nothing g4 True
    -- A few tests with morphisms
    check_morphism ("Erroneous G1->G2" ++ nm_m1) Nothing g1 m1 g2 False
    check_morphism ("Ok G1->G2" ++ nm_m2) Nothing g1 m2 g2 True
    check_morphism ("Erroneous G1->G2" ++ nm_m3) Nothing g1 m3 g2 False
    check_morphism "⊙ G_A_B_C_D -> ⊙ G_A_B_C_D (identity)" Nothing g4 (gid g4) g4 True -- identity morphism
    check_morphism ("G_A_B_C_D -> ⊙ G_A_B_C_D (" ++ nm_m4 ++ ")") Nothing g3 m4 g4 True
    check_morphism ("⊙ G_A_B_C_D -> G_A_B (" ++ nm_m5 ++ ")") Nothing g4 m5 g1 True
    check_morphism "⊙ G_A_B_C -> G_A_B (composition with identity)" Nothing g4 (gid g1 `ogm` m5)  g1 True
    check_morphism "⊙ G_A_B_C -> G_A_B_C (composition via g1)" Nothing g4 (m2 `ogm` m5)  g3 True

do_main = do
    test_gerrs
    test_G_A_B_C_D

main :: IO ()
main = do
   option_main_save do_main saveDrawings



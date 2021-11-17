------------------
-- Project: PCs/Fragmenta
-- Module: 'SG_ref_tests2'
-- Description: Tests which focus on SGs refinement
-- Author: Nuno Amálio
-----------------
{-# LANGUAGE UnicodeSyntax #-}

import SGrs
import Grs
import Utils
import CheckUtils
import LoadCheckDraw

-- amm_1 = 
--    let ns' = ["Def", "Elem", "Attr", "Connector", "Node"] in
--    let es' = ["IConnector", "IConnectorSelf", "INode", "INodeSelf", "ESrc", "ETgt", "EHasAttrs", "EContainsElems"] in
--    let s = [("IConnector", "Connector"), ("IConnectorSelf", "Connector"), ("INode", "Node"), ("INodeSelf", "Node"), ("ESrc", "Connector"), 
--            ("ETgt", "Connector"), ("EHasAttrs", "Elem"), ("EContainsElems", "Def")] in
--    let t = [("IConnector", "Elem"), ("IConnectorSelf", "Connector"), ("INode", "Elem"), ("INodeSelf", "Node"), ("ESrc", "Node"), 
--            ("ETgt", "Node"), ("EHasAttrs", "Attr"), ("EContainsElems", "Elem")] in
--    let nt = [("Def", Nnrml), ("Elem", Nabst), ("Attr", Nnrml), ("Connector", Nnrml), ("Node", Nnrml)] in
--    let et = [("IConnector", Einh), ("IConnectorSelf", Einh), ("INode", Einh), ("INodeSelf", Einh), ("ESrc", Erel Bi), 
--             ("ETgt", Erel Bi), ("EHasAttrs", Erel Bi), ("EContainsElems", Ecomp Bi)] in
--    let sm = [("EHasAttrs", Sm Many), ("EContainsElems", Sm $ Val 1), ("ESrc", Sm Many), ("ETgt", Sm Many)] in
--    let tm = [("EHasAttrs", Sm Many), ("EContainsElems", Sm Many), ("ESrc", Sm $ Val 1), ("ETgt", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_1 = 
--    let ns' = ["Def", "Name", "Connector", "Node", "NA1", "NA2", "NB1", "NB2", "CA", "CB"] in
--    let es' = ["ICA", "ICB", "INA1", "INA2", "INB1", "INB2", "EContainsCs", "EContainsNs", "EHasName", "ECASrc", 
--             "ECATgt", "ECBSrc", "ECBTgt"] in
--    let s = [("ICA", "CA"), ("ICB", "CB"), ("INA1", "NA1"), ("INA2", "NA2"), ("INB1", "NB1"), ("INB2", "NB2"), 
--            ("EHasName", "Node"), ("EContainsCs", "Def"), ("EContainsNs", "Def"), ("ECASrc", "CA"), ("ECATgt", "CA"), 
--            ("ECBSrc", "CB"), ("ECBTgt", "CB")] in
--    let t = [("ICA", "Connector"), ("ICB", "Connector"), ("INA1", "Node"), ("INA2", "Node"), ("INB1", "Node"), ("INB2", "Node"), 
--             ("EHasName", "Name"), ("EContainsCs", "Connector"), ("EContainsNs", "Node"), ("ECASrc", "NA1"), ("ECATgt", "NA2"),
--             ("ECBSrc", "NB1"), ("ECBTgt", "NB2")] in
--    let nt = [("Def", Nnrml), ("Name", Nnrml), ("Connector", Nabst), ("Node", Nabst), ("NA1", Nnrml), ("NA2", Nnrml), ("NB1", Nnrml), 
--             ("NB2", Nnrml), ("CA", Nnrml), ("CB", Nnrml)] in
--    let et = [("ICA", Einh), ("ICB", Einh),  ("INA1", Einh), ("INA2", Einh), ("INB1", Einh), ("INB2", Einh),
--             ("EContainsCs", Ecomp Bi), ("EContainsNs", Ecomp Bi), ("EHasName", Erel Bi), ("ECASrc", Erel Bi), ("ECATgt", Erel Bi),
--             ("ECBSrc", Erel Bi), ("ECBTgt", Erel Bi)] in
--    let sm = [("EContainsCs", Sm $ Val 1), ("EContainsNs", Sm $ Val 1), ("EHasName", Rm 0 $ Val 1),  ("ECASrc", Sm Many), ("ECATgt", Sm Many),
--             ("ECBSrc", Sm Many), ("ECBTgt", Sm Many)] in
--    let tm = [("EContainsCs", Sm Many), ("EContainsNs", Sm Many), ("EHasName", Sm $ Val 1), ("ECASrc", Sm $ Val 1), ("ECATgt", Sm $ Val 1), 
--             ("ECBSrc", Sm $ Val 1), ("ECBTgt", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_1 = 
--    let mv = [("Def", "Def"), ("Name", "Attr"), ("Connector", "Connector"), ("Node", "Node"), 
--             ("NA1", "Node"), ("NA2", "Node"), ("NB1", "Node"), ("NB2", "Node"), ("CA", "Connector"), ("CB", "Connector")] in
--    let me = [("ICA", "IConnectorSelf"), ("ICB", "IConnectorSelf"), ("INA1", "INodeSelf"), ("INA2", "INodeSelf"), ("INB1", "INodeSelf"),
--             ("INB2", "INodeSelf"), ("EContainsCs", "EContainsElems"), ("EContainsNs", "EContainsElems"), ("EHasName", "EHasAttrs"),
--             ("ECASrc", "ESrc"), ("ECATgt", "ETgt"), ("ECBSrc", "ESrc"), ("ECBTgt", "ETgt")] in
--    cons_gm mv me

-- mm_2 = 
--    let ns' = ["Def", "Name", "Elem", "Connector", "Node", "NA1", "NA2", "NB1", "NB2", "CA", "CB"] in
--    let es' = ["IConnector", "INode", "ICA", "ICB", "INA1", "INA2", "INB1", "INB2", "EContains", "EHasName", "ECASrc", "ECATgt", 
--              "ECBSrc", "ECBTgt"] in
--    let s = [("IConnector", "Connector"), ("INode", "Node"), ("ICA", "CA"), ("ICB", "CB"), ("INA1", "NA1"), ("INA2", "NA2"), ("INB1", "NB1"), 
--            ("INB2", "NB2"), ("EHasName", "Node"), ("EContains", "Def"), ("ECASrc", "CA"), ("ECATgt", "CA"), 
--            ("ECBSrc", "CB"), ("ECBTgt", "CB")] in
--    let t = [("IConnector", "Elem"), ("INode", "Elem"), ("ICA", "Connector"), ("ICB", "Connector"), ("INA1", "Node"), ("INA2", "Node"), 
--          ("INB1", "Node"), ("INB2", "Node"), ("EHasName", "Name"), ("EContains", "Elem"), ("ECASrc", "NA1"), ("ECATgt", "NA2"),
--          ("ECBSrc", "NB1"), ("ECBTgt", "NB2")] in
--    let nt =  [("Def", Nnrml), ("Name", Nnrml), ("Elem", Nabst), ("Connector", Nabst), ("Node", Nabst), ("NA1", Nnrml), ("NA2", Nnrml), ("NB1", Nnrml), 
--              ("NB2", Nnrml), ("CA", Nnrml), ("CB", Nnrml)] in
--    let et =  [("IConnector", Einh), ("INode", Einh), ("ICA", Einh), ("ICB", Einh),  ("INA1", Einh), ("INA2", Einh), ("INB1", Einh), ("INB2", Einh),
--              ("EContains", Ecomp Bi), ("EHasName", Erel Bi), ("ECASrc", Erel Bi), ("ECATgt", Erel Bi), ("ECBSrc", Erel Bi), ("ECBTgt", Erel Bi)] in
--    let sm = [("EContains", Sm $ Val 1), ("EHasName", Rm 0 $ Val 1), ("ECASrc", Sm Many), ("ECATgt", Sm Many), ("ECBSrc", Sm Many), ("ECBTgt", Sm Many)] in
--    let tm = [("EContains", Sm Many), ("EHasName", Sm $ Val 1), ("ECASrc", Sm $ Val 1), ("ECATgt", Sm $ Val 1), ("ECBSrc", Sm $ Val 1), ("ECBTgt", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_2 = 
--    let mv = [("Def", "Def"), ("Name", "Attr"), ("Elem", "Elem"), ("Connector", "Connector"), ("Node", "Node"), 
--             ("NA1", "Node"), ("NA2", "Node"), ("NB1", "Node"), ("NB2", "Node"), ("CA", "Connector"), ("CB", "Connector")] in
--    let me = [("IConnector", "IConnector"), ("ICA", "IConnectorSelf"), ("ICB", "IConnectorSelf"), ("INode", "INode"), ("INA1", "INodeSelf"), 
--             ("INA2", "INodeSelf"), ("INB1", "INodeSelf"), ("INB2", "INodeSelf"), ("EContains", "EContainsElems"), ("EHasName", "EHasAttrs"),
--             ("ECASrc", "ESrc"), ("ECATgt", "ETgt"), ("ECBSrc", "ESrc"), ("ECBTgt", "ETgt")] in
--   cons_gm mv me

-- mm_3 = 
--    let ns' = ["Def", "Name", "Connector", "Node", "NA1", "NA2", "NB1", "NB2", "CA", "CB", "CC", "NC1", "NC2"] in
--    let es' = ["ICA", "ICB", "ICC", "INA1", "INA1Is", "INA2", "INA2Is", "INB1", "INB1Is", "INB2", "INB2Is", "EContainsCs", "EContainsNs", 
--              "EHasName", "ECASrc", "ECATgt", "ECBSrc", "ECBTgt", "ECCSrc", "ECCTgt"] in
--    let s = [("ICA", "CA"), ("ICB", "CB"), ("ICC", "CC"), ("INA1", "NA1"), ("INA1Is", "NA1"), ("INA2", "NA2"), ("INA2Is", "NA2"), ("INB1", "NB1"), 
--            ("INB1Is", "NB1"), ("INB2", "NB2"), ("INB2Is", "NB2"), 
--            ("EHasName", "Node"), ("EContainsCs", "Def"), ("EContainsNs", "Def"), ("ECASrc", "CA"), ("ECATgt", "CA"), 
--            ("ECBSrc", "CB"), ("ECBTgt", "CB"), ("ECCSrc", "CC"), ("ECCTgt", "CC")] in
--    let t = [("ICA", "Connector"), ("ICB", "Connector"), ("ICC", "Connector"), ("INA1", "Node"), ("INA1Is", "NC2"), ("INA2", "Node"), ("INA2Is", "NC1"), 
--            ("INB1", "Node"), ("INB1Is", "NC1"), ("INB2", "Node"), ("INB2Is", "NC2"),
--            ("EHasName", "Name"), ("EContainsCs", "Connector"), ("EContainsNs", "Node"), ("ECASrc", "NA1"), ("ECATgt", "NA2"),
--            ("ECBSrc", "NB1"), ("ECBTgt", "NB2"), ("ECCSrc", "NC1"), ("ECCTgt", "NC2")] in
--    let nt = [("Def", Nnrml), ("Name", Nnrml), ("Connector", Nabst), ("Node", Nabst), ("NA1", Nnrml), ("NA2", Nnrml), ("NB1", Nnrml), 
--             ("NB2", Nnrml), ("CA", Nnrml), ("CB", Nnrml), ("CC", Nnrml), ("NC1", Nvirt), ("NC2", Nvirt)] in
--    let et =  [("ICA", Einh), ("ICB", Einh), ("ICC", Einh), ("INA1", Einh), ("INA1Is", Einh), ("INA2", Einh), ("INA2Is", Einh),  
--              ("INB1", Einh), ("INB1Is", Einh), ("INB2", Einh), ("INB2Is", Einh),
--              ("EContainsCs", Ecomp Bi), ("EContainsNs", Ecomp Bi), ("EHasName", Erel Bi), ("ECASrc", Erel Bi), ("ECATgt", Erel Bi),
--              ("ECBSrc", Erel Bi), ("ECBTgt", Erel Bi), ("ECCSrc", Erel Bi), ("ECCTgt", Erel Bi)] in
--    let sm = [("EContainsCs", Sm $ Val 1), ("EContainsNs", Sm $ Val 1), ("EHasName", Rm 0 $ Val 1),  ("ECASrc", Sm Many), ("ECATgt", Sm Many),
--              ("ECBSrc", Sm Many), ("ECBTgt", Sm Many), ("ECCSrc", Sm Many), ("ECCTgt", Sm Many)] in
--    let tm = [("EContainsCs", Sm Many), ("EContainsNs", Sm Many), ("EHasName", Sm $ Val 1), ("ECASrc", Sm $ Val 1), ("ECATgt", Sm $ Val 1), 
--              ("ECBSrc", Sm $ Val 1), ("ECBTgt", Sm $ Val 1), ("ECCSrc", Sm $ Val 1), ("ECCTgt", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_3 = 
--    let mv = [("Def", "Def"), ("Name", "Attr"), ("Connector", "Connector"), ("Node", "Node"), 
--             ("NA1", "Node"), ("NA2", "Node"), ("NB1", "Node"), ("NB2", "Node"), ("NC1", "Node"), ("NC2", "Node"), 
--             ("CA", "Connector"), ("CB", "Connector"), ("CC", "Connector")] in
--    let me = [("ICA", "IConnectorSelf"), ("ICB", "IConnectorSelf"), ("ICC", "IConnectorSelf"), ("INA1", "INodeSelf"), 
--             ("INA1Is", "INodeSelf"), ("INA2", "INodeSelf"), ("INA2Is", "INodeSelf"), ("INB1", "INodeSelf"), ("INB1Is", "INodeSelf"),
--             ("INB2", "INodeSelf"), ("INB2Is", "INodeSelf"), ("EContainsCs", "EContainsElems"), ("EContainsNs", "EContainsElems"), ("EHasName", "EHasAttrs"),
--             ("ECASrc", "ESrc"), ("ECATgt", "ETgt"), ("ECBSrc", "ESrc"), ("ECBTgt", "ETgt"), ("ECCSrc", "ESrc"), ("ECCTgt", "ETgt")] in
--    cons_gm mv me

def_path = "Tests/SGRefTests2/"
img_path = "Tests/SGRefTests2/img/"

saveDrawings = do
   putStrLn "Savings graphs..."
   draw_def def_path img_path "amm_1.sg"
   draw_def def_path img_path "mm_1.sg"
   draw_def def_path img_path "mm_2.sg"
   draw_def def_path img_path "mm_3.sg"

do_main = do
    (nm_amm, sg_amm)<-load_sg_def def_path "amm_1.sg"
    (nm_mm1, sg_mm1)<-load_sg_def def_path "mm_1.sg"
    (nm_mm2, sg_mm2)<-load_sg_def def_path "mm_2.sg"
    (nm_mm3, sg_mm3)<-load_sg_def def_path "mm_3.sg"
    (nm_m1, m1)<-load_morphism_def def_path $ "m_mm_1.gm"
    (nm_m2, m2)<-load_morphism_def def_path $ "m_mm_2.gm"
    (nm_m3, m3)<-load_morphism_def def_path $ "m_mm_3.gm"
    check_report_wf "Abstract metamodel 1" (Just Total) sg_amm True
    check_report_wf "metamodel 1" (Just Total) sg_mm1 True
    check_report_wf "metamodel 2" (Just Total) sg_mm2 True
    check_report_wf "metamodel 3" (Just Total) sg_mm3 True
    check_morphism ("morphism " ++ nm_m1 ++ " with SG " ++ nm_mm1) (Just TotalM) sg_mm1 m1 sg_amm True
    check_morphism ("morphism " ++ nm_m2 ++ " with SG " ++ nm_mm2) (Just TotalM) sg_mm2 m2 sg_amm True
    check_morphism ("morphism " ++ nm_m3 ++ " with SG " ++ nm_mm3) (Just TotalM) sg_mm3 m3 sg_amm True

main = option_main_save do_main saveDrawings



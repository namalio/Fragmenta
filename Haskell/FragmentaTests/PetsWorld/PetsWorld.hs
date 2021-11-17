
------------------
-- Project: PCs/Fragmenta
-- Module: 'PetsWorld'
-- Description: Module dedicated to the pets world example.
-- Author: Nuno Amálio
-----------------
module PetsWorldTest where

import Gr_Cls
import Frs
import Grs
import LoadCheckDraw
import CheckUtils
import Mdls
import Relations
import Sets
import Utils

def_path = "FragmentaTests/PetsWorld/"
img_path = "FragmentaTests/PetsWorld/img/"

saveDrawings = do
   draw_mdl def_path img_path "M_AHW"
   draw_mdl def_path img_path "M_PW"

do_main = do 
   amdl<-load_mdl_def def_path "M_AHW"
   cmdl<-load_mdl_def def_path "M_PW"
   rms<-load_rm_cmdl_def def_path "M_PW"
   (nm_m1, m1)<-load_morphism_def def_path "F_PW1.gm"
   (nm_m2, m2)<-load_morphism_def def_path "F_PW2.gm"
   (nm_m3, m3)<-load_morphism_def def_path "F_PW3.gm"
   (nm_m4, m4)<-load_morphism_def def_path "F_PW4.gm"
   (nm_m5, m5)<-load_morphism_def def_path "F_PW5.gm"
   check_report_wf "M_AHW" (Just Total) amdl True
   check_report_wf "M_PW" (Just Total) cmdl True
   check_morphism "Refinement of M_AHW by M_PW " (Just TotalM) cmdl rms amdl True


main = do
    option_main_save do_main saveDrawings

-- do_sphm = do
--    load_check_draw "Tests/f_SPHM.fr" "Tests/img/" 

-- do_sph1 = do
--    load_check_draw "Tests/f_SPH1.fr" "Tests/img/" 

-- do_sph2 = do
--    load_check_draw "Tests/f_SPH2.fr" "Tests/img/" 

-- do_fpw1 = do
--    load_check_draw "Tests/f_PW1.fr" "Tests/img/" 

-- do_fpw2 = do
--    load_check_draw "Tests/f_PW2.fr" "Tests/img/"

-- do_fpw3 = do
--    load_check_draw "Tests/f_PW3.fr" "Tests/img/" 

-- fr_morph_1 =
--    let mv = [("Pet", "Pet"), ("Name", "Other"), ("PName", "Other"), ("Group", "Other"), ("PetHotel", "PetHotel"), 
--              ("PetRoom", "PetRoom"), ("PetOwner", "Other"), ("RoomNumber", "Other")] in
--    let me = [("EPet_name", "EAnyPetRel"), ("EPetOwner_name", "EAnyOtherRel"), ("EOwns", "EAnyPetRel"), ("EHosts", "EHosts"), 
--              ("EPetRoom_number", "EAnyPetRoomRel"), ("EPetHotel_name", "EAnyPetHotelRel"), ("EPetHotel_rooms", "EPetHotel_rooms"),
--              ("EPartOf", "EAnyPetHotelRel")] in
--    cons_gm mv me

-- exmp1 = do
--    fia<-load_check_fr "Tests/f_APH.fr"
--    fif<-load_check_fr "Tests/f_SPHM.fr"
--    when ((not $ isNil fif) && (not $ isNil fia)) $ do
--       let (_, f) = theM fif
--       let (_, af) = theM fia
--       check_morphism "Morphism (weak model)" WeakM fr_morph_1 f af True
--       check_morphism "Morphism (partial model)" PartialM fr_morph_1 f af True
--       check_morphism "Morphism (total model)" (FullM Total) fr_morph_1 f af True


-- fr_morph_2a =
--    let mv = [("Pet", "Pet"), ("Name", "Other"), ("PetRoom", "PetRoom"), ("PetOwner", "Other")] in
--    let me = [("EPet_name", "EAnyPetRel"), ("EPetOwner_name", "EAnyOtherRel"), ("EOwns", "EAnyPetRel"), ("EHosts", "EHosts")] in
--    cons_gm mv me

-- fr_morph_2b =
--    let mv = [("PName", "Other"), ("Group", "Other"), ("PetHotel", "PetHotel"), 
--              ("PPetRoom", "PetRoom"), ("RoomNumber", "Other")] in
--    let me = [("EPetHotel_name", "EAnyPetHotelRel"), ("EPetHotel_rooms", "EPetHotel_rooms"),
--              ("EPartOf", "EAnyPetHotelRel"), ("EGroup_name", "EAnyOtherRel"), ("EPetRoom_number", "EAnyPetRoomRel")] in
--    cons_gm mv me

-- fr_morph_2b' = replace_in_gm fr_morph_2b [("PPetRoom", "PetRoom"), ("PName", "Name")] []

-- exmp2 = do
--    fia<-load_check_fr "Tests/f_APH.fr"
--    fif1<-load_check_fr "Tests/f_SPH1.fr"
--    fif2<-load_check_fr "Tests/f_SPH2.fr"
--    when (isNil fif2) $ putStrLn $ "Could not load" ++  "f_SPH2.fr"
--    when ((not $ isNil fia) && (not $ isNil fif1) && (not $ isNil fif2)) $ do
--       let (_, af) = theM fia
--       let (_, f1) = theM fif1
--       let (_, f2) = theM fif2
--       check_report_wf "Abstract Fragment" (Just Total) af True
--       check_report_wf "Fragment 1" (Just Partial) f1 True
--       check_report_wf "Fragment 2" (Just Partial) f2 True
--       check_morphism "Morphism 2a (weak model)" WeakM fr_morph_2a f1 af True
--       check_morphism "Morphism 2b (weak model)" WeakM fr_morph_2b f2 af True
--       let ufs = union_frs [f1, f2]
--       check_report_wf "Union of Fragments" (Just Total) ufs True
--       saveFrDrawing "Tests/img/" "F_U_Fs_SPH1_2" ufs 
--       let cfs = consSeamlessCompFs [f1, f2]
--       check_report_wf "Colimit composition of Fragments" (Just Total) cfs True
--       saveFrDrawing "Tests/img/" "F_CC_Fs_SPH1_2" cfs
--       let ugms = fr_morph_2a `union_gm` fr_morph_2b
--       check_morphism "Union of Morphisms 1 and 2 with respect to union composition" WeakM ugms ufs af True
--       check_morphism "Typing Union of Morphisms 1 and 2 with respect to union composition" (FullM Total) ugms ufs af True
--       let ugms' = fr_morph_2a `union_gm` fr_morph_2b'
--       check_morphism "Union of Morphisms 1 and 2 with respect to colimit composition" WeakM ugms' cfs af True
--       check_morphism "Typing of Union of Morphisms 1 and 2 with respect to colimit composition" (FullM Total) ugms' cfs af True


-- fr_morph_3a =
--    let mv = [("Pet", "Pet"), ("Name", "Other"),  ("PName", "Other"), ("PetOwner", "Other"), ("PPHCard", "POther"), ("City", "Other"), 
--             ("Country", "POther"), ("Date", "POther")]  in
--    let me = [("EPet_name", "EAnyPetRel"), ("EPet_dob", "EAnyPetRel"), ("EPetOwner_name", "EAnyOtherRel"),  ("EPetOwner_city", "EAnyOtherRel"), 
--              ("EPetOwner_country", "EAnyOtherRel"), ("EHolds", "EAnyOtherRel"), ("EOwns", "EAnyPetRel")] in
--    cons_gm mv me

-- fr_morph_3a' = replace_in_gm fr_morph_3a [("PName", "Name"), ("PPHCard", "PHCard")] []

-- fr_morph_3b =
--    let mv = [("PPet", "Pet"), ("Dog", "Pet"), ("Cat", "Pet"), ("Gecko", "Pet"), ("Chamaeleon", "Pet"), ("Mammal", "Pet"), ("Reptile", "Pet"), 
--             ("HungryStatus", "Other"), ("starving", "Other"), ("hungry", "Other"), ("fed", "Other"), ("full", "Other")]  in
--    let me = [("EIstarving", "EIOther_Other"), ("EIhungry", "EIOther_Other"), ("EIfed", "EIOther_Other"), ("EIfull", "EIOther_Other"),
--              ("EIDog_PPet", "EIPet_Pet"), ("EICat_PPet", "EIPet_Pet"), ("EIChamaeleon_PPet", "EIPet_Pet"), ("EIGecko_PPet", "EIPet_Pet"),
--              ("EIDog_Mammal", "EIPet_Pet"), ("EICat_Mammal", "EIPet_Pet"), ("EIChamaeleon_Reptile", "EIPet_Pet"), 
--              ("EIGecko_Reptile", "EIPet_Pet"), ("EPet_hstatus", "EAnyPetRel")] in
--    cons_gm mv me

-- fr_morph_3b' = replace_in_gm fr_morph_3b [("PPet", "Pet")] []

-- fr_morph_3c =
--    let mv = [("MammalHotel", "PetHotel"), ("PetRoom", "PetRoom"), ("PHCard", "POther"), ("PetRoomId", "POther"), ("PMammal", "Pet"), ("Nat", "Other"), ("PName2", "Other"), 
--             ("PHCardId", "Other"), ("PCountry", "POther"), ("PCity", "Other")]  in
--    let me = [("EMammalHotel_city", "EAnyPetHotelRel"), ("EMammalHotel_country", "EAnyPetHotelRel"), ("EMammalHotel_name", "EAnyPetHotelRel"), 
--             ("EMammalHotel_lcards", "EAnyPetHotelRel"),  ("EMammalHotel_rooms", "EPetHotel_rooms"), ("EPHCard_id", "EAnyOtherRel"),
--             ("EPHCard_points", "EAnyOtherRel"), ("EPetRoom_capacity", "EAnyPetRoomRel"), ("EPetRoom_id", "EAnyPetRoomRel"), ("EHosts", "EHosts")] in
--    cons_gm mv me

-- fr_morph_3c' = replace_in_gm fr_morph_3c [("PMammal", "Mammal"), ("PName2", "Name"), ("PCountry", "Country"), ("PCity", "City")] []

-- exmp3 = do
--    fia<-load_check_fr "Tests/f_APH.fr"
--    fifpw1<-load_check_fr "Tests/f_PW1.fr"
--    fifpw2<-load_check_fr "Tests/f_PW2.fr"
--    fifpw3<-load_check_fr "Tests/f_PW3.fr"
--    when (isNil fifpw2) $ putStrLn $ "Could not load" ++  "f_PW2.fr"
--    when ((not $ isNil fia) && (not $ isNil fifpw1) && (not $ isNil fifpw2)) $ do
--       let (_, af) = theM fia
--       let (_, fpw1) = theM fifpw1
--       let (_, fpw2) = theM fifpw2
--       let (_, fpw3) = theM fifpw3
--       check_report_wf "Abstract Fragment" (Just Total) af True
--       check_report_wf "Fragment F_PW1" (Just Partial) fpw1 True
--       check_report_wf "Fragment F_PW2" (Just Partial) fpw2 True
--       check_report_wf "Fragment F_PW3" (Just Partial) fpw3 True
--       check_morphism "Morphism 3a (weak model)" WeakM fr_morph_3a fpw1 af True
--       check_morphism "Morphism 3b (weak model)" WeakM fr_morph_3b fpw2 af True
--       check_morphism "Morphism 3c (weak model)" WeakM fr_morph_3c fpw3 af True
--       let ufs = union_frs [fpw1, fpw2, fpw3]
--       check_report_wf "Union of Fragments (Pet world)" (Just Total) ufs True
--       saveFrDrawing "Tests/img/" "F_U_Fs_PW" ufs
--       let ugms = fr_morph_3a `union_gm` (fr_morph_3b `union_gm` fr_morph_3c)
--       check_morphism "Union of Morphisms 1, 2 and 3" WeakM ugms ufs af True
--       check_morphism "Typing Union of Morphisms 1, 2 and 3" (FullM Total) ugms ufs af True
--       let cfs = consSeamlessCompFs [fpw1, fpw2, fpw3]
--       check_report_wf "Colimit composition of Fragments" (Just Total) cfs True
--       saveFrDrawing "Tests/img/" "F_CC_Fs_PW" cfs
--       check_morphism "Typing Union of Morphisms 1, 2 and 3 with respect to union" (FullM Total) ugms ufs af True
--       let ugms_ = fr_morph_3a' `union_gm` (fr_morph_3b' `union_gm` fr_morph_3c')
--       let ugms' = cons_gm (no_dups $ mV ugms_) (mE ugms_)
--       check_morphism "Union of Morphisms with respect to colimit composition (Pet world)" WeakM ugms' cfs af True
--       check_morphism "Typing of Union of Morphisms with respect to colimit composition (Pet world)" (FullM Total) ugms' cfs af True

      --check_morphism "Morphism 2b (weak model)" WeakM fr_morph_2b f2 af True

--At some point, I need to lift this to the models level.


import Gr_Cls
import Grs
import Relations
import LoadCheckDraw
import CheckUtils
import Utils

def_path = "Tests/GFGTests/"
img_path = "Tests/GFGTests/img/"

saveDrawings= do
    draw_def def_path img_path "gfg_felines.gfg"
    draw_def def_path img_path "gfg_pets_world.gfg"
    draw_def def_path img_path "feline-canidae.gfg"
    draw_def def_path img_path "person-vehicle-any.gfg"
    draw_def def_path img_path "person-vehicle-inh.gfg"

do_main = do
   (nm_gfg1, gfg1)<-load_gfg_def def_path "gfg_felines.gfg"
   (nm_gfg2, gfg2)<-load_gfg_def def_path "gfg_pets_world.gfg"
   (nm_gfg3, gfg3)<-load_gfg_def def_path "feline-canidae.gfg"
   (nm_gfg4, gfg4)<-load_gfg_def def_path "person-vehicle-any.gfg"
   (nm_gfg5, gfg5)<-load_gfg_def def_path "person-vehicle-inh.gfg"
   check_report_wf nm_gfg1 (Just Total) gfg1 False
   check_report_wf nm_gfg2 (Just Total) gfg2 True
   check_report_wf nm_gfg3 (Just Total) gfg3 True
   check_report_wf nm_gfg4 (Just Total) gfg4 True
   check_report_wf nm_gfg5 (Just Total) gfg5 True

main = do
   option_main_save do_main saveDrawings

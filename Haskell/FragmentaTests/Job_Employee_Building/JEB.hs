-------------------------
-- Project: PCs/Fragmenta
-- Module: 'JEB' (Job, Employee, Building)
-- Description: Example of Fragmenta paper ('Related Work' section), nodes Person, Vehicle, Any
-- Author: Nuno Amálio
--------------------------
import Gr_Cls
import Grs
import Frs
import Mdls
import Utils
import CheckUtils
import LoadCheckDraw
import NumString

def_path = "FragmentaTests/Job_Employee_Building/"
img_path = "FragmentaTests/Job_Employee_Building/img/"

saveDrawings= do
    draw_mdl def_path img_path "m_JEB"

do_main = do
    (nm_mdl, mdl)<-loadMdl def_path "m_JEB"
    check_report_wf nm_mdl (Just Total) mdl True

main = do
   option_main_save do_main saveDrawings

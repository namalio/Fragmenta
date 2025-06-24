cd ..
runhaskell Statecharts/StCsUtils.hs -g
cd Statecharts/MM/img
dot -Tpdf F_AH.gv -o F_AH.pdf
dot -Tpdf StCs_AMM_gfg.gv -o StCs_AMM_gfg.pdf
dot -Tpdf StCs_AMM_Mdl.gv -o StCs_AMM_Mdl.pdf
dot -Tpdf StCs_AMM_rf.gv -o StCs_AMM_rf.pdf
dot -Tpdf StCs_AMM_uf.gv -o StCs_AMM_uf.pdf
dot -Tpdf F_MM1.gv -o F_MM1.pdf
dot -Tpdf F_MM2.gv -o F_MM2.pdf
dot -Tpdf F_MM3.gv -o F_MM3.pdf
dot -Tpdf F_MM4.gv -o F_MM4.pdf
dot -Tpdf F_MM5.gv -o F_MM5.pdf
dot -Tpdf StCs_MM_gfg.gv -o StCs_MM_gfg.pdf
dot -Tpdf StCs_MM_Mdl.gv -o StCs_AMM_Mdl.pdf
dot -Tpdf StCs_MM_rf.gv -o StCs_AMM_rf.pdf
dot -Tpdf StCs_MM_uf.gv -o StCs_AMM_uf.pdf
cd ../../Examples/img
dot -Tpdf StC_SimpleWatch.gv -o StC_SimpleWatch.pdf
dot -Tpdf Stc_BoolSetter.gv -o Stc_BoolSetter.pdf
dot -Tpdf Stc_BoolSetter.gv -o Stc_BoolSetter.pdf
dot -Tpdf Stc_Buzzer.gv -o Stc_Buzzer.pdf
dot -Tpdf Stc_WBuzzer.gv -o Stc_WBuzzer.pdf
dot -Tpdf Stc_WBuzzerWStatus.gv -o Stc_WBuzzerWStatus.pdf
dot -Tpdf Stc_WBuzzerWStatus2.gv -o Stc_WBuzzerWStatus2.pdf
dot -Tpdf StC_TVSet.gv -o StC_TVSet.pdf
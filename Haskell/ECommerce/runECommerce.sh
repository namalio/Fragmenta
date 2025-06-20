cd ..
runhaskell ECommerce/commerce.hs -g
cd ECommerce/img
dot -Tpdf F_AP.gv -o F_AP.pdf
dot -Tpdf F_P.gv -o F_P.pdf
dot -Tpdf F_NF.gv -o F_NF.pdf
dot -Tpdf F_PS.gv -o F_PS.pdf
dot -Tpdf F_PBe.gv -o F_PBe.pdf
dot -Tpdf F_PF.gv -o F_PF.pdf
dot -Tpdf F_PBk.gv -o F_PBk.pdf
dot -Tpdf F_PP.gv -o F_PF.pdf
dot -Tpdf F_E.gv -o F_E.pdf
dot -Tpdf F_BTs.gv -o F_BTs.pdf
dot -Tpdf M_AC_gfg.gv -o M_AC_gfg.pdf
dot -Tpdf M_AC_Mdl.gv -o M_AC_Mdl.pdf
dot -Tpdf M_AC_uf.gv -o M_AC_uf.pdf
dot -Tpdf M_AC_rf.gv -o M_AC_rf.pdf
dot -Tpdf M_CC_gfg.gv -o M_CC_gfg.pdf
dot -Tpdf M_CC_Mdl.gv -o M_CC_Mdl.pdf
dot -Tpdf M_CC_uf.gv -o M_CC_uf.pdf
dot -Tpdf M_CC_rf.gv -o M_CC_rf.pdf
dot -Tpdf CI1.gv -o CI1.pdf
dot -Tpdf CI2.gv -o CI2.pdf
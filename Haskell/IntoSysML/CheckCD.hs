module IntoSysML.CheckCD(
    savePDGDrawing
    , checkPDG
) where

import IntoSysML.IntoSysMLCD
import IntoSysML.IntoSysMLASD
import Gr_Cls
import Grs
import SGrs
import Sets
import Relations
import TheNil
import LoadCheckDraw
import SimpleFuns
import Grs (acyclicG)

-- builds the ports graph
cPDG:: SGr String String->ASD String String->CDG String String ->Gr String String
cPDG sg asd cd = 
    let r1 = trim . gCDPortsRel $ cd 
        ns = gCDPorts sg cd
        srcr r = foldr (\(p1, p2) sr->("E_" ++ p1 ++ "_" ++ p2, p1) `intoSet` sr) nil r
        tgtr r = foldr (\(p1, p2) tr->("E_" ++ p1 ++ "_" ++ p2, p2) `intoSet` tr) nil r 
        gIps p = img (inv . fV . etm $ cd) (gOFPDeps asd $ appl (fV . etm $ cd) p) `intersec` gBlIPorts cd (gBlIOfPort cd p)
        r2 = trim $ foldr (\p dr->(gIps p `cross`  singles p) `union` dr) nil ns
        cut x = take (length x - 3) x
        trim = foldr (\p ar->mapP cut p `intoSet` ar) nil in
    consG (fmap cut ns) (dom_of $ srcr r1 `union` srcr r2) (srcr r1 `union` srcr r2) (tgtr r1 `union` tgtr r2)

savePDGDrawing:: FilePath ->SGr String String->ASD String String->CDG String String ->IO()
savePDGDrawing path sg asd cd = 
    let nm = gCDName cd in
    saveGDrawing path ("pdg_" ++ nm) False (cPDG sg asd cd)

checkPDG :: SGr String String->ASD String String->CDG String String->Bool
checkPDG sg asd cd= acyclicG (cPDG sg asd cd)
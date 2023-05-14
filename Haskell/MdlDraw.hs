
module MdlDraw (wrMdlAsGraphviz) where

import Mdls
import FrsDraw
import SGsDraw
import Sets ( toList ) 

data MdlDrawing = MdlDrawing String [FrDrawing] deriving(Show) 

consMdlDrawingDesc :: String -> Mdl String String -> MdlDrawing
consMdlDrawingDesc nm mdl = MdlDrawing nm (map (\(fnm, f)-> consFrDrawingDesc fnm f) (toList . mfd $ mdl))

wrMdlGraphvizDesc (MdlDrawing nm fds) = 
   "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" ++ (foldr (\fd ds-> (wrFrGraphvizDesc PartOf fd) ++ ds) "" fds) ++ "}"

wrMdlAsGraphviz :: String -> Mdl String String -> String
wrMdlAsGraphviz nm mdl = wrMdlGraphvizDesc . consMdlDrawingDesc nm $ mdl
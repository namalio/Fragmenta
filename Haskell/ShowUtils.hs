module ShowUtils(
   showElems
   , showElems'
   , wrSepElems
   , showStrs
   , showNode
   , showEdge
   , showEdges
   , slimShow
   , showNodes) where
import SimpleFuns (butLast)

showStrs :: Foldable t => t String -> String -> String
showStrs xs sep = foldl (\ss s->if null ss then s else ss++sep++s) "" xs

showElems :: (Foldable t, Show a) => t a -> String-> String
showElems xs sep = foldr (\s ss->if null ss then (show s) else (show s)++sep++ss) "" xs

showElems' :: (Foldable t, Show a) => t a -> String
showElems' xs  = showElems xs ", "

showEdges :: (Functor t, Foldable t, Show a) => t a -> String
showEdges xs  = showStrs (fmap showEdge xs) ", "

showNodes :: (Functor t, Foldable t, Show a) => t a -> String
showNodes xs  = showStrs (fmap showNode xs) ", "

do_indent 0 = ""
do_indent n = "   " ++ do_indent(n-1)

shortenENm::Show a=>a->String
shortenENm = (drop 1) . slimShow

slimShow::Show a=>a->String
slimShow = drop 1 . butLast . show

shortenNNm::Show a=>a->String
shortenNNm = slimShow

showNode :: Show a => a -> String
showNode = shortenNNm 

showEdge :: Show b => b -> String
showEdge = shortenENm 

-- Writes elements separated by some separator
-- Takes an identation level (a natural number)
wrSepElems [] _ _ _ _ = ""
wrSepElems (s:ss) sep spaced ind i
   | null ss = (if ind then (do_indent i) else "") ++ s
   | otherwise = 
   let spc = if spaced then " " else "" in
   let dind = if ind then do_indent i else "" in
      dind++s++sep++spc++(wrSepElems ss sep spaced False i)
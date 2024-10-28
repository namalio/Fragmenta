module ShowUtils(
   showElems
   , showElems'
   , showThemSlimmed
   , wrSepElems
   , showStrs
   , showNode
   , showEdge
   , showEdges
   , slimStr
   , slimShow
   , showNodes
   , strOfTxtExp
   , strOfTxtExps
   , do_indent) where
import SimpleFuns (butLast)

showStrs :: Foldable t => t String -> String -> String
showStrs xs sep = foldl (\ss s->if null ss then s else ss++sep++s) "" xs

showElems :: (Foldable t, Show a) => t a ->(a->String)->String-> String
showElems xs showF sep = foldr (\s ss->if null ss then showF s else showF s++sep++ss) "" xs

showElems' :: (Foldable t, Show a) => t a -> String
showElems' xs  = showElems xs show ", "

showThemSlimmed :: (Foldable t, Show a) => t a -> String
showThemSlimmed xs  = showElems xs slimShow ", "

showEdges :: (Functor t, Foldable t, Show a) => t a -> String
showEdges xs  = showStrs (fmap showEdge xs) ", "

showNodes :: (Functor t, Foldable t, Show a) => t a -> String
showNodes xs  = showStrs (fmap showNode xs) ", "

do_indent :: (Eq n, Num n) => n -> String
do_indent 0 = ""
do_indent n = "   " ++ do_indent(n-1)

shortenENm::Show a=>a->String
shortenENm = (drop 1) . slimShow

slimStr::String->String
slimStr = drop 1 . butLast 

slimShow::Show a=>a->String
slimShow = slimStr . show

shortenNNm::Show a=>a->String
shortenNNm = slimShow

showNode :: Show a => a -> String
showNode = shortenNNm 

showEdge :: Show b => b -> String
showEdge = shortenENm 

-- Writes elements separated by some separator
-- Takes an identation level (a natural number)
wrSepElems :: (Eq t, Num t, Foldable c) => c String ->String -> Bool -> Bool -> t -> String
--wrSepElems [] _ _ _ _ = ""
wrSepElems ss sep spaced ind i = 
   let spc = if spaced then " " else "" 
       dind = if ind then do_indent i else "" 
       str s e = if null s || all (== ' ') s then e else dind++e++sep++spc in
   foldr (\e s->(str s e)++s) (if ind then (do_indent i) else "")  ss
   -- | null ss = (if ind then (do_indent i) else "") ++ s
   -- | otherwise = 
   -- dind++s++sep++spc++(wrSepElems ss sep spaced False i)

strOfTxtExp::Either String [String]->String
strOfTxtExp (Left b) = b
strOfTxtExp (Right bs) = "{" ++ showStrs bs "," ++ "}"

strOfTxtExps::[Either String [String]]->[String]
strOfTxtExps = fmap strOfTxtExp
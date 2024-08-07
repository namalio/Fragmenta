module ParsingG (loadGraph) where

import Relations
import Sets ( singles, set )
import Grs (Gr, unionG )
import Text.ParserCombinators.ReadP
    ( ReadP,
      (<++),
      between,
      char,
      many,
      readP_to_S,
      skipSpaces,
      string )
import Control.Applicative hiding (many,empty)
import TheNil
import MyMaybe
import ParsingCommon
import Gr_Cls

-- A Node has a name 
-- An edge definition has an optional name, a source and a target node (Strings)
data GElem = ElemN String | ElemE String String String  
   deriving(Eq, Show)
data GDef = GDef String [GElem] 
   deriving(Eq, Show)

gd_name (GDef nm _) = nm


extract_elem::GElem->Gr String String
extract_elem (ElemN n) = consG (singles n) nil nil nil
extract_elem (ElemE e s t) = 
   let e' = nm_of_edge e s t in 
   consG (set [s, t]) (singles e') (singles (e', s)) (singles (e', t))
   where nm_of_edge enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)

extract_g::[GElem]->Gr String String
extract_g = foldl (\g e-> g `unionG` (extract_elem e)) empty

--extract_sg ((ElemN (NodeDef n nty)):es) = (cons_sg (cons_g [n] [] [] []) [(n, nty)] [] [] []) `union_sg` (extract_sg es)
--extract_sg ((ElemE (EdgeDef e s t ety om1 om2)):es) = 
--   let e' = nm_of_edge ety e s t in 
--   let sm = ext_mult_s e' om1 in
--   let tm = ext_mult_s e' om2 in
--   (cons_sg (cons_g [s, t] [e'] [(e', s)] [(e', t)]) [] [(e', ety)] sm tm)  `union_sg` (extract_sg es)
--   where nm_of_edge Einh _ s t = "EI" ++ s ++ "_" ++ t
--         nm_of_edge _ enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)
--extract_sg ((ElemClE (ClEnum s v)):es) = 

cons_g_fr_gd::GDef->Gr String String
cons_g_fr_gd (GDef _ elems ) = extract_g elems

parse_g_node::ReadP GElem
parse_g_node = do
   string "node"
   skipSpaces
   nm<-parseId
   skipSpaces
   return (ElemN nm)

parse_edge_name::ReadP String
parse_edge_name = do
   nm<-(between (char '[') (char ']') parseId) <++ (return "")
   return nm

parse_g_edge::ReadP GElem
parse_g_edge = do
   string "edge"
   skipSpaces
   sn<-parseId 
   skipSpaces
   string "->"
   skipSpaces
   tn<-parseId
   skipSpaces
   enm<-parse_edge_name
   skipSpaces
   return (ElemE enm sn tn)

parse_g_elem::ReadP GElem
parse_g_elem = do
   skipSpaces
   e<-parse_g_node <|> parse_g_edge
   return e

parse_graph::ReadP GDef
parse_graph = do
   string "Graph"
   skipSpaces
   g_nm<-parseId
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_g_elem) 
   return (GDef g_nm elems)

--parseFr ls = 
--   let (pcnm, st) = splitAt'(\c->c=='@') $ snd $ splitAt' (\c->c==' ')(head ls) in 
--   let elems = parseTo parseElem (tail ls) in
--   PCDef pcnm st elems



loadGDefFrFile :: FilePath -> IO (Maybe GDef)
loadGDefFrFile fn = do   
    contents <- readFile fn
    let g = parseMaybe parse_graph contents
    return g

test_g = "Graph A_B {\n"
   ++ "node A\n"
   ++ "node B\n"
   ++ "edge A->B"
   ++ "}"


loadGraph :: FilePath -> IO (Maybe (String, (Gr String String)))
loadGraph fn = do
   g_def<-loadGDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   og <- if isNil g_def 
      then do
         putStrLn "Graph definition could not be parsed"
         return (Nothing)
      else do
         let gd = the g_def
         return(Just (gd_name gd, cons_g_fr_gd gd))
   return og

test1 = readP_to_S parse_graph test_g

test2 = do
   g<-loadGraph "Tests/G_Car_Wheels_I1.g"
   putStrLn $ show g

--test2 = do
--   sg<-loadSG "Tests/SG_Employee_Car.sg"
--   putStrLn $ show sg

--test3 = readP_to_S parse_rel "rel Pet->POther[AnyRel1]: *,*"


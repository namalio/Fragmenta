
-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GwTParsing'
-- Description: Module responsible for parsing Fragmenta's Graphs with Typing (GwTs)
-- Author: Nuno Amálio
--------------------------
module ParsingGwT (loadGwT) where

import Relations
import Grs
import GrswT
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many, empty)
import TheNil
import MyMaybe
import ParsingCommon
import Sets ( singles, set )
import Gr_Cls

-- A node element has a name and a type
-- An edge definition has an optional name, a source and a target node (Strings), and a type (another string)
data GwTElem = ElemN String String | ElemE String String String  String
   deriving(Eq, Show)
data GwTDef = GwTDef String [GwTElem] 
   deriving(Eq, Show)

gwtd_name :: GwTDef -> String
gwtd_name (GwTDef nm _) = nm

extract_elem::GwTElem->GrwT String String
extract_elem (ElemN n nty) = consGWT (consG (singles n) nil nil nil) (consGM (singles (n, nty)) nil)
extract_elem (ElemE e s t ety) = 
   let e' = nm_of_edge e s t in 
   consGWT (consG (set [s, t]) (singles e') (singles (e', s)) (singles (e', t))) (consGM nil (singles (e', "E"++ety)))
   where nm_of_edge enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)

extract_gwt::[GwTElem]->GrwT String String
extract_gwt = foldl (\g e-> g `unionGWT` (extract_elem e)) empty

cons_gwt_fr_gd::GwTDef->GrwT String String
cons_gwt_fr_gd (GwTDef _ elems ) = extract_gwt elems

parse_gwt_node::ReadP GwTElem
parse_gwt_node = do
   string "node"
   skipSpaces
   nm<-parse_until_chs " :"
   skipSpaces
   string ":"
   skipSpaces
   ty<-parseId
   skipSpaces
   return (ElemN nm ty)

parse_edge_name::ReadP String
parse_edge_name = do
   nm<-(between (char '[') (char ']') parseId) <++ (return "")
   return nm

parse_gwt_edge::ReadP GwTElem
parse_gwt_edge = do
   string "edge"
   skipSpaces
   sn<-parseId 
   skipSpaces
   string "->"
   skipSpaces
   tn<-parse_until_chs " :["
   skipSpaces
   enm<-parse_edge_name
   skipSpaces
   string ":"
   skipSpaces
   ty<-parseId
   skipSpaces
   return (ElemE enm sn tn ty)

parse_gwt_elem::ReadP GwTElem
parse_gwt_elem = do
   skipSpaces
   e<-parse_gwt_node <|> parse_gwt_edge
   return e

parse_gwt::ReadP GwTDef
parse_gwt = do
   string "GrwT"
   skipSpaces
   g_nm<-parseId
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_gwt_elem) 
   skipSpaces
   return (GwTDef g_nm elems)

--parseFr ls = 
--   let (pcnm, st) = splitAt'(\c->c=='@') $ snd $ splitAt' (\c->c==' ')(head ls) in 
--   let elems = parseTo parseElem (tail ls) in
--   PCDef pcnm st elems

loadGwTDefFrFile :: FilePath -> IO (Maybe GwTDef)
loadGwTDefFrFile fn = do   
    contents <- readFile fn
    let g = parseMaybe parse_gwt contents
    return g

test_gwt = "GrwT A_B {\n"
   ++ "node A : TA\n"
   ++ "node B : TB\n"
   ++ "edge A->B : TA_B"
   ++ "}"


loadGwT:: FilePath -> IO (Maybe (String, (GrwT String String)))
loadGwT fn = do
   g_def<-loadGwTDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   ogwt <- if isNil g_def 
      then do
         putStrLn "Graph with typing definition could not be parsed"
         return (Nothing)
      else do
         let gd = the g_def
         return(Just (gwtd_name gd, cons_gwt_fr_gd gd))
   return ogwt

test1 :: [(GwTDef, String)]
test1 = readP_to_S parse_gwt test_gwt

test2 = readP_to_S parse_gwt_node "node A : TA\n"

test3 :: GrwT String String
test3 = 
   cons_gwt_fr_gd (the $ parseMaybe parse_gwt test_gwt) 

test4 :: [(GwTElem, String)]
test4 = readP_to_S parse_gwt_node "node v-20: Nat"

test5 = do
   g<-loadGwT "Tests/CarWheels/G_Car_Wheels_I1.gwt"
   putStrLn $ show g
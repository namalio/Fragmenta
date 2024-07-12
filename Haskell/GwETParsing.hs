
-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GwTParsing'
-- Description: Module responsible for parsing Fragmenta's Graphs with Typing (GwTs)
-- Author: Nuno Amálio
--------------------------
module GwETParsing (loadGwET) where

import Relations
import Grs
import GrswET
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many, empty)
import TheNil
import ParsingCommon ( parseMaybe, parseId )
import Sets ( singles, set )
import Gr_Cls 

-- A node element has a name and a type
-- An edge definition has an optional name, a source and a target node (Strings), and a type (another string)
data GwETElem = ElemN String String (Maybe String) 
               | ElemE String String String  String (Maybe String)
   deriving(Eq, Show)
data GwETDef = GwETDef String [GwETElem] 
   deriving(Eq, Show)

gwetd_name :: GwETDef -> String
gwetd_name (GwETDef nm _) = nm

extractElem::GwETElem->GrwET String String
extractElem (ElemN n nty et) = 
   let g = consG (singles n) nil nil nil
       t = consGM (singles (n, nty)) nil
       t' = if isNil et then emptyGM else consGM (singles (n, the et)) nil in
   consGWET g t t'
extractElem (ElemE e s t ety et) = 
   let e' = nm_of_edge e s t 
       g = consG (set [s, t]) (singles e') (singles (e', s)) (singles (e', t)) 
       tm = consGM nil (singles (e', "E"++ety))
       tm' = if isNil et then emptyGM else consGM nil (singles (e', "E"++ the et)) in 
   consGWET g tm tm'
   where nm_of_edge enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)

--extract_gwet::[GwETElem]->GrwET String String
--extract_gwet = foldl (\g e-> g `unionGWT` (extractElem e)) empty

consGwETFrGD::GwETDef->GrwET String String
consGwETFrGD (GwETDef _ elems) = 
   foldl (\g e-> g `unionGWET` extractElem e) empty elems

parse_ET::ReadP (Maybe String)
parse_ET = do
   string "::"
   skipSpaces
   ety<-parseId
   skipSpaces
   return (Just ety)

parse_gwt_node::ReadP GwETElem
parse_gwt_node = do
   string "node"
   skipSpaces
   nm<-parseId
   skipSpaces
   string ":"
   skipSpaces
   ty<-parseId
   skipSpaces
   et <- parse_ET <++ (return Nothing)
   return (ElemN nm ty et)

parse_edge_name::ReadP String
parse_edge_name = do
   nm<-(between (char '[') (char ']') parseId) <++ (return "")
   return nm

parse_gwt_edge::ReadP GwETElem
parse_gwt_edge = do
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
   string ":"
   skipSpaces
   ty<-parseId
   skipSpaces
   et <- parse_ET <++ (return Nothing)
   return (ElemE enm sn tn ty et)

parse_gwet_elem::ReadP GwETElem
parse_gwet_elem = do
   skipSpaces
   e<-parse_gwt_node <|> parse_gwt_edge
   return e

parse_gwet::ReadP GwETDef
parse_gwet = do
   string "GrwET"
   skipSpaces
   g_nm<-parseId
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_gwet_elem) 
   return (GwETDef g_nm elems)

--parseFr ls = 
--   let (pcnm, st) = splitAt'(\c->c=='@') $ snd $ splitAt' (\c->c==' ')(head ls) in 
--   let elems = parseTo parseElem (tail ls) in
--   PCDef pcnm st elems



loadGwETDefFrFile :: FilePath -> IO (Maybe GwETDef)
loadGwETDefFrFile fn = do   
   readFile fn >>= return . parseMaybe parse_gwet
   --putStrLn contents
   --let g = parseMaybe parse_gwet contents
   --return g

test_gwt = "GrwT A_B {\n"
   ++ "node A : TA\n"
   ++ "node B : TB\n"
   ++ "edge A->B : TA_B"
   ++ "}"


loadGwET:: FilePath -> IO (Maybe (String, GrwET String String))
loadGwET fn = do
   g_def<-loadGwETDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   ogwt <- if isNil g_def 
      then do
         putStrLn "Definition of Graph with extra typing could not be parsed"
         return Nothing
      else do
         let gd = the g_def
         return(Just (gwetd_name gd, consGwETFrGD gd))
   return ogwt

test1 :: [(GwETDef, String)]
test1 = readP_to_S parse_gwet test_gwt
test2 :: [(GwETElem, String)]
test2 = readP_to_S parse_gwt_node "node A : TA\n"

test3 :: IO ()
test3 = do
   g<-loadGwET "Tests/CarWheels/G_Car_Wheels_I1.gwt"
   putStrLn $ show g
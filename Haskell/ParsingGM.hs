module ParsingGM (loadMorphism) where

import Sets ( intoSet )
import Relations 
import Grs
import Gr_Cls
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many)
import TheNil
import MyMaybe
import ParsingCommon

-- A Node mapping maps a node onto another
data NodeMapping = NodeMapping String String
   deriving(Eq, Show)
-- A Edge mapping maps an edge onto another
data EdgeMapping = EdgeMapping String String
   deriving(Eq, Show)
-- A morphism definition has a name, and two collections of node and edge mappings, respectively
data MorphismDef = MorphismDef String [NodeMapping] [EdgeMapping]
   deriving(Eq, Show)

morphDNm::MorphismDef->String
morphDNm (MorphismDef nm _ _) = nm

consGMFrD::MorphismDef->GrM String String
consGMFrD (MorphismDef _ nms ems) = 
   let nr = foldr (\nm r-> (gNMInfo nm) `intoSet` r) nil nms 
       er = foldr (\em r-> (gEMInfo em) `intoSet` r) nil ems in
   consGM nr er

gNMInfo::NodeMapping->(String, String)
gNMInfo (NodeMapping n1 n2) = (n1, n2) 

gEMInfo::EdgeMapping->(String, String)
gEMInfo (EdgeMapping e1 e2) = (e1, e2) 

--extract_node_pairs::[NodeMapping]->Rel String String
--extract_node_pairs = foldr (\nm lps-> (gNMInfo nm) `intoSet` lps) nil

--extract_edge_pairs::[EdgeMapping]->Rel String String
--extract_edge_pairs ems = foldr (\em lps-> (gEMInfo em) `intoSet` lps) nil ems


parse_map::ReadP (String, String)
parse_map = do
   nm1<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   nm2<-parse_id
   return $ (nm1, nm2)

parse_nodeM::ReadP NodeMapping
parse_nodeM = do
   (nm1, nm2)<-parse_map
   return $ NodeMapping nm1 nm2

parse_edgeM::ReadP EdgeMapping
parse_edgeM = do
   (nm1, nm2)<-parse_map
   return $ EdgeMapping ("E"++nm1) ("E"++nm2)

--map_sep::ReadP ()
--map_sep = do
--   char '\n'
--   skipSpaces
--   return ()

parse_nodeMappings::ReadP [NodeMapping]
parse_nodeMappings = do
   string "nodes"
   skipSpaces
   nms<-between (char '{') (skipSpaces >> char '}') (many (skipSpaces >>parse_nodeM))
   return (nms)

parse_edgeMappings::ReadP [EdgeMapping]
parse_edgeMappings = do
   string "edges"
   skipSpaces
   ems<-between (char '{') (skipSpaces >> char '}') (many (skipSpaces >>parse_edgeM))
   return (ems)

parse_morphism::ReadP MorphismDef
parse_morphism = do
   string "Morphism"
   skipSpaces
   m_nm<-parse_id
   skipSpaces
   char '{'
   skipSpaces
   nms<-parse_nodeMappings
   skipSpaces 
   ems<-parse_edgeMappings
   skipSpaces 
   char '}'
   skipSpaces
   return $ MorphismDef m_nm nms ems

loadMorphDefFrFile :: FilePath -> IO (Maybe MorphismDef)
loadMorphDefFrFile fn = do   
    contents <- readFile fn
    let m = parseMaybe parse_morphism contents
    return m

loadMorphism :: FilePath -> IO (Maybe (String, GrM String String))
loadMorphism fn = do
   m_def<-loadMorphDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   om <- if isNil m_def 
      then do
         putStrLn $ "Morphism definition of file '" ++fn++ "' could not be parsed"
         return (Nothing)
      else do
         let md = the m_def
         return(Just (morphDNm md, consGMFrD md))
   return om

test1 = do
   m<-loadMorphism "Tests/m_Employee_Car.gm"
   putStrLn $ show m

test2 = readP_to_S parse_edgeMappings "edges {\n\tA->B\n\tB->C\n}"
test3 = readP_to_S parse_morphism "Morphism A {\n nodes{A->B}\n edges {C->D\nD->E}}"
test4 = readP_to_S parse_morphism "Morphism M_Employee_Car {\n\tnodes {\n\t   Employee->Employee\n\t   Car->Car\n\t}\n\tedges {\n\t   Owns->Owns\n\t   ICar_Car->ICar_Car\n\t   IEmployee_Employee->IEmployee_Employee\n\t}\n}"
test5 = readP_to_S parse_morphism "Morphism F_MM_4 {\n\tnodes {\n\t\tOperatorVal->Attribute\n\t\tOpChoice->Attribute\n\t\tOpParallel->Attribute\n\t\tOpIf->Attribute\n\t\tOpInterleave->Attribute\n\t\tOpThrow->Attribute\n\t}\n\tedges {}\n}\n"

test6 = do
   contents <- readFile "PCs/F_MM_4.gm"
   putStrLn $ show contents

test7 = do
   contents <- readFile "IntoSysML/MM/F_B1.gm"
   putStrLn $ show contents
   return $ readP_to_S parse_morphism contents


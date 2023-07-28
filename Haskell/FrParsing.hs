module FrParsing (loadFragment, loadSG) where

import Sets ( set, singles, union, Set(..) )
import Relations
import Grs ( consG, unionGM )
import SGrs
import Frs ( consF, Fr )
import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many,empty)
import TheNil
import MyMaybe
import CommonParsing
import SGElemTys
import Mult
import PathExpressions
import Gr_Cls

-- Edge definition: optional name, source and a target nodes (Strings), edge type, two optional multiplicities, an optional path expression
data EdgeDef = EdgeDef String String String SGETy Mult Mult (Maybe (PE String String)) 
   deriving(Eq, Show)
data EdgeDep = EdgeDep String String
   deriving(Eq, Show)
-- A Node has a name and a type
data NodeDef = NodeDef String SGNTy 
   deriving(Eq, Show)
-- Enumeration cluster: a name and associated values
data ClEnum = ClEnum String [String]
   deriving(Eq, Show)
data SGElem = ElemN NodeDef | ElemE EdgeDef | ElemD EdgeDep | ElemClE ClEnum 
   deriving(Eq, Show)
data SGDef = SGDef String [SGElem] 
   deriving(Eq, Show)

--data Proxy = Proxy String String 
--   deriving(Eq, Show)
-- Certain nodes have a partial typing
--data InstanceOfN = InstanceOfN String String 
--   deriving(Eq, Show)
-- Certain edges have a partial typing
--data InstanceOfE = InstanceOfE String String 
--   deriving(Eq, Show)
-- Either: (i) a proxy reference indicating the node represented by the proxy
-- (ii) The partial type of a node
-- (iii) The partial type of an edge
data FrRef = Proxy String String | InstanceOfN String String | InstanceOfE String String
   deriving(Eq, Show)
-- A fragment definition has a name, a SG, and a list of proxy references
data FrDef = FrDef String SGDef [FrRef] 
   deriving(Eq, Show)

sgd_name :: SGDef -> String
sgd_name (SGDef nm _) = nm

frd_sg_def :: FrDef -> SGDef
frd_sg_def (FrDef _ sgd _) = sgd

frd_fname::FrDef->String
frd_fname (FrDef fnm _ _) = fnm

ext_mult_t::String->Mult->Rel String Mult
ext_mult_t e EmptyS = singles (e, singles (Sm $ Val 1))
ext_mult_t e m = singles (e, m)

ext_mult_s::String->Mult->Rel String Mult
ext_mult_s _ EmptyS = nil
ext_mult_s e m = singles (e, m)


extract_elem::SGElem->SGr String String
extract_elem (ElemN (NodeDef n nty)) = consSG (consG (singles n) nil nil nil) (singles (n, nty)) nil nil nil nil nil
extract_elem (ElemE (EdgeDef e s t ety m1 m2 pe)) = 
   let e' = nm_of_edge ety e s t in 
   let sm = ext_mult_s e' m1 in
   let tm = ext_mult_s e' m2 in
   let pei = if ety `elem` [Eder, Epath] then singles (e', the pe) else nil in
   consSG (consG (set [s, t]) (singles e') (singles (e', s)) (singles (e', t))) nil (singles (e', ety)) sm tm pei nil
   where nm_of_edge Einh _ s t = "EI" ++ s ++ "_" ++ t
         nm_of_edge _ enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)
extract_elem (ElemD (EdgeDep se te)) =  consSG empty nil nil nil nil nil (singles (nm_e se, nm_e te))
   where nm_e e = "E"++ e
extract_elem (ElemClE (ClEnum ne vs)) = 
   let f_nty = Set (ne, Nenum) (set $ map (\v->(v, Nval)) vs) in
   let f_ety = set (map (\v->("EI"++v, Einh)) vs) in
   consSG (consG (Set ne (set vs)) (set $ map (\v->"EI"++v) vs) (set $ map (\v->("EI"++v, v)) vs) (set $ map (\v->("EI"++v, ne)) vs)) f_nty f_ety nil nil nil nil

extract_sg::[SGElem]->SGr String String
extract_sg = foldl (\sg e-> sg `unionSG` (extract_elem e)) empty

--extract_sg ((ElemN (NodeDef n nty)):es) = (cons_sg (cons_g [n] [] [] []) [(n, nty)] [] [] []) `union_sg` (extract_sg es)
--extract_sg ((ElemE (EdgeDef e s t ety om1 om2)):es) = 
--   let e' = nm_of_edge ety e s t in 
--   let sm = ext_mult_s e' om1 in
--   let tm = ext_mult_s e' om2 in
--   (cons_sg (cons_g [s, t] [e'] [(e', s)] [(e', t)]) [] [(e', ety)] sm tm)  `union_sg` (extract_sg es)
--   where nm_of_edge Einh _ s t = "EI" ++ s ++ "_" ++ t
--         nm_of_edge _ enm s t = "E"++ (if null enm then s ++ "_" ++ t else enm)
--extract_sg ((ElemClE (ClEnum s v)):es) = 

cons_sg_fr_sgd::SGDef->SGr String String
cons_sg_fr_sgd (SGDef _ elems) = extract_sg elems

t_union :: (Eq a1, Eq a2, Eq a3) =>(Set a1, Set a2, Set a3)-> (Set a1, Set a2, Set a3) -> (Set a1, Set a2, Set a3)
t_union (e1a, e2a, e3a) (e1b, e2b, e3b) = (e1a `union` e1b, e2a `union` e2b, e3a `union` e3b)

edgId::String->String
edgId e = "E"++e

gProxyInfo::[FrRef]->(Set String, Rel String String, Rel String String)
gProxyInfo [] = (nil, nil, nil)
gProxyInfo ((Proxy p r):rs) = (singles . edgId $ p, singles (edgId p, p), singles (edgId p, r)) `t_union` (gProxyInfo rs)
gProxyInfo (_:rs) = gProxyInfo rs

gInstanceOfM::[FrRef]->GrM String String
gInstanceOfM [] = emptyGM
gInstanceOfM ((InstanceOfN n r):rs) = (consGM (singles (n, r)) nil) `unionGM` gInstanceOfM rs
gInstanceOfM ((InstanceOfE e r):rs) = (consGM nil (singles (edgId e, edgId r))) `unionGM` gInstanceOfM rs
gInstanceOfM (_:rs) = gInstanceOfM rs

cons_fr_fr_frd::FrDef->Fr String String
cons_fr_fr_frd (FrDef _ sgd rs ) = 
   let (esr, s, t) = gProxyInfo rs 
       et = gInstanceOfM rs in
   consF (cons_sg_fr_sgd sgd) esr s t et

parse_fin_node::SGNTy->ReadP NodeDef
parse_fin_node nty= do
   nm<-parse_id
   skipSpaces
   return (NodeDef nm nty)

parse_nodea::ReadP NodeDef
parse_nodea = do
   string "nodea"
   skipSpaces
   n<-parse_fin_node Nabst
   return n

parse_noden::ReadP NodeDef
parse_noden = do
   string "node"
   skipSpaces
   n<-parse_fin_node Nnrml
   return n

parse_proxy::ReadP NodeDef
parse_proxy = do
   string "proxy"
   skipSpaces
   n<-parse_fin_node Nprxy
   return n

parse_nvirt::ReadP NodeDef
parse_nvirt = do
   string "virtual"
   skipSpaces
   n<-parse_fin_node Nvirt
   return n

--parse_nopt::ReadP NodeDef
--parse_nopt = do
--   string "opt"
--   skipSpaces
--   n<-parse_fin_node Nopt
--   return n

parse_sg_node::ReadP NodeDef
parse_sg_node = do
   n<-parse_noden <|> parse_nodea <|> parse_proxy <|>  parse_nvirt 
-- <|> parse_nopt 
   return n

parse_edge_name::ReadP String
parse_edge_name = do
   nm<-(between (char '[') (char ']') parse_id) <++ (return "")
   return nm

parse_mult_many::ReadP MultVal
parse_mult_many = do
   char '*'
   return (Many)

parse_mult_val::ReadP MultVal
parse_mult_val = do
   n<-parse_number
   return (Val $ read n)

parse_smult::ReadP MultVal
parse_smult = do
   m<-parse_mult_many <|> parse_mult_val
   return m

parse_range_mult::ReadP MultC
parse_range_mult = do
   n<-parse_number
   skipSpaces
   string ".."
   skipSpaces
   m<-parse_smult
   skipSpaces
   return (Rm (read n) m)

parse_single_mult::ReadP MultC
parse_single_mult = do
   m<-parse_smult
   skipSpaces
   return (Sm m)

parse_multc::ReadP MultC
parse_multc = do
   m<-parse_range_mult <|> parse_single_mult
   return m

parse_mult::ReadP Mult
parse_mult = do
   ms<-sepBy (parse_multc) (char ',')
   return (set ms)   

parse_edge_info::ReadP(String, String, String)
parse_edge_info = do
   s<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   t<-parse_id
   skipSpaces
   enm<-parse_edge_name
   skipSpaces
   return (s, t, enm)


parse_rel_::SGETy->ReadP EdgeDef
parse_rel_ ek = do
   (s, t, e)<-parse_edge_info
   char ':'
   skipSpaces
   m1<-parse_mult
   skipSpaces
   char ';'
   skipSpaces
   m2<-parse_mult
   skipSpaces
   return (EdgeDef e s t ek m1 m2 Nothing)

parse_rel::ReadP EdgeDef
parse_rel = do
   string "rel"
   skipSpaces
   ed<-parse_rel_ (Erel Dbi)
   return ed

parse_opt_mult::ReadP Mult
parse_opt_mult = do
   char ':'
   skipSpaces
   m<-parse_mult
   return m

parse_rel_uni::SGETy->ReadP EdgeDef
parse_rel_uni ety = do
   (s, t, e)<-parse_edge_info
   m<-parse_opt_mult <++ return (singles $ Sm $ Val 1)
   skipSpaces
   return (EdgeDef e s t ety nil m Nothing)

parse_relu::ReadP EdgeDef
parse_relu = do
   string "relu"
   skipSpaces
   ed<-parse_rel_uni (Erel Duni)
   return ed

--parse_wander::ReadP EdgeDef
--parse_wander = do
--   string "wander"
--   skipSpaces
--   (s, t, e)<-parse_edge_info
--   return (EdgeDef e s t Ewander (singles msole_many) (singles msole_many) Nothing)


parse_PEA_nrml::ReadP (PEA String)
parse_PEA_nrml = do
   rn<-parse_id -- parses names of relation
   return (Edg $ "E" ++ rn)

parse_PEA_inv::ReadP (PEA String)
parse_PEA_inv = do
   rn<-parse_id -- parses names of relation
   char '~'
   return (Inv $ "E" ++ rn)   

parse_PEA::ReadP (PEA String)
parse_PEA = do
   pea <- parse_PEA_nrml <|> parse_PEA_inv 
   return pea

parse_PE_At::ReadP (PEC String String)
parse_PE_At = do
   pea <- parse_PEA
   skipSpaces
   return (At $ pea)

parse_PE_Dres::ReadP (PEC String String)
parse_PE_Dres = do
   s<-parse_id -- parses names of restricting set
   skipSpaces
   string "◁"
   skipSpaces
   pea<-parse_PEA -- parses names of relation
   skipSpaces
   return (Dres s pea)

parse_PE_Rres::ReadP (PEC String String)
parse_PE_Rres = do
   pea<-parse_PEA -- parses names of relation
   skipSpaces
   string "▷"
   skipSpaces
   s<-parse_id -- parses names of restricting set
   skipSpaces
   return (Rres pea s)

parse_PE_Smpl::ReadP (PEC String String)
parse_PE_Smpl= do
   pe <- parse_PE_At  <|> parse_PE_Dres  <|> parse_PE_Rres 
   return pe

parse_PE_Scmp::ReadP (PE String String)
parse_PE_Scmp = do
   pe1<-parse_PE_Smpl -- parses path expression
   skipSpaces
   string "⨾"
   skipSpaces
   pe2<-parse_PEa -- parses path expression
   skipSpaces
   return (SCmp pe1 pe2)

parse_PEa::ReadP (PE String String)
parse_PEa = do
   pe <- (fmap Ec parse_PE_Smpl) <|> parse_PE_Scmp
   return pe

parse_PE::ReadP (PE String String)
parse_PE = do
   string "<->"
   skipSpaces
   pe <- parse_PEa
   return pe

--parse_dedge_info::ReadP(String, String, String, String)
--parse_dedge_info = do
--   sn<-parse_id 
--   skipSpaces
--   string "->"
--   skipSpaces
--   tn<-parse_id
--   skipSpaces
--   char '['
--   skipSpaces
--   enm<-parse_id
--   skipSpaces
--   string ":"
--   skipSpaces
--   ed<-parse_id
--   skipSpaces
--   char ']'
--   skipSpaces
--   return (sn, tn, enm, ed)

parse_der::ReadP EdgeDef
parse_der = do
   string "derived"
   skipSpaces
   s<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   t<-parse_id
   skipSpaces
   char '['
   skipSpaces
   e<-parse_id
   skipSpaces
   pe<-parse_PE
   skipSpaces
   char ']'
   skipSpaces
   char ':'
   skipSpaces
   m1<-parse_mult
   skipSpaces
   char ';'
   skipSpaces
   m2<-parse_mult
   skipSpaces
   return (EdgeDef e s t Eder m1 m2 (Just pe))

parse_path::ReadP EdgeDef
parse_path = do
   string "path"
   skipSpaces
   s<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   t<-parse_id
   skipSpaces
   char '['
   skipSpaces
   e<-parse_id
   skipSpaces
   pe<-parse_PE
   skipSpaces
   char ']'
   skipSpaces
   return (EdgeDef e s t Epath nil nil (Just pe))

parse_compu::ReadP EdgeDef
parse_compu = do
   string "compu"
   skipSpaces
   ed<-parse_rel_uni (Ecomp Duni)
   return ed

parse_comp::ReadP EdgeDef
parse_comp = do
   string "comp"
   skipSpaces
   ed<-parse_rel_ (Ecomp Dbi)
   return ed

parse_inh::ReadP EdgeDef
parse_inh = do
   string "inh"
   skipSpaces
   sn<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   tn<-parse_id
   skipSpaces
   return (EdgeDef "" sn tn Einh nil nil Nothing)

parse_sg_edge::ReadP EdgeDef
parse_sg_edge = do
   e <- parse_rel <|> parse_relu  <|> parse_comp  <|> parse_compu  <|> parse_inh <|> parse_der <|> parse_path 
   return e

end_of_sep_term::ReadP ()
end_of_sep_term = do
   char ',' <|> char '\n'
   skipSpaces
   return ()

parse_enum::ReadP ClEnum
parse_enum = do
   string "enum"
   skipSpaces
   nm<-parse_id
   skipSpaces
   char ':'
   skipSpaces
   vals<-endBy (parse_id) (end_of_sep_term)
   skipSpaces
   return (ClEnum nm vals)

parse_edge_dep::ReadP EdgeDep
parse_edge_dep = do
   string "dependency"
   skipSpaces
   edg1<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   edg2<-parse_id
   skipSpaces
   return (EdgeDep edg1 edg2)

parse_sg_elemN::ReadP SGElem
parse_sg_elemN = do
   n<-parse_sg_node
   return (ElemN n)

parse_sg_elemE::ReadP SGElem
parse_sg_elemE = do
   e<-parse_sg_edge
   return (ElemE e)

parse_sg_enumE::ReadP SGElem
parse_sg_enumE = do
   e<-parse_enum
   return (ElemClE e)

parse_sg_ED::ReadP SGElem
parse_sg_ED = do
   e<-parse_edge_dep
   return (ElemD e)

parse_sg_elem::ReadP SGElem
parse_sg_elem = do
   skipSpaces
   e<-parse_sg_elemN <|> parse_sg_elemE <|> parse_sg_enumE <|> parse_sg_ED 
   return e

parse_sg::ReadP SGDef
parse_sg = do
   string "SG"
   skipSpaces
   sg_nm<-parse_id
   skipSpaces
   elems<-between (char '{') (char '}') (many parse_sg_elem) 
   return (SGDef sg_nm elems)

parseProxyRef::ReadP FrRef
parseProxyRef = do
   string "ref"
   skipSpaces
   pnm<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   nnm<-parse_id
   skipSpaces
   return (Proxy pnm nnm)

parseInstanceOfN::ReadP FrRef
parseInstanceOfN = do
   string "iON"
   skipSpaces
   nnm<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   tnnm<-parse_id
   skipSpaces
   return (InstanceOfN nnm tnnm)

parseInstanceOfE::ReadP FrRef
parseInstanceOfE = do
   string "iOE"
   skipSpaces
   enm<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   tenm<-parse_id
   skipSpaces
   return (InstanceOfE enm tenm)

parseFrRef::ReadP FrRef
parseFrRef = do
   r <- parseProxyRef <|> parseInstanceOfN  <|> parseInstanceOfE
   return r

parse_fr :: ReadP FrDef
parse_fr = do
   string "fragment"
   skipSpaces
   fnm<-parse_id
   skipSpaces
   char '{'
   skipSpaces
   sg<-parse_sg
   skipSpaces
   refs<-manyTill parseFrRef (char '}')
   return (FrDef fnm sg refs)

loadFrDefFrFile :: FilePath -> IO (Maybe FrDef)
loadFrDefFrFile fn = do   
    contents <- readFile fn
    let fr = parseMaybe parse_fr contents
    return fr

loadSGDefFrFile :: FilePath -> IO (Maybe SGDef)
loadSGDefFrFile fn = do   
    contents <- readFile fn
    let sg = parseMaybe parse_sg contents
    return sg

test_sg = "SG SG_Person1 {\n"
   ++ "node Person\n"
   ++ "node Hotel\n"
   ++ "node City\n"
   ++ "node Vehicle\n"
   ++ "rel Hotel->Person[Hosts]: 1,*\n"
   ++ "relu Person->City[lives]: 1\n"
   ++ "rel Person->Vehicle[Owns]:1,*\n"
   ++ "}"


loadFragment :: FilePath -> IO (Maybe (String, (Fr String String)))
loadFragment fn = do
   fr_def<-loadFrDefFrFile fn
   --return (toMaybeP (appl_f_M frd_fname fr_def) (appl_f_M cons_fr_fr_frd fr_def))
   ofr <- if isNil fr_def 
      then do
         putStrLn $ "Fragment definition of file " ++ (show fn) ++ " could not be parsed."
         return (Nothing)
      else do
         let frd = the fr_def
         return(Just (frd_fname frd,cons_fr_fr_frd frd)) -- This as a function here.
   return ofr 

loadSG :: FilePath -> IO (Maybe (String, SGr String String))
loadSG fn = do
   sg_def<-loadSGDefFrFile fn
   --return (toMaybeP (appl_f_M sgd_name sg_def) (appl_f_M cons_sg_fr_sgd sg_def))
   osg <- if isNil sg_def 
      then do
         putStrLn $ "SG definition of file " ++ (show fn) ++ " could not be parsed"
         return (Nothing)
      else do
         let sgd = the sg_def
         return(Just (sgd_name sgd, cons_sg_fr_sgd sgd))
   return osg

test1 :: IO ()
test1 = do
   fr<-loadFragment "Tests/f_Person1.fr"
   putStrLn $ show fr

test2 :: IO ()
test2 = do
   sg<-loadSG "Tests/SG_Employee_Car.sg"
   putStrLn $ show sg

test3 = readP_to_S parse_rel "rel Pet->POther[AnyRel1]: *,*"
test4 = readP_to_S parse_mult "4"
test5a = readP_to_S parse_PE "<-> Serves"
test5b = readP_to_S parse_PE "<-> Serves~"
test5c = readP_to_S parse_PE "<-> Serves⨾ HotelRoom_zone"
test5d = readP_to_S parse_PE "<-> Serves⨾ HotelRoom_zone~"
test5e = readP_to_S parse_PE "<-> Serves~⨾ HotelRoom_zone"
test5f = readP_to_S parse_PE "<-> Hosts ▷ Reptile⨾ Pet_status"
test6 :: [(EdgeDef, String)]
test6 = readP_to_S parse_der "derived Car->Wheel[HasWheels_1 <-> HasWheels]: 1,4"
test7 :: [(SGDef, String)]
test7 = readP_to_S parse_sg test_sg


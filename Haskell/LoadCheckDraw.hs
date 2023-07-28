
module LoadCheckDraw(
    load_def
    , draw_to_file
    , wrapSG
    , wrapG
    , unwrapG
    , unwrapSG
    , unwrapSGWithinP
    , draw_def
    , draw_mdl
    , loadSG
    , loadG
    , loadGwT
    , loadGwET
    , loadF
    , loadM
    , load_gfg_def
    , load_mdl_def
    , load_rm_cmdl_def
    , saveSGDrawing
    , saveFrDrawing
    , saveGDrawing
    , saveGwTDrawing
    , saveGFGDrawing
    , saveDrawingWithMdlFrs) 
where

import Gr_Cls ( emptyGM, GR(ns), GrM )
import GrParsing ( loadGraph )
import qualified GwTParsing as GwtP (loadGwT)
import qualified GwETParsing as GwetP (loadGwET)
import GFGrParsing ( loadGFG )
import GrsDraw
import SGsDraw
import FrsDraw
import GwTDraw ( wrGwTAsGraphviz )
import GwETDraw
import GFGrsDraw
import Grs 
import GFGrs 
import Frs 
import GrswT
import GrswET
import SGrs
import ParseUtils
import TheNil
import MyMaybe
import qualified FrParsing as FP (loadSG, loadFragment)
import Control.Monad(forM, forM_, when)
import MorphismParsing
import MdlDraw
import Mdls
import Relations

data GKind = Graph | SG | GwT | GwET | Fr | GFG
    deriving (Eq, Show)

type PossibleG a b = Either (Gr a b) (Either (SGr a b) (Either (GrwT a b) (Either (GrwET a b) (Either (Fr a b) (GFGr a b)))))
--    deriving (Eq, Show)

wrapG :: a -> Either a b
wrapG = Left 
wrapSG :: a1 -> Either a2 (Either a1 b)
wrapSG = Right . Left 
wrapGwT :: a1 -> Either a2 (Either a3 (Either a1 b))
wrapGwT = Right . Right . Left 
wrapGwET :: a1 -> Either a2 (Either a3 (Either a4 (Either a1 b)))
wrapGwET = Right . Right . Right . Left 
wrapFr :: a1 -> Either a2 (Either a3 (Either a4 (Either a5 (Either a1 b))))
wrapFr = Right . Right . Right . Right . Left
wrapGFG :: b -> Either a2 (Either a3 (Either a4 (Either a5 (Either a1 b))))
wrapGFG = Right . Right . Right . Right . Right 

pg_kind :: Either a1 (Either a2 (Either a3 (Either a4 (Either a5 b)))) -> GKind
pg_kind (Left _) = Graph
pg_kind (Right (Left _)) = SG
pg_kind (Right (Right (Left _))) = GwT
pg_kind (Right (Right (Right (Left _)))) = GwET
pg_kind (Right (Right (Right (Right (Left _))))) = Fr
pg_kind (Right (Right (Right (Right (Right _))))) = GFG

unwrapG :: Either a b -> a
unwrapG (Left g) = g
unwrapSG :: Either a1 (Either a2 b) -> a2
unwrapSG (Right (Left sg)) = sg
unwrapGwT :: Either a1 (Either a2 (Either a3 b)) -> a3
unwrapGwT (Right (Right (Left gwt))) = gwt
unwrapGwET :: Either a1 (Either a2 (Either a3 (Either a4 b))) -> a4
unwrapGwET (Right (Right (Right (Left gwet)))) = gwet
unwrapFr :: Either a1 (Either a2 (Either a3 (Either a4 (Either a5 b)))) -> a5
unwrapFr (Right (Right (Right (Right (Left fr))))) = fr
unwrapGFG :: Either a1 (Either a2 (Either a3 (Either a4 (Either a5 b)))) -> b
unwrapGFG (Right (Right (Right (Right (Right gfg))))) = gfg

unwrapGWithinP :: Maybe (a, Either b1 b2) -> (a, b1)
unwrapGWithinP (Just (nm, pg)) = (nm, unwrapG pg)
unwrapSGWithinP :: Maybe (a, Either a1 (Either b1 b2)) -> (a, b1)
unwrapSGWithinP (Just (nm, pg)) = (nm, unwrapSG pg)
unwrapGwTWithinP :: Maybe (a, Either a1 (Either a2 (Either b1 b2))) -> (a, b1)
unwrapGwTWithinP (Just (nm, pg)) = (nm, unwrapGwT pg)
unwrapGwETWithinP :: Maybe (a, Either a1 (Either a2 (Either a3 (Either b1 b2))))-> (a, b1)
unwrapGwETWithinP (Just (nm, pg)) = (nm, unwrapGwET pg)
unwrapFrWithinP :: Maybe (a, Either a1 (Either a2 (Either a3 (Either a4 (Either b1 b2)))))-> (a, b1)
unwrapFrWithinP (Just (nm, pg)) = (nm, unwrapFr pg)
unwrapGFGWithinP :: Maybe(a, Either a1 (Either a2 (Either a3 (Either a4 (Either a5 b)))))-> (a, b)
unwrapGFGWithinP (Just (nm, pg)) = (nm, unwrapGFG pg)

load_gen path fnm load wrap = do 
    o_g<-load $ path ++ fnm 
    if isSomething o_g
      then do 
        let Just (nm_g, g) = o_g
        return $ Just (nm_g, wrap g)
      else return Nothing

def_kind :: String -> GKind
def_kind fnm =
    let (_, ext) = splitAtStr "." fnm in
    case ext of
        "g" -> Graph
        "sg" -> SG
        "gwt" -> GwT
        "gwet" -> GwET
        "fr" -> Fr
        "gfg" -> GFG

load_def path fnm = do
    d<-case (def_kind fnm) of
        Graph -> load_gen path fnm loadGraph wrapG
        SG -> load_gen path fnm FP.loadSG wrapSG
        GwT -> load_gen path fnm GwtP.loadGwT wrapGwT
        GwET -> load_gen path fnm GwetP.loadGwET wrapGwET
        Fr -> load_gen path fnm FP.loadFragment wrapFr
        GFG -> load_gen path fnm loadGFG wrapGFG
    return d

loadSG::FilePath->String->IO(String, SGr String String)
loadSG path fnm = do 
    d<- load_def path fnm
    let (nm, sg) = unwrapSGWithinP d
    return (nm, sg)

loadG :: FilePath -> String -> IO (String, Gr String String)
loadG path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapGWithinP d
    return (nm, g)

loadGwT :: FilePath ->String -> IO (String, GrwT String String)
loadGwT path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapGwTWithinP d
    return (nm, g)

loadGwET :: FilePath ->String -> IO (String, GrwET String String)
loadGwET path fnm = do 
    d<- load_def path fnm
    let (nm, g) = unwrapGwETWithinP d
    return (nm, g)

loadF::FilePath ->String ->IO (String, Fr String String)
loadF path fnm = do 
    d<- load_def path fnm
    let (nm, f) = unwrapFrWithinP d
    return (nm, f)

load_gfg_def :: String -> String -> IO (String, GFGr String String)
load_gfg_def path fnm = do 
    d<- load_def path fnm
    return (unwrapGFGWithinP d)

load_mdl_def path nm = do 
    (_, gfg)<-load_gfg_def path (nm ++ ".gfg")
    fd <- forM (ns gfg) (\fn-> do
        (_, f)<-loadF path (fn ++ ".fr")
        return (fn, f))
    return $ consMdl gfg fd

load_rm_cmdl_def path nm = do 
    (_, gfg)<-load_gfg_def path (nm ++ ".gfg")
    mds <- forM (ns gfg) (\fn-> do
        (_,m)<-loadM path (fn ++ ".gm")
        return m)
    return $ unionGMs mds

loadM :: String -> String -> IO (String, GrM String String)
loadM path fnm = do
    om1<-loadMorphism $ path ++ fnm
    return (the om1)

draw_def :: String -> String -> String -> IO ()
draw_def dpath ipath fnm = do
    d<-load_def dpath fnm 
    when (isSomething d) $ do
        let (nm, pg) = the d
        draw_to_file ipath nm pg

draw_to_file::String->String->PossibleG String String->IO()
draw_to_file path nm pg = do
    case (pg_kind pg) of
        Graph->saveGDrawing path nm $ unwrapG pg
        SG->saveSGDrawing path nm $ unwrapSG pg
        GwT->saveGwTDrawing path nm $ unwrapGwT pg
        GwET->saveGwETDrawing path nm $ unwrapGwET pg
        Fr->saveFrDrawing path nm $ unwrapFr pg
        GFG->saveGFGDrawing path nm $ unwrapGFG pg

draw_mdl :: String -> String -> String -> IO ()
draw_mdl dpath ipath mnm = do
    mdl<-load_mdl_def dpath mnm
    saveGFGDrawing ipath (mnm ++ "_gfg") (mgfg mdl)
    forM_ (ns . mgfg $ mdl) (\fn-> do 
        saveFrDrawing ipath (fn) $ appl (mfd mdl) fn)
    let ufs = mufs mdl
    saveFrDrawing ipath (mnm ++ "_uf") ufs
    let rf = reso_m mdl
    saveFrDrawing ipath (mnm ++ "_rf") rf
    saveDrawingWithMdlFrs ipath mnm  mdl

saveSGDrawing path nm sg = do
   putStrLn "Writing the GraphViz file" 
   let draw_src = wrSGGraphvizDesc nm StandAlone (consSGDrawingDesc sg emptyGM)
   writeFile (path ++ nm ++ ".gv") draw_src

-- checkAndSaveSGDraw path nm sg t = do
--    let errs = check_wf nm (Just t) sg
--    if errs == nile
--      then saveSGDrawing path nm sg
--      else putStrLn $ show_err errs

saveFrDrawing :: String -> String -> Fr String String -> IO ()
saveFrDrawing path nm f = do
   putStrLn "Writing GraphViz file" 
   let draw_src = wrFrGraphvizDesc StandAlone (consFrDrawingDesc nm f) 
   writeFile (path ++ nm ++ ".gv") draw_src

saveGDrawing :: GR g => String -> String -> g String String -> IO ()
saveGDrawing path nm g = do
   putStrLn "Writing the graph's GraphViz file..." 
   let draw_src = wrGAsGraphviz nm g
   writeFile (path ++ nm ++ ".gv") draw_src

saveGwTDrawing::String->String->GrwT String String->IO ()
saveGwTDrawing path nm gwt = do
   putStrLn "Writing the graph's GraphViz file..." 
   let draw_src = wrGwTAsGraphviz nm gwt
   writeFile (path ++ nm ++ ".gv") draw_src

saveGwETDrawing::String->String->GrwET String String->IO ()
saveGwETDrawing path nm gwet = do 
   putStrLn "Writing the graph's GraphViz file..." 
   let draw_src = wrGwETAsGraphviz nm gwet
   writeFile (path ++ nm ++ ".gv") draw_src

saveGFGDrawing::(GR g, Eq a)=>[Char] ->String ->g String a -> IO ()
saveGFGDrawing path nm gfg = do
   putStrLn "Writing GraphViz file" 
   let draw_src = wrGFGAsGraphviz nm gfg 
   writeFile (path ++ nm ++ ".gv") draw_src

saveDrawingWithMdlFrs path nm mdl = do
   let draw_src = wrMdlAsGraphviz nm mdl
   writeFile (path ++ nm ++ "_Mdl.gv") draw_src
---------------------------------------
-- Project: PCs/Fragmenta
-- Module: PCTrees (PCTs)
-- Description: Handles representation of PCs as PCTs, a recursive datatype representation of abstract syntax
-- Author: Nuno Amálio
-------------------------------------
module PCs.PCTrees
  ( PT(..)
  , TOp(..)
  , PCTD(..)
  , PCTTypeD(..)
  , withinRel
  , consPCTD
  , atomsOfCPTs
  , atomsOfPTs
  , show_pctd
  , isOperator
  , isAtom
  ) 
  where

import PCs.PCs
import Gr_Cls
import Grs
import GrswT
import Sets
import Relations
import TheNil
import MyMaybe
import PCs.MM_Names
import ShowUtils
import ParseUtils
import PCs.TxtExpAST
import PCs.PCTreesAST 
  ( read_pctty
  , read_opctty
  , cParam
  , PT(..)
  , TOp(..)
  , PCTD(..)
  , DTDef(..)
  , ROp(..)
  , PCTTypeD(..)
  , Param(..)
  , VTerm(..)
  , gPTs
  )
import MMI
import SimpleFuns 
  (butLast
  , pairUp
  )
import PCs.Common
   (Id
   )
--import PCs.PCTrees_Exp
--import PCs.ParsingPCTxtExp2
import PCs.ParsingTxtExp
import SimpleFuns

opseqC :: TOp
opseqC = OpSeq False
opseqO :: TOp
opseqO = OpSeq True

--rearrangeT :: PT -> PD
--rearrangeT (OpB opseqC (Kappa (PD k ps cts t1)) t2) = PD k ps nil (OpB opseqC (Kappa (PD (k++"0") nil cts t1)) t2)
--rearrangeT (Kappa pd) = pd

show_top :: TOp -> String
show_top OpExtChoice = "◻︎"
show_top OpIntChoice = "⊓"
show_top (OpSeq o) = (if o then "O" else "") ++  "⇥"
show_top (OpParallel ps) = "∥" ++ (show ps)
show_top (OpInterleave) = "⦀"
show_top (OpThrow ps) = "𝛩" ++ (show ps)
show_top (OpIf g) = "𝜄" ++ (showExp g)

--show_pt :: PT -> String
--show_pt (Kappa id ps cpds pt) =  "𝜅 " ++ id ++ (show_params ps) ++ "{" ++ (show_pds cpds)++ "} @ " ++ (show_pt pt)

--show_pts :: Foldable t => t Pt -> String
--show_pts pts = 
--  if null pts then "" else (foldr (\pt pts'->(show_pt pt) ++ finish pts') "" pts) 
--  where finish pts_ =  if null pts_ then "" else "∙\n   " ++ pts_ 

show_params :: (Foldable t, Functor t) => t Param -> String
show_params ps = 
  if null ps then "" else "(" ++ (showStrs (fmap show ps) ",") ++ ")" 

--show_binding :: Foldable t => (t String) -> String
--show_binding bs = if null bs then "" else "(" ++ (showStrs bs ",") ++ ")"

showPCExps::(Foldable t, Functor t) => t Exp -> String
showPCExps es = if null es then "" else "(" ++ showStrs (fmap showExp es) "," ++ ")"

--show_bindings :: Foldable t => (t PCExp) -> String
--show_bindings bss = if null bss then "" else "(" ++ showStrs bss "," ++ ")"

--if null bss then "" else "(" ++ foldr (\bs s-> (show_binding bs) ++ s) nil bss ++ ")"

show_renamings :: Foldable t => t (String, String) -> String
show_renamings rs = if null rs then "" else "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧"

show_guard :: Maybe Exp -> String
show_guard oe = if isNil oe then "" else " {" ++ (showExp $ the oe) ++ "}"

show_bop0::String->PCTTypeD->String
show_bop0 id td = id ++ ":" ++ (show td)

show_bop::ROp->String
show_bop (OpRExtChoice v td) = "◻︎" ++ (show_bop0 v td)
show_bop (OpRIntChoice v td) = "⊓" ++ (show_bop0 v td)

show_pt :: PT -> String
show_pt (Atom e og) = "𝛼 " ++ showExp e ++ (show_guard og)
show_pt (Kappa id ps cpts pt) =  "𝜅 " ++ id ++ (show_params ps) ++ "{" ++ (show_pts cpts) ++ "} @ " ++ (show_pt pt)
show_pt (OpKappa id bop pt) = "𝛾𝜅 " ++ id ++ (show_bop bop) ++ " @ " ++ (show_pt pt)
show_pt (OpB op pt1 pt2) = "(𝛾 " ++ show_top op ++ ")" ++ (show_pt pt1) ++ " [" ++ (show_pt pt2) ++ "]"
show_pt (Rho id og es rs) = "𝜌 " ++ id ++ (showPCExps es) ++ (show_renamings rs) ++ (show_guard og)
show_pt NilT = "𝜑"
show_pt StopT = "𝛉"
show_pt SkipT = "𝜉"

--show_pts :: [PT] -> String
--show_pts = foldr (\pt s->show_pt pt  ++ "∙" ++ s) ""

show_pts :: Foldable t => t PT -> String
show_pts pts = 
  if null pts then "" else (foldr (\pt pts'->(show_pt pt) ++ finish pts') "" pts) 
  where finish pts_ =  if null pts_ then "" else "∙\n   " ++ pts_ 

show_vt::VTerm->String
show_vt (VTerm id tds) =  id ++ foldr (\td s->"."  ++ show td ++ s) "" tds

show_dt::DTDef->String
show_dt (DTDef id ts) = "𝛅 " ++ id ++ "{" ++ (foldl (\s vt->show_vt vt ++ (if null s then "" else ", ") ++ s) "" ts) ++ "}"

-- Shows the data items
show_dts::[DTDef]->String
show_dts = foldr (\d s->show_dt d ++ "\n" ++ s) "" 

show_pctd :: PCTD -> String
show_pctd (PCTD id ds pts) = "PC " ++ id ++ "\n" ++ show_dts ds ++ (show_pts pts)

andThenO :: Eq a => (PT, Set a, Set a) -> (PT,[PT], Set a, Set a) -> (PT, [PT], Set a, Set a)
andThenO (t, urs, gks) (t', pts, urs', gks') = (OpB opseqO t t', pts, urs `union` urs', gks `union` gks')

andThenC :: Eq a => (PT, Set a, Set a) -> (PT, [PT], Set a, Set a) -> (PT, [PT], Set a, Set a)
andThenC (t, urs, gks) (t', pts, urs', gks') = (OpB opseqC t t', pts, urs `union` urs', gks `union` gks')

andAfter :: Eq a => (PT, Set a, Set a) -> (PT, [PT], Set a, Set a) -> (PT, Set a, Set a)
andAfter (Kappa k ps cts pt0, urs, gks) (pt', pts, urs', gks') = 
  let nid = k++"0" 
      pt1 = Rho nid Nothing nil nil in 
  (Kappa k ps (((Kappa nid nil nil pt0):cts)++pts) (OpB opseqC pt1 pt'), urs `union` urs', gks `union` gks')
  --(OpB opseqC t t', rs `union` rs', gcs `union` gcs')

--rearrangeT :: PT -> PD
--rearrangeT (OpB opseqC (Kappa (PD k ps cts t1)) t2) = PD k ps nil (OpB opseqC (Kappa (PD (k++"0") nil cts t1)) t2)
--rearrangeT (Kappa pd) = pd

withOp :: Eq a => (PT, [PT], Set a, Set a) -> (TOp, (PT, [PT], Set a, Set a)) -> (PT, [PT], Set a, Set a)
withOp (pt, pts, urs, gps) (op, (pt', pts', urs', gps')) = 
  if pt' == NilT then (pt, pts, urs, gps) else (OpB op pt pt', pts++pts', urs `union` urs', gps `union` gps')

toTOp :: PCs_CMM_Ns -> Maybe Exp -> [Exp] -> TOp
toTOp CMM_VOpExtChoice _ _= OpExtChoice
toTOp CMM_VOpIntChoice _ _= OpIntChoice
toTOp CMM_VOpParallel _ bs = OpParallel bs
toTOp CMM_VOpInterleave _ _ = OpInterleave
toTOp CMM_VOpThrow _ ps = OpThrow ps
toTOp CMM_VOpIf og _ = OpIf (the og)


--Creates an atom leaf
leafA::PC String String->Id->(PT, Set Id, Set Id)
leafA pc n = 
   let e = parse $ expOfAtom pc n
       gs = str_of_ostr $ guardOf pc n
       og = if isNil gs then Nothing else Just . parse $ gs in
   (Atom e og, nil, nil)

openACOf :: MMI String String -> GrwT String String -> String -> Bool
openACOf mmi pc n = 
  let ac = nextAfterC mmi pc n in
  isSomething ac && openAC pc (the ac)

atomPT::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, [PT], Set Id, Set Id)
atomPT mmi pc r n gks = 
    let t1 = leafA pc n 
        t2 = optPT mmi pc r (nextAfterN mmi pc n) gks in
    if openACOf mmi pc n then t1 `andThenO` t2 else t1 `andThenC` t2

bOpOf::String->String->PCTTypeD->ROp
bOpOf op v td = opOf op v td
  where opOf "VOpChoice" = OpRExtChoice
        opOf "VOpIntChoice" = OpRIntChoice

-- Handles processes combined with replicated operators
combinedPr::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, [PT], Set Id, Set Id)
combinedPr mmi pc r n gps =
  let (t, pts, urs, gps2) = consPT mmi pc r (quantifiedOpStart mmi pc n) (gunion [singles n, gps]) 
      (v, etd) = varBQuantifiedOp pc n 
      td = read_ty (expOf pc (gCRSG mmi) etd) in  
  (OpKappa  n (bOpOf (opQuantifiedOp (gCRSG mmi)  pc n) (butLast v) td) t, pts, urs, gunion [singles n, gps, gps2])
  where read_ty "Int" = Int
        read_ty "Bool" = Bool
        read_ty s = DT s

process::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
process mmi pc r n gks = 
  let gks1 = n `intoSet` gks
      (t, pds, urs, gks2) = consPT mmi pc r (the $ processStart mmi pc n) gks1 
      ps = fmap (\(id, t)->cParam id (read_opctty t)) $ paramsOf pc n in
  (Kappa n ps pds t, urs, gunion [gks1, gks2])

-- atque is latin for and then
atque :: Eq a => (PT, Set a, Set a) -> (PT, [PT], Set a, Set a) -> (PT, Set a, Set a)
atque (pt, urs, gks) (pt', pts, urs', gks') = 
  if pt' == NilT then (pt, urs, gks) else (pt, urs, gks) `andAfter` (pt', pts, urs', gks')

prPT::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
prPT mmi pc r n gks =
  (process mmi pc r n gks) `atque` (optPT mmi pc r (nextAfterN mmi pc n) (n `intoSet` gks))

--cWUnionAt4::Eq d=>(Set d)->(a, b, c, Set d)->(a, b, c, Set d)
--cWUnionAt4 w (x, y, z, w')  = (x, y, z, w `union` w')

refOrPr::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, [PT], Set Id, Set Id)
refOrPr mmi pc r n gps 
    | n `elem` gps = (Rho n Nothing nil nil, [], nil, nil)
    | isNodeOfTys n [CMM_Quantification] (gCRSG mmi) pc = 
      let (pt, pts, urs, gps') = combinedPr mmi pc r n gps in (pt, pts, urs, gps `union` gps')   
    | otherwise = let (pt, urs, gps') = prPT mmi pc r n gps in (Rho n Nothing nil nil, [pt], urs, gps `union` gps')

refLeaf :: MMI String String -> PC String String -> Id ->Set Id -> (PT, Set Id, Set Id)
refLeaf mmi pc n gks = 
  let rn = nmOfRefP mmi pc n 
      urs = if rn `elem` gks || not (isNodeOfTys rn [CMM_Process] (gCRSG mmi) pc) then nil else singles rn 
      gs = guardOfOp mmi pc n in
  (Rho rn (if isNil gs then Nothing else Just . parse . the $ gs) (fmap parse (expsOfRef mmi pc n)) (renamingsOf pc n), urs, nil)

andThen:: Eq a => (PT, Set a, Set a) -> (PT, [PT], Set a, Set a) -> (PT, [PT], Set a, Set a)
andThen (t, urs, gks) (t', pts, urs', gks') = 
  if t' == NilT then (t, [], urs, gks) else (OpB opseqC t t', pts, urs `union` urs', gks `union` gks')

refPT :: MMI String String -> PC String String -> Rel Id Id->Id -> Set Id -> (PT, [PT], Set Id, Set Id)
refPT mmi pc r n gps = 
   if innerRef pc n then doInnerRef else (refLeaf mmi pc n gps) `andThen` optPT mmi pc r (nextAfterN mmi pc n) gps
   where doInnerRef = 
            let n' = nmOfRefP mmi pc n 
                (pt, urs, gps') = refLeaf mmi pc n gps in 
            if n' `elem` gps then (pt, [], nil, gps `union` gps') 
            else let (pt', urs', gps'') = prPT mmi pc r n' gps in (pt, [pt'], urs', gunion [gps, gps', gps'', set1 n'])

-- PT constructor for operators
opPT::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, [PT], Set Id, Set Id)
opPT mmi pc r n gks = 
   let gs = guardOfOp mmi pc n 
       og = if isNil gs then Nothing else Just . parse . the $ gs
       es = fmap (parse) (expsOf pc n) in
   opPTs mmi pc r (toTOp (read_cmm $ opValOfOp (gCRSG mmi) pc n) og es) (branchesOfOp mmi pc n) gks

-- PT constructor for optionals
optPT::MMI String String->PC String String->Rel Id Id->Maybe Id->Set Id->(PT, [PT], Set Id, Set Id)
optPT mmi pc r on gks
   | isNil on = (NilT, nil, nil, nil) 
   | otherwise = consPT mmi pc r (the on) gks

-- General PT constructor
consPT::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, [PT], Set Id, Set Id)
consPT mmi pc r n gks 
    | isNodeOfTys n [CMM_Atom] (gCRSG mmi) pc = atomPT mmi pc r n gks
    | isNodeOfTys n [CMM_Process] (gCRSG mmi) pc = refOrPr mmi pc r n gks
    | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc = refPT mmi pc r n gks
    | isNodeOfTys n [CMM_Quantification] (gCRSG mmi) pc = refOrPr mmi pc r n gks
    | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = opPT mmi pc r n gks 
    | isNodeOfTys n [CMM_Stop] (gCRSG mmi) pc = (StopT, [], nil, nil)
    | isNodeOfTys n [CMM_Skip] (gCRSG mmi) pc = (SkipT, [], nil, nil)


opPTs::MMI String String->PC String String->Rel Id Id->TOp->Set Id->Set Id->(PT, [PT], Set Id, Set Id)
opPTs _ _ _ _ EmptyS _ = (NilT, nil, nil, nil)
opPTs mmi pc r op (Set b bs) gps = 
   let n = the $ nextNode mmi pc b
       (pt, pts, urs, gps') = consPT mmi pc r n gps in
   (pt, pts, urs, gps') `withOp`  (op, opPTs mmi pc r op bs $ gps' `union` gps)

seqPTs::MMI String String->PC String String->Rel Id Id->Set Id->Set Id->([PT], Set Id)
seqPTs _ _ _ EmptyS gps = (nil, gps)
seqPTs mmi pc r (Set n ns) gps  
    | n `elem` gps = seqPTs mmi pc r ns gps
    | otherwise = 
        let (pt, urs, gps1) = prPT mmi pc r n gps 
            (pts, gps2) = seqPTs mmi pc r (ns `union` urs `sminus` gps1) (gps `union` gps1) in 
        (pt:pts, gunion [gps, gps1, gps2])
    
consDef::PC String String->String->DTDef
consDef pc n = 
  DTDef (nmOfNamed pc n) $ split_ts (enumTermsOf pc n)
  where split_ts (Set t EmptyS) = [split_t t]
        split_ts (Set t ts) = (split_t t:split_ts ts)
        split_t t = let (s1, s2) = splitAtStr "." t in VTerm s1 (split' s2) 
        split' [] = []
        split' s = let (s1, s2) = splitAtStr "." s in (read_pctty s1):split' s2

-- Constructs a PCTD from a single PC
toPCTD::MMI String String->PC String String->PCTD
toPCTD mmi pc = 
  let r = relKs mmi pc
      ds = foldr (\d ds'->consDef pc d:ds') [] (ntyNsPC (gCRSG mmi) pc CMM_Definition)
      (pts, _) = seqPTs mmi pc r (set1 $ startNode mmi pc) nil in 
  PCTD (getPCName pc) ds pts

-- Constructs a PCTD from a PCs model
consPCTD::MMI String String->PC String String->[PC String String]->PCTD
consPCTD mmi pc ipcs = 
   let pts' = toPTs ipcs 
       PCTD id ds pts = toPCTD mmi pc in
   PCTD id ds (pts'++pts)
   where toPTs [] = []
         toPTs (pc:pcs) = (toPTs pcs) ++ (gPTs $ toPCTD mmi pc)

-- Need to make more general here in the future
revname :: Exp -> Id -> Id -> Exp
revname e@(ExpId id) k p = if id == k then ExpId p else e
revname e@(ExpDot (ExpId id) e') k p = if id == k then ExpDot (ExpId p) e' else e
revname e _ _ = e

rename :: PT -> Id -> Id -> PT
rename (Atom e og) k p = Atom (revname e k p) og
rename (OpB op t1 t2) k p = OpB op (rename t1 k p) (rename t2 k p)
rename pct _ _ = pct

rename_pd:: PT -> Id -> Id -> PT
rename_pd (Kappa nm ps cpds t) k p = Kappa nm ps (foldr (\pd pds->(rename_pd pd k p):pds) [] cpds) (rename t k p)

within :: PT -> Set Id
within (Atom e _) = atomsOfExp e
within (OpB _ t1 t2) = (within t1) `union` (within t2)
--within (Kappa nm _ cts t) = foldr (\ct wcts->(within ct) `union` wcts) nil cts `union` (singles nm) `union` (within t)
within (Rho _ _ _ _) = nil
within NilT = nil
within StopT = nil
within SkipT = nil

relWithinRel_pds :: [PT] -> Rel Id Id
relWithinRel_pds = foldr (\pd r->(relWithin pd) `union` r) nil

relWithinRel :: Id -> PT -> Rel Id Id
relWithinRel nc (Atom e _) = foldr (\a r-> pairUp nc a `intoSet` r) nil (atomsOfExp e)
relWithinRel nc (OpB _ t1 t2) =  (relWithinRel nc t1) `union` (relWithinRel nc t2)
--relWithinRel nc (Kappa nm _ cts t) = singles (nc, nm) `union` (relWithinRel_pts cts) `union` (relWithin t)
relWithinRel _ (Rho _ _ _ _) = nil
relWithinRel _ NilT = nil
relWithinRel _ StopT = nil
relWithinRel _ SkipT = nil

relWithin :: PT -> Rel Id Id
relWithin (Kappa nm _ cpds pt) = (relWithinRel_pds cpds) `union` relWithinRel nm pt

atomsPCTD :: PCTD ->Set Id
atomsPCTD (PCTD _ _ pts) = atomsOfCPTs pts

atomsOfCPTs :: Foldable t=>t PT ->Set Id
atomsOfCPTs = foldr (\pt s ->atomsOfPT pt `union` s) nil

atomsOfPTs :: PT -> PT ->Set Id
atomsOfPTs t1 t2 = atomsOfPT t1 `union` atomsOfPT t2

atomsOfExp::Exp->Set Id
atomsOfExp (ExpId id)    = singles id
atomsOfExp (ExpDot e1 _) = atomsOfExp e1
atomsOfExp _             = nil

atomsOfPT :: PT ->Set Id
atomsOfPT (Atom e _)               = atomsOfExp e
atomsOfPT (OpB (OpThrow as) t1 t2) = gunion (fmap atomsOfExp as) `union` atomsOfPTs t1 t2
atomsOfPT (OpB _ t1 t2)            = atomsOfPTs t1 t2
atomsOfPT (OpKappa _ _ t)          = atomsOfPT t
atomsOfPT (Kappa _ _ cts t)        = foldr (\ct ps->(atomsOfPT ct) `union` ps) nil cts `union` (atomsOfPT t)
atomsOfPT (Rho _ _ _ rs)           = foldr (\(_, to) ps->(singles to) `union` ps) nil rs
atomsOfPT NilT                     = nil
atomsOfPT  StopT                   = nil
atomsOfPT  SkipT                   = nil

isOperator :: PT -> Bool
isOperator (OpB _ _ _) = True
isOperator _ = False

isAtomic :: PT -> Bool
isAtomic (Atom _ _) = True
isAtomic (Kappa {}) = True
isAtomic NilT = True
isAtomic StopT = True
isAtomic SkipT = True
isAtomic (Rho _ _ _ _) = True
isAtomic (OpB (OpSeq _) t NilT) = isAtom t
isAtomic _ = False

--isSole :: PT -> Bool
--isSole (Atom _ _) = True
--isSole (Kappa _) = True
--isSole (OpB _ t1 _) = isAtomic t1 
--isSole NilT = True
--isSole StopT = True
--isSole SkipT = True
--isSole (Rho _ _ _ _) = True


--isAtomAny :: PCT -> Bool
--isAtomAny (Atom _ _) = isSomething as
--isAtomAny _ = False

isAtom :: PT -> Bool
isAtom (Atom _ _) = True
isAtom _ = False

-- iKs0::PT->Set Id
-- iKs0 (Atom {}) = nil
-- iKs0 (StopT) = nil
-- iKs0 (SkipT) = nil
-- iKs0 NilT = nil
-- iKs0 (OpB _ t1 t2) = iKs t1 `union` iKs t2
-- iKs0 (OpKappa _ _ t) = iKs t
-- iKs0 (Kappa id _ cts t) = set1 id `union` iKs t `union` gunion (fmap iKs cts)
-- iKs0 (Rho id _ _ _) = set1 id

-- iKs::PT->Set Id
-- iKs (Atom {}) = nil
-- iKs (StopT) = nil
-- iKs (SkipT) = nil
-- iKs NilT = nil
-- iKs (OpB _ t1 t2) = iKs0 t1 `union` iKs0 t2
-- iKs (OpKappa _ _ t) = iKs0 t
-- iKs (Kappa id _ cts t) = iKs0 t `union` gunion (fmap iKs0 cts)
-- iKs t@(Rho id _ _ _) = iKs0 t
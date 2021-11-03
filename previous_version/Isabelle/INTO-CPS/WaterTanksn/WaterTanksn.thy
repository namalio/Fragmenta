
(********  
  Description: Theory that defines the WaterTanksn PDG
  Author:      Nuno Amálio
***********)


theory WaterTanksn
imports "../Base/PDGs" "../../Fragmenta/Fragmenta_GraphsL" "../Base/My_Str"

begin
definition G_BaseWTsn :: "PDGr"
where
   "G_BaseWTsn \<equiv> \<lparr>NsG=[''sw'', ''cwli'', ''cvo'', ''dwi''], 
   EsG = [''e_cwli_cvo''], 
   srcG = [(''e_cwli_cvo'', ''cwli'')], 
   tgtG=[(''e_cwli_cvo'', ''cvo'')]\<rparr>"

definition G_ConnectorToBase:: "nat \<Rightarrow> PDGr"
where
  "G_ConnectorToBase n \<equiv> (if n = 0 then emptyGL
    else 
      \<lparr>NsG=[''t''@(str_nat n)@''wlo'', ''t''@(str_nat n)@''vi''], 
      EsG = [''e_sw_t''@(str_nat n)@''wi'',
        ''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wlo'', 
        ''e_t''@(str_nat n)@''wo_dwi'', 
        ''e_t''@(str_nat n)@''wlo_cwli'', 
        ''e_cvo_t''@(str_nat n)@''vi'', 
        ''e_t''@(str_nat n)@''vi_t''@(str_nat n)@''wo''], 
      srcG = [(''e_sw_t''@(str_nat n)@''wi'', ''sw''), 
        (''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wlo'',''t''@(str_nat n)@''wi'' ),
        (''e_t''@(str_nat n)@''wo_dwi'', ''t''@(str_nat n)@''wo''), 
        (''e_t''@(str_nat n)@''wlo_cwli'', ''t''@(str_nat n)@''wlo''), 
        (''e_cvo_t''@(str_nat n)@''vi'', ''cvo''), 
        (''e_t''@(str_nat n)@''vi_t''@(str_nat n)@''wo'', ''t''@(str_nat n)@''vi'')], 
      tgtG=[(''e_sw_t''@(str_nat n)@''wi'', ''t''@(str_nat n)@''wi''),
        (''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wlo'',''t''@(str_nat n)@''wlo'' ),
        (''e_t''@(str_nat n)@''wo_dwi'', ''dwi''), 
        (''e_t''@(str_nat n)@''wlo_cwli'', ''cwli''), 
        (''e_cvo_t''@(str_nat n)@''vi'', ''t''@(str_nat n)@''vi''), 
        (''e_t''@(str_nat n)@''vi_t''@(str_nat n)@''wo'', ''t''@(str_nat n)@''wo'')]\<rparr>)"

definition G_DrainToTankOne :: "PDGr"
where
  "G_DrainToTankOne \<equiv>  \<lparr>NsG=[''dwo''],
      EsG = [''e_dwi_dwo'', ''e_dwo_t1wi''],
      srcG = [(''e_dwi_dwo'', ''dwi''), (''e_dwo_t1wi'', ''dwo'')],
      tgtG = [(''e_dwi_dwo'', ''dwo''), (''e_dwo_t1wi'', ''t1wi'')]\<rparr>"

definition connectToBase:: "nat \<Rightarrow> PDGr"
where
  "connectToBase n \<equiv> consUG G_BaseWTsn (G_ConnectorToBase n)"

definition connectToBase_loop:: "nat \<Rightarrow> PDGr"
where
  "connectToBase_loop n \<equiv> consUG (connectToBase n) (G_DrainToTankOne)"

(*definition connectInflowToTankn:: "nat\<Rightarrow>PDGr"
where
  "connectInflowToTankn n = \<lparr>NsG=[], EsG = [''e_iwout_t''@(str_nat n)@''win''],
    srcG = [(''e_iwout_t''@(str_nat n)@''win'', ''iwout'')],
    tgtG = [(''e_iwout_t''@(str_nat n)@''win'', ''t''@(str_nat n)@''win'')]\<rparr>" *)

definition consTankN:: "nat \<Rightarrow> PDGr"
where 
  "consTankN n \<equiv> \<lparr>NsG=[''t''@(str_nat n)@''wi'', ''t''@(str_nat n)@''wo''],
    EsG=[''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wo''],
    srcG = [(''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wo'', ''t''@(str_nat n)@''wi'')],
    tgtG = [(''e_t''@(str_nat n)@''wi_t''@(str_nat n)@''wo'', ''t''@(str_nat n)@''wo'')]\<rparr>"

definition consLinkMinus1:: "nat \<Rightarrow> PDGr"
where
  "consLinkMinus1 n \<equiv> if n \<le> 1 then emptyGL
    else \<lparr>NsG= [], 
      EsG = [''e_t''@(str_nat (n-1))@''wo_t''@(str_nat n)@''wi''],
      srcG  = 
        [(''e_t''@(str_nat (n-1))@''wo_t''@(str_nat n)@''wi'', ''t''@(str_nat (n-1))@''wo'')],
      tgtG = 
        [(''e_t''@(str_nat (n-1))@''wo_t''@(str_nat n)@''wi'', ''t''@(str_nat n)@''wi'')]\<rparr>"

definition consTankNWithLinkToMinus1:: "nat \<Rightarrow> PDGr"
where
  "consTankNWithLinkToMinus1 n \<equiv> 
    (case n of 0 \<Rightarrow> emptyGL | Suc k \<Rightarrow> 
      (if k = 0 then (consTankN (Suc k))   
        else consUG (consTankN (Suc k)) (consLinkMinus1 (Suc k))))" 

primrec consNConnectedTanks:: "nat \<Rightarrow> PDGr"
where
  "consNConnectedTanks 0 = emptyGL" |
  "consNConnectedTanks (Suc n) = consUG (consTankNWithLinkToMinus1 (Suc n))
    (consNConnectedTanks n)"

definition genPDGOfWtsn :: "nat \<Rightarrow> PDGr"
where
  "genPDGOfWtsn n \<equiv> (if n = 0 then emptyGL else
    consUG (consNConnectedTanks n) (connectToBase n))"

definition genPDGOfWtsn_loop :: "nat \<Rightarrow> PDGr"
where
  "genPDGOfWtsn_loop n \<equiv> (if n = 0 then emptyGL else
    consUG (consNConnectedTanks n) (connectToBase_loop n))"

value "genPDGOfWtsn 1"

value "genPDGOfWtsn_loop 1"

value "genPDGOfWtsn 2"

value "genPDGOfWtsn 3"

value "genPDGOfWtsn_loop 2"

(*The function that produces increasingly bigger PDGs*)
primrec genWTsn :: "nat \<Rightarrow> (nat \<times> PDGr) list"
where
  "genWTsn 0 = [(0, genPDGOfWtsn 0)]"
  | "genWTsn (Suc n) = ((Suc n), genPDGOfWtsn (Suc n))#(genWTsn n)"

(*The function that produces increasingly bigger PDGs with loops*)
primrec genWTsn_loop :: "nat \<Rightarrow> (nat \<times> PDGr) list"
where
  "genWTsn_loop 0 = [(0, genPDGOfWtsn_loop 0)]"
  | "genWTsn_loop (Suc n) = ((Suc n), genPDGOfWtsn_loop (Suc n))#(genWTsn_loop n)"


end


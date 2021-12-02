(*  Title:      Multiplicities
    Description: Theory of multiplicities used in SGs.
    Author:     Nuno Amálio
*)
theory Fragmenta_Mult
  imports Main Fragmenta_SGElemTys "../Extra/Rel_Extra"
begin

(*Multiplicity values: a natural number or 0*)
datatype MultVal = val nat | many ("*")

(*Multiplicities: either a range multiplicity or a single multiplicity value*)
datatype MultC = rm nat MultVal | sm MultVal

definition leq_MV::"MultVal \<Rightarrow> MultVal  \<Rightarrow> bool" (infixl "\<le>\<^sub>M\<^sub>V" 100)
  where
  "m1 \<le>\<^sub>M\<^sub>V m2 \<equiv> m2 = * \<or> (\<exists> j k . m1 = val j \<and> m2 = val k \<and> j \<le> k)"

lemma leq_MV_simp[simp]:"val j \<le>\<^sub>M\<^sub>V val k \<longleftrightarrow> j \<le> k"
  by (simp add: leq_MV_def)

definition ok_multC :: "MultC \<Rightarrow> bool"
where
  "ok_multC mv \<equiv> (case mv of (rm lb ub) \<Rightarrow> val lb \<le>\<^sub>M\<^sub>V ub
      | (sm mv) \<Rightarrow> True)"

lemma ok_multVal_sm_many[simp]: "ok_multC (sm *)"
  by (simp add: ok_multC_def)

lemma ok_multVal_sm_one[simp]: "ok_multC (sm (val 1))"
  by (simp add: ok_multC_def)

lemma not_ok_multVal_sm_one[simp]: "\<not>ok_multC (rm 10 (val 5))"
  by (simp add: ok_multC_def)

definition MultC_set :: "MultC set"
  where
  "MultC_set = {m . ok_multC m}"

definition is_mmany::"MultC \<Rightarrow> bool"
  where 
  "is_mmany m = (case m of (rm 0 *) \<Rightarrow> True
    | (sm *) \<Rightarrow> True)"

definition is_mrange::"MultC \<Rightarrow> bool"
  where 
  "is_mrange m = (case m of (rm 0 (val ub)) \<Rightarrow> ub \<ge> 2
    | (sm (val k)) \<Rightarrow> k\<ge> 0)"

definition within_m::"nat\<Rightarrow>MultVal \<Rightarrow> MultVal \<Rightarrow>bool" 
  where
    "within_m k lb ub \<equiv> lb \<le>\<^sub>M\<^sub>V (val k) \<and> (val k) \<le>\<^sub>M\<^sub>V ub"

definition mlb::"MultC \<Rightarrow>MultVal"
  where
  "mlb m = (case m of (sm *)\<Rightarrow>val 0
    | (sm (val k)) \<Rightarrow> val k
    | (rm lb ub) \<Rightarrow> val lb)"

definition mub::"MultC \<Rightarrow>MultVal"
  where
  "mub m = (case m of (sm m)\<Rightarrow>m
    | (rm lb ub) \<Rightarrow> ub)"

definition leq_M::"MultC \<Rightarrow> MultC  \<Rightarrow> bool" (infixl "\<le>\<^sub>\<MM>" 100)
  where
  "m1 \<le>\<^sub>\<MM> m2 \<equiv> (mlb m2) \<le>\<^sub>M\<^sub>V (mlb m1) \<and> (mub m1) \<le>\<^sub>M\<^sub>V (mub m2)"

definition allowedm::"SGET \<Rightarrow>MultC\<times> MultC \<Rightarrow> bool" (infixl "\<propto>" 100)
  where
  "et \<propto> mp \<equiv> et = erel dbi \<or> et = eder
    \<or> et =ecomp duni \<and> fst mp = sm (val 1)
    \<or> et = ecomp dbi \<and> fst mp \<in> {rm 0 (val 1), sm (val 1)}
    \<or> et = erel duni \<and> is_mmany(fst mp)
    \<or> et = ewander \<and> is_mmany(fst mp) \<and> is_mmany(snd mp)"

definition rbounded::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow>MultC\<Rightarrow>bool" 
  where
  "rbounded r xs m \<equiv> (\<forall> x \<in> xs. within_m (card(r ``{x})) (mlb m) (mub m))"

definition rMultOk::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow>'b set\<Rightarrow>MultC\<Rightarrow>MultC\<Rightarrow>bool"
  where
  "rMultOk r xs ys m1 m2 \<equiv> 
    {m1, m2} \<subseteq> {sm (val 1)} \<and> bij_on r xs ys
    \<or> {m1, m2} \<subseteq> {rm 0 (val 1)} \<and> pinj_on r xs ys
    \<or> m1 = rm 0 (val 1) \<and> m2 = sm (val 1) \<and> injf_on r xs ys
    \<or> m1 = sm (val 1) \<and> m2 = rm 0 (val 1) \<and> injf_on (r\<inverse>) ys xs
    \<or> is_mmany m1 \<and> m2 = sm (val 1) \<and> fun_on r xs ys
    \<or> m1 = sm (val 1) \<and> is_mmany m2 \<and> fun_on (r\<inverse>) ys xs
    \<or> is_mmany m1 \<and> is_mmany m2 \<and> rel_on r xs ys
    \<or> is_mmany m1 \<and> is_mrange m2 \<and> rel_on r xs ys \<and> rbounded r xs m2
    \<or> is_mrange m1 \<and> is_mmany m2 \<and> rel_on r xs ys \<and> rbounded (r\<inverse>) ys m1
    \<or> is_mmany m1 \<and> m2 = rm 0 (val 1)\<and> pfun_on r xs ys
    \<or> m1 = rm 0 (val 1)\<and> is_mmany m2 \<and>  pfun_on (r\<inverse>) ys xs
    \<or> is_mrange m1 \<and> is_mrange m2 \<and> rel_on r xs ys \<and> rbounded r xs m2 \<and> rbounded (r\<inverse>) ys m1
    \<or> is_mrange m1 \<and> m2 = sm (val 1) \<and> fun_on r xs ys \<and> rbounded (r\<inverse>) ys m1
    \<or> m1 = sm (val 1) \<and> is_mrange m2 \<and> fun_on (r\<inverse>) ys xs \<and> rbounded r xs m2
    \<or> is_mrange m1 \<and> m2 = rm 0 (val 1) \<and> pfun_on r xs ys \<and> rbounded (r\<inverse>) ys m1
    \<or> m1 = rm 0 (val 1) \<and> is_mrange m2 \<and> pfun_on (r\<inverse>) ys xs \<and> rbounded r xs m2"

end
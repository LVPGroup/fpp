
theory Set_Relation
imports Main HOL.Real

begin


subsection \<open>set definition\<close>
definition Set0 :: "nat set"
  where "Set0 \<equiv> {0, 2, 4, 6}"

definition Set1 :: "nat set"
  where "Set1 \<equiv> {..<100}"

definition Set2 :: "nat set"
  where "Set2 \<equiv> {10..100}"

lemma "11 \<in> Set2" unfolding Set2_def by simp

definition Set3 :: "nat set"
  where "Set3 \<equiv> {n. n mod 2 = 0 \<and> n < 100}"

lemma "24 \<in> Set3" unfolding Set3_def by simp

definition Set4 :: "real set"
  where "Set4 \<equiv> {25.0 .. 125.0}"

lemma "25.0 \<in> Set4" unfolding Set4_def by simp

lemma "10 \<in> \<nat>" by simp
lemma "-10 \<in> \<int>" by simp
lemma "3 / 4 \<in> \<rat>" by simp

value "2 \<in> Set0"
value "5 \<in> Set0"
value "7 \<notin> Set0"
value "20 \<in> Set1"
value "101 \<in> Set1"


value "card Set0"
value "card Set1"
value "card Set2"

value "card {1::int,2,2,3}"

lemma "finite Set0"
  unfolding Set0_def by simp

lemma "finite Set1"
  unfolding Set1_def by simp

lemma "finite Set2"
  unfolding Set2_def by simp

lemma "finite Set3"
  unfolding Set3_def by simp

lemma "infinite Set4"
  unfolding Set4_def by simp

lemma "infinite S \<Longrightarrow> card S = 0"
  by simp

lemma "card {} = 0" by simp

datatype Element = a | b | c

value "a = b"
value "a = c"
value "b = c"

lemma "\<forall>x::Element. x = a \<or> x = b \<or> x = c" using Element.nchotomy by simp

lemma "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" by simp

lemma lm1: "{x::Element. True} = {a, b, c}" using Element.nchotomy by auto

lemma lm2: "card {a, b, c} = 3" by auto

lemma "card {x::Element. True} = 3" using lm1 lm2 by simp

lemma "card (UNIV :: Element set) = 3" using lm1 lm2 by simp
  
lemma "infinite (UNIV :: int set)" using infinite_UNIV_int by simp

lemma "{} = {x. False}" by simp

lemma "UNIV = {x. True}" by simp


lemma "{0,2,4,6} = {2,4,6,0}" by auto

lemma "{0,2,4,6} = {2,4,4,6,6,0}" by auto

lemma "x\<in>A \<Longrightarrow> insert x A = A" by auto

definition Set5 :: "nat set"
  where "Set5 \<equiv> {1,2,3}"

definition Set6 :: "nat set"
  where "Set6 \<equiv> {1,2,3,4}"

lemma "Set5 \<subseteq> Set6" by (simp add: Set5_def Set6_def)

lemma "Set5 \<subseteq> Set5" by (simp add: Set5_def Set6_def)

lemma "{} \<subseteq> {}" by simp

lemma "UNIV \<subseteq> UNIV" by simp

lemma "{} \<subseteq> A" by simp

lemma "A \<subseteq> UNIV" by simp

lemma "Set5 \<subset> Set6" unfolding Set5_def Set6_def by auto

subsection \<open>set operation\<close>

abbreviation Set7 :: "nat set"
  where "Set7 \<equiv> {1,2,3,4,5}"

abbreviation Set8 :: "nat set"
  where "Set8 \<equiv> {4,5,6,7,8}"

value "Set7 \<inter> Set8"
value "Set7 \<union> Set8"
value "Set7 - Set8"
value "- Set7"

lemma "A \<times> B = {(x,y). x\<in>A \<and> y\<in>B}" by simp

abbreviation Set9 :: "nat set"
  where "Set9 \<equiv> {1,2,3}"

abbreviation Set10 :: "nat set"
  where "Set10 \<equiv> {4,5,6}"

value "Set9 \<times> Set10"
value "card (Set9 \<times> Set10)"

abbreviation Set11 :: "char list set"
  where "Set11 \<equiv> {''a'', ''b''}"

value "Set9 \<times> Set10 \<times> Set11"
value "card (Set9 \<times> Set10 \<times> Set11)"

value "Pow Set9"

subsection \<open>inductive set\<close>

inductive_set Even :: "int set" 
  where zeroe: "0 \<in> Even" |
        plus2: "n \<in> Even \<Longrightarrow> n + 2 \<in> Even" |
        minus2: "n \<in> Even \<Longrightarrow> n - 2 \<in> Even"

lemma even_lm1: "x\<in>Even \<Longrightarrow> 2 dvd x"
  apply(erule Even.induct)
    apply simp
   apply (simp_all add:dvd_def)
   apply clarify
   apply (rule_tac x = "k + 1" in exI, simp)
  apply clarify
  by (rule_tac x = "k - 1" in exI, simp)

lemma "0 \<in> Even" using zeroe by simp
lemma "2 \<in> Even" using zeroe plus2 by fastforce
lemma "-2 \<in> Even" using zeroe minus2 by fastforce
lemma "1 \<notin> Even" using even_lm1 by fastforce

inductive_set string_set :: "string set"
  where nil_str: "Nil \<in> string_set" |
        cons_str: "\<lbrakk>x\<in>string_set\<rbrakk> \<Longrightarrow>chr#x\<in>string_set"

lemma "''abcd'' \<in> string_set" 
  using nil_str cons_str by blast

  
inductive_set trancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" 
  for R :: "('a \<times> 'a) set"
where
  R_into_trancl: "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> trancl R"
| R_trancl:      "(x, y) \<in> trancl R \<and> (y, z) \<in> R \<Longrightarrow> (x, z) \<in> trancl R" 


term "trancl A"

definition "graph1 \<equiv> {(''v1'',''v2''),(''v2'',''v3''),(''v3'',''v4'')}"
lemma "trancl graph1 = graph1 \<union> {(''v1'',''v3''),(''v1'',''v4''),(''v2'',''v4'')}"
  using R_into_trancl R_trancl sorry


inductive_set even :: "nat set" and
               odd :: "nat set" where
  zero: "0 \<in> even" | 
  EvenI: "n \<in> odd \<Longrightarrow> Suc n \<in> even" | 
  OddI: "n \<in> even \<Longrightarrow> Suc n \<in> odd"

lemma even_lm2: "(x\<in>even \<longrightarrow> 2 dvd x) \<and> (x\<in>odd \<longrightarrow> 2 dvd (Suc x))"
  apply(rule even_odd.induct)
    apply simp
   apply (simp_all add:dvd_def)
   apply clarify
   by (rule_tac x = "Suc k" in exI, simp)

lemma "0 \<in> even" using zero by simp
lemma "2 \<in> even" using zero EvenI[of 1] OddI[of 0]
  by (metis Suc_1 numeral_1_eq_Suc_0 numerals(1)) 
lemma "1 \<in> odd" using zero OddI by fastforce


subsection \<open>relation\<close>

definition "Vset \<equiv> {''v1'',''v2'',''v3'',''v4''}"

value "Vset \<times> Vset"

value "graph1 \<subseteq> Vset \<times> Vset"

lemma "Domain R = {x. \<exists>y. (x,y)\<in>R}" by auto

lemma "Range R = {y. \<exists>x. (x,y)\<in>R}" by auto

value "Domain graph1"
value "Range graph1"
value "Field graph1"

lemma "Domain R = {x. \<exists>y. (x,y)\<in>R}" by auto
lemma "Range R = {y. \<exists>x. (x,y)\<in>R}" by auto

lemma "R \<subseteq> A \<times> B \<Longrightarrow> Domain R \<subseteq> A" by auto
lemma "R \<subseteq> A \<times> B \<Longrightarrow> Range R \<subseteq> B" by auto

lemma "A \<noteq> {} \<and> B \<noteq> {} \<Longrightarrow> Domain (A \<times> B) = A" by auto
lemma "A \<noteq> {} \<and> B \<noteq> {} \<Longrightarrow> Range (A \<times> B) = B" by auto


value "Id_on Vset"

value "total_on Vset graph1"


value "graph1\<inverse>"

definition "graph2 \<equiv> {(''v1'',''v1''),(''v2'',''v2''),(''v1'',''v3''),(''v2'',''v3''),(''v3'',''v4''),(''v4'',''v5'')}"

value "graph2 `` {''v1'',''v2''}"
value "graph2 `` {''v3'',''v4''}"

value "graph1"
value "graph2"
value "graph1 O graph2"

value "Id_on {''v1'',''v2'',''v3''}"

definition "ID = {(x,y). x = y}"
lemma "ID = Id"
  unfolding Id_def ID_def by auto

definition "Id_int = (Id :: (int \<times> int) set)"

definition "Id_real = (Id :: (real \<times> real) set)"

lemma "Id_on {x::int. True} = Id_int"
  unfolding ID_def Id_on_def Id_int_def by auto

lemma "R O Id = R" by auto
lemma "Id O R = R" by auto

lemma "total {(x::int,y). x < y}" 
  apply(simp add: total_on_def)
  apply(rule allI)+
  apply(rule impI) by auto
  
lemma "total_on {1::int,2} {(1,1),(1,2)}" 
  by (simp add:total_on_def)

lemma "total_on {1::int,2} {(1,1),(1,2),(2,1)}" 
  by (simp add:total_on_def)

lemma "total_on {1::int,2} {(1,1),(1,2),(2,2)}" 
  by (simp add:total_on_def)

lemma "total_on {1::int,2} {(1,2),(2,2)}" 
  by (simp add:total_on_def)

lemma "total_on {1::int,2} ({1,2}\<times>{1,2})" 
  by (simp add:total_on_def)

lemma "refl_on {1::int,2} {(1,1),(2,2)}"
  by (simp add:refl_on_def)

lemma "refl_on {1::int,2} {(1,1),(2,2),(1,2)}"
  by (simp add:refl_on_def)

value "refl_on {1::int,2} {(1,1),(2,2),(1,2)}"

lemma "refl {(x::int,y). x = y}"
  by (simp add:refl_on_def)

lemma "refl {(x::int,y). x \<le> y}"
  by (simp add:refl_on_def)

lemma "refl {(x::int,y). x < y} = False"
  by (simp add:refl_on_def)

lemma "refl Id"
  using refl_Id by simp


lemma "sym {(1,1),(2,2)}" 
  by (simp add: sym_def)

lemma "sym {(x::int,y). x \<noteq> y}"
  by (simp add: sym_def)

lemma "sym {(x::int,y). x \<le> y} = False"
  apply (simp add: sym_def)
  apply(rule_tac x = 1 in exI)
  apply(rule_tac x = 2 in exI) by simp
  

lemma "sym {(x::int,y). x = y}"
  by (simp add: sym_def)

lemma "sym Id"
  using sym_Id by simp

value "trans {(1::int,2),(2,3),(1,3)}"

lemma "trans {(x::int,y). x < y}"
  by (simp add:trans_def)

lemma "trans {(x::int,y). x \<le> y}"
  by (simp add:trans_def)

lemma "trans {(x::int,y). x = y}"
  by (simp add:trans_def)

lemma "trans {(x::int,y). x \<noteq> y} = False"
  apply (simp add:trans_def)
  apply (rule_tac x = 1 in exI)
  apply (rule_tac x = 2 in exI)
  by simp

lemma "trans Id"
  by (simp add:trans_def)

lemma "refl {} = False" 
  unfolding refl_on_def by auto

lemma "sym {} = True"
  unfolding sym_def by auto

lemma "trans {} = True"
  unfolding trans_def by auto

lemma "refl UNIV = True"
  unfolding refl_on_def by auto

lemma "sym UNIV = True"
  unfolding sym_def by auto

lemma "trans UNIV = True"
  unfolding trans_def by auto


definition equiv_on :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where "equiv_on A r \<equiv> refl_on A r \<and> sym r \<and> trans r"

definition equiv :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "equiv r \<equiv> equiv_on UNIV r"

lemma "equiv_on A (A\<times>A)"
  unfolding equiv_on_def refl_on_def sym_def trans_def by auto

lemma "equiv_on A (Id_on A)"
  unfolding equiv_on_def refl_on_def sym_def trans_def by auto

lemma "equiv UNIV = True"
  unfolding equiv_def equiv_on_def refl_on_def sym_def trans_def by auto

lemma "equiv Id = True"
  unfolding equiv_def equiv_on_def refl_on_def sym_def trans_def by auto

lemma "refl {} = False"
  unfolding refl_on_def by auto
lemma "sym {} = True"
  unfolding sym_def by auto
lemma "trans {} = True"
  by auto



end


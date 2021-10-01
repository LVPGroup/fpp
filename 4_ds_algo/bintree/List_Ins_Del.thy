(* Author: Tobias Nipkow *)

section \<open>List Insertion and Deletion\<close>

theory List_Ins_Del
imports Sorted_Less
begin

subsection \<open>Elements in a list\<close>

lemma sorted_Cons_iff:
  "sorted(x # xs) = ((\<forall>y \<in> set xs. x < y) \<and> sorted xs)"
by(simp add: sorted_wrt_Cons)

lemma sorted_snoc_iff:
  "sorted(xs @ [x]) = (sorted xs \<and> (\<forall>y \<in> set xs. y < x))"
by(simp add: sorted_wrt_append)
(*
text\<open>The above two rules introduce quantifiers. It turns out
that in practice this is not a problem because of the simplicity of
the "isin" functions that implement @{const set}. Nevertheless
it is possible to avoid the quantifiers with the help of some rewrite rules:\<close>

lemma sorted_ConsD: "sorted (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> x \<notin> set xs"
by (auto simp: sorted_Cons_iff)

lemma sorted_snocD: "sorted (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow> x \<notin> set xs"
by (auto simp: sorted_snoc_iff)

lemmas isin_simps2 = sorted_lems sorted_ConsD sorted_snocD
*)

lemmas isin_simps = sorted_mid_iff' sorted_Cons_iff sorted_snoc_iff


subsection \<open>Inserting into an ordered list without duplicates:\<close>

fun ins_list :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ins_list x [] = [x]" |
"ins_list x (a#xs) =
  (if x < a then x#a#xs else if x=a then a#xs else a # ins_list x xs)"

lemma set_ins_list: "set (ins_list x xs) = set xs \<union> {x}"
by(induction xs) auto

lemma sorted_ins_list: "sorted xs \<Longrightarrow> sorted(ins_list x xs)"
by(induction xs rule: induct_list012) auto

lemma ins_list_sorted: "sorted (xs @ [a]) \<Longrightarrow>
  ins_list x (xs @ a # ys) =
  (if x < a then ins_list x xs @ (a#ys) else xs @ ins_list x (a#ys))"
by(induction xs) (auto simp: sorted_lems)

text\<open>In principle, @{thm ins_list_sorted} suffices, but the following two
corollaries speed up proofs.\<close>

corollary ins_list_sorted1: "sorted (xs @ [a]) \<Longrightarrow> a \<le> x \<Longrightarrow>
  ins_list x (xs @ a # ys) = xs @ ins_list x (a#ys)"
by(auto simp add: ins_list_sorted)

corollary ins_list_sorted2: "sorted (xs @ [a]) \<Longrightarrow> x < a \<Longrightarrow>
  ins_list x (xs @ a # ys) = ins_list x xs @ (a#ys)"
by(auto simp: ins_list_sorted)

lemmas ins_list_simps = sorted_lems ins_list_sorted1 ins_list_sorted2

text\<open>Splay trees need two additional \<^const>\<open>ins_list\<close> lemmas:\<close>

lemma ins_list_Cons: "sorted (x # xs) \<Longrightarrow> ins_list x xs = x # xs"
by (induction xs) auto

lemma ins_list_snoc: "sorted (xs @ [x]) \<Longrightarrow> ins_list x xs = xs @ [x]"
by(induction xs) (auto simp add: sorted_mid_iff2)


subsection \<open>Delete one occurrence of an element from a list:\<close>

fun del_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del_list x [] = []" |
"del_list x (a#xs) = (if x=a then xs else a # del_list x xs)"

lemma del_list_idem: "x \<notin> set xs \<Longrightarrow> del_list x xs = xs"
by (induct xs) simp_all

lemma set_del_list:
  "sorted xs \<Longrightarrow> set (del_list x xs) = set xs - {x}"
by(induct xs) (auto simp: sorted_Cons_iff)

lemma sorted_del_list: "sorted xs \<Longrightarrow> sorted(del_list x xs)"
apply(induction xs rule: induct_list012)
apply auto
by (meson order.strict_trans sorted_Cons_iff)

lemma del_list_sorted: "sorted (xs @ a # ys) \<Longrightarrow>
  del_list x (xs @ a # ys) = (if x < a then del_list x xs @ a # ys else xs @ del_list x (a # ys))"
by(induction xs)
  (fastforce simp: sorted_lems sorted_Cons_iff intro!: del_list_idem)+

text\<open>In principle, @{thm del_list_sorted} suffices, but the following
corollaries speed up proofs.\<close>

corollary del_list_sorted1: "sorted (xs @ a # ys) \<Longrightarrow> a \<le> x \<Longrightarrow>
  del_list x (xs @ a # ys) = xs @ del_list x (a # ys)"
by (auto simp: del_list_sorted)

corollary del_list_sorted2: "sorted (xs @ a # ys) \<Longrightarrow> x < a \<Longrightarrow>
  del_list x (xs @ a # ys) = del_list x xs @ a # ys"
by (auto simp: del_list_sorted)

corollary del_list_sorted3:
  "sorted (xs @ a # ys @ b # zs) \<Longrightarrow> x < b \<Longrightarrow>
  del_list x (xs @ a # ys @ b # zs) = del_list x (xs @ a # ys) @ b # zs"
by (auto simp: del_list_sorted sorted_lems)

corollary del_list_sorted4:
  "sorted (xs @ a # ys @ b # zs @ c # us) \<Longrightarrow> x < c \<Longrightarrow>
  del_list x (xs @ a # ys @ b # zs @ c # us) = del_list x (xs @ a # ys @ b # zs) @ c # us"
by (auto simp: del_list_sorted sorted_lems)

corollary del_list_sorted5:
  "sorted (xs @ a # ys @ b # zs @ c # us @ d # vs) \<Longrightarrow> x < d \<Longrightarrow>
   del_list x (xs @ a # ys @ b # zs @ c # us @ d # vs) =
   del_list x (xs @ a # ys @ b # zs @ c # us) @ d # vs" 
by (auto simp: del_list_sorted sorted_lems)

lemmas del_list_simps = sorted_lems
  del_list_sorted1
  del_list_sorted2
  del_list_sorted3
  del_list_sorted4
  del_list_sorted5

text\<open>Splay trees need two additional \<^const>\<open>del_list\<close> lemmas:\<close>

lemma del_list_notin_Cons: "sorted (x # xs) \<Longrightarrow> del_list x xs = xs"
by(induction xs)(fastforce simp: sorted_Cons_iff)+

lemma del_list_sorted_app:
  "sorted(xs @ [x]) \<Longrightarrow> del_list x (xs @ ys) = xs @ del_list x ys"
by (induction xs) (auto simp: sorted_mid_iff2)

end

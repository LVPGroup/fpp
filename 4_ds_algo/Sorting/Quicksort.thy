
section \<open>Quicksort with function package\<close>

theory Quicksort
imports "HOL-Library.Multiset"
begin

context linorder
begin

fun quicksort :: "'a list \<Rightarrow> 'a list" where
  "quicksort []     = []"
| "quicksort (x#xs) = quicksort [y\<leftarrow>xs. \<not> x\<le>y] 
                        @ [x] @ 
                      quicksort [y\<leftarrow>xs. x\<le>y]"

lemma [code]:
  "quicksort []     = []"
  "quicksort (x#xs) = quicksort [y\<leftarrow>xs. y<x] @ [x] @ quicksort [y\<leftarrow>xs. x\<le>y]"
  by (simp_all add: not_le)

lemma mset_quicksort [simp]:
  "mset (quicksort xs) = mset xs"
apply(induct xs rule: quicksort.induct)
  apply simp
  by (simp add: add.commute)

lemma "[y\<leftarrow>xs . \<not> x \<le> y] = (filter ((>) x) xs)"
  by (meson local.leD local.leI) 

lemma set_quicksort [simp]: "set (quicksort xs) = set xs"
proof -
  have "set_mset (mset (quicksort xs)) = set_mset (mset xs)"
    by simp
  then show ?thesis by (simp only: set_mset_mset)
qed

lemma sorted_quicksort: "sorted (quicksort xs)"
apply(induct xs rule: quicksort.induct)
  apply simp
  by (auto simp add: sorted_append not_le less_imp_le)

theorem sort_quicksort:
  "sort = quicksort"
  by (rule ext, rule properties_for_sort) 
      (fact mset_quicksort sorted_quicksort)+

end

end

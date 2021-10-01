
section\<open>Merge Sort\<close>

theory MergeSort
imports "HOL-Library.Multiset"
begin

context linorder
begin

fun merge :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge (x#xs) (y#ys) =
      (if x \<le> y then 
        x # merge xs (y#ys) 
      else y # merge (x#xs) ys)"
| "merge xs [] = xs"
| "merge [] ys = ys"


fun msort :: "'a list \<Rightarrow> 'a list"
where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = merge (msort (take (size xs div 2) xs))
                    (msort (drop (size xs div 2) xs))"

lemma mset_merge:
  "mset (merge xs ys) = mset xs + mset ys"
  by (induct xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge:
  "set (merge xs ys) = set xs \<union> set ys"
  by (induct xs ys rule: merge.induct) auto

lemma mset_msort:
  "mset (msort xs) = mset xs"
apply(induct xs rule: msort.induct)
  apply simp apply simp
  apply(simp add:mset_merge, 
        metis append_take_drop_id mset.simps(2) mset_append)
done
(*  by (induct xs rule: msort.induct)
    (simp_all, metis append_take_drop_id mset.simps(2) mset_append)*)


lemma sorted_merge:
  "sorted (merge xs ys) \<longleftrightarrow> sorted xs \<and> sorted ys"
  by (induct xs ys rule: merge.induct) 
      (auto simp add: set_merge ball_Un not_le less_le)


lemma sorted_msort:
  "sorted (msort xs)"
  apply (induct xs rule: msort.induct)
  apply simp apply simp apply(simp add:sorted_merge)
done

theorem msort_sort:
  "sort = msort"
  by (rule ext, rule properties_for_sort) (fact mset_msort sorted_msort)+

end

end

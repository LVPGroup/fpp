
theory InsertSort
imports
  Complex_Main
  "HOL-Library.Multiset"
begin


context linorder
begin

fun insort :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insort x [] = [x]" |
"insort x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort x ys))"

fun isort :: "'a list \<Rightarrow> 'a list" where
"isort [] = []" |
"isort (x#xs) = insort x (isort xs)"

value "isort [100,39,2::nat, 3,5,10,300]"
subsubsection "Functional Correctness"

lemma mset_insort: "mset (insort x xs) = add_mset x (mset xs)"
apply(induction xs)
apply auto
done

lemma mset_isort: "mset (isort xs) = mset xs"
apply(induction xs)
apply simp
apply (simp add: mset_insort)
done

lemma insort_set: "set (insort x xs) = insert x (set xs)"
  apply(induct xs) by auto

lemma sorted_insort: "sorted (insort a xs) = sorted xs"
apply(induction xs) apply simp
apply(case_tac "a \<le> aa")
  apply auto[1]  
  apply simp
  apply(rule iffI)
    apply (simp add: insort_set)
    apply (simp add: insort_set)
done

lemma sorted_isort: "sorted (isort xs)"
apply(induction xs)
apply(auto simp: sorted_insort)
done
end

end

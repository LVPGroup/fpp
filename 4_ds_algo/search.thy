theory search
  imports Main
begin
  
fun liner_search_iter :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat option" where
  "liner_search_iter _ [] _ = None"|
  "liner_search_iter x (x0 # xs) idx = (if x=x0 then (Some idx) else (liner_search_iter x xs (idx+1)))"

fun liner_search :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "liner_search a xs = liner_search_iter a xs 0"
  
value "liner_search (5::int) [3, 4::int, 6, 7, 8, 5]"
value "take (3::nat) [a, b, c, d]"
value "nth [1, 2, 3::int] 1"
  
  
  
lemma liner_search_some: "liner_search_iter x xs v = Some vi \<Longrightarrow> \<exists> ui. liner_search_iter x xs u = Some ui"
  proof(induction xs arbitrary: v u)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume "x=a"
      then have " liner_search_iter x (a # xs) u = Some u"
        by simp 
      then show ?case
        by blast 
    next
      assume "\<not> x=a"
      then have "liner_search_iter x (a # xs) u = liner_search_iter x xs (u+1)" by simp
      then show ?case
        by (metis Cons.IH Cons.prems liner_search_iter.simps(2)) 
    qed
  qed
  
lemma liner_search_none: "liner_search_iter x xs v = None \<Longrightarrow> liner_search_iter x xs u = None"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis liner_search_some option.exhaust option.simps(2)) 
qed
  
  
lemma "liner_search x xs = None \<Longrightarrow> x \<notin> (set xs)"
  apply(simp)
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then have "liner_search_iter x xs 1 = None"
    by (metis add.left_neutral liner_search_iter.simps(2) option.simps(3))
  then have a0: "liner_search_iter x xs 0 = None"
    by (metis liner_search_none) 
  then have "x \<noteq> a"
    using Cons.prems by auto
  then show ?case
    using Cons.IH a0 by auto 
qed
 
  (*
lemma "(a # xs) ! idx = xs ! (THE u. (Suc u) = idx)"
  by *)
  
lemma liner_search_iter_Suc: "liner_search_iter x xs u = Some v \<Longrightarrow> liner_search_iter x xs (Suc u) = Some (Suc v)"
  proof(induction xs arbitrary: u v)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume "x=a"
      then show ?case
        using Cons.prems by auto 
    next
      assume "\<not> x=a"
      then have "liner_search_iter x (a # xs) (Suc u) = liner_search_iter x xs (Suc(Suc u))" by simp
      then show ?case
        by (metis Cons.IH Cons.prems Suc_eq_plus1 \<open>x \<noteq> a\<close> liner_search_iter.simps(2)) 
    qed
  qed
  
lemma liner_search_iter_gt0: "Some idx = liner_search_iter x xs 1 \<Longrightarrow> idx > 0"
  proof(induction xs)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume "x = a"
      then have "liner_search_iter x (a # xs) 1 = Some 1" by simp
      then show ?case
        using Cons.prems by auto 
    next
      assume "\<not> x = a"
      then have "liner_search_iter x (a # xs) 1 = liner_search_iter x xs (Suc 1)" by simp
          
      then show ?case using liner_search_iter_Suc
        by (metis Cons.prems One_nat_def gr0_conv_Suc liner_search_some option.inject) 
    qed
  qed
    
lemma liner_search_iter_inject: "\<lbrakk>liner_search_iter x xs u = Some w;liner_search_iter x xs v = Some w\<rbrakk> \<Longrightarrow> u = v"
  proof(induction xs arbitrary: w)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume a0: "x = a"
      then have "liner_search_iter x (a # xs) v = Some v" by simp
      then have "liner_search_iter x (a # xs) u = Some u" using a0 by simp
          
      then show ?case
        using Cons.prems(1) Cons.prems(2) \<open>liner_search_iter x (a # xs) v = Some v\<close> by auto 
    next
      assume a1: "\<not> x = a"
      then have a2: "liner_search_iter x (a # xs) u = liner_search_iter x xs (u+1)" by simp
      then have "liner_search_iter x (a # xs) v = liner_search_iter x xs (v+1)" using a1 by simp
      then have "liner_search_iter x xs (u+1) = Some w"
        using Cons.prems(1) \<open>liner_search_iter x (a # xs) u = liner_search_iter x xs (u + 1)\<close> by auto
      then have b1: "liner_search_iter x xs u = Some (w-1)"
        by (metis One_nat_def add.right_neutral add_Suc_right add_implies_diff liner_search_iter_Suc liner_search_some option.inject)
      then have "liner_search_iter x xs (v+1) = Some w"
        using Cons.prems(2) \<open>liner_search_iter x (a # xs) v = liner_search_iter x xs (v + 1)\<close> by auto
      then have b2: "liner_search_iter x xs v = Some (w-1)"
        by (metis One_nat_def add.right_neutral add_Suc_right add_implies_diff liner_search_iter_Suc liner_search_some option.inject)
      then show ?case using b1 b2
        using Cons.IH by blast 
    qed
      
  qed
  
lemma "liner_search x xs = Some idx \<Longrightarrow> x = xs ! idx"
  apply(simp)
  proof(induction xs arbitrary: idx)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    then show ?case proof(cases "x = a")
      assume "x = a"
      then show ?thesis
        using Cons.prems by auto 
    next
      assume "\<not> x = a"
        then have "Some idx = liner_search_iter x xs 1"
          using Cons.prems by auto
      then have "idx \<noteq> 0"
        by (simp add: liner_search_iter_gt0) 
      have "(a # xs) ! idx = xs ! (idx - 1)" using nth_Cons_Suc
        by (simp add: \<open>idx \<noteq> 0\<close> nth_Cons')
      then have " liner_search_iter x xs 0 = Some (idx-1)" using liner_search_iter_inject
      proof -
        have f1: "0 < idx"
          by (simp add: \<open>Some idx = liner_search_iter x xs 1\<close> liner_search_iter_gt0)
        obtain nn :: "nat \<Rightarrow> nat" where
          "(\<not> 0 < idx \<or> idx = Suc (nn idx)) \<and> (0 < idx \<or> (\<forall>n. idx \<noteq> Suc n))"
          by (metis (no_types) gr0_conv_Suc)
        then show ?thesis
          using f1 by (metis One_nat_def Suc_eq_plus1_left \<open>Some idx = liner_search_iter x xs 1\<close> add_left_cancel diff_Suc_Suc diff_zero liner_search_iter_Suc liner_search_some option.inject)
      qed
      then show ?thesis
        using Cons.IH \<open>(a # xs) ! idx = xs ! (idx - 1)\<close> by auto 
    qed
qed

value "(5::int) div (2::int)"
  
function binary_search_iter :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat option" where
  "binary_search_iter x xs l r = (if l \<le> r then 
  (let mid=(l+r) div 2; mid_v=xs ! (nat mid) in 
      (if mid_v=x 
        then (Some (nat mid)) 
        else (if mid_v < x 
              then (binary_search_iter x xs (mid+1) r) 
              else (binary_search_iter x xs l (mid-1))))) else None)"
  by pat_completeness auto
termination apply (relation "measure (\<lambda> (x, xs, l, r). nat (r-l+1))") 
    apply auto
  done
    
value "binary_search_iter (5::int) [1, 2, 3, 4, 5, 6, 7, 8] 0 7"
  
fun binary_search :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> nat option" where
  bin_Nil: "binary_search _ [] = None"|
  bin_xs: "binary_search x xs = binary_search_iter x xs 0 ((int (length xs))-1)"
  
value "binary_search (5::int) [1, 3, 4, 6, 7, 8]"
value "binary_search (5::int) [1, 3, 5, 6, 7, 8]"
  
  
lemma "\<lbrakk>sorted xs; binary_search x xs=None\<rbrakk> \<Longrightarrow> x \<notin> set xs"
  proof(induction xs)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    assume a0: "sorted xs \<Longrightarrow> binary_search x xs = None \<Longrightarrow> x \<notin> set xs"
      and sorted_a_xs: "sorted (a # xs)"
      and search_a_xs: "binary_search x (a # xs) = None"
    then have "sorted xs" by simp
    then show ?case 
        then have 
  then show ?case 
qed
  
  
end
  
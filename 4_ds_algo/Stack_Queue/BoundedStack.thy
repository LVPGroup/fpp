(*
bounded stack using List as its implementation
*)
theory BoundedStack
imports Main
begin


section {* implementation by list *}

record 'a stack = stk :: "'a list" 
                  maxsize :: nat

locale bstack_list
begin

fun push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" 
where "push v s = (if length (stk s) < maxsize s then 
                  s\<lparr>stk := v # stk s\<rparr> 
               else s)"

fun pop :: "'a stack \<Rightarrow> ('a \<times> 'a stack)" 
where "pop s = (case stk s of x # xs \<Rightarrow> (x, s\<lparr>stk := xs\<rparr>))"

definition top :: "'a stack \<Rightarrow> 'a"
  where "top s \<equiv> hd (stk s)"

definition "emp s \<equiv> stk s = []"

definition "full s \<equiv> length (stk s) = maxsize s"

definition "notfull s \<equiv> length (stk s) < maxsize s"

definition "valid s \<equiv> notfull s \<or> full s"
  
lemma "notfull s \<Longrightarrow> top (push v s) = v" 
  by(simp add:top_def notfull_def)

lemma "notfull s \<Longrightarrow> pop (push x s) = (x, s)"
  by (simp add:notfull_def) 

lemma "full s \<Longrightarrow> push x s = s"
  by (simp add:full_def) 

lemma "\<not> emp s \<Longrightarrow> top s = fst (pop s)"
  by (simp add: emp_def list.case_eq_if top_def)

lemma "\<lbrakk>\<not> emp s; (v, s0) = pop s; valid s \<rbrakk> \<Longrightarrow> push v s0 = s"
  apply(simp add: emp_def valid_def full_def notfull_def) 
  apply(case_tac "stk s") apply simp
  by auto

end


section {* implementation by type *}

typedef (overloaded) 'a bstack =
  "{xs :: ('a list \<times> nat). length (fst xs) \<le> snd xs}"
  morphisms alist_of Abs_bstack
proof -
  have "([],0) \<in> {xs. length (fst xs) \<le> snd xs}" by simp
  thus ?thesis by blast
qed

thm alist_of_inverse
thm alist_of
thm Abs_bstack_inverse
thm Abs_bstack_inject

locale bstack_type
begin

definition capacity :: "'a bstack \<Rightarrow> nat"
where "capacity s \<equiv> snd (alist_of s)"

definition size :: "'a bstack \<Rightarrow> nat"
where "size s \<equiv> length (fst (alist_of s))"

definition isfull :: "'a bstack \<Rightarrow> bool"
where "isfull s \<equiv> size s = capacity s"

definition isempty :: "'a bstack \<Rightarrow> bool"
where "isempty s \<equiv> fst (alist_of s) = []"

lemma Abs_bstack: "length (fst xs) \<le> snd xs \<Longrightarrow> alist_of (Abs_bstack xs) = xs"
  apply (rule Abs_bstack_inverse) by simp

lemma [code abstype]: "Abs_bstack (alist_of bs) = bs"
  by (simp add:alist_of_inverse)

lemma "xs = alist_of bs \<Longrightarrow> length (fst xs) \<le> snd xs" 
  using alist_of by auto

lemma bstack_valid: "size s \<le> capacity s"
  apply(simp add:capacity_def size_def)
  using alist_of by blast

definition newstack :: "nat \<Rightarrow> 'a bstack"
where "newstack n \<equiv> Abs_bstack ([],n)"

definition push :: "'a \<Rightarrow> 'a bstack \<Rightarrow> 'a bstack"
where "push v s \<equiv> (if \<not>isfull s then 
                      Abs_bstack (v # fst (alist_of s), snd (alist_of s)) 
                   else s)"

definition pop :: "'a bstack \<Rightarrow> ('a option \<times> 'a bstack)"
where "pop s \<equiv> (if \<not> isempty s then 
                  (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s))) 
                else (None, s))"

definition top :: "'a bstack \<Rightarrow> 'a option"
where "top s \<equiv> (if \<not> isempty s then 
                  (Some (hd (fst (alist_of s)))) 
                else None)"

lemma "\<not> isfull s \<Longrightarrow> top (push v s) = Some v" 
  apply(simp add:top_def isfull_def capacity_def isempty_def size_def push_def)
  by (metis Abs_bstack bstack_valid capacity_def fst_conv length_Cons 
        less_Suc_eq list.distinct(1) list.sel(1) not_less size_def snd_conv) 

lemma "\<not> isfull s \<Longrightarrow> pop (push x s) = (Some x, s)"
  apply(simp add:pop_def isfull_def capacity_def isempty_def size_def push_def)
  by (metis (no_types, lifting) Abs_bstack alist_of alist_of_inverse fst_conv length_Cons 
      less_Suc_eq list.distinct(1) list.sel(1) list.sel(3) mem_Collect_eq not_less prod_eq_iff snd_conv)

lemma "isfull s \<Longrightarrow> push x s = s"
  by (simp add:isfull_def size_def capacity_def push_def) 

lemma "\<not> isempty s \<Longrightarrow> top s = fst (pop s)"
  by (simp add: isempty_def top_def pop_def)

lemma "\<lbrakk>\<not> isempty s; (v, s0) = pop s \<rbrakk> \<Longrightarrow> push (the v) s0 = s"
  apply(simp add: pop_def isempty_def isfull_def size_def capacity_def push_def)
  by (metis alist_of_inverse Abs_bstack bstack_valid capacity_def size_def fst_conv 
        length_Cons less_Suc_eq list.exhaust_sel not_less prod.exhaust_sel snd_conv)
  

end

end
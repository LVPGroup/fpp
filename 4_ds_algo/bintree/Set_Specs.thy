(* Author: Tobias Nipkow *)

section \<open>Specifications of Set ADT\<close>

theory Set_Specs
imports List_Ins_Del
begin

text \<open>The basic set interface with traditional \<open>set\<close>-based specification:\<close>

locale Set =
fixes empty :: "'s"
fixes insert :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes delete :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
fixes set :: "'s \<Rightarrow> 'a set"
fixes invar :: "'s \<Rightarrow> bool"
assumes set_empty:    "set empty = {}"
assumes set_isin:     "invar s \<Longrightarrow> isin s x = (x \<in> set s)"
assumes set_insert:   "invar s \<Longrightarrow> set(insert x s) = set s \<union> {x}"
assumes set_delete:   "invar s \<Longrightarrow> set(delete x s) = set s - {x}"
assumes invar_empty:  "invar empty"
assumes invar_insert: "invar s \<Longrightarrow> invar(insert x s)"
assumes invar_delete: "invar s \<Longrightarrow> invar(delete x s)"

lemmas (in Set) set_specs =
  set_empty set_isin set_insert set_delete invar_empty invar_insert invar_delete

text \<open>The basic set interface with \<open>inorder\<close>-based specification:\<close>

locale Set_by_Ordered =
fixes empty :: "'t"
fixes insert :: "'a::linorder \<Rightarrow> 't \<Rightarrow> 't"
fixes delete :: "'a \<Rightarrow> 't \<Rightarrow> 't"
fixes isin :: "'t \<Rightarrow> 'a \<Rightarrow> bool"
fixes inorder :: "'t \<Rightarrow> 'a list"
fixes inv :: "'t \<Rightarrow> bool"
assumes inorder_empty: "inorder empty = []"
assumes isin: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  isin t x = (x \<in> set (inorder t))"
assumes inorder_insert: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(insert x t) = ins_list x (inorder t)"
assumes inorder_delete: "inv t \<and> sorted(inorder t) \<Longrightarrow>
  inorder(delete x t) = del_list x (inorder t)"
assumes inorder_inv_empty:  "inv empty"
assumes inorder_inv_insert: "inv t \<and> sorted(inorder t) \<Longrightarrow> inv(insert x t)"
assumes inorder_inv_delete: "inv t \<and> sorted(inorder t) \<Longrightarrow> inv(delete x t)"

begin

text \<open>It implements the traditional specification:\<close>

definition set :: "'t \<Rightarrow> 'a set" where
"set = List.set o inorder"

definition invar :: "'t \<Rightarrow> bool" where
"invar t = (inv t \<and> sorted (inorder t))"

sublocale Set
  empty insert delete isin set invar
proof(standard, goal_cases)
  case 1 show ?case by (auto simp: inorder_empty set_def)
next
  case 2 thus ?case by(simp add: isin invar_def set_def)
next
  case 3 thus ?case by(simp add: inorder_insert set_ins_list set_def invar_def)
next
  case (4 s x) thus ?case
    by (auto simp: inorder_delete set_del_list invar_def set_def)
next
  case 5 thus ?case by(simp add: inorder_empty inorder_inv_empty invar_def)
next
  case 6 thus ?case by(simp add: inorder_insert inorder_inv_insert sorted_ins_list invar_def)
next
  case 7 thus ?case by (auto simp: inorder_delete inorder_inv_delete sorted_del_list invar_def)
qed

end


text \<open>Set2 = Set with binary operations:\<close>

locale Set2 = Set
  where insert = insert for insert :: "'a \<Rightarrow> 's \<Rightarrow> 's" (*for typing purposes only*) +
fixes union :: "'s \<Rightarrow> 's \<Rightarrow> 's"
fixes inter :: "'s \<Rightarrow> 's \<Rightarrow> 's"
fixes diff  :: "'s \<Rightarrow> 's \<Rightarrow> 's"
assumes set_union:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> set(union s1 s2) = set s1 \<union> set s2"
assumes set_inter:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> set(inter s1 s2) = set s1 \<inter> set s2"
assumes set_diff:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> set(diff s1 s2) = set s1 - set s2"
assumes invar_union:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> invar(union s1 s2)"
assumes invar_inter:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> invar(inter s1 s2)"
assumes invar_diff:   "\<lbrakk> invar s1; invar s2 \<rbrakk> \<Longrightarrow> invar(diff s1 s2)"

end

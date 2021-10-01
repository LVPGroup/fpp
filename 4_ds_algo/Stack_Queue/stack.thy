theory stack
  imports Main
begin

type_synonym 'a stack = "'a list"

definition push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" 
where "push v s = v#s"

primrec pop :: "'a stack \<Rightarrow> ('a \<times> 'a stack)" 
where "pop (x # xs) = (x, xs)"

(*definition empty :: "'a stack \<Rightarrow> 'a stack"
  where "empty s = []"*)

definition top :: "'a stack \<Rightarrow> 'a"
  where "top s \<equiv> hd s"

definition "emp s \<equiv> s = []"

lemma "top (push v s) = v" 
  apply(induct s) 
  by(simp add:top_def push_def)+

lemma "pop (push v s) = (v, s)"
  by (simp add:push_def)
  
lemma "\<forall>v s. pop (push v s) = (v, s)"
  by (simp add:push_def)

lemma "\<not> emp s \<Longrightarrow> top s = fst (pop s)"
  apply(induct s)
  by(simp add: emp_def top_def)+

lemma "\<not> emp s \<Longrightarrow> (v, s0) = pop s \<Longrightarrow> push v s0 = s"
  apply(simp add: emp_def push_def) 
  apply(induct s) by auto

end
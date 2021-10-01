theory Queue
  imports Main
begin

type_synonym 'a queue = "'a list"

definition isempty :: "'a queue \<Rightarrow> bool" 
where "isempty q \<equiv> (q = [])"

abbreviation "emptyq \<equiv> []"

fun enqueue :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" 
where "enqueue xs x = x # xs"

fun dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" 
where "dequeue xs = (last xs, butlast xs)"

lemma "dequeue (enqueue emptyq a) = (a, emptyq)" by auto

fun listenq :: "'a queue \<Rightarrow> 'a list \<Rightarrow> 'a queue" where
  "listenq q [] = q" |
  "listenq q (x # xs) = listenq (enqueue q x) xs"

fun deq2list :: "'a queue \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "deq2list [] lst = lst"|
  "deq2list q lst = 
      (let (x, xq) = dequeue(q) in 
        (deq2list xq (x # lst)))"

definition "list_enqueue l \<equiv> listenq [] l"
definition "dequeue_list q \<equiv> deq2list q []"

lemma listenq_rev: "listenq q xs = (rev xs) @ q"
proof(induction q xs rule: listenq.induct) 
  case (1 q) (* \<And>q. listenq q emptyq = rev emptyq @ q *)
  thus ?case by auto
next
  case (2 q x xs)  (* \<And>q x xs. listenq (enqueue q x) xs = rev xs @ enqueue q x 
                                  \<Longrightarrow> listenq q (x # xs) = rev (x # xs) @ q *)
  thus ?case by simp
qed

lemma deq2list_ind: "deq2list q xs = q @ xs"
proof(induction q xs rule: deq2list.induct)
  case (1 lst)
  show ?case by auto
next
  case (2 v va lst) 
  obtain xa y where o0: "v # va = y @ [xa]"
    using rev_exhaust by blast 
  hence o1: "dequeue (v # va) = (xa, y)" by simp
  hence o2: "deq2list y (xa # lst) = y @ (xa # lst)" 
    using "2.IH" by auto
  with o1 have "deq2list (v # va) lst = deq2list y (xa # lst)"
    by auto
  thus ?case
    using o1 o2 by auto
qed

lemma deqall_expand_rev: "deq2list (listenq [] xs) [] = rev xs"
proof(induction xs)
case Nil
  thus ?case by auto 
next
  case (Cons a xs)
  thus ?case by (simp add: deq2list_ind listenq_rev)
qed

lemma "dequeue_list q = q"
  apply(simp add:dequeue_list_def)
  using deq2list_ind[of q "[]"] by auto

theorem queue_cor: "dequeue_list (list_enqueue xs) = rev xs"
  apply(simp add:dequeue_list_def list_enqueue_def)
  using deqall_expand_rev by auto

end
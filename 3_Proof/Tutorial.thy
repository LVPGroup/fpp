theory Tutorial
imports Main
begin

(* Basic tactics *)

theorem prop1:
  \<open>(A\<longrightarrow>B\<longrightarrow>C)\<longrightarrow>(A\<longrightarrow>B)\<longrightarrow>A\<longrightarrow>C\<close>
  apply(rule impI)
  apply(rule impI)
  apply(rule impI)
  apply(subgoal_tac \<open>B\<longrightarrow>C\<close>)
  apply(erule mp)
  apply(erule mp)
  apply assumption
  apply(erule mp)
  apply assumption
  done

thm prop1

theorem peirce:
  \<open>((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P\<close>
  apply(subst imp_conv_disj)
  apply(subst imp_conv_disj)
  apply(subst de_Morgan_disj)
  apply(subst not_not)
  apply rule
  apply(erule disjE)
  apply(erule conjE)
  apply assumption
  apply assumption
  done

theorem
  \<open>((P\<longrightarrow>Q)\<longrightarrow>P)\<longrightarrow>P\<close>
  apply(rule impI)
  apply(drule Meson.imp_to_disjD)
  apply(erule disjE)
  apply(drule Meson.not_impD)
  apply(erule conjunct1)
  apply assumption
  done

(* Induction *)

theorem
  \<open>sum (\<lambda>x. (2::nat)^x) {x. x<n} = 2^n-1\<close>
  apply(induct n)
  apply simp
  apply(subgoal_tac \<open>{x. x<Suc n} = insert n {x. x<n}\<close>)
  by auto

primrec rev_append :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>rev_append [] l2 = l2\<close> |
  \<open>rev_append (x#l1) l2 = rev_append l1 (x#l2)\<close>

theorem rev_append_correct:
  \<open>rev_append l1 l2 = rev l1 @ l2\<close>
  by (induct l1 arbitrary: l2) auto

(* Inductive types *)

datatype 'a tree = Leaf | Branch \<open>'a tree\<close> 'a \<open>'a tree\<close>

primrec inorder :: \<open>'a tree \<Rightarrow> 'a list\<close> where
  \<open>inorder Leaf = []\<close> |
  \<open>inorder (Branch left x right) = inorder left @ x # inorder right\<close>

primrec mirror :: \<open>'a tree \<Rightarrow> 'a tree\<close> where
  \<open>mirror Leaf = Leaf\<close> |
  \<open>mirror (Branch left x right) = Branch (mirror right) x (mirror left)\<close>

theorem mirror_correct:
  \<open>inorder (mirror tree) = rev (inorder tree)\<close>
  by (induct tree; simp)

(* Inductive predicates *)

inductive even_ind :: \<open>nat \<Rightarrow> bool\<close> where
  even_0: \<open>even_ind 0\<close> |
  even_SS: \<open>even_ind n \<Longrightarrow> even_ind (Suc (Suc n))\<close>

thm even_0 even_SS
thm even_ind.induct

theorem \<open>even_ind n = even n\<close>
proof
  assume \<open>even_ind n\<close>
  then show \<open>even n\<close>
    by induct auto
next
  assume \<open>even n\<close>
  then have \<open>\<exists>k. n=k+k\<close> by presburger
  then obtain k where k: \<open>n=k+k\<close> by blast
  have \<open>even_ind (k+k)\<close>
    by (induct k) (auto intro: even_ind.intros)
  then show \<open>even_ind n\<close> using k by simp
qed

theorem
  fixes list::\<open>'a::order list\<close>
  assumes assum: \<open>\<forall>i. Suc i < length list \<longrightarrow> list!i \<le> list!(Suc i)\<close>
  shows \<open>\<forall>i j. j < length list \<longrightarrow> i\<le>j \<longrightarrow> list!i \<le> list!j\<close>
proof clarify
  fix i j :: nat
  assume j_less: \<open>j < length list\<close>
  assume \<open>i\<le>j\<close>

  then obtain k where k: \<open>i+k=j\<close>
    using le_Suc_ex by blast

  from k j_less
  have \<open>list!i \<le> list!(i+k)\<close>
  proof (induct k arbitrary: j)
    (* Case 1: k=0 *)
    show \<open>list!i \<le> list!(i+0)\<close> by simp
  next
    (* Case 2: k = Suc k' *)
    fix k' j
    assume IH: \<open>\<And>j. i+k'=j \<Longrightarrow> j<length list \<Longrightarrow> list!i \<le> list!(i+k')\<close>
    assume a1: \<open>i+Suc k'=j\<close>
    assume a2: \<open>j<length list\<close>

    from a1 a2 have *: \<open>Suc (i+k') < length list\<close> by simp
    with IH have \<open>list!i \<le> list!(i+k')\<close> by simp
    also from assum[rule_format, OF *] have \<open>list!(i+k') \<le> list!Suc (i+k')\<close> .
    finally show \<open>list!i \<le> list!(i+Suc k')\<close> by simp
  qed

  with k show \<open>list!i \<le> list!j\<close> by simp
qed

end
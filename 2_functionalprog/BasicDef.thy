theory BasicDef
  imports Main HOL.Real
begin

subsection \<open>Bool\<close>

value "True \<and> False"

value "True \<longrightarrow> False"

value "False \<longrightarrow> True"

definition "TRUE \<equiv> True"

definition "FALSE \<equiv> False"

definition "A \<equiv> TRUE \<and> FALSE"
value A

consts boolconst :: bool
specification (boolconst)
   "boolconst = False"
  by auto

definition AND :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "AND a b \<equiv> \<not>a \<and> \<not>b"

definition "lAND \<equiv> \<lambda>a b. \<not>a \<and> \<not>b"

value "AND True False"
value "lAND True False"
value "True \<and> False"

lemma "\<forall>a b. (AND a b) = (\<not>(a \<or> b))" 
  by (simp add:AND_def)

lemma "\<forall>a b. (AND a b) = (lAND a b)"
  by (simp add:AND_def lAND_def)

subsection \<open>Nat number\<close>

value "3::nat"

value "(1::nat) + 2"

value "(3::nat) - 2"

value "(2::nat) * 2"

value "(2::nat)^3"

value "(8::nat) div 3"

value "(6::nat) mod 4"

value "(2::nat) dvd 6"

value "(2::nat) < 4"

value "(2::nat) \<le> 4"

value "min (2::nat) 4"

value "max (2::nat) 4"

value "Min {1::nat, 3, 4}"

value "Max {1::nat, 3, 4}"

(* value "of_nat (5::nat)" *)

(* value "op ^^ (\<lambda>x::nat. x + 2) 3 4" *)


definition next_nat :: "nat \<Rightarrow> nat"
  where "next_nat n \<equiv> Suc n"

definition next_nat2 :: "nat \<Rightarrow> nat"
  where "next_nat2 n \<equiv> n + 1"

lemma "next_nat n = next_nat2 n"
  by (simp add: next_nat_def next_nat2_def)

definition times5 :: "nat \<Rightarrow> nat"
  where "times5 n \<equiv> 5 * n"

definition greater :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "greater m n \<equiv> (m > n)"

definition greater2 :: "(nat \<times> nat) \<Rightarrow> bool"
  where "greater2 mn \<equiv> (fst mn > snd mn)"

definition greater3 :: "(nat \<times> nat) \<Rightarrow> bool"
  where "greater3 \<equiv> \<lambda>(m,n). (m > n)"

definition greater4 :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "greater4 \<equiv> \<lambda>m n. (m > n)"

lemma "\<forall>m n. greater2 (m,n) = greater3 (m,n)"
   by (simp add: greater2_def greater3_def) 

lemma "\<forall>m n. greater3 (m,n) = greater4 m n"
  by (simp add: greater3_def greater4_def) 

value "greater4 10"

(* value "greater3 10" *)

subsection \<open>integer\<close>

value "- (4::int)"

value "(5::int) div 3"

value "sgn (- (15::int))"

definition test :: "int \<rightharpoonup> int"
  where "test n \<equiv> (if n > 0 then Some n else None)"


subsection \<open>function type\<close>

definition f :: "nat \<Rightarrow> nat"
  where "f x \<equiv> 2 * x + 1"

definition g :: "nat \<Rightarrow> nat"
  where "g x \<equiv> 3 * x + 1"

term f
term g

term "True"

definition h :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "h x y \<equiv> x + y"

term h

definition h2 :: "(nat \<times> nat) \<Rightarrow> nat"
  where "h2 \<equiv> \<lambda>(x,y). x + y"

value "h 3 5"
value "h 3"
value "h2 (3,5)"

(* value "h2 3" *)

subsection \<open>term, expression, formula\<close>

consts cst1 :: int
specification(cst1)
  "cst1 = 1" by simp

consts cst2 :: int
specification(cst2)
  "cst2 > 1"
  using gt_ex by auto

definition "cst3 = (3::int)"
term cst3

thm cst3_def

consts fun1 :: "nat \<Rightarrow> nat"
specification(fun1)
  fun1def: "fun1 n = Suc n"
  by auto

lemma "fun1 2 = 3"
  using fun1def by simp

axiomatization fun2 :: "nat \<Rightarrow> nat" where fun2_def: "fun2 n = n + 2"

lemma "fun2 5 = 7"
  using fun2_def by simp

definition fun2' :: "nat \<Rightarrow> nat"
  where "fun2' n \<equiv> n + 2"

lemma "fun2 = fun2'"
  using fun2_def fun2'_def by auto

term "cst1"

term "''a string''"

term "\<lambda>x. y"
value "(\<lambda>x. y) a"

term "\<lambda>x. True"
value "(\<lambda>x. True) 2"
value "(\<lambda>x. True) ''abc''"
value "(\<lambda>x. True) 2.0"

term "\<lambda>x. Suc x"
value "(\<lambda>x. Suc x) 5"

term "\<lambda>x. (x::int) + 10"

term "\<lambda>x. \<lambda>y. x * y"
term "\<lambda>x y. x * y"
value "(\<lambda>x y. x * y) (5::int) (6::int)"
value "(\<lambda>x y. x * y) (5.0::real) (6::int)"
value "(\<lambda>x y. x * y) (5.0::real) (6.5::real)"

term "\<lambda>x y. (x::int) * y"
value "(\<lambda>x y. (x::int) * y) 5 6"

term "\<lambda>x. (x::int) + a"
value "(\<lambda>x. (x::int) + a) 1"

lemma "(\<lambda>x y. x * y) = (\<lambda>x. \<lambda>y. x * y)"
  by simp

definition "lam1 \<equiv> \<lambda>x y z. (if x \<ge> y then
                               if x \<ge> z then x else z
                             else 
                               if y \<ge> z then y else z)"
term "lam1"
value "lam1 (2::int) 3 1"

definition "lam2 \<equiv> \<lambda>f x. f x"
term "lam2"
value "lam2 Suc 1"

term "(\<lambda>f x. f x)"
value "(\<lambda>f x. f x) Suc 1"

definition "lam3 \<equiv> \<lambda>f g x y. f (g x y)"
value "lam3 Suc plus 10 20"
term "(\<lambda>f g x y. f (g x y))"
value "(\<lambda>f g x y. f (g x y)) Suc plus 10 20"

definition f1 :: "nat \<Rightarrow> nat"
  where "f1 \<equiv> \<lambda>x. 2 * x + 1"

definition g1 :: "nat \<Rightarrow> nat"
  where "g1 \<equiv> \<lambda>x. 3 * x + 1"

lemma "f1 = f"
  unfolding f_def f1_def by auto

lemma "g1 = g"
  unfolding g_def g1_def by auto

definition addint :: "int \<Rightarrow> int"
  where "addint i \<equiv> i + 1"

definition addint2 :: "int \<Rightarrow> int"
  where "addint2 \<equiv> \<lambda>i. (i + 1)"

thm addint_def

lemma "addint = addint2"
  unfolding addint_def addint2_def by simp

lemma "addint = (\<lambda>i. (i + 1))"
  unfolding addint_def by simp


definition if1 :: "bool \<Rightarrow> string"
  where "if1 b \<equiv> if b then 
                    ''its true'' 
                 else ''its false''"
value "if1 True"
value "(\<lambda>b. if b then 
              ''its true'' 
            else ''its false'') True"

term "if b then e1 else e2"


term "let x = i; y = i + 1 in (x + y) * 2"

definition let1 :: "nat \<Rightarrow> nat"
  where "let1 i = (let x = i; y = i + 1 in (x + y) * 2)"

value "let1 3"

lemma "(let x = i; y = i + 1 in (x + y) * 2) = (i + (i + 1)) * 2"
  by simp

definition let2 :: "nat \<Rightarrow> nat"
  where "let2 i = (let x = i; y = i + 1 in
                    (\<lambda>x. (Suc x) + y) x + (\<lambda>y. (Suc y) + x) y)"

lemma "let x = i; y = i + 1 
       in (\<lambda>x. (Suc x) + y) x + (\<lambda>y. (Suc y) + x) y = ((\<lambda>x. (Suc x) + (i + 1)) i + (\<lambda>y. (Suc y) + i) (i + 1))"
  by simp

value "let2 3"


term "let x = (5::nat) in x * 2"


definition case1 :: "nat \<Rightarrow> string"
  where "case1 n \<equiv> case n of 0 \<Rightarrow> ''zero'' |
                             (Suc m) \<Rightarrow> ''not zero''"

primrec case2 :: "nat \<Rightarrow> string"
  where "case2 0 = ''zero''" |
        "case2 (Suc m) = ''not zero''"

lemma "case1 x = case2 x" 
  apply(simp add:case1_def) apply(induct x) apply(cases x) by simp+ 

value "case1 0"
value "case1 1"



end
  
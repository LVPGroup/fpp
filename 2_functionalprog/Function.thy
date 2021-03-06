theory Function
  imports HOL.Fun Main HOL.Real "~~/src/HOL/ex/Sqrt"
begin

subsection \<open>function and relation\<close>

type_synonym ('a, 'b) rel = "('a \<times> 'b) set" 

definition func :: "('a, 'b) rel \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("_ : _ \<rightarrow> _" [80,80,80] 81)
  where "func f X Y \<equiv> f \<subseteq> X \<times> Y \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and> Domain f = X
                        \<and> (\<forall>x y1 y2. (x, y1)\<in>f \<and> (x, y2)\<in>f \<longrightarrow> y1 = y2)" 


subsection \<open>total and partial function\<close>

definition sqrt :: "real \<rightharpoonup> real"
  where "sqrt r \<equiv> (if r \<ge> 0 then Some (root 2 r) else None)"

definition Pred :: "nat \<rightharpoonup> nat"
  where "Pred n \<equiv> (if n > 0 then Some (n - 1) else None)"

value "Pred 9"
value "Pred 0"

definition minus_nat :: "nat \<Rightarrow> nat \<rightharpoonup> nat"
  where "minus_nat a b \<equiv> (if a \<ge> b then Some (a - b) else None)"

value "minus_nat 6 3"

value "minus_nat 3 8"

subsection \<open>injective, surjective, bijective\<close>

definition add1 :: "nat \<Rightarrow> nat"
  where "add1 n \<equiv> n + 1"

lemma "inj add1 = True" 
  unfolding add1_def by auto

lemma "surj add1 = False"
  apply(simp add:add1_def surj_def)
  apply(rule_tac x = 0 in exI)
  by auto

definition add2 :: "real \<Rightarrow> real"
  where "add2 r \<equiv> r + 1"

lemma add2_lm1: "inj add2 = True"
  by (simp add:add2_def inj_def)

lemma add2_lm2: "surj add2 = True"
  apply (simp add:add2_def surj_def) 
  apply(rule allI)
  by (metis add_diff_cancel_left' diff_minus_eq_add)
  
lemma "bij add2 = True"
  using add2_lm1 add2_lm2 by (simp add:bij_def)


lemma "f = g \<longleftrightarrow> (\<forall>x. f x = g x)"
  by auto

lemma "f = g \<longleftrightarrow> {(x,y). y = f x} = {(x,y). y = g x}"
  by auto


subsection \<open>function operation\<close>

definition fun1 :: "int \<Rightarrow> int"
  where "fun1 x \<equiv> x + 1"

value "fun_upd f a b"
value "f(a := b)"

value "fun1 2"

term "fun1(2 := 2)"

value "(fun1(2 := 2)) 2"

value "(fun1(1 := 1, 2 := 2, 3 := 3)) 2"
value "(fun1(1 := 1, 2 := 2, 3 := 3)) 1"
value "(fun1(1 := 1, 2 := 2, 3 := 3)) 3"

value "(fun1(x := y)) x"

lemma "(f(x := y)) x = y"
  by auto

lemma "z \<noteq> x \<Longrightarrow> (f(x := y)) z = f z"
  by auto

lemma "f(x := y, x := z) = f(x := z)"
  by auto

value "(fun1(x := y, x := z)) x"

definition "fun2 x \<equiv> fun1 x * 2"
value "fun2 3"

definition "fun3 \<equiv> (\<lambda>x. (fun1(x := fun1 x * 2)) x)"
value "fun3 3"

definition fun4 :: "int \<Rightarrow> int"
  where "fun4 x \<equiv> x * 2"
value "fun4 ` {1,2,3}"

value "fun4 ` {1..10}"

lemma "fun4 ` {x. x > 5 \<and> x < 12} = {12,14,16,18,20,22}"
  using fun4_def by auto

thm fun4_def
thm swap_def

definition "fun5 \<equiv> Fun.swap 2 3 fun4"

value "fun4 2"
value "fun4 3"
value "fun5 2"
value "fun5 3"

lemma "(Fun.swap a b f) a = f b"
  by auto

lemma "(Fun.swap a b f) b = f a"
  by auto

lemma "c \<noteq> a \<and> c \<noteq> b \<Longrightarrow> Fun.swap a b f c = f c"
  by auto

definition suc :: "int \<Rightarrow> int"
  where "suc n \<equiv> n + 1"

lemma bij_suc: "bij suc"
  unfolding suc_def bij_def inj_def surj_def 
  apply(rule conjI)
  apply auto apply(rule_tac x = "y - 1" in exI) by simp

definition "suc_inv \<equiv> the_inv suc"

definition pred :: "int \<Rightarrow> int"
  where "pred n \<equiv> n - 1"

value "pred 1"
value "pred 0"

lemma "suc_inv x = pred x"
  unfolding suc_inv_def pred_def the_inv_into_def suc_def using bij_suc by force

definition suc2 :: "nat \<Rightarrow> nat"
  where "suc2 n \<equiv> n + 2"

lemma "inj suc2"
  unfolding suc2_def inj_def by simp

definition "suc2_inv = the_inv suc2"

lemma "suc2_inv 3 = 1"
  unfolding suc2_inv_def the_inv_into_def suc2_def by simp

lemma "suc2_inv 1 = 0" (* its wrong *)
   sorry

definition pred2 :: "nat \<Rightarrow> nat"
  where "pred2 n \<equiv> n - 2"

value "pred2 1"
value "pred2 0"

definition f6 :: "int \<Rightarrow> int"
  where "f6 x \<equiv> (if x < 0 then x + 1 else 10)"

value "f6 (-2)"
value "f6 2"
value "f6 3"

lemma "\<not>(\<exists>x. f6 x = 5)"
  unfolding f6_def by simp

definition "f6_inv \<equiv> the_inv f6"

lemma "f6_inv (-1) = -2"
  unfolding f6_inv_def the_inv_into_def f6_def by auto

definition f7 :: "int \<Rightarrow> int"
  where "f7 n \<equiv> n + 2"

definition g7 :: "int \<Rightarrow> int"
  where "g7 n \<equiv> n * 2"

value "(f7 \<circ> g7) 3"
value "(g7 \<circ> f7) 3"

lemma "(f7 \<circ> g7) x = x * 2 + 2"
  unfolding f7_def g7_def comp_def by simp

lemma "(g7 \<circ> f7) x = (x + 2) * 2"
  unfolding f7_def g7_def comp_def by simp

lemma "(f \<circ> g) x = f (g x)"
  by auto

lemma "(g \<circ> f) x = g (f x)"
  by auto

lemma "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  by auto

value "id (2::int)"
value "id ''hello''"
value "id (0::nat)"
value "id (2.0 :: real)"

lemma "f \<circ> id = f"
  by auto

lemma "id \<circ> f = f"
  by auto


subsection \<open>polymorphism\<close>

definition addi :: "int \<Rightarrow> int \<Rightarrow> int"
  where "addi x y \<equiv> x + y"

definition first :: "('a \<times> 'b) \<Rightarrow> 'a"
  where "first p \<equiv> case p of (a,b) \<Rightarrow> a"

definition second :: "('a \<times> 'b) \<Rightarrow> 'b"
  where "second p \<equiv> case p of (a,b) \<Rightarrow> b"

value "first (2::int, 3::nat)"
value "second (2::int, 3::nat)"
value "first (2.0::real, ''hello'')"
value "second (2.0::real, ''hello'')"

type_synonym 'a array = "'a list"

primrec array_assn :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" ("_[_] := _")
  where "array_assn [] i v = []" |
        "array_assn (x # xs) i v =
            (case i of 0 \<Rightarrow> v # xs | 
                  Suc j \<Rightarrow> x # list_update xs j v)"

definition query :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" ("_[_]")
  where "arr[i] \<equiv> arr ! i"

definition arr1 :: "int array"
  where "arr1 \<equiv> [1,2,3]"
definition "arr2 \<equiv> arr1[1] := 8"
value "arr2[1]"

definition arr3 :: "string array"
  where "arr3 \<equiv> [''aaaa'',''bbbb'',''cccc'']"
definition "arr4 \<equiv> arr3[1] := ''eeee''"
value "arr4[1]"

type_synonym ('k,'v) kvstore = "'k \<rightharpoonup> 'v"

definition getv :: "('k,'v) kvstore \<Rightarrow> 'k \<Rightarrow> 'v option"
  where "getv m k \<equiv> m k"

definition update :: "('k,'v) kvstore \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) kvstore" ("_ [_ :\<rightarrow> _]")
  where "update m k v \<equiv> m(k:= Some v)"

datatype 'v valT = I int | S string | L "'v list" | T "'v set"

record info = name :: string
              addr :: string
              val  :: int

type_synonym imap = "(int, info valT) kvstore"
type_synonym smap = "(string, info valT) kvstore"

definition kvs1 :: "imap"
  where "kvs1 \<equiv> (\<lambda>i. None)"

value "kvs1 1"

definition "kvs2 \<equiv> kvs1[1 :\<rightarrow> (S ''hello'')]"
value "kvs2 1"
definition "kvs3 \<equiv> kvs2[2 :\<rightarrow> (T {\<lparr>name = ''david'',addr = ''beijing'', val = 1\<rparr>})]"
value "kvs3 1"
value "kvs3 2"

definition kvs4 :: "imap"
  where "kvs4 \<equiv> \<lambda>x::int. if x > 5 \<and> x < 10 then Some (I x) else kvs3 x"

value "kvs4 1"
value "kvs4 2"
value "kvs4 4"
value "kvs4 6"

value "(2::int) + (3::int)"
value "(2.5::real) + (3::int)"
value "(2.5::real) + (3.4::real)"



end
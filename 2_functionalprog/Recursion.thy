theory Recursion
  imports HOL.Fun Main 
begin

subsection \<open>primitive recursive functions\<close>

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "add x 0 = x" |
        "add x (Suc y) = Suc (add x y)"

value "add 5 6"

primrec prede :: "nat \<Rightarrow> nat"
  where "prede 0 = 0" |
        "prede (Suc x) = x"

primrec sub :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sub x 0 = x" |
        "sub x (Suc y) = prede (sub x y)"

value "sub 8 2"
value "sub 2 5"

primrec time :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "time x 0 = 0" |
        "time x (Suc y) = add (time x y) x"

value "time 5 6"

primrec fact :: "nat \<Rightarrow> nat"
  where "fact 0 = 1" |
        "fact (Suc n) = time (fact n) (add n 1)"

value "fact 5"

primrec exp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "exp x 0 = 1" |
        "exp x (Suc y) = time (exp x y) x"

value "exp 2 5"


subsection \<open>total recursive functions\<close>

fun A :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "A 0 n = n + 1" |
        "A (Suc m) 0 = A m 1" |
        "A (Suc m) (Suc n) = A m (A (Suc m) n)"

value "A 3 3"

(*
primrec fib2 :: "nat \<Rightarrow> nat"
  where "fib2 0 = 1" |
        "fib2 (Suc n) = (case n of 0 \<Rightarrow> 1 |
                                  Suc m \<Rightarrow> fib2 m + fib2 n)"
*)

fun fib :: "nat \<Rightarrow> nat"
  where "fib 0 = 1" |
        "fib (Suc 0) = 1" |
        "fib (Suc (Suc n)) = fib n + fib (Suc n)"

value "fib 9"


primrec sep0 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "sep0 [] a = []" |
        "sep0 (x # xs) a = 
            (case xs of [] \<Rightarrow> [x] |
                        _ \<Rightarrow> x#a#(sep0 xs a))"

value "sep0 [a,b,c,d,e,f] x"

fun sep :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "sep [] a = []" |
        "sep [x] a = [x]" |
        "sep (x#y#zs) a = x # a # sep (y#zs) a"

value "sep [a,b,c,d,e,f] x"


subsection \<open>fun vs. function\<close>

function f1 :: "nat \<Rightarrow> nat"
  where "f1 0 = f1 1" |
        "f1 n = f1 (Suc n)"
  by auto  
termination sorry (* this function is not terminated *)

fun fib2 :: "nat \<Rightarrow> nat"
  where "fib2 0 = 1" |
        "fib2 (Suc 0) = 1" |
        "fib2 (Suc (Suc 0)) = 2" |
        "fib2 (Suc (Suc n)) = fib2 n + fib2 (Suc n)"

value "fib2 0"
value "fib2 2"
value "fib2 9"

function fib3 :: "nat \<Rightarrow> nat"
where  "fib3 0 = 1" |
       "fib3 1 = 1" |
(*     "fib3 2 = 2" | *)
      "fib3 (n + 2) = fib3 n + fib3 (n + 1)"
apply atomize_elim
apply arith
  by auto 
termination by lexicographic_order


lemma "fib3 0 = 1"
  by simp

lemma "fib3 2 = 2"
  using fib3.simps(1) fib3.simps(2) fib3.simps(3)[of 0]
    by (metis add.left_neutral one_add_one)



function ev :: "nat \<Rightarrow> bool"
  where "ev (2 * n) = True" | 
        "ev (2 * n + 1) = False"
apply atomize_elim
  by arith+
termination by (relation "{}") simp

(*
function ev_case :: "nat \<Rightarrow> bool"
  where "ev_case n = (case n of (2 * m) \<Rightarrow> True |
                                (2 * m + 1) => False)"
*)

lemma "ev 4 = True"
  using ev.simps(1)[of 2] by simp

lemma "ev 102 = True"
  using ev.simps(1)[of 51] by simp

lemma "ev 101 = False"
  using ev.simps(2)[of 50] by simp


subsection \<open>pattern match\<close>

definition first :: "('a \<times> 'b) \<Rightarrow> 'a"
  where "first p \<equiv> case p of (a,_) \<Rightarrow> a"

definition second :: "('a \<times> 'b) \<Rightarrow> 'b"
  where "second p \<equiv> case p of (_,b) \<Rightarrow> b"

primrec gt0 :: "nat \<Rightarrow> bool"
  where "gt0 0 = False" |
        "gt0 (Suc _) = True"


fun addcase :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "addcase x y = 
          (case y of 0 \<Rightarrow> x |
               (Suc z) \<Rightarrow> Suc (add x z))"

value "addcase 5 6"

fun sep0case :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "sep0case xs a = 
    (case xs of [] \<Rightarrow> [] |
                (x # xs) \<Rightarrow> (case xs of [] \<Rightarrow> [x] |
                                        _ \<Rightarrow> x#a#(sep0 xs a)))"

value "sep0case [a,b,c,d,e,f] x"

fun sep2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" 
  where "sep2 (x#y#zs) a = x # a # sep2 (y#zs) a" |
        "sep2 xs a = xs"

thm sep2.simps

fun fib1_case :: "nat \<Rightarrow> nat"
  where "fib1_case n = 
            (case n of 0 \<Rightarrow> 1 |
                      (Suc 0) \<Rightarrow> 1 |
                      (Suc (Suc n)) \<Rightarrow> fib1_case n + fib1_case (n + 1))"

value "fib1_case 6"

fun len2 :: "'a list \<Rightarrow> bool"
  where "len2 [] = False" |
        "len2 [_] = False" |
        "len2 (_#_#_) = True"

value "len2 [x]"
value "len2 [x,y]"

function gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gcd x 0 = x" | 
        "gcd 0 y = y" | 
        "x < y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (Suc x) (y - x)" | 
        "x \<ge> y \<Longrightarrow> gcd (Suc x) (Suc y) = gcd (x - y) (Suc y)"
by (atomize_elim, auto, arith)
termination by lexicographic_order

lemma "gcd 8 24 = 8"
  using gcd.simps(3)[of 7 23] gcd.simps(3)[of 7 15] 
        gcd.simps(4)[of 7 7] gcd.simps(2)[of "Suc 7"]
  by force

(*
function check :: "string \<Rightarrow> bool"
  where "check (''good'') = True" | 
        "check s = False"
     apply auto[1] apply simp
     *)

function check :: "string \<Rightarrow> bool"
  where "check ''good'' = True" | 
        "s \<noteq> ''good'' \<Longrightarrow> check s = False"
  by auto
termination by (relation "{}") simp

value "check ''good''"
lemma "check ''aaaa'' = False"
  using check.simps(2) by simp

definition check3 :: "string \<Rightarrow> bool"
  where "check3 s \<equiv> (s = ''good'')"

value "check3 ''good''"

subsection \<open>mutual, nested, high-order recursion\<close>

function even :: "nat \<Rightarrow> bool"
     and odd :: "nat \<Rightarrow> bool"
where "even 0 = True" | 
      "odd 0 = False" | 
      "even (Suc n) = odd n" | 
      "odd (Suc n) = even n"
  by pat_completeness auto
termination by lexicographic_order

value "even 4"


function nest :: "nat \<Rightarrow> nat"
  where "nest 0 = 0" |
        "nest (Suc n) = nest ((nest n))"
  by pat_completeness auto

lemma nest_is_zero: "nest_dom n \<Longrightarrow> nest n = 0"
  by (induct rule:nest.pinduct) (auto simp: nest.psimps)

termination 
  by (relation "measure (\<lambda>n. n)") (auto simp: nest_is_zero)


lemma "nest n = 0"
  apply(induct n)
  using nest.simps by simp+
  
subsection \<open>tail recursion\<close>

fun fact_help :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "fact_help i a = 
    (if i = 0 then a 
      else fact_help (i - 1) (i * a))"


definition fact2 :: "nat \<Rightarrow> nat"
  where "fact2 m \<equiv> fact_help m 1"


end
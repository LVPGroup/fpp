theory Listprog
  imports Main 

begin

subsection \<open>define lists\<close>

definition lst1 :: "int list"
  where "lst1 \<equiv> Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))"

value "lst1"

definition lst2 :: "int list"
  where "lst2 \<equiv> 1 # (2 # (3 # (4 # [])))"

value "lst2"

definition lst3 :: "int list"
  where "lst3 \<equiv> [1,2,3,4]"

definition lst4 :: "int list"
  where "lst4 \<equiv> [1..4]"
value "lst4"

definition lst5 :: "nat list"
  where "lst5 \<equiv> [1..<5]"

lemma "lst1 = lst2"
  by (simp add: lst1_def lst2_def)

lemma "lst2 = lst3"
  by (simp add: lst2_def lst3_def)

definition "lst6 \<equiv> [''aa'',''bb'',''cc'',''dd'']"

subsection \<open>functions on lists\<close>

value "hd [a,b,c,d,e]"
value "last [a,b,c,d,e]"
value "tl [a,b,c,d,e]"
value "butlast [a,b,c,d,e]"
value "[a,b,c,d,e]!0"
value "[a,b,c,d,e]!7"
value "nths [(1::int)..20] {1,3,5,7}"
value "nths [(1::int)..20] {5,6,7,8}"
value "length [(10::int)..20]"
value "take 5 [(1::int)..20]"
value "takeWhile (\<lambda>x. 2 dvd x) [(1::int)..20]"
value "takeWhile (\<lambda>x. x < 8) [(1::int)..20]"
value "distinct [(1::int)..20]"
value "distinct [a,b,c,d,a]"



value "[a,b,c]@[d,e,f]"
value "concat [[a,b,c],[c,d,e],[e,f,g]]"
value "replicate 4 a"
value "rev [a,b,c,d,e]"
value "rotate1 [(1::int)..6]"
value "rotate 4 [(1::int)..10]"
lemma "rotate n = (rotate1^^n)"
  by (simp add:rotate_def)
value "splice [a1,a2,a3,a4] [b1,b2,b3,b4,b5]"
value "splice [(1::int)..8] [(11::int)..15]"
definition "lst7 \<equiv> [(1::int)..5]"
value "list_update lst7 2 8"
value "lst7[2 := 8]"
value "drop 5 [(1::int)..10]"
value "dropWhile (\<lambda>x. x < 8) [(1::int)..10]"
value "dropWhile (\<lambda>x. 2 dvd x) [(1::int)..20]"
value "remdups [(1::int),1,2,2,3,4,5,1,1,6,3,7]"
value "remove1 2 [(1::int),1,2,2,3,4,5,1,1,6,3,7]"
value "removeAll 2 [(1::int),1,2,2,3,4,5,1,1,6,3,7]"




value "set [a,b,c,d]"
value "set [(1::int),2,3,4,2,3,4,6]"
value "zip [a,b,c,d] [(1::int)..8]"



value "filter (\<lambda>x. 2 dvd x) [(1::int)..20]"
value "find (\<lambda>x. 5 dvd x) [(1::int)..20]"
value "find (\<lambda>x. x > 30) [(1::int)..20]"
value "sort [(4::int), 6,1,9,20]"
value "sorted [(4::int), 6,1,9,20]"
value "sorted [(1::int)..20]"

lemma "sorted (sort lst)"
  using sorted_sort by simp


value "sum_list [1::int,2,3,4]"
value "sum_list [a,b,c,d]"
value "prod_list [1::int,2,3,4,5]"
value "prod_list [a,b,c,d]"


subsection \<open>string by list\<close>


definition "charAt str n \<equiv> str ! n"
definition "compareTo str1 str2 \<equiv> (str1 = str2)"
value "charAt ''abcde'' 2"
value "compareTo ''abc'' ''abcd''"

primrec startsWith :: "string \<Rightarrow> string \<Rightarrow> bool"
  where "startsWith str []  = True" |
        "startsWith str (x # xs) = (case str of 
            [] \<Rightarrow> False |
            (y # ys) \<Rightarrow> x = y \<and> startsWith ys xs)"

value "startsWith ''abcde'' ''ab''"

definition "endsWith str suffix \<equiv> startsWith (rev str) (rev suffix)"

value "endsWith ''aabbdedc'' ''edc''"

primrec contains :: "string \<Rightarrow> string \<Rightarrow> bool"
  where "contains [] str = 
          (if str = [] then True else False)" |
        "contains (x # xs) str = 
            (if startsWith (x#xs) str then True 
              else contains xs str)"

value "contains ''abcde'' ''bc''"

definition "substring str m n \<equiv> take (n - m) (drop m str)"
value "substring ''12345678'' 2 5"

fun indexOf0 :: "string \<Rightarrow> string \<Rightarrow> (int \<times> int)"
  where "indexOf0 [] sub = 
            (if sub = [] then (0,0) else (-1,-1))" |
        "indexOf0 (x # xs) sub = 
            (if startsWith (x#xs) sub then (0,0)  
             else 
                let idx = indexOf0 xs sub in
                  (fst idx + 1, snd idx))"

definition "indexOf str sub \<equiv> 
              (let idx = indexOf0 str sub in
                  if snd idx = -1 then -1 
                  else fst idx)"

value "indexOf ''abcde'' ''cde''"

subsection \<open>stack\<close>

type_synonym 'a stack = "'a list"

definition push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack"
  where "push a stk \<equiv> a # stk"

(*definition pop :: "'a stack \<Rightarrow> ('a \<times> 'a stack)"
  where "pop s \<equiv> (hd s, tl s)"*)
primrec pop :: "'a stack \<Rightarrow> ('a \<times> 'a stack)" 
where "pop (x # xs) = (x, xs)"

definition empty :: "'a stack \<Rightarrow> 'a stack"
  where "empty s = []"

definition top :: "'a stack \<Rightarrow> 'a"
  where "top s \<equiv> hd s"

fun search0 :: "'a stack \<Rightarrow> 'a \<Rightarrow> (int \<times> int)"
  where "search0 [] a = (-1, -1)" |
        "search0 (x#xs) a = 
            (if x = a then (0,0) else 
                let idx = search0 xs a in
                  (1 + fst idx,snd idx))"

definition "search st a \<equiv> 
              (let idx = search0 st a in
                  if snd idx = -1 then -1 
                  else fst idx)"

value "search [1::int,2,3,4,5] 4"

value "push a [b,b,b]"
value "pop [a,b,c,d]"
value "top [a,b,c,d]"

subsection \<open>FIFO queue\<close>

type_synonym 'a queue = "'a list \<times> nat"

definition initq :: "nat \<Rightarrow> 'a queue"
  where "initq msize \<equiv> ([]::'a list, msize)"

definition enque :: "'a queue \<Rightarrow> 'a \<Rightarrow> ('a queue \<times> bool)"
  where "enque q a \<equiv> 
          (if length (fst q) = snd q then (q, False)
           else ((a # fst q, snd q), True))"

definition deque :: "'a queue \<Rightarrow> ('a queue \<times> 'a option)"
  where "deque q \<equiv> 
            (if fst q = [] then (q, None)
             else ((butlast (fst q), snd q), 
                    Some (last (fst q))))"

definition q1 :: "int queue"
  where "q1 = (initq 2)"

value "q1"
value "enque (fst (enque q1 0)) 1"
value "enque (fst (enque (fst (enque q1 0)) 1)) 2"

value "enque ([1::int,2,3,4,5],5) 0"

value "deque ([]::int list,6)"

end

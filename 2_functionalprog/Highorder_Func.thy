theory Highorder_Func
  imports Main HOL.Real
begin

subsection \<open>first and high order functions\<close>

definition fof1 :: "nat \<Rightarrow> nat"
  where "fof1 x \<equiv> x ^ 2"

value "fof1 2"

fun fof2 :: "(nat \<times> nat) \<Rightarrow> nat"
  where "fof2 (x,y) = x + y"

value "fof2 (2,3)"

fun fof3 :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat"
  where "fof3 (x,y,z) = x + y * z"

value "fof3 (2,3,4)"

definition arith :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "arith ops x y \<equiv> ops x y"

value "arith plus 10 20"
value "arith minus 10 20"

definition hof1 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "hof1 f x y \<equiv> f x y"

value "hof1 plus (1::int) 2"
value "hof1 times (3::int) 4"
value "hof1 plus (1.5::real) 2"
value "hof1 append ''hello'' ''world''"
value "hof1 append [a,b,c] [e,f,g]"

subsection \<open>types of high-order functions\<close>

type_synonym ('a,'b,'c,'d) hoftype0 = "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"
type_synonym ('a,'b,'c,'d) hoftype1 = "'a \<Rightarrow> ('b \<Rightarrow> ('c \<Rightarrow> 'd))"
type_synonym ('a,'b,'c,'d) hoftype2 = "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'd"
type_synonym ('a,'b,'c,'d) hoftype3 = "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd)"
type_synonym ('a,'b,'c,'d) hoftype4 = "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd"

definition hoft0 :: "(int, int, int, int) hoftype0"
  where "hoft0 \<equiv> (\<lambda>a. \<lambda>b. \<lambda>c. a + b + c)"

definition hoft1 :: "(int, int, int, int) hoftype1"
  where "hoft1 \<equiv> (\<lambda>a. \<lambda>b. \<lambda>c. a + b + c)"


definition hoft2 :: "(int, int, int, int) hoftype2"
  where "hoft2 \<equiv> \<lambda>f. 1"

definition hoft3 :: "(int, int, int, int) hoftype3"
  where "hoft3 \<equiv> (\<lambda>f. (\<lambda>x. f x + 1))"

definition hoft4 :: "(int, int, int, int) hoftype4"
  where "hoft4 \<equiv> (\<lambda>f. \<lambda>x. f x + 1)"

subsection \<open>definition and usage of high-order functions\<close>
definition hof2 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c)"
  where "hof2 x f \<equiv> f x"

term "hof2 (1::int) plus"
term "hof2 (2::int) plus"

lemma "hof2 (1::int) plus = (\<lambda>x. x + 1)"
  unfolding hof2_def by auto

lemma "hof2 (2::int) plus = (\<lambda>x. x + 2)"
  unfolding hof2_def by auto

lemma "hof2 (m::nat) plus = (\<lambda>x. x + m)"
  unfolding hof2_def by auto

lemma "hof2 (n::nat) times = (\<lambda>x. x * n)"
  unfolding hof2_def by auto


type_synonym hoftype = "real \<Rightarrow> real"
definition limit :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" 
  where "limit f x\<^sub>0 A \<equiv> 
    \<forall>(\<epsilon>::real)>0. (\<exists>\<delta>>0. (\<forall>x. 0 < \<bar>x - x\<^sub>0\<bar> \<and> \<bar>x - x\<^sub>0\<bar> < \<delta> 
                                \<longrightarrow> \<bar>f(x) - A\<bar> < \<epsilon>))"


primrec map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "map f [] = []" |
        "map f (x # xs) = f x # map f xs"

definition "f1 x \<equiv> x^2"
definition "l1 \<equiv> [1::int, 2, 3, 4, 5, 6]"
value "map f1 l1"

primrec filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "filter f [] = []" |
        "filter f (x # xs) = 
            (if f x then x # (filter f xs) 
             else filter f xs)"

definition "f2 x \<equiv> (2 dvd x)"
definition "l2 \<equiv> [(1::int)..20]"
value "filter f2 l2"

primrec fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" 
  where "fold f [] = id" |
        "fold f (x # xs) = fold f xs \<circ> f x"

primrec foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" 
  where "foldr f [] = id" |
        "foldr f (x # xs) = f x \<circ> foldr f xs"

definition ff :: "int \<Rightarrow> nat \<Rightarrow> nat"
  where "ff i \<equiv> (\<lambda>x. x + nat i)"

definition "f4 \<equiv> fold ff [1..3]"
definition "f5 \<equiv> foldr ff [1..3]"

lemma "f4 = (ff 3) \<circ> (ff 2) \<circ> (ff 1)"
  unfolding f4_def using upto.simps fold.simps(1) fold.simps(2) by force

lemma "f5 = (ff 1) \<circ> (ff 2) \<circ> (ff 3)"
  unfolding f5_def using upto.simps foldr.simps(1) foldr.simps(2) by force

lemma "f4 = (\<lambda>x. x + 6)"
  unfolding f4_def ff_def using upto.simps fold.simps(1) fold.simps(2) by force

lemma "f5 = (\<lambda>x. x + 6)"
  unfolding f5_def ff_def using upto.simps fold.simps(1) fold.simps(2) by force

value "f4 1"
value "f5 1"

primrec foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" 
  where "foldl f a [] = a" |
        "foldl f a (x # xs) = foldl f (f a x) xs"

value "foldl plus 123 [1..10]"


subsection \<open>Map Reduce implementation\<close>

definition MapReduce :: 
  "'a list \<Rightarrow> \<comment> \<open> input \<close>
    ('a \<Rightarrow> ('k1 \<times>'v1) list) \<Rightarrow>  \<comment> \<open> mapping \<close>
    (('k1 \<times>'v1) list list \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow>  \<comment> \<open> shuffling \<close>
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k2 \<times> 'v2)) \<Rightarrow>  \<comment> \<open> reducing \<close>
    ('k2 \<times> 'v2) list"
  where "MapReduce input m spl r \<equiv> map r (spl (map m input))"

type_synonym webpage = "string list"

fun split0 :: "string \<Rightarrow> webpage \<Rightarrow> webpage"
  where "split0 (x#y#xs) l = 
          (if l = [] then 
             if x \<noteq> CHR '' '' then split0 (y#xs) [[x]]
             else split0 (y#xs) l
           else 
             if x = CHR '' '' then
                if y = CHR '' '' then split0 xs l
                else split0 xs (l@[[y]])
             else 
                if y = CHR '' '' then
                  split0 (y#xs) (butlast l@[last l @[x]])
                else
                  split0 xs (butlast l@[last l @[x,y]]))" |
        "split0 [x] l = (if l = [] then [[x]]
                        else butlast l@[last l @[x]])" |
        "split0 [] l = l"

definition "split s \<equiv> split0 s []"

value "split ''This is the first article, it has 100 words, these are bus and car ...''"

primrec countword :: 
  "string \<Rightarrow> (string \<times> nat) list 
          \<Rightarrow> (string \<times> nat) list"
  where "countword s [] = [(s,1)]" |
        "countword s (x # xs) = 
            (if fst x = s then 
              (fst x, snd x + 1) # xs 
            else x # (countword s xs))"

primrec countwebpage :: 
  "webpage \<Rightarrow> (string \<times> nat) list 
           \<Rightarrow> (string \<times> nat) list"
  where "countwebpage [] kvs = kvs" |
        "countwebpage (x # xs) kvs = 
            (let kvs1 = countword x kvs in countwebpage xs kvs1)"

definition mapper :: "webpage \<Rightarrow> (string \<times> nat) list"
  where "mapper a \<equiv> countwebpage a []"

primrec shuffword :: 
  "(string \<times> nat) \<Rightarrow> (string \<times> (nat list)) list 
                  \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffword kv [] = [(fst kv, [snd kv])]" |
        "shuffword kv (x # xs) = 
            (if fst kv = fst x then 
              (fst x, (snd kv) # (snd x))#xs 
             else x # (shuffword kv xs))"

primrec shuffwords :: 
  "(string \<times> nat) list \<Rightarrow> (string \<times> (nat list)) list 
                        \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffwords [] kvs = kvs" |
        "shuffwords (x # xs) kvs = shuffwords xs (shuffword x kvs)"

primrec shuffall :: 
  "(string \<times> nat) list list \<Rightarrow> (string \<times> (nat list)) list 
                            \<Rightarrow> (string \<times> (nat list)) list"
  where "shuffall [] kvs = kvs" |
        "shuffall (x # xs) kvs = shuffall xs (shuffwords x kvs)"

definition "shuff l \<equiv> shuffall l []"
(*
definition reducer :: "string \<times> (nat list) \<Rightarrow> (string \<times> nat)"
  where "reducer kvs \<equiv> (fst kvs, sum_list (snd kvs))"*)
fun reducer :: "string \<times> (nat list) \<Rightarrow> (string \<times> nat)"
  where "reducer (k,vlist) = (k, foldl plus 0 vlist)"

definition news :: "webpage list"
  where "news \<equiv> [split ''This is the first article, it has 100 words, these are bus and car ...'',
                 split ''This is the second article, it has 1000 words, The These are train and plane and car'',
                 split ''Those are plane and bus'']"

value "split ''Those are plane and bus''"
value "MapReduce news mapper shuff reducer"
                                      
definition webpages0 :: "webpage list"
  where "webpages0 \<equiv> [split ''Bus Car Train'',
                     split ''Train Plane Car'',
                     split ''Bus Bus Plane'']"

definition webpages :: "webpage list"
  where "webpages \<equiv> [split ''Dear Bear River'',
                     split ''Car Car River'',
                     split ''Dear Car Bear'']"

value "webpages"
value "map mapper webpages"
value "shuff (map mapper webpages)"
value "MapReduce webpages mapper shuff reducer"

subsection \<open>curring\<close>

fun concat2 :: "(string \<times> string) \<Rightarrow> string"
  where "concat2 (x,y) = x@y"

fun concat3 :: "(string \<times> string \<times> string) \<Rightarrow> string"
  where "concat3 (x,y,z) = x@y@z"

value "concat2 (''aaa'',''bbb'')"
value "concat3 (''aaa'',''bbb'',''ccc'')"

definition "concat2c \<equiv> curry concat2"
definition "concat3c \<equiv> curry concat3"

term "concat2c"
term "concat3c"

definition "concathello \<equiv> concat2c ''hello''"

value "concathello ''world''"

value "curry concat2 ''hello'' ''world''"

term "curry (concat3c ''hello'')"

fun concat2c' :: "string \<Rightarrow> string \<Rightarrow> string"
  where "concat2c' x y = x@y"

fun concat3c' :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string"
  where "concat3c' x y z = x@y@z"

definition "concat2' \<equiv> case_prod concat2c'"
definition "concat3' \<equiv> case_prod concat3c'"
definition "concat3'' \<equiv> case_prod concat3'"

term "concat2'"
term "concat3'"
term "concat3''"

lemma "concat2' (x,y) = concat2 (x,y)"
  using concat2c'.simps concat2.simps 
    by (simp add: concat2'_def) 

lemma "concat3'' ((x,y),z) = concat3 (x,y,z)"
  using concat3c'.simps concat3.simps
    by (simp add:concat3''_def concat3'_def)

fun add0 :: "(int \<times> int) \<Rightarrow> int"
  where "add0 (x,y) = x + y"

value "add0 (10,23)"

fun add1 :: "int \<Rightarrow> int \<Rightarrow> int"
  where "add1 x y = x + y"

(*definition curry :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "curry g x y = g (x, y)"
*)

term "curry add0"
term "case_prod add1"

lemma "add1 = curry add0"
  using add0.simps add1.simps curry_def by force

lemma "add0 = case_prod add1"
  using add0.simps add1.simps by force

lemma "case_prod (curry f) = f"
  by auto

lemma "curry (case_prod f) = f"
  by auto


fun addxyz :: "(int \<times> int \<times> int) \<Rightarrow> int"
  where "addxyz (x,y,z) = x + y + z"

term "curry addxyz"
term "curry addxyz 1"

lemma "curry addxyz 1 = (\<lambda> (x,y). x + y +1)"
  using addxyz.simps curry_def by force

fun addxyz2 :: "((int \<times> int) \<times> int) \<Rightarrow> int"
  where "addxyz2 ((x,y),z) = x + y + z"

term "curry addxyz2"
term "curry (curry addxyz2)"

term "curry (curry addxyz2) 1"

fun addxyz3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "addxyz3 x y z = x + y + z"
term "case_prod addxyz3"
term "case_prod (case_prod addxyz3)"

end
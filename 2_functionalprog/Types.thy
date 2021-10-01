theory Types
  imports Main HOL.Real
begin



subsection \<open>datatype\<close>

datatype ITree = Leaf int | Node ITree int ITree

term Leaf
term Node

primrec ITreeSum :: "ITree \<Rightarrow> int"
  where "ITreeSum (Leaf v) = v" |
        "ITreeSum (Node left v right) = ITreeSum left + v + ITreeSum right"

definition "ITree1 \<equiv> Node (Node (Leaf 4) 5 (Node (Leaf 1) 8 (Leaf 2))) 10 (Node (Leaf 7) 9 (Leaf 15))"

value "ITreeSum ITree1"

datatype Fruit = APPLE | ORANGE | BANANA

term APPLE

value APPLE

lemma "APPLE \<noteq> ORANGE" by simp

primrec showfruit :: "Fruit \<Rightarrow> string"
  where "showfruit APPLE = ''it is an apple''" |
        "showfruit ORANGE = ''it is an orange''" |
        "showfruit BANANA = ''it is a banana''"

datatype Exp = B bool | I int | N nat

term B
term I
term N


datatype Type = Bool | Integer | Nature

value "B True"

primrec type :: "Exp \<Rightarrow> Type"
  where "type (B a) = Bool" |
        "type (I a) = Integer" |
        "type (N a) = Nature"

value "type (B a)"

datatype boolex = Const bool | Var nat | Neg boolex | And boolex boolex | Or boolex boolex
type_synonym env = "nat \<Rightarrow> bool"

primrec eval :: "boolex \<Rightarrow> env \<Rightarrow> bool"
  where "eval (Const a) ev = a" |
        "eval (Var v) ev = ev v" |
        "eval (Neg e) ev = (\<not> eval e ev)" |
        "eval (And e1 e2) ev = (eval e1 ev \<and> eval e2 ev)" |
        "eval (Or e1 e2) ev = (eval e1 ev \<or> eval e2 ev)"

definition env1 :: "env"
  where "env1 n \<equiv> (if n mod 2 = 0 then True else False)"

value "eval (Var 1) env1"

value "eval (And (Var 2) (Var 4)) env1"

value "eval (And (Or (Const True) (Var 1)) (Neg (Var 4))) env1"

subsubsection \<open>mutual recursion\<close>

datatype aexp = IF bexp aexp aexp | Add aexp aexp | Sub aexp aexp | Num nat
   and   bexp = Less aexp aexp | And bexp bexp | Neg bexp

primrec evala :: "aexp \<Rightarrow> nat" and
        evalb :: "bexp \<Rightarrow> bool" where
  "evala (IF b a1 a2) = (if (evalb b) then evala a1 else evala a2)" |
  "evala (Add a1 a2) = (evala a1) + (evala a2)" |
  "evala (Sub a1 a2) = (evala a1) - (evala a2)" |
  "evala (Num a) = a" |
  "evalb (Less a1 a2) = (evala a1 < evala a2)" |
  "evalb (And b1 b2) = (evalb b1 \<and> evalb b2)" |
  "evalb (Neg b) = (\<not> evalb b)"

value "evala (IF (Less (Num 10) (Num 20)) (Num 1) (Num 2))"

value "evalb (Less (Num 50) (Num 100))"

subsection \<open>product, pair and tuple\<close>

typedecl Vertex

record Vert = xpos :: int
              ypos :: int

axiomatization v1 :: Vertex 
        and    v2 :: Vertex 
        and    v3 :: Vertex
        and    v4 :: Vertex
        and    v5 :: Vertex
        and    v6 :: Vertex
        and    v7 :: Vertex
        where assum: "distinct [v1,v2,v3,v4,v5,v6,v7]"


definition rel1 :: "Vertex \<times> Vertex"
  where "rel1 \<equiv> (v1,v2)"

definition Agraph :: "(Vertex \<times> Vertex) set"
  where "Agraph \<equiv> {(v1, v2), (v1, v3), (v2, v4), (v4, v3), (v4, v5), (v3, v6), (v5, v7), (v6, v7)}"

term "()"

term "(v1, v2)"

term "Pair v1 v2"

term Pair

lemma "(v1, v2) = Pair v1 v2" by simp

definition "conn1 \<equiv> (v1, v2)"

lemma "fst conn1 = v1" by (simp add:conn1_def)

lemma "snd conn1 = v2" by (simp add:conn1_def)

lemma "(v1, v2) \<noteq> (v2, v1)"
  using assum by auto

lemma "(x,y) = (a,b) \<longleftrightarrow> x = a \<and> y = b"
  by auto

definition h :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "h x y \<equiv> x + y"

term h

definition h2 :: "(nat \<times> nat) \<Rightarrow> nat"
  where "h2 \<equiv> \<lambda>(x,y). x + y"

lemma "case_prod h = h2" 
  unfolding h_def h2_def by simp

lemma "curry h2 = h"
  unfolding h_def h2_def by simp

value "h2 (Pair 1 2)"
value "h2 (1,2)"
value "h 1 2"

lemma "(a,b,c) = (a,(b,c))" by simp

term "((a,b),c)"

term "(a,b,c)"

value "fst ((a,b),c)"
value "fst (a,b,c)"
value "snd ((a,b),c)"
value "snd (a,b,c)"
value "fst (fst ((a,b),c))"
value "snd (fst ((a,b),c))"



subsection \<open>record\<close>


record coord2d = Xpt :: int
                 Ypt :: int

term Xpt
term Ypt

print_record coord2d

definition coord1 :: "coord2d"
  where "coord1 \<equiv> \<lparr>Xpt = 20, Ypt = 30\<rparr>"

value "Xpt coord1"

definition coord1' :: "coord2d"
  where "coord1' \<equiv> coord1\<lparr>Ypt := 50\<rparr>"

value "coord1'"

definition incX :: "coord2d \<Rightarrow> coord2d"
  where "incX r \<equiv> r\<lparr>Xpt := Xpt r + 1\<rparr>"

value "incX coord1"

lemma "coord1\<lparr>Ypt := 50\<rparr> = \<lparr>Xpt = 20, Ypt = 50\<rparr>"
  unfolding coord1_def by simp

record coord3d = coord2d + 
                  Zpt :: int

definition coord3 :: "coord3d"
  where "coord3 \<equiv> \<lparr>Xpt = 20, Ypt = 30, Zpt = 40\<rparr>"

value "Xpt coord3"
value "Zpt coord3"

definition coord3' :: "coord3d"
  where "coord3' \<equiv> coord3\<lparr>Zpt := 50\<rparr>"

value "coord3'"

value "coord2d.more coord3"

term "\<lparr>Xpt = 20, Ypt = 30, Zpt = 40\<rparr>"


record coord4d = coord3d +
                 Time :: int

definition coord4 :: "coord4d"
  where "coord4 \<equiv> \<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000\<rparr>"

value "\<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000\<rparr>"
value "coord4d.make 20 30 40 1000"

type_synonym recT1 = "\<lparr>Xpt :: int, Ypt :: int, Time :: int\<rparr>"

print_record recT1

type_synonym recT2 = "\<lparr>Xpt :: int, Ypt :: int, Zpt :: int, Time :: int\<rparr>"

print_record recT2

value "coord2d.more coord4"

lemma "\<lparr>Xpt = a1, Ypt = b1\<rparr> = \<lparr>Xpt = a2, Ypt = b2\<rparr> \<longleftrightarrow> a1 = a2 \<and> b1 = b2"
  by simp

lemma "r = \<lparr>Xpt = Xpt r, Ypt = Ypt r, \<dots> = coord2d.more r\<rparr>"
  by simp


value "coord2d.Xpt coord1"

value "coord2d.make 5 5"

term Time

definition "coord5 \<equiv> coord4d.extend coord4 (True)"
value "coord5"
value "\<lparr>Xpt = 20, Ypt = 30, Zpt = 40, Time = 1000, \<dots> = True\<rparr>"
value "more coord5"

value "coord2d.more coord4"

value "coord2d.truncate \<lparr>Xpt = Xpt coord1, Ypt = Ypt coord1, \<dots> = 50::int\<rparr>"

term "\<lparr>Xpt = 10, Ypt = 20, \<dots> = 40::int \<rparr>"

value "Xpt \<lparr>Xpt = 10, Ypt = 20, \<dots> = p\<rparr>"

value "coord2d.truncate coord3"

value "coord3d.fields 100"
value "coord4d.fields 200"
value "coord2d.more coord4"
value "coord3d.more coord4"
term "coord4d.fields"
term "coord3d.more"
value "coord3d.more (coord3d.extend coord3 ''hello'')"

value "coord2d.extend coord1 (coord3d.fields 50)"

subsection \<open>parameteric types\<close>

record 'a Coord3d = xpos :: 'a
                    ypos :: 'a
                    zpos :: 'a

record 'a Coord4d = "'a Coord3d " +
                    Time :: 'a

definition coord6 :: "int Coord3d"
  where "coord6 \<equiv> \<lparr>xpos = 10, ypos = 20, zpos = 30\<rparr>"

definition coord7 :: "real Coord3d"
  where "coord7 \<equiv> \<lparr>xpos = 10.3::real, ypos = 20.3, zpos = 30.5\<rparr>"

definition "coord9 \<equiv> \<lparr>xpos = 10.3::real, ypos = 20.3, zpos = 30.5, Time = 1000.0\<rparr>"

value "Coord3d.extend coord6 ''hello''"
value "Coord3d.extend coord7 ''good''"

value "truncate coord9"

record ('a, 'b, 'c) COORD3d = Xp :: 'a
                              Yp :: 'b
                              Zp :: 'c

definition coord10 :: "(int, string, real) COORD3d"
  where "coord10 \<equiv> \<lparr>Xp = 10, Yp = ''20w'', Zp = 30.5\<rparr>"

datatype 'a Tree = Leaf 'a | Node "'a Tree" 'a "'a Tree"

type_synonym itree = "int Tree"
type_synonym stree = "string Tree"

primrec count :: "'a Tree \<Rightarrow> nat"
  where "count (Leaf _) = 1" |
        "count (Node l _ r) = count l + count r + 1"

definition Tree1 :: "int Tree"
  where "Tree1 \<equiv> Node (Node (Leaf 4) 5 (Node (Leaf 1) 8 (Leaf 2))) 10 (Node (Leaf 7) 9 (Leaf 15))"

definition Tree2 :: "string Tree"
  where "Tree2 \<equiv> Node (Leaf ''a'') ''b'' (Leaf ''c'')"

value "count Tree1"
value "count Tree2"

datatype 'a array = Null | Conn 'a "'a array" ("_,_")

primrec length :: "'a array \<Rightarrow> nat"
  where "length Null = 0" |
        "length (Conn a arr) = 1 + length arr"

primrec nth :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" ("_[_]")
  where "nth (Conn a arr) i = (case i of 0 \<Rightarrow> a | Suc k \<Rightarrow> nth arr k)"

primrec array_update :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" ("_[_] := _")
  where "array_update (Conn a arr) i v =
          (case i of 0 \<Rightarrow> Conn v arr | Suc j \<Rightarrow> Conn a (array_update arr j v))"

definition arr1 :: "int array"
  where "arr1 \<equiv> (1,2,3,Null)"

value "arr1[2]"
value "length arr1"

value "arr1[2] := 10"

definition arr2 :: "string array"
  where "arr2 \<equiv>(''hello'', ''world'', ''next'', ''word'', Null)"

value "arr2[1]"
value "arr2[0]"

value "arr2[0] := ''hi''"


subsection \<open>type declare, synonym, typedef\<close>
type_synonym mynat = nat

definition nat1 :: "mynat \<Rightarrow> mynat"
  where "nat1 n \<equiv> n + 1"

value "nat1 15"

type_synonym 'a array_alias = "'a array"
type_synonym 'a array_synonym = "'a array"

type_synonym coord3d_t = coord3d

definition coord8 :: "coord3d_t"
  where "coord8 \<equiv> coord3"

value "coord8"


typedecl BOOL

axiomatization T :: BOOL and F :: BOOL 
  and AND :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  and OR :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  and NOT :: "BOOL \<Rightarrow> BOOL"
  where ANDs: "AND a b = (if (a = T \<and> b = T) then T else F)"
   and  ORs: "OR a b = (if (a = T \<or> b = T) then T else F)"
   and  NOTs: "NOT a \<equiv> (if a = T then F else T)"
   (* and TF: "T \<noteq> F" *)

definition xorBOOL :: "BOOL \<Rightarrow> BOOL \<Rightarrow> BOOL"
  where "xorBOOL a b \<equiv> OR (AND a (NOT b)) (AND (NOT a) b)"

(* value T *)

lemma "xorBOOL T F = T" 
  unfolding xorBOOL_def using ANDs NOTs ORs by simp

lemma "xorBOOL T T = F" 
  unfolding xorBOOL_def using ANDs NOTs ORs by auto

lemma "xorBOOL F F = F" 
  unfolding xorBOOL_def using ANDs NOTs ORs by auto

lemma "xorBOOL F T = T" 
  unfolding xorBOOL_def using ANDs NOTs ORs by simp

typedef Even = "{x::nat. x mod 2 = 0}"
(*  morphisms rep abs *)
proof -
  have "(2::nat) mod 2 = 0" by simp
  hence "2\<in>{x::nat. x mod 2 = 0}" by simp
  thus ?thesis by meson 
qed

term Rep_Even
thm Rep_Even
term Abs_Even
thm Abs_Even_inject
thm Abs_Even_inverse
thm Rep_Even_inject
thm Rep_Even_inverse


(*
lemma "(rep n) mod 2 = 0" 
  using rep by auto

lemma "rep (abs x) mod 2 = 0"
  using rep abs_inverse by auto

lemma "m\<in>{x. x mod 2 = 0} \<Longrightarrow> n\<in>{x. x mod 2 = 0} \<Longrightarrow> abs m = abs n \<longleftrightarrow> m = n"
  using abs_inject by simp
*)

instantiation Even :: zero
begin
definition Zero_even_def: "0 = Abs_Even 0"
instance ..
end
term "0::Even"

instantiation Even :: one
begin
definition One_even_def: "1 = Abs_Even 2"
instance ..
end
term "1::Even"

definition SUC :: "Even \<Rightarrow> Even"
  where "SUC n \<equiv> Abs_Even (Suc (Suc (Rep_Even n)))"

lemma "SUC 0 = 1"
  using SUC_def Zero_even_def One_even_def Rep_Even Abs_Even_inverse Abs_Even_inject
  by (metis (mono_tags, lifting) Suc_eq_plus1_left mem_Collect_eq mod_0
        numeral_1_eq_Suc_0 numeral_One one_add_one) 

definition ADD :: "Even \<Rightarrow> Even \<Rightarrow> Even"
  where "ADD m n \<equiv> Abs_Even ((Rep_Even m) + (Rep_Even n))"

lemma "ADD (SUC 0) (SUC 0) = SUC (SUC 0)"
  unfolding SUC_def ADD_def using Rep_Even Abs_Even_inverse
  by (metis (mono_tags, lifting) Suc_eq_plus1_left Zero_even_def add_Suc_shift 
        mem_Collect_eq mod_0 mod_add_self1 numeral_1_eq_Suc_0 numeral_One one_add_one) 

typedef three = "{(True, True), (True, False), (False, True)}"
  by blast

term Abs_three
term Rep_three
thm Abs_three_inject
thm Abs_three_inverse

definition "One = Abs_three (True, True)"
definition "Two = Abs_three (True, False)"
definition "Three = Abs_three (False, True)"
lemma three_distinct: "One \<noteq> Two" "One \<noteq> Three" "Two \<noteq> Three"
  by (simp_all add: One_def Two_def Three_def Abs_three_inject)

lemma three_cases:
fixes x :: three obtains "x = One | x = Two | x = Three"
  by (cases x) (auto simp: One_def Two_def Three_def Abs_three_inject)

end
  
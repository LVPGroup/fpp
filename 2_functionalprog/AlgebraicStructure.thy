theory AlgebraicStructure
imports Main "HOL-Library.Monad_Syntax" "HOL-Library.State_Monad" HOL.Real "~~/src/HOL/ex/Sqrt"
begin

section \<open>monoid\<close>

class monoid =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70) 
  fixes neutral :: 'a ("\<one>")
  assumes assoc : "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
     and  neutr : "x \<otimes> \<one> = x"
     and  neutl : "\<one> \<otimes> x = x"
begin

lemma "(w \<otimes> x) \<otimes> (y \<otimes> z) = w \<otimes> x \<otimes> y \<otimes> z"
  using assoc by auto

end

instantiation int :: monoid
begin
definition mult_int_def : "x \<otimes> y = (x :: int) + y"
definition neutral_int_def : "\<one> = (0::int)"

instance 
  apply standard using neutral_int_def mult_int_def by auto
end

value "(1::int) \<otimes> 2"

instantiation nat :: monoid
begin
definition mult_nat_def : "x \<otimes> y = (x :: nat) + y"
definition neutral_nat_def : "\<one> = (0::nat)"

instance 
  apply standard using neutral_nat_def mult_nat_def by auto
end

value "(1::nat) \<otimes> 2"

instantiation bool :: monoid
begin
definition mult_bool_def : "x \<otimes> y = ((x::bool) \<and> y)"
definition neutral_bool_def : "\<one> = True"

instance 
  apply standard using mult_bool_def neutral_bool_def by auto
end

value "True \<otimes> True"
value "True \<otimes> False"
value "False \<otimes> False"

instantiation list :: (type) monoid  
begin
definition mult_list_def : "(x :: 'a list) \<otimes> y = x @ y"
definition neutral_list_def : "\<one> = []"

instance 
  apply standard using neutral_list_def mult_list_def by auto

end

value "[1::nat,2,3] \<otimes> [4,5,6]"
value "''abcde'' \<otimes> ''fghij''"

instantiation set :: (type) monoid
begin
definition mult_set_def : "(x :: 'a set) \<otimes> y = x \<union> y"
definition neutral_set_def : "\<one> = {}"

instance 
  apply standard using mult_set_def neutral_set_def by auto
end

value "{1::int,2,3} \<otimes> {3,4,5,6}"

interpretation setintersect : monoid "(\<inter>)" UNIV
  unfolding class.monoid_def by auto


instantiation prod :: (monoid, monoid) monoid
begin
definition mult_prod_def : "x \<otimes> y = (fst x \<otimes> fst y, snd x \<otimes> snd y)"
definition neutral_prod_def : "\<one> = (\<one>,\<one>)"

instance 
  apply standard using mult_prod_def neutral_prod_def neutr neutl
  apply (simp add: assoc)
  apply (simp add: mult_prod_def neutr neutral_prod_def)
  by (simp add: mult_prod_def neutl neutral_prod_def) 

end

value "(''aaaa'',{1::int,2,3}) \<otimes> (''cccc'',{4,5,6})"

value "(''aaa'',''bbb'',''ccc'') \<otimes> (''ddd'',''eee'',''fff'') \<otimes> (''ggg'',''hhh'',''iii'')"

value "(''aa'',{1::int},1::nat) \<otimes> (''cc'',{2},2) \<otimes> (''ee'',{3},3)"

value "(''aaa'', 20::int, False,{1::int}) \<otimes> (''ddd'', 30::int, False,{2})"

value "foldl (\<otimes>) \<one> [''aa'',''bb'',''cc'']"

value "foldl (\<otimes>) \<one> [1::int,2,3,4,5]"

value "foldl (\<otimes>) \<one> [(''aa'',{1::int},1::nat),(''bb'',{2},2),(''cc'',{3},3),(''dd'',{4},4)]"

value "foldl (\<otimes>) \<one> [(1::int,''bb''),(2,''dd''),(3,''ff'')]"

(* count the elements and their sum in a list *)
value "foldl (\<otimes>) \<one> (map (\<lambda>x. (1::int,x)) [1::int,2,3,4,5])"

(* count the elements and their sum in a list *)
value "foldl (\<otimes>) \<one> (map (\<lambda>x. (1::int,x)) [''aa'',''bb'',''cc'',''dd''])"


interpretation fun_monoid: monoid comp id
  unfolding class.monoid_def by auto


section \<open>monad\<close>

subsection \<open>motivation example\<close>

definition eval :: int
where "eval \<equiv> let x = 1;
                  y = x + 5;
                  z = x + y;
                  z = z * 2
               in z div 2"

(*
definition bind_option :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"
  where "bind_option a f \<equiv> (case a of Some x \<Rightarrow> f x | None \<Rightarrow> None)"

adhoc_overloading Monad_Syntax.bind bind_option
*)

subsection \<open>option monad\<close>

thm Option.bind.simps

definition returno :: "'a \<Rightarrow> 'a option" where
"returno a = Some a"

definition add :: "int option \<Rightarrow> int option \<Rightarrow> int option"
  where "add x y \<equiv> do {
                     mx \<leftarrow> x; 
                     my \<leftarrow> y; 
                     returno (mx + my)
                   }"
thm add_def
value "add (Some 2) None"

value "add (Some 3) (Some 5)"

definition adds :: "int option \<Rightarrow> int option"
where "adds x \<equiv> do {
                  a \<leftarrow> x;
                  b \<leftarrow> add (Some a) (Some 1);
                  c \<leftarrow> add (Some b) (Some 2);
                  d \<leftarrow> add (Some c) (Some 3);
                  returno d
                }"

thm adds_def
value "adds (Some 2)"

definition safe_div :: "int option \<Rightarrow> int option \<Rightarrow> int option"
  where "safe_div x y \<equiv> 
    do {
      mx \<leftarrow> x; 
      my \<leftarrow> y; 
      if my \<noteq> 0 then returno (mx div my) else None
    }"
thm safe_div_def

value "safe_div (Some 5) (Some 0)"
value "safe_div (Some 6) (Some 2)"
value "safe_div (Some 5) None"
value "safe_div None (Some 5)"

definition comps :: "int option \<Rightarrow> int option"
  where "comps x \<equiv> 
    do {
       a \<leftarrow> add x (Some (-3)); 
       b \<leftarrow> safe_div (Some 6) (Some a);
       c \<leftarrow> add (Some b) (Some (-6));
       d \<leftarrow> safe_div (Some 15) (Some c);
       returno d
     }"

value "comps (Some 3)"
value "comps (Some 4)"
value "comps (Some 5)"

subsection \<open>list monad\<close>

context begin

definition returnl :: "'a \<Rightarrow> 'a list"
where "returnl a \<equiv> [a]"

definition "sqr_even l \<equiv> 
  do {
    x \<leftarrow> l;
    if x mod 2 = 0 then 
      returnl (x * x) 
    else returnl x
  }"

thm sqr_even_def
value "sqr_even [1..10]"

definition "list_double l \<equiv> 
  do {
    x \<leftarrow> l;
    [x,2*x]
  }"

thm list_double_def
value "list_double [1..5]"


definition "prod1 xs ys \<equiv> 
  do {
    x \<leftarrow> xs; 
    y \<leftarrow> ys; 
    returnl (x, y)
  }"

thm prod1_def
value "prod1 [a,b,c] [e,f,g]"

definition "prod2 xs ys \<equiv> concat (map (\<lambda>x. concat (map (\<lambda>y. [(x,y)]) ys)) xs)"

lemma "prod1 xs ys = prod2 xs ys"
  unfolding prod1_def List.bind_def prod2_def returnl_def by simp

definition list2 :: "string list \<Rightarrow> (nat \<times> string) list"
  where "list2 ss \<equiv> do {
                      x \<leftarrow> ss;
                      let y = x@''#'';
                      let z = y@''@'';
                      returnl (length x,z@z)
                    }"
thm list2_def
value "list2 [''aaa'',''bb'',''cccc'']"
thm List.bind_def

(*
double vlen(double * v) {
  double d = 0.0;
  int n;
  for (n = 0; n < 3; ++n)
    d += v[n] * v[n];
  return sqrt(d);
}
*)
definition vlen :: "real list \<Rightarrow> real"
  where "vlen l \<equiv> foldl plus 0.0 ((l \<bind> (\<lambda>x. [x * x]))\<bind> (\<lambda>x. [x + 1]))"
definition vlen2 :: "real list \<Rightarrow> real"
  where "vlen2 l \<equiv> foldl plus 0.0 (do {
                                     x \<leftarrow> l;
                                     let y = x * x;
                                     returnl (y + 1)
                                    })"

thm vlen_def
thm vlen2_def
value "vlen [1,2,3,5]"
value "vlen2 [1,2,3,5]"

definition list3 :: "real list \<Rightarrow> real list"
  where "list3 l \<equiv> ((l \<bind> (\<lambda>x. [x * x]))\<bind> (\<lambda>x. [x + 100]))\<bind> (\<lambda>x. [x + 1000])"

definition list32 :: "real list \<Rightarrow> real list"
  where "list32 l \<equiv> do {
                      x \<leftarrow> l;
                      let y = x * x;
                      let z = y + 100;
                      returnl (z + 1000)
                    }"

thm list3_def
thm list32_def
value "list3 [1,2,3,5]"
value "list32 [1,2,3,5]"

end

subsection \<open>set monad\<close>

definition returns :: "'a \<Rightarrow> 'a set"
where "returns a = {a}"

definition set1 :: "int set \<Rightarrow> (int \<times> string) set"
  where "set1 s \<equiv> do {
                     x \<leftarrow> s;
                     if x mod 2 = 0 then 
                       returns (3 * x, ''aaa'') 
                     else returns (0,'''')
                  }"

value "set1 {0..10}"

definition set2 :: "int set \<Rightarrow> (int \<times> string) set"
  where "set2 s \<equiv> (s \<bind> (\<lambda>x. if x mod 2 = 0 then {(3 * x, ''aaa'')} else {(0,'''')})) \<bind> (\<lambda>(x,y). {(x+1,y@''__'')})"

definition set22 :: "int set \<Rightarrow> (int \<times> string) set"
  where "set22 s \<equiv> do {
                     x \<leftarrow> s;
                     if x mod 2 = 0 then do {
                       let (x,y) = (3 * x, ''aaa'');
                       returns (x+1,y@''__'')
                     } else do {
                       let (x,y) = (0,'''');
                       returns (x+1,y@''__'')
                     }
                   }"
thm set2_def
thm set22_def
value "set2 {0..10}"
value "set22 {0..10}"

definition set3 :: "int set \<Rightarrow> (int \<times> string) set"
  where "set3 s \<equiv> (s \<bind> (\<lambda>x. {(x*2,''*2'')})) \<bind> (\<lambda>(x,y). {(x+1,y@''__'')})"

definition set32 :: "int set \<Rightarrow> (int \<times> string) set"
  where "set32 s \<equiv> do {
                     x \<leftarrow> s;
                     (x,y) \<leftarrow> {(x*2,''*2'')};
                     returns (x+1,y@''__'')
                   }"

value "set3 {0..10}"
value "set32 {0..10}"


subsection \<open>state monad\<close>

lemma "Pair a = (\<lambda>s. (a,s))" by auto

type_synonym 'v stack = "'v list"

definition pop :: "('v stack,'v option) state"
where "pop \<equiv> State (\<lambda>s. case s of [] \<Rightarrow> (None, []) |
                                  (x#xs) \<Rightarrow> (Some x,xs))"

definition push :: "'v \<Rightarrow> ('v stack,'v option) state"
where "push v \<equiv> State (\<lambda>s. case s of [] \<Rightarrow> (None, [v]) |
                                     (x#xs) \<Rightarrow> (None,v#x#xs))"

primrec pushn :: "'v list \<Rightarrow> ('v stack, 'v option) state"
where "pushn [] = State_Monad.return None" |
      "pushn (x#xs) = do {
                        push x; 
                        pushn xs
                      }"

primrec popn :: "nat \<Rightarrow> ('v stack,('v option) list) state"
where "popn 0 = State_Monad.return []" |
      "popn (Suc n) = do {
                        a \<leftarrow> pop; 
                        as \<leftarrow> popn n; 
                        State_Monad.return (a#as)
                      }"

value "run_state (pushn [1::int,2,3,4,5]) []"

value "run_state (pushn [1::int,2,3,4,5]) [0,0,0]"

value "run_state (popn 5) [0::int,1,2,3,4,5,6]"

value "run_state (do {
                    pushn [1::int,2,3,4,5];
                    popn 4
                  }) []"

thm foldl.simps

definition stackops :: "(int stack,int option) state"
where "stackops \<equiv>
  do {
    State_Monad.return (0::int);
    push (1::int);
    push 2;
    push 3;
    push 4;
    State_Monad.return None
  }"
thm stackops_def
value "run_state stackops []"


definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where "swap l i j \<equiv> (let temp = l!i in (l[i := l!j])[j := temp])"

value "swap [0::nat,1,2,3,4] 0 4"


fun insert :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> (('a::linorder) list,('a::linorder) list) state"
where "insert l i = 
  (if i \<noteq> 0 \<and> l!i < l!(i-1) then do {
    let l1 = swap l (i-1) i;
    insert l1 (i - 1)
  } else do {
    State_Monad.return l 
  })"

value "run_state (insert [3::int,2,8,4,3] 1) []"

function isort :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> (('a::linorder) list,('a::linorder) list) state"
where "isort l i = 
  (if i < length l then do {
    l' \<leftarrow> insert l i;
    isort l' (i + 1)
  } else do {    
    State_Monad.return l
  })"
by auto
termination 
apply (relation "measure (\<lambda>(l,i). length l - i)")
apply auto
 sorry

thm isort.simps

value "(run_state (isort ([1::int,0,2,8,4,3,6,2]) 1) [])"

subsection \<open>I/O monad\<close>

type_synonym Name = "string"
type_synonym IOStreams = "Name \<Rightarrow> string"
type_synonym IOState = "(IOStreams,string) state"

definition "nl \<equiv> CHR 0x0A"

definition newIO :: "Name \<Rightarrow> IOState"
where "newIO x \<equiv> State (\<lambda>s. (''OK'', s(x := ([]::string))))"

definition putChar :: "Name \<Rightarrow> char \<Rightarrow> IOState"
where "putChar x c \<equiv> State (\<lambda>s. ([c],s(x := s x @ [c])))"

definition putStr :: "Name \<Rightarrow> string \<Rightarrow> IOState"
where "putStr x c \<equiv> State (\<lambda>s. (c, s(x := s x @ c)))"

definition putStrLn :: "Name \<Rightarrow> string \<Rightarrow> IOState"
where "putStrLn x c \<equiv> putStr x (c@[nl])"

definition getChar :: "Name \<Rightarrow> IOState"
where "getChar x \<equiv> State (
          \<lambda>s. case s x of [] \<Rightarrow> ([],s) |
                         (y#xs) \<Rightarrow> ([y],s(x := xs)))"

primrec getline :: "string \<Rightarrow> (string \<times> string)"
where "getline [] = ([],[])" |
      "getline (x#xs) = (let (a,b) = getline xs in 
                           if x = nl then ([],xs) 
                           else (x#a,b))"

definition getLine :: "Name \<Rightarrow> IOState"
where "getLine x = State (
        \<lambda>s. let str = s x; 
                (a,b) = getline str in 
              (a, s(x := b)))"

definition init :: "IOStreams"
where "init = (\<lambda>x. [])"

definition printIO :: "Name \<Rightarrow> IOState \<Rightarrow> (string \<times> string)"
where "printIO x sm \<equiv> (fst (run_state sm init), (snd (run_state sm init)) x)"

value "printIO ''io1''
        (do {
            newIO ''io1'';
            putStrLn ''io1'' (''aaa'');
            putStrLn ''io1'' (''bbb'');
            putStrLn ''io1'' (''ccc'');
            putChar ''io1'' (CHR ''d'');
            x \<leftarrow> getChar ''io1'';
            State_Monad.return x
          })"

value "printIO ''io2''
        (do {
            newIO ''io1'';
            putStrLn ''io1'' (''aaa'');
            putStrLn ''io1'' (''bbb'');
            putStrLn ''io1'' (''ccc'');
            putChar ''io1'' (CHR ''d'');
            x \<leftarrow> getChar ''io1'';
            newIO ''io2'';
            putStrLn ''io2'' (x);
            putStrLn ''io2'' (''fff'');
            putStrLn ''io2'' (''ggg'');
            getLine ''io2'';
            getLine ''io2'';
            y \<leftarrow> getLine ''io2'';
            State_Monad.return y
          })"

value "printIO ''io2''
        (do {
            newIO ''io1'';
            putStrLn ''io1'' (''aaa'');
            putStrLn ''io1'' (''bbb'');
            putStrLn ''io1'' (''ccc'');
            putChar ''io1'' (CHR ''d'');
            getChar ''io1'';
            newIO ''io2'';
            putStrLn ''io2'' (''eee'');
            putStrLn ''io2'' (''fff'');
            putStrLn ''io2'' (''ggg'');
            x \<leftarrow> getLine ''io2'';
            State_Monad.return x
          })"


section \<open>functor\<close>

typedecl ('a, 'b, 'c, 'd) F
consts map_F :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b' \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c') \<Rightarrow> ('a, 'b, 'c, 'd) F \<Rightarrow> ('a', 'b', 'c', 'd') F"
functor map_F sorry

typedecl 'a T
consts map_t :: "('a \<Rightarrow> 'a') \<Rightarrow> 'a T \<Rightarrow> 'a' T"
functor map_t sorry

primrec maplist2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
  where "maplist2 f [] = []" |
        "maplist2 f (x # xs) = f x # maplist2 f xs"

functor maplist2
proof 
  fix f g x
  show "(maplist2 f \<circ> maplist2 g) x = maplist2 (f \<circ> g) x"
    apply(induct x)
      using maplist2.simps by auto
next
  {
    fix x
    have "(maplist2 id) x = id x"
      apply(induct x)
        using maplist2.simps by auto
  }
  then show "maplist2 id = id" by blast
qed

thm AlgebraicStructure.list.comp
thm list.comp

(*
functor map (* map function on list is a functor *)
 by auto
(* Duplicate fact declaration "AlgebraicStructure.list.comp" vs. "AlgebraicStructure.list.comp" *)
*)

primrec mapsome :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
  where "mapsome f None = None" |
        "mapsome f (Some a) = Some (f a)"

functor mapsome
proof
  fix f g x
  show "(mapsome f \<circ> mapsome g) x = mapsome (f \<circ> g) x"
    apply(induct x)
      using mapsome.simps by auto
next
  show "mapsome id = id"
    using mapsome.simps
    by (metis eq_id_iff not_None_eq) 
qed

datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

primrec maptree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
  where "maptree f (Leaf a) = Leaf (f a)" |
        "maptree f (Node l r) = Node (maptree f l) (maptree f r)"

lemma lmmt1: "(maptree f \<circ> maptree g) x = (maptree (f \<circ> g)) x"
  apply(induct x)
  using maplist2.simps by auto

lemma lmmt2: "(maptree id) x = id x"
  apply(induct x)
  using maptree.simps by auto

functor maptree
proof 
  fix f::"'b \<Rightarrow> 'c" 
  fix g::"'a \<Rightarrow> 'b" 
  fix x::"'a tree"
  show "(maptree f \<circ> maptree g) x = maptree (f \<circ> g) x"
    using lmmt1 by simp
next
  show "maptree id = id" 
    using lmmt2 by blast
qed

(*
locale Functor =
  fixes fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a T \<Rightarrow> 'b T"
  assumes "fmap f \<circ> fmap g = fmap (f \<circ> g)"
*)


end
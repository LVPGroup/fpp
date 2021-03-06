theory Classes
  imports Main HOL.Real
begin

subsection \<open>definition of classes\<close>
class additive =
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70)
  assumes assoc : "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"

print_locale additive

instantiation int :: additive
begin

definition add_int_def : "x \<oplus> y = (x::int) + y"

instance proof
  fix x y z :: int
  show "x \<oplus> y \<oplus> z = x \<oplus> (y \<oplus> z)" unfolding add_int_def by simp
qed

end

value "(2::int) \<oplus> 12"

instantiation bool :: additive
begin
definition add_bool_def : "x \<oplus> y = ((x::bool) \<or> y)"

instance proof
  fix x y z :: bool
  show "x \<oplus> y \<oplus> z = x \<oplus> (y \<oplus> z)" unfolding add_bool_def by simp
qed

end

value "True \<oplus> False"

datatype Number = Natural nat | Integer int | Real real

instantiation Number :: additive
begin

definition addnum :: "Number \<Rightarrow> Number \<Rightarrow> Number"
  where "addnum x y \<equiv> Real ((case x of Real r \<Rightarrow> r | Natural n \<Rightarrow> of_nat n | Integer i \<Rightarrow> of_int i)
                           + (case y of Real r \<Rightarrow> r | Natural n \<Rightarrow> of_nat n | Integer i \<Rightarrow> of_int i))"

definition add_Number_def : "x \<oplus> y = addnum x y"

instance proof
  fix x y z :: Number
  show "x \<oplus> y \<oplus> z = x \<oplus> (y \<oplus> z)"
    unfolding add_Number_def addnum_def
    by auto
qed

end

value "(Real 2.0) \<oplus> (Integer 3)"

interpretation list_add : additive append
proof 
  fix x y z :: "'a list"
  show "(x @ y) @ z = x @ y @ z" by auto
qed

subsection \<open>parametric polymorphism and ad-hoc polymorphism (overloading)\<close>


subsection \<open>semigroup, monoid\<close>
class semigroup =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc : "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

print_locale semigroup

instantiation int :: semigroup
begin
definition multi_int_def : "i \<otimes> j = i + (j::int)"

instance proof
  fix x y z :: int have "(x + y) + z = x + (y + z)" by simp
  then show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)" unfolding multi_int_def by simp
qed
end


thm multi_int_def

instantiation nat :: semigroup
begin
definition multi_nat_def : "i \<otimes> j = i + (j::nat)"

instance proof
  fix x y z :: nat have "(x + y) + z = x + (y + z)" by simp
  then show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)" unfolding multi_nat_def by simp
qed
end

instantiation prod :: (semigroup, semigroup) semigroup
begin
definition
mult_prod_def : "p1 \<otimes> p2 = (fst p1 \<otimes> fst p2, snd p1 \<otimes> snd p2)"

instance proof
  fix p1 p2 p3 :: "('a :: semigroup) \<times> ('b :: semigroup)"
  show "(p1 \<otimes> p2) \<otimes> p3 = p1 \<otimes> (p2 \<otimes> p3)"
  unfolding mult_prod_def by (simp add: assoc)
qed
end


class monoidl = semigroup + 
  fixes neutral :: 'a ("\<one>")
  assumes neutl : "\<one> \<otimes> x = x"

print_locale semigroup
print_locale monoidl
thm monoidl_axioms
thm semigroup_axioms

subclass (in monoidl) semigroup 
  using semigroup_axioms by simp

instantiation nat and int :: monoidl
begin

definition neutral_nat_def : "\<one> = (0::nat)"

definition neutral_int_def : "\<one> = (0::int)"

instance proof
  fix n::nat
  show "\<one> \<otimes> n = n" unfolding neutral_nat_def multi_nat_def by simp
next
  fix n::int
  show "\<one> \<otimes> n = n" unfolding neutral_int_def multi_int_def by simp
qed
end

instantiation prod :: (monoidl,monoidl) monoidl
begin

definition neutral_prod_def: "\<one> = (\<one>,\<one>)"

instance proof
  fix p :: "'a :: monoidl \<times> 'b :: monoidl"
  show "\<one> \<otimes> p = p"
    unfolding neutral_prod_def mult_prod_def by (simp add:neutl)
qed
end


class monoid = monoidl + 
  assumes neutr: "x \<otimes> \<one> = x"

instantiation int and nat :: monoid
begin

instance proof
  fix x :: int
  show "x \<otimes> \<one> = x"
    by (simp add: multi_int_def neutral_int_def)
next
  fix x :: nat
  show "x \<otimes> \<one> = x"
    by (simp add: multi_nat_def neutral_nat_def)
qed   
end

instantiation prod :: (monoid, monoid) monoid
begin
instance proof
  fix p :: "('a :: monoid) \<times> ('b :: monoid)"
  show "p \<otimes> \<one> = p"
    by (simp add: mult_prod_def neutr neutral_prod_def)
qed

end

class group = monoidl + 
  fixes inverse :: "'a \<Rightarrow> 'a" ("\<ominus>_" [1000] 900)
  assumes invl : "\<ominus>x \<otimes> x = \<one>"

lemma (in group) left_cancel: "x \<otimes> y = x \<otimes> z \<longleftrightarrow> y = z"
proof
assume "x \<otimes> y = x \<otimes> z"
then have "\<ominus>x \<otimes> (x \<otimes> y) = \<ominus>x \<otimes> (x \<otimes> z)" by simp
then have "(\<ominus>x \<otimes> x) \<otimes> y = (\<ominus>x \<otimes> x) \<otimes> z" using assoc by simp
then show "y = z" using neutl and invl by simp
next
assume "y = z"
then show "x \<otimes> y = x \<otimes> z" by simp
qed

subclass (in group) monoidl
  using monoidl_axioms by auto

subclass (in group) monoid
proof
  fix x
  from invl have "\<ominus>x \<otimes> x = \<one>" by simp
  with assoc [symmetric] neutl invl have "\<ominus>x \<otimes> (x \<otimes> \<one>) = \<ominus>x \<otimes> x" by simp
  with left_cancel show "x \<otimes> \<one> = x" by simp
qed


instantiation int :: group
begin
definition inverse_int_def : "\<ominus>x = - (x::int)"

instance proof
  fix x :: int
  show "\<ominus>x \<otimes> x = \<one>"
    by (simp add: inverse_int_def multi_int_def neutral_int_def) 
qed
end


lemma "(x::int) \<otimes> y \<otimes> z = (x \<otimes> y) \<otimes> z"
  by simp


interpretation list_monoid: monoid append "[]"
proof 
  fix x y z :: "'a list"
  show "(x @ y) @ z = x @ y @ z" by auto
next
  fix x :: "'a list"
  show "[] @ x = x" by auto
next
  fix x :: "'a list"
  show "x @ [] = x" by auto
qed

lemma "(xs @ ys) @ zs = xs @ (ys @ zs)"
  using list_monoid.assoc by auto

interpretation fun_monoid: monoid comp id
proof
  fix x y z :: "'a \<Rightarrow> 'a"
  show "x \<circ> y \<circ> z = x \<circ> (y \<circ> z)" by auto
next
  fix x :: "'a \<Rightarrow> 'a"
  show "id \<circ> x = x" by auto
next
  fix x :: "'a \<Rightarrow> 'a"
  show "x \<circ> id = x" by auto
qed

lemma "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  using fun_monoid.assoc by auto


class eqclass =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<asymp>" 70)
  assumes refl : "a \<asymp> a"
    and   sym : "a \<asymp> b \<longleftrightarrow> b \<asymp> a"
    and   trans : "a \<asymp> b \<and> b \<asymp> c \<longrightarrow> a \<asymp> c"

instantiation nat :: eqclass
begin
 
definition eq_nat_def : "x \<asymp> y = (x = (y :: nat))"

instance proof
  fix a :: nat
  show "a \<asymp> a" using eq_nat_def by simp
next
  fix a b :: nat
  show "a \<asymp> b = b \<asymp> a" using eq_nat_def by auto
next
  fix a b c :: nat
  show "a \<asymp> b \<and> b \<asymp> c \<longrightarrow> a \<asymp> c" using eq_nat_def by auto
qed

end

instantiation int :: eqclass
begin
 
definition eq_int_def : "x \<asymp> y = (x = (y :: int))"

instance proof
  fix a :: int
  show "a \<asymp> a" using eq_int_def by simp
next
  fix a b :: int
  show "a \<asymp> b = b \<asymp> a" using eq_int_def by auto
next
  fix a b c :: int
  show "a \<asymp> b \<and> b \<asymp> c \<longrightarrow> a \<asymp> c" using eq_int_def by auto
qed

end

instantiation prod :: (eqclass, eqclass) eqclass
begin
 
definition eq_prod_def : "x \<asymp> y = (fst x = fst y \<and> snd x = snd y)"

instance proof
  fix p :: "'a :: eqclass \<times> 'b :: eqclass"
  show "p \<asymp> p" using eq_prod_def by simp
next
  fix a b :: "'a :: eqclass \<times> 'b :: eqclass"
  show "a \<asymp> b = b \<asymp> a" using eq_prod_def by auto
next
  fix a b c :: "'a :: eqclass \<times> 'b :: eqclass"
  show "a \<asymp> b \<and> b \<asymp> c \<longrightarrow> a \<asymp> c" using eq_prod_def by auto
qed

end

lemma "((1::nat) + 2) \<asymp> 3"
  by (simp add: eq_nat_def) 

lemma "((1::int) + 2) \<asymp> 3"
  by (simp add: eq_int_def) 

lemma "(a::int) \<asymp> c \<and> (b::nat) \<asymp> d \<Longrightarrow> (a,b) \<asymp> (c,d)"
  unfolding eq_prod_def eq_int_def eq_nat_def by simp

instantiation list :: (type) eqclass
begin

definition eq_list_def : "xs \<asymp> ys = ((xs::'a list) = ys)"

instance proof
  fix a :: "'a list"
  show "a \<asymp> a" by (simp add: eq_list_def)
next
  fix a b :: "'a list"
  show "a \<asymp> b = b \<asymp> a" using eq_list_def by auto
next
  fix a b c :: "'a list"
  show "a \<asymp> b \<and> b \<asymp> c \<longrightarrow> a \<asymp> c" using eq_list_def by auto
qed

end


end

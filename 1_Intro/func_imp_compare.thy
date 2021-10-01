theory func_imp_compare
  imports Main
begin

primrec insert :: "int \<Rightarrow> int list \<Rightarrow> int list"
  where "insert x [] = [x]" |
        "insert x (y#ys) =  (if x \<le> y then (x#y#ys) else y#(insert x ys))"

definition insert_sort :: "int list \<Rightarrow> int list" 
  where "insert_sort xs = (foldr insert xs) []"

value "insert_sort [9,5,7]"

value "((insert 9) \<circ> (insert 5) \<circ> (insert 7)) []" 
  
value "insert_sort [4,3,7,5,35,9,8,22]"
  
value "sort [4::int,3,7,5,35,9,8,22]"
  
  
end
  
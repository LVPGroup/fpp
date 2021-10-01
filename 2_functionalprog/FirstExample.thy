theory FirstExample
(* imports theories (packages) *)
imports Main
begin

(* declarations *)
type_synonym NatType = nat

(* definitions *)
primrec multip :: "NatType \<Rightarrow> NatType \<Rightarrow> NatType"
  where m_zero: "multip 0 n = 0" |
        m_suc:  "multip (Suc m) n = n + multip m n"

(* proofs *)
lemma correctness: "multip m n = m * n"
  proof(induct m)
    case 0
    then show "multip 0 n = 0 * n" by simp
  next
    case (Suc m)
    assume "multip m n = m * n"
    then show "multip (Suc m) n = Suc m * n" 
      using m_suc by fastforce
  qed

end


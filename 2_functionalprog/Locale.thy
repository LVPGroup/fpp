theory Locale
  imports Main
begin

subsection \<open>definition\<close>

locale loc1

locale database0 =
  fixes update :: "'s \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 's" ("_ [_ := _]")
    and query  :: "'s \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
(*    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "+" 50) *)
  assumes updt_que: "s[k := v] \<rhd> k = Some v"
(*context database0*)
begin
thm database0_axioms
fun updates :: "'s \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 's"
  where "updates s [] = s" |
        "updates s ((k,v) # xs) = updates (update s k v) xs"

end

subsection \<open>extension\<close>

context database0
begin
definition queries :: "'s \<Rightarrow> 'k list \<Rightarrow> ('v option) list"
  where "queries s ks \<equiv> map (query s) ks"

thm database0.queries_def

end


definition (in database0) queries2 :: "'s \<Rightarrow> 'k list \<Rightarrow> ('v option) list"
  where "queries2 s ks \<equiv> map (query s) ks"

(*
context
begin
definition "fun1 \<equiv> \<lambda>x. Suc x"
end

lemma "fun1 2 = 3" unfolding fun1_def by simp
*)


term "database0"
thm database0_def
thm database0.queries_def
thm database0.queries2_def
thm database0.updates.simps
term database0.queries

subsection \<open>locale instance and expression\<close>

context
begin

definition "locexp1 \<equiv> database0"
thm database0_def 
thm locexp1_def
term locexp1
term database0

type_synonym ('k,'v) store_map = "'k \<rightharpoonup> 'v"

fun update :: "('k,'v) store_map \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) store_map"
  where "update m k v = m(k := Some v)"

definition query :: "('k,'v) store_map \<Rightarrow> 'k \<Rightarrow> 'v option"
  where "query m k = m k" 

term "database0 update query"

lemma "database0 update query = (\<forall>s k v. query (update s k v) k = Some v)"
  by (simp add: database0_def query_def) 

definition "locexp2 \<equiv> database0 update query"

lemma "locexp1 update query = True"
  unfolding locexp1_def database0_def query_def using update.simps by simp

lemma db0_lm: "database0 update query = True"
  unfolding database0_def query_def using update.simps by simp

term "database0 update"
lemma "database0 update = (\<lambda>q. \<forall>s k v. q (update s k v) k = Some v)"
  unfolding database0_def by simp

term "database0.queries query"
thm database0.queries_def

subsection \<open>locale interpretation\<close>

interpretation database0 update query
  using db0_lm by simp

thm queries_def
thm updates.simps
end


subsection \<open>sublocale\<close>

locale database1 =
  fixes update :: "'s1 \<Rightarrow> 'k1 \<Rightarrow> 'v1 \<Rightarrow> 's1" ("_ [_ := _]")
    and query  :: "'s1 \<Rightarrow> 'k1 \<Rightarrow> 'v1 option" ("_ \<rhd> _")
    and op2 :: "'k1 \<Rightarrow> 'v1"
  assumes updt_que: "s[k := v] \<rhd> k = Some v"


context database1
begin

(* thm queries_def *) (* error *)

sublocale database0 
  unfolding database0_def using updt_que by simp 

thm queries_def

end

sublocale database1 \<subseteq> database0 using database0_axioms by auto
sublocale database0 \<subseteq> database1 using database0_axioms 
  by (simp add: database0_def database1_def) 

locale database'1 = database0 update1 query1
  for update1 :: "'s \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 's" ("_ [_ := _]")
    and query1  :: "'s \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
begin

thm queries_def

end

sublocale database'1 \<subseteq> database0 where update = update1 and query = query1
  using database0_axioms by auto

sublocale database'1 \<subseteq> database0 update1 query1
  using database0_axioms by auto

lemma "l1 < l2 \<Longrightarrow>l1 \<subseteq> l2"
  by auto

locale database'2 = database0
begin
thm queries_def
term update
end

locale database = database0 update query
  for update :: "'s \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 's" ("_ [_ := _]")
    and query  :: "'s \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
  +
  fixes init :: 's
  assumes init_ : "\<forall>k. (init \<rhd> v) = None"
begin

thm queries_def
thm queries2_def

sublocale database0 using database0_axioms by simp

definition "suc x \<equiv> Suc x"

thm queries_def

end

thm database_def
thm database_axioms_def

sublocale database \<subseteq> database0 using database0_axioms by simp


thm database_def
thm database_axioms_def

print_locale database0

locale database' = database0 +
  fixes init :: 'a
  assumes init_ : "\<forall>k. init \<rhd> k = None"
begin

thm queries_def
thm queries2_def

sublocale database0 using database0_axioms by simp

thm queries_def

definition "suc x \<equiv> Suc (Suc x)"

end


sublocale database' < database0 using database0_axioms by simp
sublocale database' \<subseteq> database0 using database0_axioms by simp

subsection \<open>database example\<close>
locale db_list
begin
type_synonym ('k,'v) store_list = "('k \<times> 'v) list"

definition init :: "('k,'v) store_list"
  where "init \<equiv> []"

fun update :: "('k,'v) store_list \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) store_list" ("_ [_ := _]")
  where "update [] k v = [(k,v)]" |
        "update (x # xs) k v = (if fst x = k then (k,v)#xs else x # update xs k v)"

primrec query :: "('k,'v) store_list \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
  where "query [] k = None" |
        "query (x # xs) k = (if fst x = k then Some (snd x) else query xs k)"

definition "suc_in_dblist x \<equiv> Suc x"

lemma lm_db_list_updtque: "((s[k := v]) \<rhd> k) = Some v" 
  apply(induct s)
  using update.simps query.simps apply force
  using update.simps query.simps apply force
  done

lemma lm_db_list_init: "\<forall>k. init \<rhd> k = None"
  unfolding init_def using query.simps(1) by simp

thm database.intro
thm database0.intro

interpretation database update query init 
  using lm_db_list_updtque lm_db_list_init 
    database.intro[where query="query" and init="init"]
    database0.intro[where query="query"]
    database_axioms.intro[of query init] by force

interpretation database' update query init
  using lm_db_list_updtque lm_db_list_init 
    database'.intro[where query="query" and init="init"]
    database0.intro[where query="query"]
    database'_axioms.intro[of query init] by force

lemma "queries (updates s [(k,v)]) [k] = [Some v]"
  by (simp add: db_list.lm_db_list_updtque queries_def)

thm suc_def
thm query.simps
thm updates.cases
thm queries_def

end

lemma "db_list.query (db_list.update s k v) k = Some v"
  by (simp add: db_list.lm_db_list_updtque)
  
thm db_list.query.simps
thm db_list.update.simps



print_locale db_list
print_locales

thm database0.queries_def


thm database0.queries_def

locale db_map
begin
type_synonym ('k,'v) store_map = "'k \<rightharpoonup> 'v"

definition init :: "('k,'v) store_map"
  where "init \<equiv> \<lambda>x. None"

fun update :: "('k,'v) store_map \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) store_map" ("_ [_ := _]")
  where "update m k v = m(k := Some v)"

definition query :: "('k,'v) store_map \<Rightarrow> 'k \<Rightarrow> 'v option" ("_ \<rhd> _")
  where "query m k = m k" 

lemma lm_db_map_updtque: "query (update m k v) k = Some v"
  using update.simps by (simp add: query_def) 
  
lemma lm_db_map_init: "query init k = None"
  unfolding init_def query_def by simp

interpretation database update query init
  using lm_db_map_updtque lm_db_map_init
      database.intro[of update query]
      database0.intro[of query update] 
      database_axioms.intro[of query init] by fastforce

thm update.simps

(*value "query (update init (1::int, ''aaa'')) (1::int)"*)

end

thm db_map.query_def

lemma (in db_map) "(init[(1::int) := ''aaa'']) \<rhd> (1::int) = Some ''aaa''"
  using lm_db_map_updtque by force

locale statemachine =
  fixes S0 :: "'s set"
  fixes step :: "'a \<Rightarrow> ('s \<times> 's) set"
begin

inductive_set r_states :: "'s set"
  where zero: "x \<in> S0 \<Longrightarrow> x \<in> r_states" |
        step: "\<lbrakk>x \<in> r_states; \<exists>e. (x,y)\<in>step e\<rbrakk> \<Longrightarrow> y \<in> r_states"

primrec run :: "'a list \<Rightarrow> ('s \<times> 's) set" 
  where run_Nil: "run [] = Id" |
        run_Cons: "run (a#as) = step a O run as"

definition execute  :: "'a list \<Rightarrow> 's \<Rightarrow> 's set" 
  where "execute as s = Image (run as) {s} " 

(*
definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
  "reachable s1 s2 \<equiv>  (\<exists>as. (s1,s2) \<in> run as)"

definition reachable0 :: "'s \<Rightarrow> bool"  where
  "reachable0 s \<equiv> (\<exists>s0\<in>S0. reachable s0 s)"

lemma "r_states = {s. reachable0 s}"
proof
  {
    fix t
    assume "t\<in>r_states"
    then have "reachable0 t"
    proof (induct t)
      case (zero x)
      then show ?case using reachable0_def reachable_def run.simps by blast
    next
      case (step x y)
      assume a0: "x \<in> r_states"
        and  a1: "reachable0 x"
        and  a2: "\<exists>e. (x, y) \<in> step e"
      then obtain s0 and as where "s0\<in>S0 \<and> (s0,x) \<in> run as"
        unfolding reachable0_def reachable_def by auto
      moreover
      from a2 obtain e where "(x,y)\<in>step e" by auto
      ultimately have "(s0, y) \<in> run (as @ [e])" using run.simps(2) 
        apply(induct as)
         apply simp
        
      ultimately show ?case unfolding reachable0_def reachable_def
        using exI[of "\<lambda>x. \<exists>as. (x, y) \<in> run as" s0] 
    qed
  }
  then show "r_states \<subseteq> Collect reachable0" by auto

  {
    fix t
    assume "reachable0 t"
    have "t:r_states" sorry
  }
  then show "Collect reachable0 \<subseteq> r_states" by auto
qed
*)

end

locale statemachine_dt = statemachine +
  assumes oneinit: "card S0 = 1"
    and   determ: "\<forall>a s t r. (s, t)\<in>step a \<and> (s, r)\<in>step a \<longrightarrow> t = r"
    and   enabled0: "\<forall>s a. s\<in>r_states \<longrightarrow> (\<exists> s'. (s,s') \<in> step a)"
begin

sublocale statemachine .

end

print_locale statemachine

print_locale statemachine_dt



end

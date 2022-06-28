theory structured_internship_machine
  imports Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  
begin

(*--------------- INITIAL SETUP ----------------*)

datatype State = S_1 | S_2 

definition \<Sigma> :: "State set" where
"\<Sigma> = {S_1, S_2}"


type_synonym INPUT = nat
type_synonym OUT =  bool

record STEP =
INPUT::INPUT
STATE:: State
OUT:: OUT

type_synonym path = "(nat \<Rightarrow> STEP)"

(* transition function *)
fun t:: "State \<times> INPUT \<Rightarrow> State \<times> OUT" where
"t (S_1, 0) = (S_1, False)"|
"t (S_1, n) = (S_2, True) "|
"t (S_2, 0) = (S_2, True)"|
"t (S_2, n) = (S_1, False) "


definition INITIAL_NODE:: State where
"INITIAL_NODE = S_1"


(*-----------------SETS------------------*)

(*set of all valid paths*)
definition paths:: "path set" where
"paths \<equiv> {p::path. STATE(p(0)) = INITIAL_NODE \<and> (\<forall>n. t(STATE(p n),INPUT(p n)) = (STATE(p(Suc(n))), OUT(p n)))}"

(*set of all valid cyclic paths*)
definition cyclic_paths:: "path set" where
"cyclic_paths \<equiv> {p::path. p \<in> paths \<and> (\<exists>n m. n \<noteq> m \<and> STATE(p n) = STATE(p m))}"

(*-----------------EXAMPLE PATHS------------------*)

definition specific_path:: "nat \<Rightarrow> STEP" where
"specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"

(*-----------------HELPER LEMMAS------------------*)

lemma specific_path_state: "\<forall>n. STATE(specific_path n) = S_1" using specific_path_def by simp

lemma specific_path_out: "\<forall>n. OUT(specific_path n) = False" using specific_path_def by simp

lemma specific_path_in: "\<forall>n. INPUT(specific_path n) = 0" using specific_path_def by simp

(*show that spec path holds property 1 of paths*)
lemma spec_path_cond1: "STATE(specific_path(0)) = S_1" using specific_path_state by auto

(*show that spec path holds property 2 of paths*)
lemma spec_path_cond2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))"
  by (simp add: specific_path_in specific_path_out specific_path_state)

lemma init_is_s1 [simp]: "INITIAL_NODE \<equiv> S_1"
  by (simp add: INITIAL_NODE_def)

lemma paths_2: "\<forall>p \<in> paths. t(STATE(p n),INPUT(p n)) = (STATE(p(Suc(n))), OUT(p n))"
  by (simp add: paths_def)

lemma s2_to_s1: "\<forall>p\<in>paths. STATE(p n) = S_2 \<and> INPUT(p n) = 1 \<longrightarrow> STATE(p (Suc n)) = S_1"
  by (metis One_nat_def Pair_inject paths_2 t.simps(4))

lemma s1_to_s2: "\<forall>p\<in>paths. STATE(p n) = S_1 \<and> INPUT(p n) = 1 \<longrightarrow> STATE(p (Suc n)) = S_2"
  by (metis One_nat_def old.prod.inject paths_2 t.simps(2))

lemma s2_to_s2: "\<forall>p\<in>paths. STATE(p n) = S_2 \<and> INPUT(p n) = 0 \<longrightarrow> STATE(p (Suc n)) = S_2"
  by (metis Pair_inject paths_2 t.simps(3))

lemma s1_to_s1: "\<forall>p\<in>paths. STATE(p n) = S_1 \<and> INPUT(p n) = 0 \<longrightarrow> STATE(p (Suc n)) = S_1"
  by (metis old.prod.inject paths_2 t.simps(1))

lemma gr_0_is_1:  "n>0 \<Longrightarrow> t(s, n) = t(s, 1)"
  by (metis One_nat_def State.exhaust gr0_implies_Suc t.simps(2) t.simps(4))

lemma input_gr_0_s1_t_simp: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<longrightarrow> t(STATE (p n), INPUT(p n)) = (S_2, True)"
  by (simp add: gr_0_is_1)

lemma input_gr_0_s2_t_simp: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<longrightarrow> t(STATE (p n), INPUT(p n)) = (S_1, False)"
  by (simp add: gr_0_is_1)

lemma input_0_s1_t_simp: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) = 0 \<longrightarrow> t(STATE (p n), INPUT(p n)) = (S_1, False)" 
  by simp

lemma input_0_s2_t_simp: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) = 0 \<longrightarrow> t(STATE (p n), INPUT(p n)) = (S_2, True)" 
  by simp

lemma out_to_t_simp: "\<forall>p \<in> paths. OUT(p n) = snd(t(STATE(p n), INPUT(p n)))"
  by (simp add: paths_2)

lemma state_to_t_simp:  "\<forall>p \<in> paths. STATE(p (Suc n)) = fst(t(STATE(p n), INPUT(p n)))"
  by(simp add: paths_2)

(*-----------------SUB LEMMAS------------------*)

lemma specific_in_paths: "specific_path \<in> paths"
  apply(auto simp add: paths_def spec_path_cond1 spec_path_cond2)
  done

method interval_induct for i::nat =
  (induction i, simp, case_tac "Suc i = Suc n")

lemma stays_in_s_2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_2"
  apply(interval_induct i)
  using input_gr_0_s1_t_simp state_to_t_simp apply fastforce
  by (metis Suc_lessD greaterThanLessThan_iff not_less_less_Suc_eq s2_to_s2)

lemma stays_in_s_1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_1"
  apply(interval_induct i)
  using input_gr_0_s2_t_simp state_to_t_simp apply fastforce
  by (metis Suc_lessD greaterThanLessThan_iff not_less_less_Suc_eq s1_to_s1)

(*-----------------MAIN LEMMAS------------------*)

lemma "paths \<noteq> {}"
  using specific_in_paths by auto

lemma security_s1_to_s2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = True"
  apply(auto simp add: out_to_t_simp)
  apply(simp add: stays_in_s_2)
  done

lemma security_s2_to_s1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = False"
  apply(auto simp add: out_to_t_simp)
  apply(simp add: stays_in_s_1)
  done







end
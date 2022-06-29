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

definition specific_path:: "path" where
"specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"

fun specific_path_2:: "path" where
"specific_path_2 0 = \<lparr> INPUT = 1 ,STATE = S_1,OUT = True \<rparr>"|
"specific_path_2 n = \<lparr> INPUT = 0,STATE = S_2, OUT = True \<rparr>"

definition two_cyclic_path:: "path \<Rightarrow> bool" where
"two_cyclic_path p \<equiv> p \<in> paths \<and> (\<forall>n. INPUT(p n) = 1)"

definition reachable:: "State \<Rightarrow> bool" where
"reachable st \<equiv>  (\<exists>p\<in>paths. \<exists>n.  STATE(p n) = st)"

(*-----------------HELPER LEMMAS------------------*)

lemma specific_path_state: "\<forall>n. STATE(specific_path n) = S_1" using specific_path_def by simp

lemma specific_path_out: "\<forall>n. OUT(specific_path n) = False" using specific_path_def by simp

lemma specific_path_in: "\<forall>n. INPUT(specific_path n) = 0" using specific_path_def by simp

(*show that spec path holds property 1 of paths*)
lemma spec_path_cond1: "STATE(specific_path(0)) = S_1" using specific_path_state by auto

(*show that spec path holds property 2 of paths*)
lemma spec_path_cond2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))"
  by (simp add: specific_path_in specific_path_out specific_path_state)

lemma specific_path_2_state: "\<forall>n > 0. STATE(specific_path_2 n) = S_2"
proof
  fix n::nat
  show "0 < n \<longrightarrow> STATE (specific_path_2 n) = S_2 "
  proof
    assume a: "0 < n"
    show "STATE (specific_path_2 n) = S_2"
    by (metis a bot_nat_0.not_eq_extremum select_convs(2) specific_path_2.elims) 
  qed
qed

lemma specific_path_2_out: "\<forall>n. OUT(specific_path_2 n) = True"
  by (metis select_convs(3) specific_path_2.elims)

lemma specific_path_2_in: "\<forall>n > 0. INPUT(specific_path_2 n) = 0"
proof
  fix n::nat
  show "0 < n \<longrightarrow> INPUT(specific_path_2 n) = 0"
  proof
    assume a: "0 < n"
    show "INPUT(specific_path_2 n) = 0"
    using a gr0_conv_Suc by fastforce
  qed
qed

(*show that spec path holds property 1 of paths*)
lemma spec_path_2_cond1: "STATE(specific_path_2(0)) = S_1" by simp

(*show that spec path holds property 2 of paths*)
lemma spec_path_2_cond2: "\<forall>n. t(STATE(specific_path_2 n),INPUT(specific_path_2 n)) = (STATE(specific_path_2(Suc(n))), OUT(specific_path_2 n))"
  by (smt (verit, best) select_convs(1) spec_path_2_cond1 
specific_path_2.elims specific_path_2.simps(2) specific_path_2_out 
specific_path_2_state t.simps(2) t.simps(3) zero_less_one)

lemma two_cyclic_path_input: "\<forall>p. two_cyclic_path p \<longrightarrow> INPUT(p n) = 1" using two_cyclic_path_def by simp

lemma init_is_s1 [simp]: "INITIAL_NODE \<equiv> S_1"
  by (simp add: INITIAL_NODE_def)

lemma paths_1: "\<forall>p \<in> paths. STATE(p 0) = S_1" by(simp add: paths_def)

lemma paths_2: "\<forall>p \<in> paths. t(STATE(p n),INPUT(p n)) = (STATE(p(Suc(n))), OUT(p n))"
  by (simp add: paths_def)

lemma not_s_1: "s \<noteq> S_1 \<longrightarrow> s = S_2" using State.exhaust by auto

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

lemma "\<forall>p \<in> paths. INPUT(p n) = 0 \<longrightarrow> STATE(p n) = S_1 \<or> STATE(p n) = S_2"
  using State.exhaust by blast

(*-----------------SUB LEMMAS------------------*)


method state_case for p :: "nat \<Rightarrow> STEP" and n :: nat=
  (rule, cases "STATE (p(n))" rule: State.exhaust, auto)

method auto_two_cyclic for p :: "nat \<Rightarrow> STEP" and n :: nat=
  (state_case p n, auto simp add: out_to_t_simp state_to_t_simp two_cyclic_path_input)

lemma specific_in_paths: "specific_path \<in> paths"
  apply(auto simp add: paths_def spec_path_cond1 spec_path_cond2)
  done

lemma specific_2_in_paths: "specific_path_2 \<in> paths"
  apply(auto simp add: paths_def spec_path_2_cond1 spec_path_2_cond2)
  done

method interval_induct for i::nat =
  (induction i, simp, case_tac "Suc i = Suc n")

method enhanced_interval_induct for i::nat =
  (induction i, simp, case_tac "Suc i = Suc n",
     (auto simp add: state_to_t_simp gr_0_is_1))

lemma stays_in_s_2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_2"
  by (enhanced_interval_induct i)
  
lemma stays_in_s_1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_1"
  by (enhanced_interval_induct i)

lemma odd_p1: "\<forall>p \<in> paths. two_cyclic_path p \<longrightarrow> STATE(p (2*n + 1)) = S_2"
  apply(auto simp add: state_to_t_simp)
  apply(auto simp add: two_cyclic_path_input)
  apply(induction n)
   apply(auto simp add: paths_1 state_to_t_simp two_cyclic_path_def)
  done

lemma even_p1: "\<forall>p \<in> paths. two_cyclic_path p \<longrightarrow> STATE(p (2*n)) = S_1"
  apply(auto)
  apply(induction n)
   apply(auto simp add: paths_1)
  apply(simp add: state_to_t_simp two_cyclic_path_input)
  done
   
(*-----------------MAIN LEMMAS------------------*)

lemma "paths \<noteq> {}"
  using specific_in_paths by auto

method machine_security = 
(auto simp add: out_to_t_simp, ((simp add: stays_in_s_2; fail) | simp add: stays_in_s_1) )

lemma security_s1_to_s2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = True"
  by machine_security

lemma security_s2_to_s1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = False"
  by machine_security

lemma "p \<in> paths \<and> two_cyclic_path p \<longrightarrow> (OUT(p n) \<noteq> OUT(p (Suc n))) \<and> (STATE(p n) \<noteq> STATE(p (Suc n)))"
  by (auto_two_cyclic p n)

lemma two_cyclic_odd_even_prop: "\<forall>p\<in>paths. two_cyclic_path p \<longrightarrow> (odd n \<longrightarrow> STATE(p n) = S_2) \<and> (even n \<longrightarrow> STATE(p n) = S_1)"
  by (metis dvd_mult_div_cancel even_p1 odd_p1 odd_two_times_div_two_succ)

lemma all_nodes_reachable: "\<forall>s\<in>\<Sigma>. reachable s"
  apply(auto simp add: reachable_def)
  apply(case_tac "s = S_1")
  using spec_path_cond1 specific_in_paths apply blast
  using not_s_1 specific_2_in_paths specific_path_2_state by blast


end
theory internship_machine_by_apply
  imports Main

begin

datatype State = S_1 | S_2 

definition \<Sigma> :: "State set" where
"\<Sigma> = {S_1, S_2}"


type_synonym INPUT = nat
type_synonym OUT =  bool

record STEP =
INPUT::INPUT
STATE:: State
OUT:: OUT

(* transition function *)
fun t:: "State \<times> INPUT \<Rightarrow> State \<times> OUT" where
"t (S_1, 0) = (S_1, False)"|
"t (S_1, n) = (S_2, True) "|
"t (S_2, 0) = (S_2, True)"|
"t (S_2, n) = (S_1, False) "



definition INITIAL_NODE:: State where
"INITIAL_NODE = S_1"
(* Mesh topology properties*)
lemma no_dead_ends: "\<forall>s \<in> \<Sigma>. \<exists>i j. fst(t(s,i)) = j"
  by auto

definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = INITIAL_NODE \<and> (\<forall>n. t(STATE(p n),INPUT (p n)) = (STATE(p(Suc(n))), OUT(p n)))}"

lemma stays_in_s_2: "\<forall>p. p \<in> paths \<and> STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_2"
  apply (induction i,simp)
  apply (case_tac "Suc i = Suc n")
  apply (auto simp add: paths_def)
  apply (metis gr0_conv_Suc old.prod.inject t.simps(2))
  by (metis Pair_inject Suc_lessD less_antisym t.simps(3))


  thm allE[OF stays_in_s_2]

lemma stays_in_s_3: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> OUT(p i) = True"
  apply (rule, rule_tac x="p" and n1="n" and m1="m" and i1="i" in allE[OF stays_in_s_2])
  apply (simp add: paths_def)
  by (metis old.prod.inject t.simps(3))

lemma "\<forall>p \<in> paths. \<exists>m > n. INPUT(p n) > 0 \<and> STATE(p n) = S_1 \<longrightarrow> STATE(p m) = S_2"
  apply(rule)
done
end



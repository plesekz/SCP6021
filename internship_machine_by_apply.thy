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
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = INITIAL_NODE \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(Suc(n))), OUT(p n)))}"

lemma stays_in_s_2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_2"
  apply(rule)
  apply(auto)
  apply(induction i)

  (*gotta expand the state now*)
  

end
theory internship_machine
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
"t (S_2, 0) = (S_1, False) "|
"t (S_2, n) = (S_2, True)"



(*set of all paths*)
definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))}"

(*very simple S_1 loop*)
definition path:: "nat \<Rightarrow> STEP" where
"path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"


lemma path_init: "STATE(path(0)) = S_1"
  by (simp add: path_def)

lemma path_induct: "(\<forall>n. \<exists>i. t(STATE(path n),i) = (STATE(path(Suc(n))), OUT(path n)))"
proof
  fix i
  let ?case = "n = 0 \<Longrightarrow> \<exists>i. t(STATE(path n),i) = (STATE(path(Suc(n))), OUT(path n))"
  assume "n = 0"
  have 1: "t(STATE(path 0), i) = t(S_1,i)" using path_def by simp
  then have "... = t(S_1, 0)" try
qed

end

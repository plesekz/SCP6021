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
definition paths:: "(nat\<Rightarrow>STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))}"


(*general path*)
inductive p::"nat\<Rightarrow>STEP \<Rightarrow> bool" where
"tmp = \<lparr>INPUT = i, STATE = S_1, OUT = snd(t(S_1, i))\<rparr>  \<Longrightarrow>  p 0 tmp"|
"\<exists>i::nat. tmp = \<lparr> INPUT = i, STATE = s, OUT = snd(t(s,i)) \<rparr> \<Longrightarrow> p n tmp \<Longrightarrow> p (Suc n) = "



lemma non_empty_paths:
  assumes a: "paths = {}"
shows "\<not>a"
proof-
  fix p::"nat\<Rightarrow>STEP"
  let ?case1 = "STATE(p(0)) = S_1"
  let ?case2 = "(\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))"
  


  (*from paths_def have "(i,S_1,second(t (S_1, i))) \<in> paths" using t_def by simp*)
qed

end

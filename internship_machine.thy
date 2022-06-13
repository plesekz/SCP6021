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


consts t:: "State \<times> INPUT \<Rightarrow> State \<times> OUT"


definition paths:: "(nat\<Rightarrow>STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))}"


end

theory internship_machine
  imports Main
begin

datatype State = S_1 | S_2

definition \<Sigma> :: "State set" where
"\<Sigma> = {S_1, S_2}"




type_synonym INPUT = nat
type_synonym OUT = bool

type_synonym STEP = "(INPUT \<times> State \<times> OUT)"

definition F_space :: "(nat \<Rightarrow> STEP) set" where
"F_space = {f. f::(nat\<Rightarrow>STEP)}"


consts t::"State \<times> INPUT \<Rightarrow> State \<times> OUT"

definition paths:: "(nat\<Rightarrow>STEP) set" where
"paths \<equiv> {P::nat\<Rightarrow>STEP. \<forall>n. (\<exists>i out. P(0) = (i, S_1, out)) \<and> P(n+1) = (i, t (P n))}"



fun p:: "nat \<Rightarrow> STEP" where
"p 0 = (i, INITIAL, translate INITIAL)"|
"p n = (input, transition input (sanitise (p (n-1))), translate (transition input (sanitise (p (n-1)))))"


inductive p:: "nat \<Rightarrow> STEP \<Rightarrow> bool" where
"p 0 (i, INITIAL, translate INITIAL)"|
"p n (input, transition input (sanitise (p (n-1))), translate (transition input (sanitise (p (n-1)))))"

end

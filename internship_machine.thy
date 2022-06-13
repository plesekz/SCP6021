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


definition paths:: "(INPUT, State, OUT) set" where
"paths = {P::nat\<Rightarrow>STEP. P(0) = (INPUT, State, OUT) \<and> P(n+1) = (i, t (P n), translate (t (P n)))}"



fun p:: "nat \<Rightarrow> STEP" where
"p 0 = (i, INITIAL, translate INITIAL)"|
"p n = (input, transition input (sanitise (p (n-1))), translate (transition input (sanitise (p (n-1)))))"


inductive p:: "nat \<Rightarrow> STEP \<Rightarrow> bool" where
"p 0 (i, INITIAL, translate INITIAL)"|
"p n (input, transition input (sanitise (p (n-1))), translate (transition input (sanitise (p (n-1)))))"

end

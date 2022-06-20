theory counter_machine
  imports Main
begin


datatype State = S1


type_synonym INPUT_A = bool
type_synonym INPUT_B = bool
type_synonym OUT = "nat option"
type_synonym COUNT = nat

type_synonym STATE= State

definition INIT_NODE:: "STATE" where
"INIT_NODE \<equiv> S1"

record STEP =
I_A::INPUT_A
I_B::INPUT_B
OUT::OUT
STATE::State
COUNT::COUNT


fun t:: "(INPUT_A \<times> INPUT_B \<times> STATE \<times> COUNT) \<Rightarrow> (OUT \<times> STATE \<times> COUNT)" where
"t (True, True, S, C) = (Some(Suc C),S, 0::nat)"|
"t(True, False, S, C) = (None, S, Suc C)"|
"t(False, True, S, C) = ((Some C), S, 0::nat)"|
"t(False,False, S, C) = (None, S, C)"

definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat\<Rightarrow>STEP). STATE(p 0) = INIT_NODE \<and> (\<forall>n. t(I_A(p(n)), I_B (p(n)), STATE(p(n)), COUNT(p(n))) = (OUT(p(n)), STATE(p(Suc n)), COUNT(p(Suc n))))}"




end

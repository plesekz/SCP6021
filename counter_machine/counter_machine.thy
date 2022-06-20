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

type_synonym path = "nat \<Rightarrow> STEP"

definition paths:: "path set" where
"paths \<equiv> {p::path. STATE(p 0) = INIT_NODE \<and> (\<forall>n. t(I_A(p(n)), I_B (p(n)), STATE(p(n)), COUNT(p(n))) = (OUT(p(n)), STATE(p(Suc n)), COUNT(p(Suc n))))}"


definition simple_path:: "path" where
"simple_path n = \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNT= 0\<rparr>"


(*prove that paths is not empty*)

lemma "paths \<noteq> {}"
proof
  assume init_assm: "paths = {}"
  show "False"
  proof-
    fix n
    have 1: "simple_path n = \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNT= 0\<rparr>" using simple_path_def by simp
    (*show that the simple path has props of a path*)
    then have s_p_0: "simple_path 0 =  \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNT= 0\<rparr>" using simple_path_def by blast
    then have cond1: "STATE(simple_path 0) = INIT_NODE" using s_p_0 by simp
    have RHS: "(OUT(simple_path n), STATE(simple_path (Suc n)), COUNT(simple_path(Suc n))) = (Some(1),INIT_NODE, 0)" using simple_path_def by simp
    hence cond2: "\<forall>n. t(I_A(simple_path (n)), I_B (simple_path (n)), STATE(simple_path (n)), COUNT(simple_path (n))) = (OUT(simple_path n), STATE(simple_path (Suc n)), COUNT(simple_path(Suc n)))"
    by (simp add: simple_path_def)
    hence cond1_cond2: "STATE(simple_path 0) = INIT_NODE \<and> (\<forall>n. t(I_A(simple_path (n)), I_B (simple_path (n)), STATE(simple_path (n)), COUNT(simple_path (n))) = (OUT(simple_path n), STATE(simple_path (Suc n)), COUNT(simple_path(Suc n))))"
      using cond1 cond2 by blast
    thus "False" using init_assm paths_def by fastforce
  qed
qed


fun count:: "path \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"count p n 0 = 0"|
"count p n (Suc n') = (count p n n') + (if(I_A(p (Suc (n' + n))) = True) then 1 else 0 )"

value "count simple_path 0 "

lemma "count simple_path 0 n = n"
proof(induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have init: "count simple_path 0 (Suc n) = count simple_path 0 n + (if(I_A(simple_path(Suc n)) = True) then 1 else 0 )" by auto
  moreover have "... = n + (if(I_A(simple_path(Suc n)) = True) then 1 else 0 )" using Suc by simp
  moreover have "... = n + (if(True) then 1 else 0)" using simple_path_def by simp
  moreover have "... = n + 1" by auto
  moreover have "... = Suc n" by auto
  ultimately show ?case by auto
qed


(*"paths \<equiv> {p::path. STATE(p 0) = INIT_NODE \<and> (\<forall>n. t(I_A(p(n)), I_B (p(n)), STATE(p(n)), COUNT(p(n))) = (OUT(p(n)), STATE(p(Suc n)), COUNT(p(Suc n))))}"*)
lemma "\<forall>p \<in> paths. \<forall>n<n'. I_A(p n) = True \<and> I_B(p n') = True \<and> (\<forall>m. m \<in> {n<..<n'} \<longrightarrow> OUT(p m) = None) \<longrightarrow> OUT(p n') = Some(count p n (n'- n))"
proof
  fix p
  assume base: "p \<in> paths"
  show "\<forall>n<n'. I_A (p n) = True \<and> I_B (p n') = True \<and> (\<forall>m. m \<in> {n<..<n'} \<longrightarrow> OUT (p m) = None) \<longrightarrow> OUT (p n') = Some (count p n (n' - n))"
  proof(induction n')
    case 0
    then show ?case by auto
  next
    case (Suc n')
    (**)
    show ?case
    proof
      assume LHS: "\<forall>n<Suc n'. I_A (p n) = True \<and> I_B (p (Suc n')) = True \<and> (\<forall>m. m \<in> {n<..<Suc n'} \<longrightarrow> OUT (p m) = None)"
      then consider "Suc n = Suc n'"| "Suc n \<noteq> Suc n'" by auto
      then show "OUT (p (Suc n')) = Some(count p n (Suc n'- n))"
    qed
  qed
  
  qed
qed


end

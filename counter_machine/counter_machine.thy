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
COUNTER::COUNT


fun t:: "(INPUT_A \<times> INPUT_B \<times> STATE \<times> COUNT) \<Rightarrow> (OUT \<times> STATE \<times> COUNT)" where
"t (True, True, S, C) = (Some(Suc C),S, Suc 0::nat)"|
"t(True, False, S, C) = (None, S, Suc C)"|
"t(False, True, S, C) = ((Some C), S, 0::nat)"|
"t(False,False, S, C) = (None, S, C)"

type_synonym path = "nat \<Rightarrow> STEP"

definition paths:: "path set" where
"paths \<equiv> {p::path. STATE(p 0) = INIT_NODE \<and> (\<forall>n. t(I_A(p(n)), I_B (p(n)), STATE(p(n)), COUNTER(p(n))) = (OUT(p(n)), STATE(p(Suc n)), COUNTER(p(Suc n))))}"


definition simple_path:: "path" where
"simple_path n = \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNTER= 0\<rparr>"


(*prove that paths is not empty*)

lemma "paths \<noteq> {}"
proof
  assume init_assm: "paths = {}"
  show "False"
  proof-
    fix n
    have 1: "simple_path n = \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNTER= 0\<rparr>" using simple_path_def by simp
    (*show that the simple path has props of a path*)
    then have s_p_0: "simple_path 0 =  \<lparr>I_A=True,I_B=True, OUT= Some(1), STATE=INIT_NODE, COUNTER= 0\<rparr>" using simple_path_def by blast
    then have cond1: "STATE(simple_path 0) = INIT_NODE" using s_p_0 by simp
    have RHS: "(OUT(simple_path n), STATE(simple_path (Suc n)), COUNTER(simple_path(Suc n))) = (Some(1),INIT_NODE, 0)" using simple_path_def by simp
    hence cond2: "\<forall>n. t(I_A(simple_path (n)), I_B (simple_path (n)), STATE(simple_path (n)), COUNTER(simple_path (n))) = (OUT(simple_path n), STATE(simple_path (Suc n)), COUNTER(simple_path(Suc n)))"
    by (simp add: simple_path_def)
    hence cond1_cond2: "STATE(simple_path 0) = INIT_NODE \<and> (\<forall>n. t(I_A(simple_path (n)), I_B (simple_path (n)), STATE(simple_path (n)), COUNTER(simple_path (n))) = (OUT(simple_path n), STATE(simple_path (Suc n)), COUNTER(simple_path(Suc n))))"
      using cond1 cond2 by blast
    thus "False" using init_assm paths_def by fastforce
  qed
qed


fun count:: "path \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"count p n 0 = 0"|
"count p n (Suc n') = (count p n n') + (if(I_A(p ((n' + n))) = True) then 1 else 0 )"

value "count simple_path 0 5 "

lemma all_p_s1: "\<forall>p \<in> paths. STATE(p (n)) = S1"
  using State.exhaust by auto

lemma "count simple_path 0 n = n"
proof(induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have init: "count simple_path 0 (Suc n) = (count simple_path 0 n) + (if(I_A( simple_path((n))) = True) then 1 else 0 )"
  by simp
  moreover have "... = n + (if(I_A(simple_path(n)) = True) then 1 else 0 )" using Suc by simp
  moreover have "... = n + (if(True) then 1 else 0)" using simple_path_def by simp
  moreover have "... = n + 1" by auto
  moreover have "... = Suc n" by auto
  ultimately show ?case by auto
qed



lemma tf_count_assoc: "\<forall>p \<in> paths. \<forall>n < n'.  I_A(p(n')) =  True \<and> I_B (p(n')) = False \<longrightarrow>  Suc(count p n (n' - n)) =  (count p n (Suc n' - n))"
proof
  fix p
  assume "p \<in> paths"
  show " \<forall>n<n'. I_A (p n') = True \<and> I_B (p n') = False \<longrightarrow> Suc (count p n (n' - n)) = count p n (Suc n' - n) "
  proof
    fix n
    show  "n < n' \<longrightarrow> I_A (p n') = True \<and> I_B (p n') = False \<longrightarrow> Suc (count p n (n' - n)) = count p n (Suc n' - n)" 
    proof
      assume "n < n'"
      show "I_A (p n') = True \<and> I_B (p n') = False \<longrightarrow> Suc (count p n (n' - n)) = count p n (Suc n' - n)"
      proof
        assume "I_A (p n') = True \<and> I_B (p n') = False"
        then show "Suc (count p n (n' - n)) = count p n (Suc n' - n)"
        proof
          have "count p n (Suc n' - n) = count p n( Suc (n' - n))"
            by (metis Suc_diff_Suc \<open>n < n'\<close> diff_Suc_Suc less_SucI)
          moreover have 0: "... =  count p n (n' - n) + (if(I_A(p (n')) = True) then 1 else 0)"
          using \<open>n < n'\<close> by auto
          moreover have "... = count p n (n' - n) + 1"
            using \<open>I_A (p n') = True \<and> I_B (p n') = False\<close> by auto
          moreover have "... = Suc (count p n (n' - n))" by simp
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma ff_count_assoc: "\<forall>p \<in> paths. \<forall>n < n'.  I_A(p(n')) =  False \<and> I_B (p(n')) = False \<longrightarrow>  (count p n (n' - n)) =  (count p n (Suc n' - n))"
proof
  fix p
  assume "p \<in> paths"
  show " \<forall>n<n'. I_A (p n') = False \<and> I_B (p n') = False \<longrightarrow> (count p n (n' - n)) = count p n (Suc n' - n) "
  proof
    fix n
    show  "n < n' \<longrightarrow> I_A (p n') = False \<and> I_B (p n') = False \<longrightarrow>  (count p n (n' - n)) = count p n (Suc n' - n)" 
    proof
      assume "n < n'"
      show "I_A (p n') = False \<and> I_B (p n') = False \<longrightarrow>  (count p n (n' - n)) = count p n (Suc n' - n)"
      proof
        assume "I_A (p n') = False \<and> I_B (p n') = False"
        then show "(count p n (n' - n)) = count p n (Suc n' - n)"
        proof
          have "count p n (Suc n' - n) = count p n( Suc (n' - n))"
            by (metis Suc_diff_Suc \<open>n < n'\<close> diff_Suc_Suc less_SucI)
          moreover have 0: "... =  count p n (n' - n) + (if(I_A(p (n')) = True) then 1 else 0)"
          using \<open>n < n'\<close> by auto
          moreover have "... = count p n (n' - n) "
          by (simp add: \<open>I_A (p n') = False \<and> I_B (p n') = False\<close>)
          moreover have "... =  (count p n (n' -n))" by simp
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed
qed




(*"paths \<equiv> {p::path. STATE(p 0) = INIT_NODE \<and> (\<forall>n. t(I_A(p(n)), I_B (p(n)), STATE(p(n)), COUNT(p(n))) = (OUT(p(n)), STATE(p(Suc n)), COUNT(p(Suc n))))}"*)
lemma "\<forall>p \<in> paths. \<forall>n<n'. I_A(p n) = True \<and> (\<forall>j. j \<in> {n<..<n'} \<longrightarrow> I_B(p j) = False) \<longrightarrow> COUNTER(p n') = count p n (n' - n)"
proof
  fix p
  assume base: "p \<in> paths"
  show " \<forall>n<n'. I_A (p n) = True \<and> (\<forall>j. j \<in> {n<..<n'} \<longrightarrow> I_B (p j) = False) \<longrightarrow> COUNTER (p n') = count p n (n' - n)"
  proof(induction n')
    case 0
    then show ?case
      by presburger
  next
    case (Suc n')
    show ?case
    proof
      fix n
      show "n < Suc n' \<longrightarrow> I_A (p n) = True \<and> (\<forall>j. j \<in> {n<..<Suc n'} \<longrightarrow> I_B (p j) = False) \<longrightarrow> COUNTER (p (Suc n')) = count p n (Suc n' - n)"
      proof
        assume "n < Suc n'"
        show "I_A (p n) = True \<and> (\<forall>j. j \<in> {n<..<Suc n'} \<longrightarrow> I_B (p j) = False) \<longrightarrow> COUNTER (p (Suc n')) = count p n (Suc n' - n)"
        proof
          assume "I_A (p n) = True \<and> (\<forall>j. j \<in> {n<..<Suc n'} \<longrightarrow> I_B (p j) = False)"
          then have a_1: "I_A (p n) = True" and b: "(\<forall>j. j \<in> {n<..<Suc n'} \<longrightarrow> I_B (p j) = False)" by auto
          then consider (a) "n<n'"|(b) "n > n'" |(c) "n = n'"by linarith
          then show "COUNTER (p (Suc n')) = count p n (Suc n' - n)"
          proof (cases)
            case a
            hence IH:  "COUNTER (p n') = count p n (n' - n)" using a a_1 b Suc by auto
            have paths_1: "t(I_A(p(n')), I_B (p(n')), STATE(p(n')), COUNTER(p(n'))) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))" using paths_def base by blast
            then consider (TT) "I_A(p(n')) =  True \<and> I_B (p(n')) = True "
              |(TF) "I_A(p(n')) =  True \<and> I_B (p(n')) = False"
              |(FF) "I_A(p(n')) =  False \<and> I_B (p(n')) = False"
              |(FT) "I_A(p(n')) =  False \<and> I_B (p(n')) = True"
              by blast
            then show ?thesis
            proof(cases)
              case TT
              then show ?thesis
                  by (simp add: a b)
            next
              case TF
              then have "t(True, False, STATE(p(n')), COUNTER(p(n'))) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))" using paths_1 by simp
              then have "t(True, False, S1, count p n (n' - n)) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))"
                using IH all_p_s1 base by auto
              then have "(None, S1, Suc(count p n (n' - n))) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))" by simp
              then have "COUNTER(p(Suc n')) =  Suc(count p n (n' - n))" by simp
              then have "... = count p n (Suc n' - n)" using tf_count_assoc TF a base by blast  
              then show ?thesis
              using \<open>COUNTER (p (Suc n')) = Suc (count p n (n' - n))\<close> by presburger
            next
              case FF
              then have "t(False, False, STATE(p(n')), COUNTER(p(n'))) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))" using paths_1 by simp
              then have "t(False, False, S1, count p n (n' - n)) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n')))"
                using IH all_p_s1 base by auto
              then have "(None, S1, (count p n  (n' - n))) = (OUT(p(n')), STATE(p(Suc n')), COUNTER(p(Suc n'))) " by simp
              then have "COUNTER(p (Suc n')) = count p n (n' - n)" by simp
              then have "COUNTER(p (Suc n')) = count p n (Suc n' -n)" using ff_count_assoc
                by (simp add: FF a base)
              then show ?thesis.
            next
              case FT
              then show ?thesis 
                by (simp add: a b)
                
            qed
          next
            case b
            then show ?thesis
              using \<open>n < Suc n'\<close> by auto
          next
            case c
            then have RHS: "count p n 1 = 1"
              using a_1 by auto
            moreover have LHS: "t(I_A(p (Suc n')), I_B(p (Suc n')), S1, COUNTER(p"
          qed
      qed
    qed
    
  qed
qed

end

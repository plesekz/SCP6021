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
"t (S_2, 0) = (S_2, True)"|
"t (S_2, n) = (S_1, False) "



definition INITIAL_NODE:: State where
"INITIAL_NODE = S_1"
(* Mesh topology properties*)
lemma no_dead_ends: "\<forall>s \<in> \<Sigma>. \<exists>i j. fst(t(s,i)) = j"
  by auto


  (*check whether there is a path leading between two nodes*)
inductive path::"INPUT list \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
"fst(t (initial, i)) = current \<Longrightarrow> path [i] initial current"|
"path [i] initial node \<Longrightarrow> path is node current  \<Longrightarrow> path (i#is) initial current"


   (*general path through mesh from the initial node*)
inductive valid_path::"nat \<Rightarrow> STEP \<Rightarrow> bool" where
"valid_path 0 \<lparr>INPUT = i, STATE = INITIAL_NODE, OUT = snd(t(INITIAL_NODE, i))\<rparr>"|
"\<exists>i::nat. valid_path n \<lparr>INPUT = i, STATE = s, OUT = snd(t(s,i))\<rparr> \<Longrightarrow> valid_path (Suc n) \<lparr> INPUT = j, STATE = fst(t(s,i)), OUT = snd(t(fst(t(s,i)), j)) \<rparr>"

  (*Node is cyclic, if there is at least one such path in which it features more than once.*)
inductive cyclic_node:: "State \<Rightarrow> bool" where
"path n node node \<Longrightarrow>  cyclic_node node"

inductive cyclic_group::"State list \<Rightarrow> bool" where
"\<forall>l\<in>(set ls). cyclic_node l \<Longrightarrow> cyclic_group ls"

inductive cyclic_machine:: "bool" where
"\<forall>n\<in>\<Sigma>. cyclic_node n \<Longrightarrow> cyclic_machine"

  (*a node/group of nodes are a trap group if there is not a path to a node outside of the group*)
inductive not_a_trap_group:: "State set \<Rightarrow> bool" where
"\<exists>node\<in>grp. \<exists>onode\<in>(\<Sigma>-grp). path i  node onode \<Longrightarrow> not_a_trap_group grp"

inductive trap_group::"State set \<Rightarrow> bool" where
"\<not>(not_a_trap_group grp)\<Longrightarrow>trap_group grp"

inductive trap_node::"State \<Rightarrow> bool" where
"trap_group (set[st]) \<Longrightarrow>trap_node st"

  (*interconnectivness - a graph is interconnected if every node has a 1 cardinality path to every other*)
inductive machine_interconnectivness:: "bool" where
"\<forall>node\<in>\<Sigma>. \<forall>onode\<in>(\<Sigma>-set [(node::State)]). \<exists>i::INPUT. \<exists>out::OUT. (t (node,(i)) = (onode,out)) \<Longrightarrow> machine_interconnectivness"
  (* check with Diego, making it def, as suggested, gives unknown error. *)

inductive group_interconnectivness:: "State set \<Rightarrow> bool" where
"\<forall>node::State\<in>S. \<forall>onode\<in>(S-set [(node::State)]). \<exists>i::INPUT. \<exists>out::OUT. (t (node,(i)) = (onode,out)) \<Longrightarrow> group_interconnectivness S"



(*set of all paths*)
definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = INITIAL_NODE \<and> (\<forall>n. t(STATE(p n),INPUT(p n)) = (STATE(p(Suc(n))), OUT(p n)))}"

(*very simple S_1 loop*)
definition specific_path:: "nat \<Rightarrow> STEP" where
"specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"

(*show that spec path holds property 1 of paths*)
lemma spec_path_cond1: "STATE(specific_path(0)) = S_1" using specific_path_def by auto


(*show that spec path holds property 2 of paths*)
lemma spec_path_cond2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))"
  by (simp add: specific_path_def)


(*show spec paths is in paths*)
lemma path_in_paths: "specific_path \<in> paths"
proof-
  from specific_path_def have "specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>" by simp
  then have 1: "STATE(specific_path 0) = S_1" by (simp add: spec_path_cond1)
  then have 2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))" using spec_path_cond2 by auto
  hence "STATE(specific_path 0) = S_1 \<and> (\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n)))" by (simp add: spec_path_cond1)
  hence 3: "specific_path \<in> paths" using paths_def
  using INITIAL_NODE_def by auto
  thus ?thesis.
qed

(*paths not empty using ^*)
lemma "paths \<noteq> {}"
  using path_in_paths by auto


(*always gonna be a next output*)
lemma bigger_fish: "\<forall>q\<in>paths. \<forall>m. \<exists>n>m. \<exists>s_0. OUT(q n) = s_0" by auto


(*set defn of cyclic_paths*)
definition cyclic_paths:: "(nat \<Rightarrow> STEP) set" where
"cyclic_paths \<equiv> {q::(nat\<Rightarrow>STEP). q \<in> paths \<and> ( \<exists>n. \<exists>m. STATE(q n) = STATE(q m))}"


(* example of cyclic path that travels between s_1 and s_2 *)
definition two_cyclic_path:: "(nat \<Rightarrow> STEP) \<Rightarrow> bool" where
"two_cyclic_path p \<equiv> p \<in> paths \<and> (\<forall>n. INPUT(p n) = 1)"



(*if p is 2-cyclic, show that consecutive i/o are never the same*)
lemma "\<forall>p \<in> paths. two_cyclic_path p \<longrightarrow> (OUT(p n) \<noteq> OUT(p (Suc n))) \<and> (STATE(p n) \<noteq> STATE(p (Suc n)))"
proof
  (*break down proof by fixing and assuming p*)
  fix p
  assume p_in_paths: "p \<in> paths"
  show "two_cyclic_path p \<longrightarrow> OUT (p n) \<noteq> OUT (p (Suc n)) \<and> (STATE(p n) \<noteq> STATE(p (Suc n)))"
  proof
    assume p_two_cyclic: "two_cyclic_path p"
    (*consider state 1 and state 2*)
    consider (1) "STATE(p n) = S_1" | (2) "STATE(p n) = S_2"
    using State.exhaust by blast
    then show "OUT (p n) \<noteq> OUT (p (Suc n)) \<and> (STATE(p n) \<noteq> STATE(p (Suc n)))"
    proof(cases)
      case 1
         (*definitions*)
         from paths_def have p_paths: "t(S_1, 1) = (STATE(p (Suc n)), OUT(p n))"
           by (metis (mono_tags, lifting) "1" mem_Collect_eq p_two_cyclic two_cyclic_path_def)
         then have "(S_2, True) = (STATE(p (Suc n)), OUT(p n))" by simp
         then have suc_state: "STATE(p (Suc n)) = S_2" and p_out: "OUT(p n) = True" by simp+
         from paths_def suc_state have "t(S_2, 1) = (STATE(p(Suc (Suc n))), OUT(p (Suc n)))"
           by (metis (mono_tags, lifting) mem_Collect_eq p_two_cyclic two_cyclic_path_def)
         then have "(S_1, False) = (STATE(p(Suc (Suc n))), OUT(p (Suc n)))"
           by simp
         then have suc_out: "OUT(p (Suc n)) = False" by simp
         from suc_state 1 suc_out p_out have triv: "(OUT(p (Suc n)) \<noteq>  OUT(p n)) \<and> (STATE(p (Suc n)) \<noteq> STATE(p n))" by auto
         thus "OUT (p n) \<noteq> OUT (p (Suc n)) \<and> STATE (p n) \<noteq> (STATE (p (Suc n)))" using triv by auto 
    next
      case 2
      (*same as ^ with states switched*)
      from paths_def have p_paths: "t(S_2, 1) = (STATE(p (Suc n)), OUT(p n))"
           by (metis (mono_tags, lifting) "2" mem_Collect_eq p_two_cyclic two_cyclic_path_def)
         then have "(S_1, False) = (STATE(p (Suc n)), OUT(p n))" by simp
         then have suc_state: "STATE(p (Suc n)) = S_1" and p_out: "OUT(p n) = False" by simp+
         from paths_def suc_state have "t(S_1, 1) = (STATE(p(Suc (Suc n))), OUT(p (Suc n)))"
           by (metis (mono_tags, lifting) mem_Collect_eq p_two_cyclic two_cyclic_path_def)
         then have "(S_2, True) = (STATE(p(Suc (Suc n))), OUT(p (Suc n)))"
           by simp
         then have suc_out: "OUT(p (Suc n)) = True" by simp
         from suc_state 2 suc_out p_out have triv: "(OUT(p (Suc n)) \<noteq>  OUT(p n)) \<and> (STATE(p (Suc n)) \<noteq> STATE(p n))" by auto
         thus "OUT (p n) \<noteq> OUT (p (Suc n)) \<and> STATE (p n) \<noteq> (STATE (p (Suc n)))" using triv by auto 
       qed
     qed
   qed

(*show cyclic paths not empty using spec path*)
lemma cyclic_paths_not_empty: "cyclic_paths \<noteq> {}"
proof
  fix n
  assume 0: "cyclic_paths = {}"
  from specific_path_def have "specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>" by simp
  (* then show path n \<in> cyclic paths *)
  then have 1: "STATE(specific_path n) = S_1" by simp
  have 2:"STATE(specific_path (Suc n)) = S_1" using path_in_paths paths_def
    by (simp add: specific_path_def)
  from 1 2 have 3: "STATE(specific_path n) = STATE(specific_path (Suc n))"
    by simp
  hence "\<exists>n. \<exists> m. STATE(specific_path n) = STATE(specific_path m)"
    by auto
  hence "specific_path \<in> paths \<and> (\<exists>n. \<exists>m. STATE(specific_path n) = STATE(specific_path m))" using path_in_paths by simp
  hence 4: "specific_path \<in> cyclic_paths" using cyclic_paths_def by auto
  from 4 0 show "False" by auto
qed

(*show that if a path starts in s_1 at some time point
 then moves to s_2 then if it only has input 0 for
 some interval then it will stay in s_2 for that interval [useful for proving the security lemma]*)
lemma stays_in_s_2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_2"
proof
  fix p
  assume base: "p\<in>paths"
  show "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> STATE (p i) = S_2"
  proof (induction i)
    case 0
      then show ?case
        by simp
    next
      case (Suc i)
      show ?case
      proof
        assume LHS: "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> Suc i \<in> {n<..<m}"
        then have a: "STATE (p n) = S_1" 
        and b: "0 < INPUT (p n)"
        and c: " (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)"
        and d: "Suc i \<in> {n<..<m}" by auto
        then consider "Suc i = Suc n" | "Suc i \<noteq> Suc n" by auto
        then show "STATE (p (Suc i)) = S_2"
        proof (cases)
          case 1
          then have 0: "STATE(p i) = S_1" using a by simp
          from b have 2: "INPUT(p i) > 0" using 1 by simp
          from paths_def 2 0 have "(S_2, True) = (STATE(p (Suc i)), OUT(p i))"
            by (smt (verit) base gr0_implies_Suc mem_Collect_eq t.simps(2)) 
          then have "STATE(p (Suc i)) = S_2" by simp
          then show ?thesis.
        next
          case 2
          have a_2: "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)" using a b c by simp
          also have d_2: "i \<in> {n<..<m}"
            using "2" LHS by force
          hence IH: "STATE(p i) = S_2"
          using LHS Suc by fastforce
          hence "INPUT(p i) = 0" using a_2 d_2 by simp
          hence "t(STATE(p i), INPUT(p i)) = (STATE(p(Suc i)), OUT(p i))" using paths_def base by blast
          hence "t(S_2, 0) = (STATE(p(Suc i)), OUT(p i))" using IH
            by (simp add: \<open>INPUT (p i) = 0\<close>)
          hence "(STATE(p (Suc i)), OUT(p i)) = (S_2, True)" by simp
          hence "STATE(p (Suc i)) = S_2" by simp
          thus ?thesis.  
        qed
        qed
    qed
  qed

(*same as ^ but for s1*)
lemma stays_in_s_1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)  \<and> i \<in> {n<..<m}\<longrightarrow> STATE(p i) = S_1"
  proof
  fix p
  assume base: "p\<in>paths"
  show "STATE (p n) = S_2 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> STATE (p i) = S_1"
  proof (induction i)
    case 0
      then show ?case
        by simp
    next
      case (Suc i)
      show ?case
      proof
        assume LHS: "STATE (p n) = S_2 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> Suc i \<in> {n<..<m}"
        then have a: "STATE (p n) = S_2" 
        and b: "0 < INPUT (p n)"
        and c: " (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)"
        and d: "Suc i \<in> {n<..<m}" by auto
        then consider "Suc i = Suc n" | "Suc i \<noteq> Suc n" by auto
        then show "STATE (p (Suc i)) = S_1"
        proof (cases)
          case 1
          then have 0: "STATE(p i) = S_2" using a by simp
          from b have 2: "INPUT(p i) > 0" using 1 by simp
          from paths_def 2 0 have "(S_1, False) = (STATE(p (Suc i)), OUT(p i))"
          by (smt (verit) base gr0_implies_Suc mem_Collect_eq t.simps(4)) 
          then have "STATE(p (Suc i)) = S_1" by simp
          then show ?thesis.
        next
          case 2
          have a_2: "STATE (p n) = S_2 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)" using a b c by simp
          also have d_2: "i \<in> {n<..<m}"
            using "2" LHS by force
          hence IH: "STATE(p i) = S_1"
          using LHS Suc by fastforce
          hence "INPUT(p i) = 0" using a_2 d_2 by simp
          hence "t(STATE(p i), INPUT(p i)) = (STATE(p(Suc i)), OUT(p i))" using paths_def base by blast
          hence "t(S_1, 0) = (STATE(p(Suc i)), OUT(p i))" using IH
            by (simp add: \<open>INPUT (p i) = 0\<close>)
          hence "(STATE(p (Suc i)), OUT(p i)) = (S_1, False)" by simp
          hence "STATE(p (Suc i)) = S_1" by simp
          thus ?thesis.  
        qed
        qed
    qed
  qed


lemma security_s1_to_s2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = True"
proof
  fix p
  assume p_in_paths: "p\<in>paths"
  show "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT (p i) = True"
  proof
    assume LHS: "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> i \<in> {n<..<m}"
    show "OUT(p i) = True"
    proof-
      from LHS have a: "STATE (p n) = S_1" 
        and b: "0 < INPUT (p n)"
        and c: " (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)"
        and d: "i \<in> {n<..<m}"
          by auto
      from d c have i_input: "INPUT(p i) = 0" by blast
      from paths_def have "t(STATE(p i), INPUT(p i)) = (STATE(p(Suc i)), OUT(p i))" using p_in_paths by blast
      then have "t(S_2, 0) = (STATE(p(Suc i)), OUT(p i))" using i_input stays_in_s_2
          by (metis LHS p_in_paths)
        then have final: "OUT(p i) = True" by simp
        then show ?thesis.    
      qed
    qed
  qed


lemma security_s2_to_s1: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = False"
proof
  fix p
  assume p_in_paths: "p \<in> paths"
  show "STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = False"
  proof
    assume LHS: "STATE(p n) = S_2 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m}"
    show "OUT(p i) = False"
    proof-
      from LHS have a: "STATE(p n) = S_2" and b: "INPUT(p n) > 0" and c: "(\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0)" and d:  "i \<in> {n<..<m}" by auto
      from d c have i_input: "INPUT(p i) = 0" by blast
      from paths_def have "t(STATE(p i), INPUT(p i)) = (STATE(p(Suc i)), OUT(p i))" using p_in_paths by blast
      then have "t(S_1, 0) = (STATE(p(Suc i)), OUT(p i))" using i_input stays_in_s_2
        by (metis LHS p_in_paths stays_in_s_1)
        then have final: "OUT(p i) = False" by simp
        then show ?thesis.    
      qed
    qed
  qed

definition STATES:: "(nat \<Rightarrow> STEP) \<Rightarrow> State set" where
"STATES p = {s::State. p \<in> paths \<and> (\<exists>n. STATE(p n) = s)}"


lemma "\<forall>p \<in> paths. two_cyclic_path p \<longrightarrow> STATE(p (2*n + 1)) = S_2"
proof
  fix p
  assume p_in_paths: "p \<in> paths"
  show "two_cyclic_path p\<longrightarrow> STATE(p (2*n + 1)) = S_2"
  proof
    assume t_c_p: "two_cyclic_path p"
    show "STATE(p (2*n + 1)) = S_2"
    proof(induction n)
      case 0
      have "INPUT(p 0) = 1" using t_c_p two_cyclic_path_def by auto
      then have "t(S_1,1) = (STATE(p (Suc 0)), OUT(p 0))" using paths_def p_in_paths INITIAL_NODE_def
        by (metis (mono_tags, lifting) mem_Collect_eq) 
      then have "STATE(p (Suc 0)) = S_2" by simp
      moreover have "STATE(p (2*0 + 1)) = STATE(p (Suc 0))"
        by simp
      moreover have "STATE(p (2*0 + 1)) = S_2"
      by (simp add: calculation(1))
    then show ?case.
    next
      case (Suc n)
      have "t(STATE(p (2 * n + 1)),INPUT(p (2 * n + 1))) = (STATE(p (Suc ((2 * n + 1)))), OUT(p ((2 *  n + 1))))" using paths_def p_in_paths INITIAL_NODE_def
        by auto
      then have "t(S_2, 1) = (STATE(p (Suc ((2* n + 1)))), OUT(p ((2 *  n + 1))))"
        using Suc t_c_p two_cyclic_path_def by fastforce
      then have "STATE(p (Suc ((2* n + 1)))) = S_1" by simp
      then have "t(STATE(p (Suc ((2* n + 1)))), INPUT(p (Suc ((2* n + 1))))) = (STATE(p (Suc (Suc(2* n + 1)))), OUT(p ( (Suc ((2* n + 1))))))" 
        using paths_def p_in_paths
        by blast
      then have "t(S_1, 1) = ((STATE(p (Suc (Suc(2* n + 1)))), OUT(p ( (Suc ((2* n + 1)))))))"
        using \<open>STATE (p (Suc (2 * n + 1))) = S_1\<close> t_c_p two_cyclic_path_def by auto
      then have "STATE(p (Suc (Suc(2* n + 1)))) = S_2" by simp
      then have "STATE(p (2*(Suc n) + 1)) = S_2" by simp     
      then show ?case.
    qed
  qed

qed

lemma "\<forall>p \<in> paths. two_cyclic_path p \<longrightarrow> ((odd n \<longrightarrow> STATE(p n) = S_2) \<and> (even n \<longrightarrow> STATE(p n) = S_1))"
proof
  fix p
  assume "p \<in> paths"
  show "two_cyclic_path p \<longrightarrow> ((odd n \<longrightarrow> STATE (p n) = S_2) \<and> (even n \<longrightarrow> STATE (p n) = S_1))"
  proof
    assume "two_cyclic_path p"
    show "((odd n \<longrightarrow> STATE (p n) = S_2) \<and> (even n \<longrightarrow> STATE (p n) = S_1))"
    proof
      
    next
       
    qed
  qed
qed




lemma "\<forall>p\<in> paths. two_cyclic_path p \<longrightarrow>  STATES p = \<Sigma>"
proof
  fix p
  assume p_in_paths: "p \<in> paths"
  show "two_cyclic_path p \<longrightarrow> STATES p = \<Sigma>"
  proof
    assume two_cylcic: "two_cyclic_path p"
    show "STATES p = \<Sigma>"
    proof
    (*Set S and Set B \<forall>x. x \<in> S \<longleftrightarrow> x \<in> B*)
      have "STATE(p 0) = S_1" using p_in_paths paths_def INITIAL_NODE_def by auto
      then have "S_1 \<in> STATES p" 
    qed
  qed
qed




  



end

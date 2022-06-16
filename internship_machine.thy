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
"valid_path 0 \<lparr>INPUT = i, STATE = INITIAL_NODE, OUT = snd(t(S_1, i))\<rparr>"|
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
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. t(STATE(p n),INPUT(p n)) = (STATE(p(Suc(n))), OUT(p n)))}"

(*very simple S_1 loop*)
definition specific_path:: "nat \<Rightarrow> STEP" where
"specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"

lemma spec_path_cond1: "STATE(specific_path(0)) = S_1" using specific_path_def by auto

lemma spec_path_cond2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))"
  by (simp add: specific_path_def)


lemma path_in_paths: "specific_path \<in> paths"
proof-
  from specific_path_def have "specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>" by simp
  then have 1: "STATE(specific_path 0) = S_1" by (simp add: spec_path_cond1)
  then have 2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))" using spec_path_cond2 by auto
  hence "STATE(specific_path 0) = S_1 \<and> (\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n)))" by (simp add: spec_path_cond1)
  hence 3: "specific_path \<in> paths" using paths_def by auto
  thus ?thesis.
qed

lemma "paths \<noteq> {}"
  using path_in_paths by auto

lemma bigger_fish: "\<forall>q\<in>paths. \<forall>m. \<exists>n>m. \<exists>s_0. OUT(q n) = s_0" by auto

definition cyclic_paths:: "(nat \<Rightarrow> STEP) set" where
"cyclic_paths \<equiv> {q::(nat\<Rightarrow>STEP). q \<in> paths \<and> ( \<exists>n. \<exists>m. STATE(q n) = STATE(q m))}"


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

lemma 45: "\<forall>p \<in> paths. \<forall>i. \<exists>k. t(STATE(p i), k) = (STATE(p (Suc i)), OUT(p i)) \<and> INPUT(p i) > 0 \<longrightarrow> t(STATE(p i), INPUT(p i)) = (STATE(p (Suc i)), OUT(p i))"
  by simp

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
          (*to use IH, one must prove the preconditions, or find a falsity and use False \<longrightarrow> P*)
          then have "i \<notin> {n<..<m}" using 1 d by simp
          then have "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0) \<and> i \<in> {n<..<m} \<longleftrightarrow> False" by blast
          thus ?thesis 
        next
          case 2
          then have a_2: "STATE (p n) = S_1" 
          and b_2:" 0 < INPUT (p n)"
          and c_2: "(\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT (p j) = 0)"
            using LHS by auto
          (*show i \<in> {n<..<m}*)
          from d have e_2: "Suc i \<in> {n <..<m}" by auto
          have "Suc i > Suc n"
            using d "2" by fastforce
          then have d_2: "i \<in> {n <..<m}"
            using d by auto
          from c_2 d_2 have f: "INPUT(p i) = 0" by blast
          from a_2 b_2 c_2 d_2 have IH: "STATE(p i) = S_2"
            using Suc by blast 
          from c_2 e_2 have "INPUT(p (Suc i)) = 0" by blast
          then have i_path: "\<exists>k. t(STATE(p i), k) = (STATE(p (Suc i)), OUT(p i))" using paths_def base by blast

          then have "\<exists>k. t(STATE(p i), k) = t(STATE(p i), INPUT(p i))" using c_2 d_2
            by blast
          then have "t(STATE(p i), INPUT(p i)) = t(S_2, 0)" using f IH by simp
          then have "... = (S_2, True)" by simp
          
          
        
          
        qed
    qed
  qed
qed

  


lemma "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} \<longrightarrow> OUT(p i) = True"
proof
  assume 0: "p \<in> paths"
  assume 1: "STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and> (\<forall>j. j \<in> {n<..<m} \<longrightarrow> INPUT(p j) = 0) \<and> i \<in> {n<..<m} "
  (*show OUT(p i)*)
  from 0 1 have "\<exists>k. t(STATE(p j), k) = (STATE(p (Suc j)), OUT(p j))" using paths_def by blast
  then have "t(S_2, 0) = (STATE(p (Suc j)), OUT(p j))"
    by (metis "0" "1" State.distinct(1) stays_in_s_2)
  then have "(S_2, True) = (STATE(p (Suc j)), OUT(p j))" by simp
  then have "OUT(p j) = True" by simp
  
lemma lower_bound: "\<forall>p\<in>paths. \<exists>n::nat. m>n \<longrightarrow> (STATE(p n) = S_1) \<longrightarrow> (INPUT(p n) > 0) \<longrightarrow> (INPUT(p m) = 0) \<longrightarrow> (OUTPUT(p m) = True)"
  by auto




end

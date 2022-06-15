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
"t (S_2, 0) = (S_2, True)"|
"t (S_2, n) = (S_1, False) "


definition INITIAL_NODE:: State where
"INITIAL_NODE = S_1"
(* Mesh topology properties*)
lemma no_dead_ends: "\<forall>s \<in> \<Sigma>. \<exists>i j. fst(t(s,i)) = j"
  by auto


  (*check whether there is a path leading between two nodes*)
inductive path::"nat list \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
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

inductive not_a_trap_group:: "State set \<Rightarrow> bool" where
"\<exists>node\<in>grp. \<exists>onode\<in>(\<Sigma>-grp). path i  node onode \<Longrightarrow> not_a_trap_group grp"

inductive trap_group::"State set \<Rightarrow> bool" where
"\<not>(not_a_trap_group grp)\<Longrightarrow>trap_group grp"

inductive trap_node::"State \<Rightarrow> bool" where
"trap_group (set[st]) \<Longrightarrow>trap_node st"


(*set of all paths*)
definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(Suc(n))), OUT(p n)))}"

(*very simple S_1 loop*)
definition specific_path:: "nat \<Rightarrow> STEP" where
"specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"


lemma specific_path_init: "STATE(specific_path(0)) = S_1"
  by (simp add: specific_path_def)

lemma rhs_simp [simp]: " (STATE(specific_path(Suc(n))), OUT(specific_path n)) = (S_1, False)" using specific_path_def by simp


lemma path_induct: "(\<forall>n. \<exists>i. t(STATE(specific_path n),i) = (STATE(specific_path(Suc(n))), OUT(specific_path n)))"
proof (rule allI)
  fix n
  have 0: "t(STATE(specific_path n), 0) = (STATE(specific_path(Suc(n))), OUT(specific_path n))" using specific_path_def by simp
  then show "\<exists>i. t (STATE (specific_path n), i) = (STATE (specific_path (Suc n)), OUT (specific_path n))" using exI by simp
qed

lemma path_in_paths: "specific_path \<in> paths" using path_induct specific_path_init paths_def
  by blast


lemma "paths \<noteq> {}" using path_in_paths
  by blast

lemma big_fish: "\<forall>q\<in>paths. \<forall>m. \<exists>n>m. \<exists>s_0. OUT(q n) = s_0" by auto

definition cyclic_paths:: "(nat \<Rightarrow> STEP) set" where
"cyclic_paths \<equiv> {q::(nat\<Rightarrow>STEP). q \<in> paths \<and> ( \<exists>n. \<exists>m. STATE(q n) = STATE(q m))}"


lemma cyclic_paths_not_empty: "cyclic_paths \<noteq> {}"
proof
  fix n
  assume 0: "cyclic_paths = {}"
  from path_def have "path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>" by simp
  (* then show path n \<in> cyclic paths *)
  then have 1: "STATE(path n) = S_1" by simp
  have 2:"STATE(path (Suc n)) = S_1" using path_in_paths paths_def
    by (simp add: path_def)
  from 1 2 have 3: "STATE(path n) = STATE(path (Suc n))"
    by simp
  hence "\<exists>n. \<exists> m. STATE(path n) = STATE(path m)"
    by auto
  hence "path \<in> paths \<and> (\<exists>n. \<exists> m. STATE(path n) = STATE(path m))" using path_in_paths by simp
  hence 4: "path \<in> cyclic_paths" using cyclic_paths_def by auto
  from 4 0 show "False" by auto
qed







end

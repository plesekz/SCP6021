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

lemma spec_path_cond1: "STATE(specific_path(0)) = S_1" using specific_path_def by auto

lemma spec_path_cond2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))"
  by (simp add: specific_path_def)


lemma path_in_paths: "specific_path \<in> paths"
proof-
  from specific_path_def have "specific_path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>" by simp
  then have 1: "STATE(specific_path 0) = S_1" by (simp add: spec_path_cond1)
  then have 2: "\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n))" using spec_path_cond2 by auto
  hence "STATE(specific_path 0) = INITIAL_NODE \<and> (\<forall>n. t(STATE(specific_path n),INPUT(specific_path n)) = (STATE(specific_path(Suc(n))), OUT(specific_path n)))" sorry
  hence 3: "specific_path \<in> paths" using paths_def by auto
  thus ?thesis.
qed

lemma "paths \<noteq> {}"
  using path_in_paths by auto

lemma bigger_fish: "\<forall>q\<in>paths. \<forall>m. \<exists>n>m. \<exists>s_0. OUT(q n) = s_0" by auto

definition cyclic_paths:: "(nat \<Rightarrow> STEP) set" where
"cyclic_paths \<equiv> {q::(nat\<Rightarrow>STEP). q \<in> paths \<and> ( \<exists>n. \<exists>m. STATE(q n) = STATE(q m))}"

inductive two_cyclic_path:: "(nat \<Rightarrow> STEP) \<Rightarrow> bool" where
"\<forall>p \<in> paths. \<forall>n. INPUT(p n) = 1 \<Longrightarrow> two_cyclic_path p"

definition two_cyclic_set :: "(nat \<Rightarrow> STEP) set" where
"two_cyclic_set \<equiv> {p::(nat \<Rightarrow> STEP). two_cyclic_path p}"

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


lemma usf_simp: "i>0 \<Longrightarrow> t(st, i) = t(st, 1)"
  by (metis One_nat_def State.exhaust gr0_implies_Suc t.simps(2) t.simps(4))


(* declare [[simp_trace]] *)
lemma enters_s2_base: "\<forall>p \<in> paths. STATE(p 0) = S_1 \<and> INPUT(p 0) > 0 \<longrightarrow> STATE(p(Suc 0)) = S_2"
proof
  fix p
  assume 0: "p \<in> paths"
  show " STATE (p 0) = S_1 \<and> 0 < INPUT (p 0) \<longrightarrow> STATE (p (Suc 0)) = S_2"
  proof
    assume "STATE (p 0) = S_1 \<and> 0 < INPUT (p 0)"
    then have 1: "STATE (p 0) = S_1" and 2: "0 < INPUT (p 0)" by auto
    from paths_def have 3: "\<forall>n. t (STATE (p n), INPUT (p n)) = (STATE (p (Suc n)), OUT (p n))" using 0 by auto
    then have    "fst(t(STATE (p n), INPUT (p n))) = STATE(p (Suc n))" by (metis fstI)
    then have 4: "fst(t(STATE (p 0), INPUT (p 0))) = STATE(p (Suc 0))" using 0 1 2 by (metis "3" fstI)

    from t.simps have "t (S_1, 1) = (S_2, True)" using usf_simp by simp
    then have "t(STATE(p 0), INPUT(p 0)) = (S_2, True)" by (simp add: "1" "2" usf_simp)
    then have "fst(t(STATE(p 0), INPUT(p 0))) = S_2" by auto

    then show "STATE (p (Suc 0)) = S_2" using 1 2 4 by auto
  qed
qed

lemma enters_s2: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<longrightarrow> STATE(p(Suc n)) = S_2"
proof
  fix p
  assume 0: "p \<in> paths"
  show "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<longrightarrow> STATE (p (Suc n)) = S_2"
  proof
    assume "STATE (p n) = S_1 \<and> 0 < INPUT (p n)"
    then have 1: "STATE (p n) = S_1" and 2: "0 < INPUT (p n)" by auto
    from paths_def have 3: "\<forall>n. t (STATE (p n), INPUT (p n)) = (STATE (p (Suc n)), OUT (p n))" using 0 by auto
    then have 4: "fst(t(STATE (p n), INPUT (p n))) = STATE(p (Suc n))" by (metis fstI)

    from t.simps have "t (S_1, 1) = (S_2, True)" using usf_simp by simp
    then have "t(STATE(p n), INPUT(p n)) = (S_2, True)" by (simp add: "1" "2" usf_simp)
    then have "fst(t(STATE(p n), INPUT(p n))) = S_2" by auto

    then show "STATE (p (Suc n)) = S_2" using 1 2 4 by auto
  qed
qed

lemma stays_in_s2: "\<forall>p \<in> paths. STATE(p n) = S_2 \<and> INPUT(p n) = 0 \<longrightarrow> STATE(p(Suc n)) = S_2"
proof
  fix p
  assume 0: "p \<in> paths"
  show "STATE(p n) = S_2 \<and> INPUT(p n) = 0 \<longrightarrow> STATE (p (Suc n)) = S_2"
  proof
    assume "STATE(p n) = S_2 \<and> INPUT(p n) = 0"
    then have 1: "STATE (p n) = S_2" and 2: "0 = INPUT (p n)" by auto
    from paths_def have 3: "\<forall>n. t (STATE (p n), INPUT (p n)) = (STATE (p (Suc n)), OUT (p n))" using 0 by auto
    then have 4: "fst(t(STATE (p n), INPUT (p n))) = STATE(p (Suc n))" by (metis fstI)

    from t.simps have "t (S_2, 0) = (S_2, True)" using usf_simp by simp
    then have "t(STATE(p n), INPUT(p n)) = (S_2, True)" by (simp add: "1" "2" usf_simp)
    then have "fst(t(STATE(p n), INPUT(p n))) = S_2" by auto

    then show "STATE (p (Suc n)) = S_2" using 1 2 4 by auto
  qed
qed

lemma y'all: "\<forall>p \<in> paths. STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and>
               (\<forall>j. j \<in> {n..m} \<longrightarrow> INPUT(p j) = 0) \<longrightarrow>  i \<in> {n..m} \<longrightarrow> STATE(p i) = S_2"
proof
  fix p
  assume pa: "p\<in>paths"
  show "STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and>(\<forall>j. j \<in> {n..m} \<longrightarrow> INPUT(p j) = 0) \<longrightarrow> i \<in> {n..m}\<longrightarrow> STATE(p i) = S_2"
  proof
    assume as1: "STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<and>(\<forall>j. j \<in> {n..m} \<longrightarrow> INPUT(p j) = 0)"
    then have
        1: "STATE(p n) = S_1" and
        2: "INPUT(p n) > 0" and
        3: "\<forall>j. j \<in> {n..m} \<longrightarrow> INPUT(p j) = 0" by auto
    show "i \<in> {n..m}\<longrightarrow> STATE(p i) = S_2"
    proof(induction i)
      case 0
      then show ?case using 1 2 3 by fastforce
    next
      case (Suc i)
      then show ?case
        by (metis Suc_leD as1 atLeastAtMost_iff le_SucE pa stays_in_s2 zero_less_iff_neq_zero)
    qed
  qed
qed

lemma outputs_true: "\<forall>p \<in> paths. ((STATE(p n) = S_1) \<and> (INPUT(p n) > 0)) \<longrightarrow> (OUT(p n) = True)"
proof
  fix p
  assume pa: "p\<in>paths"
  show "STATE(p n) = S_1 \<and> INPUT(p n) > 0 \<longrightarrow> OUT(p n) = True"
  proof
    assume inp: "STATE(p n) = S_1 \<and> INPUT(p n) > 0"
    then have 1: "STATE(p n) = S_1" and 2: "INPUT(p n) > 0" by auto
    
    from paths_def have 3: "\<forall>n. t (STATE (p n), INPUT (p n)) = (STATE (p (Suc n)), OUT (p n))" using pa by auto
    then have 4: "snd(t(STATE (p n), INPUT (p n))) = OUT(p n)" by simp

    from t.simps have "t (S_1, 1) = (S_2, True)" using usf_simp by simp
    then have "t(STATE(p n), INPUT(p n)) = (S_2, True)" by (simp add: "1" "2" usf_simp)
    then have "snd(t(STATE(p n), INPUT(p n))) = True" by auto

    then show "OUT(p n) = True" using 1 2 4 by auto
  qed
qed

lemma lower_bound:
 "\<forall>p\<in>paths. (STATE(p n) = S_1) \<and> (INPUT(p n) > 0)
   \<longrightarrow> ((\<forall>m'>n. m'\<le> (n+m) \<longrightarrow> (INPUT(p m') = 0)) \<longrightarrow> (OUT(p (n+m)) = True))"
        (*m'\<in> {n..(n+m)} *)
        (*m'>n. m'\<le> (n+m) *)
proof
  fix p
  assume ap:"p\<in>paths"
  show "STATE (p n) = S_1 \<and> 0 < INPUT (p n) \<longrightarrow> ((\<forall>m'>n. m' \<le> (n+m) \<longrightarrow> INPUT (p m') = 0) \<longrightarrow> OUT (p (n+m)) = True)"
  proof
    assume as: "STATE (p n) = S_1 \<and> 0 < INPUT (p n) "
    then have
          1: "STATE (p n) = S_1" and
          2: "0 < INPUT (p n)"
      by auto
    have next_one:"STATE(p (Suc n)) = S_2" using 1 2 enters_s2 ap by auto

    show "(\<forall>m'>n. m' \<le> (n+m) \<longrightarrow> INPUT (p m') = 0) \<longrightarrow> OUT (p (n+m)) = True"
    proof(induction m)
      case 0
      have "OUT(p n) = True" using ap 1 2 outputs_true by auto
      then show ?case by auto
    next
      case (Suc m)
      then show ?case
      proof-
        from Suc.IH have "STATE(p (n+m)) = S_2" using y'all sorry
        show "(\<forall>m'>n. m' \<le> n + Suc m \<longrightarrow> INPUT (p m') = 0) \<longrightarrow> OUT (p (n + Suc m)) = True" sorry
      qed
    qed
  qed
qed



end

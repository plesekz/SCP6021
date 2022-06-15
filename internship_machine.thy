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



lemma no_dead_ends: "\<forall>s \<in> \<Sigma>. \<exists>i j. fst(t(s,i)) = j"
  by auto


(*set of all paths*)
definition paths:: "(nat \<Rightarrow> STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(Suc(n))), OUT(p n)))}"

(*very simple S_1 loop*)
definition path:: "nat \<Rightarrow> STEP" where
"path n = \<lparr> INPUT = 0,STATE = S_1,OUT = False \<rparr>"


lemma path_init: "STATE(path(0)) = S_1"
  by (simp add: path_def)

lemma rhs_simp [simp]: " (STATE(path(Suc(n))), OUT(path n)) = (S_1, False)" using path_def by simp


lemma path_induct: "(\<forall>n. \<exists>i. t(STATE(path n),i) = (STATE(path(Suc(n))), OUT(path n)))"
proof (rule allI)
  fix n
  have 0: "t(STATE(path n), 0) = (STATE(path(Suc(n))), OUT(path n))" using path_def by simp
  then show "\<exists>i. t (STATE (path n), i) = (STATE (path (Suc n)), OUT (path n))" using exI by simp
qed

lemma path_in_paths: "path \<in> paths" using path_induct path_init paths_def
  by blast


lemma "paths \<noteq> {}" using path_in_paths
  by blast


(*check whether there is a path leading between stuffs*)
inductive route::"nat list \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
"fst(t (initial, i)) = current \<Longrightarrow> route [i] initial current"|
"route [i] initial node \<Longrightarrow> route is node current  \<Longrightarrow> route (i#is) initial current"

(*general path*)
inductive p::"nat \<Rightarrow> STEP \<Rightarrow> bool" where
"p 0 \<lparr>INPUT = i, STATE = S_1, OUT = snd(t(S_1, i))\<rparr>"|
"\<exists>i::nat. p n \<lparr>INPUT = i, STATE = s, OUT = snd(t(s,i))\<rparr> \<Longrightarrow> p (Suc n) \<lparr> INPUT = j, STATE = fst(t(s,i)), OUT = snd(t(fst(t(s,i)), j)) \<rparr>"

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

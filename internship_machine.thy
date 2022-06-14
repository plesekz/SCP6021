theory internship_machine
  imports Main
begin

datatype State = S_1 | S_2 
type_synonym INPUT = nat
type_synonym OUT =  bool

(* Q: Finite set of States *)
definition Q :: "State set" where
"Q = {S_1, S_2}"

(* \<Sigma>: Finite set of Inputs | Alphabet *)
definition \<Sigma> :: "INPUT set" where
"\<Sigma> = {0, 1}"

record STEP =
INPUT::INPUT
STATE:: State
OUT:: OUT

(* Transition functions (t/\<delta> ) *)

(* \<delta> Function for Odd/Even number of Zeros Machine: S_1 = Even / S_2 = Odd *)
fun \<delta>:: "State \<times> INPUT \<Rightarrow> State" where
"\<delta> (S_1, 0) = S_2" |
"\<delta> (S_1, n) = S_1" |
"\<delta> (S_2, 0) = S_1" |
"\<delta> (S_2, n) = S_2"

(* run the automata using word (Input list) *)
fun run:: "State \<Rightarrow> INPUT list \<Rightarrow> State" where
"run st [] = st" |
"run st (Cons x xs) = run (\<delta> (st, x)) xs"
value "run S_1 [0,1,1,0]"
value "run S_1 [1,1,0]"


(* t function for Boolean Machine *)
fun t:: "State \<times> INPUT \<Rightarrow> State \<times> OUT" where
"t (S_1, 0) = (S_1, False)"|
"t (S_1, n) = (S_2, True) "|
"t (S_2, 0) = (S_1, False) "|
"t (S_2, n) = (S_2, True)"



(*set of all paths*)
definition paths:: "(nat\<Rightarrow>STEP) set" where
"paths \<equiv> {p::(nat \<Rightarrow> STEP). STATE(p(0)) = S_1 \<and> (\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))}"

(*check whether there is a path leading between stuffs*)
inductive route::"nat list \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
"fst(t (initial, i)) = current \<Longrightarrow> route [i] initial current"|
"route [i] initial node \<Longrightarrow> route is node current  \<Longrightarrow> route (i#is) initial current"

(*general path*)
inductive p::"nat\<Rightarrow>STEP \<Rightarrow> bool" where
"tmp = \<lparr>INPUT = i, STATE = S_1, OUT = snd(t(S_1, i))\<rparr>  \<Longrightarrow>  p 0 tmp"|
"\<exists>i::nat. tmp = \<lparr> INPUT = i, STATE = s, OUT = snd(t(s,i)) \<rparr> \<Longrightarrow> p n tmp \<Longrightarrow> p (Suc n) = "



lemma non_empty_paths:
  assumes a: "paths = {}"
shows "\<not>a"
proof-
  fix p::"nat\<Rightarrow>STEP"
  let ?case1 = "STATE(p(0)) = S_1"
  let ?case2 = "(\<forall>n. \<exists>i. t(STATE(p n),i) = (STATE(p(n+1)), OUT(p n)))"
  


  (*from paths_def have "(i,S_1,second(t (S_1, i))) \<in> paths" using t_def by simp*)
qed

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


lemma security: "\<forall>q \<in> paths. \<forall>S \<in> \<Sigma>. \<forall> m. q m = \<lparr>INPUT=1,STATE=S, OUT=True\<rparr>"
proof

  
  
 
qed

end

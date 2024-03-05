theory pt_general imports fixed_points
begin

section \<open>general definitions\<close>

(*states: '\<ss>*)
(*judgement: '\<jj>*)
(*predicates: '\<ss> \<Rightarrow> '\<jj>*)
(*atomic commands: '\<c>*)
(*guards: '\<b>*)
(*command interpretation (ci): '\<c> \<Rightarrow> ('\<ss> \<Rightarrow> '\<ss> set)*)
(*guard intepretation (gi): '\<b> \<Rightarrow> '\<ss> \<Rightarrow> bool*)

datatype ('\<b>, '\<c>) prog 
  = Command '\<c> (\<open>\<bullet>_\<close> [100] 100)
  | Sequential \<open>('\<b>, '\<c>) prog\<close> \<open>('\<b>, '\<c>) prog\<close> (\<open>_ \<^bold>; _\<close> [45,45] 45)
  | Choice \<open>('\<b>, '\<c>) prog\<close> \<open>('\<b>, '\<c>) prog\<close> (\<open>_ \<^bold>[\<^bold>] _\<close> [44,44] 44)
  | If \<open>'\<b>\<close> \<open>('\<b>, '\<c>) prog\<close> \<open>('\<b>, '\<c>) prog\<close>
  | While \<open>'\<b>\<close> \<open>('\<b>, '\<c>) prog\<close>
  | Ghost \<open>('\<b>, '\<c>) prog\<close>
  | Skip

definition \<open>command_req cpt pt \<equiv> \<forall> \<pp> \<c>. pt \<pp> (\<bullet>\<c>) = cpt \<pp> \<c>\<close>
lemma command_unfold: \<open>command_req cpt pt \<Longrightarrow> pt \<pp> (\<bullet>\<c>) = cpt \<pp> \<c>\<close>
  unfolding command_req_def by simp

definition \<open>skip_req pt \<equiv> \<forall> \<pp>. pt \<pp> Skip = \<pp>\<close>
lemma skip_unfold: \<open>skip_req pt \<Longrightarrow> pt \<pp> Skip = \<pp>\<close>
  unfolding skip_req_def by simp

definition \<open>ghost_req pt \<equiv> \<forall> \<pp> prog. pt \<pp> (Ghost prog) = pt \<pp> prog\<close>
lemma ghost_unfold: \<open>ghost_req pt \<Longrightarrow> pt \<pp> (Ghost prog) = pt \<pp> prog\<close>
  unfolding ghost_req_def by simp

definition \<open>fseq_req pt \<equiv> \<forall> \<pp> prog1 prog2. pt \<pp> (prog1\<^bold>;prog2) = pt (pt \<pp> prog1) prog2\<close>
lemma fseq_unfold: \<open>fseq_req pt \<Longrightarrow> pt \<pp> (prog1\<^bold>;prog2) = pt (pt \<pp> prog1) prog2\<close>
  unfolding fseq_req_def by simp

definition \<open>bseq_req pt \<equiv> \<forall> \<pp> prog1 prog2. pt \<pp> (prog1\<^bold>;prog2) = pt (pt \<pp> prog2) prog1\<close>
lemma bseq_unfold: \<open>bseq_req pt \<Longrightarrow> pt \<pp> (prog1\<^bold>;prog2) = pt (pt \<pp> prog2) prog1\<close>
  unfolding bseq_req_def by simp

notation sup (infixl "\<squnion>" 65) 
notation inf (infixl "\<sqinter>" 65) 
notation Sup ("\<Squnion> _" [55] 55) 
notation Inf ("\<Sqinter> _" [55] 55) 
notation top ("\<top>")
notation bot ("\<bottom>")

definition iverson (\<open>\<^bold>[_\<^bold>]\<close>) where \<open>iverson \<gg> \<ss> \<equiv> (if \<gg> \<ss> then \<top> else \<bottom>)\<close>

lemma iverson_top[simp]: \<open>\<gg> \<ss> \<Longrightarrow> \<^bold>[\<gg>\<^bold>] \<ss> = \<top>\<close>
  unfolding iverson_def by simp
lemma iverson_bot[simp]: \<open>\<not>\<gg> \<ss> \<Longrightarrow> \<^bold>[\<gg>\<^bold>] \<ss> = \<bottom>\<close>
  unfolding iverson_def by simp

definition lattice_if (\<open>_ \<^bold>? _ \<^bold>: _\<close> [60,60,60] 60) where \<open>\<gg> \<^bold>? \<pp> \<^bold>: \<qq> \<equiv> (\<^bold>[\<gg>\<^bold>] \<sqinter> \<pp>) \<squnion> (\<^bold>[Not \<circ> \<gg>\<^bold>] \<sqinter> \<qq>)\<close>

(*
angelic if: reachability is "good" behaviour, so we intersect the given pre with states that can actually execute the branch
demonic if: un-reachability is "good" behaviour, so we add all states that cannot reach the branch to the given pre
*)
(*
if x {
  x := True [] skip
} else {
  x := False [] skip
}


make contribution list
make repository

is equal to skip with all normal transformers
but equal to var x for demonic forwards + angelic if
*)
(*this suggests that we could categorize those predicate transformers that treat semantically equal constructs equally*)
(*dual forward if-rules*)
definition \<open>aif_req gi pt \<equiv> \<forall> \<pp> \<b> prog1 prog2. 
  pt \<pp> (If \<b> prog1 prog2) = pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) prog1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) prog2\<close>
lemma aif_unfold: \<open>aif_req gi pt \<Longrightarrow> pt \<pp> (If \<b> prog1 prog2) = pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) prog1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) prog2\<close>
  unfolding aif_req_def by simp
definition \<open>dif_req gi pt \<equiv> \<forall> \<pp> \<b> prog1 prog2. 
  pt \<pp> (If \<b> prog1 prog2) = pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) prog1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) prog2\<close>
lemma dif_unfold: \<open>dif_req gi pt \<Longrightarrow> pt \<pp> (If \<b> prog1 prog2) = pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) prog1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) prog2\<close>
  unfolding dif_req_def by simp

(*backward if is its own dual, so we only need one*)
definition \<open>bif_req gi pt \<equiv> \<forall> \<pp> \<b> prog1 prog2. 
  pt \<pp> (If \<b> prog1 prog2) = gi \<b> \<^bold>? pt \<pp> prog1 \<^bold>: pt \<pp> prog2\<close>
lemma bif_unfold: \<open>bif_req gi pt \<Longrightarrow> pt \<pp> (If \<b> prog1 prog2) = gi \<b> \<^bold>? pt \<pp> prog1 \<^bold>: pt \<pp> prog2\<close>
  unfolding bif_req_def by simp

(* (this is the only source of non-determinism)
angelic choice: all states that fulfill the property if the right choice is taken
demonic choice: all states that fulfill the property no matter which choice is taken
*)
definition \<open>achoice_req pt \<equiv> \<forall> \<pp> prog1 prog2. pt \<pp> (prog1 \<^bold>[\<^bold>] prog2) = pt \<pp> prog1 \<squnion> pt \<pp> prog2\<close>
lemma achoice_unfold: \<open>achoice_req pt \<Longrightarrow> pt \<pp> (prog1 \<^bold>[\<^bold>] prog2) = pt \<pp> prog1 \<squnion> pt \<pp> prog2\<close>
  unfolding achoice_req_def by simp

definition \<open>dchoice_req pt \<equiv> \<forall> \<pp> prog1 prog2. pt \<pp> (prog1 \<^bold>[\<^bold>] prog2) = pt \<pp> prog1 \<sqinter> pt \<pp> prog2\<close>
lemma dchoice_unfold: \<open>dchoice_req pt \<Longrightarrow> pt \<pp> (prog1 \<^bold>[\<^bold>] prog2) = pt \<pp> prog1 \<sqinter> pt \<pp> prog2\<close>
  unfolding dchoice_req_def by simp

(*
I call (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>), (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) prog \<sqinter> \<pp>), and (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) prog \<squnion> \<pp>) iteratees

*)

(*backward while rules
partial while: all states that either end up in the post or diverge
total while: all states that end up in the post
*)
definition \<open>pbwhile_req gi pt \<equiv> \<forall> \<pp> \<b> prog. 
  pt \<pp> (While \<b> prog) = gfp (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>)\<close>
lemma pbwhile_unfold: \<open>pbwhile_req gi pt \<Longrightarrow> pt \<pp> (While \<b> prog) = gfp (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>)\<close>
  unfolding pbwhile_req_def by simp
definition \<open>tbwhile_req gi pt \<equiv> \<forall> \<pp> \<b> prog. 
  pt \<pp> (While \<b> prog) = lfp (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>)\<close>
lemma tbwhile_unfold: \<open>tbwhile_req gi pt \<Longrightarrow> pt \<pp> (While \<b> prog) = lfp (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>)\<close>
  unfolding tbwhile_req_def by simp

(*forward while rules
partial while: all the states that either "fulfill the property" or are unreachable
total while: all the states that the pre terminates in
*)
definition \<open>pfwhile_req gi pt \<equiv> \<forall> \<pp> \<b> prog. 
  pt \<pp> (While \<b> prog) = \<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) prog \<sqinter> \<pp>)\<close>
lemma pfwhile_unfold: \<open>pfwhile_req gi pt \<Longrightarrow> pt \<pp> (While \<b> prog) = \<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) prog \<sqinter> \<pp>)\<close>
  unfolding pfwhile_req_def by simp
definition \<open>tfwhile_req gi pt \<equiv> \<forall> \<pp> \<b> prog. 
  pt \<pp> (While \<b> prog) = \<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) prog \<squnion> \<pp>)\<close>
lemma tfwhile_unfold: \<open>tfwhile_req gi pt \<Longrightarrow> pt \<pp> (While \<b> prog) = \<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) prog \<squnion> \<pp>)\<close>
  unfolding tfwhile_req_def by simp

(*weakest precondition for total correctness*)
definition \<open>wp cpt gi pt \<equiv> command_req cpt pt \<and> skip_req pt \<and> ghost_req pt \<and> bseq_req pt \<and> bif_req gi pt \<and> dchoice_req pt \<and> tbwhile_req gi pt\<close>
lemma wp_command[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (\<bullet>\<c>) = cpt \<pp> \<c>\<close>
  unfolding wp_def command_req_def by simp
lemma wp_skip[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> Skip = \<pp>\<close>
  unfolding wp_def skip_req_def by simp
lemma wp_ghost[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (Ghost prog) = pt \<pp> prog\<close>
  unfolding wp_def ghost_req_def by simp
lemma wp_seq[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (prog1\<^bold>; prog2) = pt (pt \<pp> prog2) prog1\<close>
  unfolding wp_def bseq_req_def by simp
lemma wp_if[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (If \<b> prog1 prog2) = gi \<b> \<^bold>? pt \<pp> prog1 \<^bold>: pt \<pp> prog2\<close>
  unfolding wp_def bif_req_def by simp
lemma wp_choice[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (prog1 \<^bold>[\<^bold>] prog2) = pt \<pp> prog1 \<sqinter> pt \<pp> prog2\<close>
  unfolding wp_def dchoice_req_def by simp
lemma wp_while[simp]: \<open>wp cpt gi pt \<Longrightarrow> pt \<pp> (While \<b> prog) = lfp (\<lambda> x.  gi \<b> \<^bold>? pt x prog \<^bold>: \<pp>)\<close>
  unfolding wp_def tbwhile_req_def by simp

fun erase_ghost where
  \<open>erase_ghost (Ghost prog) = Skip\<close> |
  \<open>erase_ghost Skip = Skip\<close> |
  \<open>erase_ghost (Command c) = Command c\<close> |
  \<open>erase_ghost (prog1\<^bold>; prog2) = (erase_ghost prog1\<^bold>; erase_ghost prog2)\<close> |
  \<open>erase_ghost (prog1 \<^bold>[\<^bold>] prog2) = (erase_ghost prog1 \<^bold>[\<^bold>] erase_ghost prog2)\<close> |
  \<open>erase_ghost (If b prog1 prog2) = If b (erase_ghost prog1) (erase_ghost prog2)\<close> |
  \<open>erase_ghost (While b prog) = While b (erase_ghost prog)\<close>

definition \<open>well_formed analysis prog \<equiv> analysis prog \<longrightarrow> analysis (erase_ghost prog)\<close>

section \<open>projection\<close>
(*regular: \<r>: pred \<Rightarrow> bool*)
(*regular projection: \<r>\<p>: pred \<Rightarrow> rpred*)

definition \<open>gc_leq_req \<r>\<p> cpt gc \<equiv> \<forall> c \<pp>. gc c \<longrightarrow> \<r>\<p> (cpt \<pp> c) \<le> \<r>\<p> \<pp>\<close>
definition \<open>gc_geq_req \<r>\<p> cpt gc \<equiv> \<forall> c \<pp>. gc c \<longrightarrow> \<r>\<p> (cpt \<pp> c) \<ge> \<r>\<p> \<pp>\<close>
definition \<open>rc_req \<r> cpt rc \<equiv> \<forall> c \<pp>. rc c \<longrightarrow> \<r> \<pp> \<longrightarrow> \<r> (cpt \<pp> c)\<close>

section \<open>inductive rules\<close>
(*require the following in \<r>\<p>_Sup and \<r>\<p>_Inf to get classical scott-continuity
definition \<open>up_directed X \<equiv> X \<noteq> {} \<and> (\<forall> x \<in> X. \<forall> y \<in> X. \<exists> z \<in> X. x \<le> z \<and> y \<le> z)\<close> 
definition \<open>down_directed X \<equiv> X \<noteq> {} \<and> (\<forall> x \<in> X. \<forall> y \<in> X. \<exists> z \<in> X. x \<ge> z \<and> y \<ge> z)\<close>*)

locale \<r>\<p>_complete_lattice =
  fixes \<r>\<p> :: \<open>('s \<Rightarrow> 'x :: complete_lattice) \<Rightarrow> ('s \<Rightarrow> 'r :: complete_lattice)\<close>
  assumes \<r>\<p>_Sup: \<open>X \<noteq> {} \<Longrightarrow> \<r>\<p> (\<Squnion> X) = \<Squnion> (\<r>\<p> ` X)\<close>
  assumes \<r>\<p>_Inf: \<open>X \<noteq> {} \<Longrightarrow> \<r>\<p> (\<Sqinter> X) = \<Sqinter> (\<r>\<p> ` X)\<close>
sublocale \<r>\<p>_complete_lattice \<subseteq> power_set_Fix_Lim_Ord \<open>(\<lambda> x. \<bottom>) :: 's \<Rightarrow> 'x\<close> .

context \<r>\<p>_complete_lattice 
begin

subsection \<open>fundamentals\<close>

lemma \<r>\<p>_mono: \<open>mono \<r>\<p>\<close> 
proof
  fix x y :: \<open>'s \<Rightarrow> 'x\<close>
  assume \<open>x \<le> y\<close>
  then have \<open>\<Squnion> {x,y} = y\<close> 
    by (simp add: le_iff_sup)
  then have \<open>\<r>\<p> y = \<Squnion> {\<r>\<p> x, \<r>\<p> y}\<close>
    using \<r>\<p>_Sup by (metis SUP_insert Sup_insert ccpo_Sup_singleton insert_not_empty)
  then show \<open>\<r>\<p> x \<le> \<r>\<p> y\<close> 
    by (simp add: le_iff_sup)
qed

lemma \<r>\<p>_join: \<open>\<r>\<p> (a \<squnion> b) = \<r>\<p> a \<squnion> \<r>\<p> b\<close> 
proof-
  have \<open>\<r>\<p> (\<Squnion> {a,b}) \<le> \<Squnion> (\<r>\<p> ` {a,b})\<close>
    using \<r>\<p>_Sup by (metis dual_order.refl insert_not_empty)
  then show ?thesis 
    by (metis SUP_insert Sup_insert \<r>\<p>_Sup cSup_singleton insert_not_empty)
qed

lemma \<r>\<p>_meet: \<open>\<r>\<p> (a \<sqinter> b) = \<r>\<p> a \<sqinter> \<r>\<p> b\<close> 
proof-
  have \<open>\<r>\<p> (\<Sqinter> {a,b}) \<ge> \<Sqinter> (\<r>\<p> ` {a,b})\<close>
    using \<r>\<p>_Inf by (metis dual_order.refl insert_not_empty)
  then show ?thesis 
    by (metis INF_insert Inf_insert \<r>\<p>_Inf cInf_singleton insert_not_empty)
qed

(*check if a predicate is regular
definition \<open>\<r> \<pp> \<equiv> \<forall> \<qq>. \<r>\<p> \<pp> = \<r>\<p> \<qq> \<longrightarrow> \<qq> \<le> \<pp>\<close>

lemma \<open>\<r> \<pp> \<Longrightarrow> \<r>\<p> \<qq> \<le> \<r>\<p> \<pp> \<Longrightarrow> \<qq> \<le> \<pp>\<close> 
  unfolding \<r>_def by (metis \<r>\<p>_join \<r>\<p>_mono antisym mono_sup sup.absorb_iff2 sup.cobounded2)
*)


(*some of the following are probably superfluous*)
lemma f_not_f_leq1: \<open>\<^bold>[f\<^bold>] \<sqinter> (a :: 's \<Rightarrow> 'x) \<le> b \<Longrightarrow> \<^bold>[Not \<circ> f\<^bold>] \<sqinter> a \<le> b \<Longrightarrow> a \<le> b\<close>
proof (rule le_funI)
  fix x
  assume \<open>\<^bold>[f\<^bold>] \<sqinter> a \<le> b\<close> \<open>\<^bold>[Not \<circ> f\<^bold>] \<sqinter> a \<le> b\<close>
  show \<open>a x \<le> b x\<close> 
  proof (cases \<open>f x\<close>)
    case True
    then have \<open>(\<^bold>[f\<^bold>] \<sqinter> a) x = a x\<close>
      by simp
    then show ?thesis 
      using \<open>\<^bold>[f\<^bold>] \<sqinter> a \<le> b\<close> by (metis le_funE)
  next
    case False
    then have \<open>(\<^bold>[Not \<circ> f\<^bold>] \<sqinter> a) x = a x\<close>
      by simp
    then show ?thesis 
      using \<open>\<^bold>[Not \<circ> f\<^bold>] \<sqinter> a \<le> b\<close> by (metis le_funE)
  qed
qed

lemma f_not_f_geq1: \<open>\<^bold>[f\<^bold>] \<squnion> (a :: 's \<Rightarrow> 'x) \<ge> b \<Longrightarrow> \<^bold>[Not \<circ> f\<^bold>] \<squnion> a \<ge> b \<Longrightarrow> a \<ge> b\<close>
proof (rule le_funI)
  fix x
  assume \<open>\<^bold>[f\<^bold>] \<squnion> a \<ge> b\<close> \<open>\<^bold>[Not \<circ> f\<^bold>] \<squnion> a \<ge> b\<close>
  show \<open>a x \<ge> b x\<close> 
  proof (cases \<open>f x\<close>)
    case True
    then have \<open>(\<^bold>[Not \<circ> f\<^bold>] \<squnion> a) x = a x\<close>
      by simp
    then show ?thesis 
      using \<open>\<^bold>[Not \<circ> f\<^bold>] \<squnion> a \<ge> b\<close> by (metis le_funE)
  next
    case False
    then have \<open>(\<^bold>[f\<^bold>] \<squnion> a) x = a x\<close>
      by simp
    then show ?thesis 
      using \<open>\<^bold>[f\<^bold>] \<squnion> a \<ge> b\<close> by (metis le_funE)
  qed
qed

lemma \<r>\<p>_f_not_f_geq1: \<open>\<r>\<p> (\<^bold>[f\<^bold>] \<sqinter> \<pp>) \<squnion> \<r>\<p> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> \<pp>) \<ge> \<r>\<p> \<pp>\<close> 
  by (metis (no_types, lifting) \<r>\<p>_join \<r>\<p>_mono f_not_f_leq1 monoD sup.cobounded1 sup.cobounded2)

lemma \<r>\<p>_f_not_f_leq1: \<open>\<r>\<p> (\<^bold>[f\<^bold>] \<squnion> \<pp>) \<sqinter> \<r>\<p> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> \<pp>) \<le> \<r>\<p> \<pp>\<close> 
  by (metis (no_types, lifting) \<r>\<p>_meet \<r>\<p>_mono f_not_f_geq1 monoD inf.cobounded1 inf.cobounded2)

lemma f_not_f_geq2: \<open>(a :: 's \<Rightarrow> 'x) \<ge> c \<Longrightarrow> b \<ge> c \<Longrightarrow> (\<^bold>[f\<^bold>] \<sqinter> a) \<squnion> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> b) \<ge> c\<close>
proof (rule le_funI, unfold sup_apply inf_apply)
  fix x
  assume \<open>a \<ge> c\<close> \<open>b \<ge> c\<close>
  show \<open>\<^bold>[f\<^bold>] x \<sqinter> a x \<squnion> (\<^bold>[Not \<circ> f\<^bold>] x \<sqinter> b x) \<ge> c x\<close> 
  proof (cases \<open>f x\<close>)
    case True
    then have \<open>\<^bold>[f\<^bold>] x \<sqinter> a x = a x\<close>
      by simp
    then show ?thesis
      using \<open>a \<ge> c\<close> by (simp add: le_fun_def le_supI1)
  next
    case False
    then have \<open>\<^bold>[Not \<circ> f\<^bold>] x \<sqinter> b x = b x\<close>
      by simp
    then show ?thesis 
      using \<open>b \<ge> c\<close> by (simp add: le_fun_def le_supI2)
  qed
qed

lemma f_not_f_leq2: \<open>(a :: 's \<Rightarrow> 'x) \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> (\<^bold>[f\<^bold>] \<squnion> a) \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> b) \<le> c\<close>
proof (rule le_funI, unfold sup_apply inf_apply)
  fix x
  assume \<open>a \<le> c\<close> \<open>b \<le> c\<close>
  show \<open>\<^bold>[f\<^bold>] x \<squnion> a x \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] x \<squnion> b x) \<le> c x\<close> 
  proof (cases \<open>f x\<close>)
    case True
    then have \<open>(\<^bold>[Not \<circ> f\<^bold>] \<squnion> b) x = b x\<close>
      by simp
    then show ?thesis 
      using \<open>b \<le> c\<close> by (simp add: le_fun_def le_infI2)
  next
    case False
    then have \<open>\<^bold>[f\<^bold>] x \<squnion> a x = a x\<close>
      by simp
    then show ?thesis 
      using \<open>a \<le> c\<close> by (simp add: le_fun_def le_infI1)
  qed
qed

lemma \<r>\<p>_f_not_f_geq2a: \<open>\<r>\<p> a \<ge> \<r>\<p> c \<Longrightarrow> \<r>\<p> b \<ge> \<r>\<p> c \<Longrightarrow> \<r>\<p> ((\<^bold>[f\<^bold>] \<sqinter> a) \<squnion> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> b)) \<ge> \<r>\<p> c\<close> 
proof-
  assume \<open>\<r>\<p> a \<ge> \<r>\<p> c\<close> \<open>\<r>\<p> b \<ge> \<r>\<p> c\<close>
  moreover have \<open>\<r>\<p> (\<^bold>[f\<^bold>] \<sqinter> a \<squnion> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> b)) \<ge> \<r>\<p> (a \<sqinter> b)\<close> 
    using f_not_f_geq2 by (simp add: \<r>\<p>_mono monoD)
  ultimately show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_meet inf.boundedI order_trans)
qed

lemma \<r>\<p>_f_not_f_geq2b: \<open>\<r>\<p> a \<ge> \<r>\<p> c \<Longrightarrow> \<r>\<p> b \<ge> \<r>\<p> c \<Longrightarrow> \<r>\<p> ((\<^bold>[f\<^bold>] \<squnion> a) \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> b)) \<ge> \<r>\<p> c\<close> 
proof-
  assume \<open>\<r>\<p> a \<ge> \<r>\<p> c\<close> \<open>\<r>\<p> b \<ge> \<r>\<p> c\<close>
  moreover have \<open>\<r>\<p> ((\<^bold>[f\<^bold>] \<squnion> a) \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> b)) \<ge> \<r>\<p> (a \<sqinter> b)\<close>
    by (metis \<r>\<p>_mono inf_mono monoD sup.cobounded2)
  ultimately show ?thesis
    by (metis (no_types, lifting) \<r>\<p>_meet inf.boundedI order_trans)
qed

lemma \<r>\<p>_f_not_f_leq2a: \<open>\<r>\<p> a \<le> \<r>\<p> c \<Longrightarrow> \<r>\<p> b \<le> \<r>\<p> c \<Longrightarrow> \<r>\<p> ((\<^bold>[f\<^bold>] \<squnion> a) \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> b)) \<le> \<r>\<p> c\<close> 
proof-
  assume \<open>\<r>\<p> a \<le> \<r>\<p> c\<close> \<open>\<r>\<p> b \<le> \<r>\<p> c\<close>
  moreover have \<open>\<r>\<p> ((\<^bold>[f\<^bold>] \<squnion> a) \<sqinter> (\<^bold>[Not \<circ> f\<^bold>] \<squnion> b)) \<le> \<r>\<p> (a \<squnion> b)\<close> 
    using f_not_f_leq2 by (simp add: \<r>\<p>_mono monoD)
  ultimately show ?thesis
    by (metis (no_types, lifting) \<r>\<p>_join sup.boundedI order_trans)
qed

lemma \<r>\<p>_f_not_f_leq2b: \<open>\<r>\<p> a \<le> \<r>\<p> c \<Longrightarrow> \<r>\<p> b \<le> \<r>\<p> c \<Longrightarrow> \<r>\<p> ((\<^bold>[f\<^bold>] \<sqinter> a) \<squnion> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> b)) \<le> \<r>\<p> c\<close> 
proof-
  assume \<open>\<r>\<p> a \<le> \<r>\<p> c\<close> \<open>\<r>\<p> b \<le> \<r>\<p> c\<close>
  moreover have \<open>\<r>\<p> ((\<^bold>[f\<^bold>] \<sqinter> a) \<squnion> (\<^bold>[Not \<circ> f\<^bold>] \<sqinter> b)) \<le> \<r>\<p> (a \<squnion> b)\<close> 
    by (metis \<r>\<p>_mono inf.cobounded2 monoD sup.mono)
  ultimately show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_join sup.boundedI order_trans)
qed

lemma lattice_if_mono: \<open>\<r>\<p> p1 \<le> \<r>\<p> q1 \<Longrightarrow> \<r>\<p> p2 \<le> \<r>\<p> q2 \<Longrightarrow> \<r>\<p> (b \<^bold>? p1 \<^bold>: p2) \<le> \<r>\<p> (b \<^bold>? q1 \<^bold>: q2)\<close>
proof -
  assume \<open>\<r>\<p> p1 \<le> \<r>\<p> q1\<close> \<open>\<r>\<p> p2 \<le> \<r>\<p> q2\<close>
  then have \<open>\<r>\<p> (\<^bold>[b\<^bold>] \<sqinter> p1) \<le> \<r>\<p> (\<^bold>[b\<^bold>] \<sqinter> q1)\<close> \<open> \<r>\<p> (\<^bold>[Not \<circ> b\<^bold>] \<sqinter> p2) \<le>  \<r>\<p> (\<^bold>[Not \<circ> b\<^bold>] \<sqinter> q2)\<close> 
    using \<r>\<p>_meet dual_order.trans by fastforce+
  then show ?thesis
    unfolding lattice_if_def by (metis \<r>\<p>_join sup.mono)
qed


subsection \<open>monotonicity\<close>

lemma mono_b_iteratee: 
  assumes \<open>mono (\<lambda> x. pt x c)\<close>
  shows \<open>mono (\<lambda> x :: 's \<Rightarrow> 'x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)\<close>
proof
  fix x y :: \<open>'s \<Rightarrow> 'x\<close>
  assume \<open>x \<le> y\<close>
  then show \<open>gi \<b> \<^bold>? pt x c \<^bold>: \<pp> \<le> gi \<b> \<^bold>? pt y c \<^bold>: \<pp>\<close> 
    using assms monoE unfolding lattice_if_def by (metis dual_order.refl inf_mono sup.mono)
qed

lemma mono_pf_iteratee: 
  assumes \<open>mono (\<lambda> x. pt x c)\<close>
  shows \<open>mono (\<lambda> x :: 's \<Rightarrow> 'x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp> :: 's \<Rightarrow> 'x)\<close>
proof
  fix x y :: \<open>'s \<Rightarrow> 'x\<close>
  assume \<open>x \<le> y\<close>
  then have \<open>\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x \<le> \<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> y\<close>
    by (simp add: le_supI2)
  then have \<open>pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<le> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> y) c\<close> 
    using assms monoE by metis
  then show \<open>pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp> \<le> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> y) c \<sqinter> \<pp>\<close> 
    by (meson dual_order.refl inf_mono)
qed

lemma mono_tf_iteratee: 
  assumes \<open>mono (\<lambda> x. pt x c)\<close>
  shows \<open>mono (\<lambda> x :: 's \<Rightarrow> 'x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp> :: 's \<Rightarrow> 'x)\<close>
proof
  fix x y :: \<open>'s \<Rightarrow> 'x\<close>
  assume \<open>x \<le> y\<close>
  then have \<open>\<^bold>[gi \<b>\<^bold>] \<sqinter> x \<le> \<^bold>[gi \<b>\<^bold>] \<sqinter> y\<close>
    by (simp add: le_infI2)
  then have \<open>pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<le> pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> y) c\<close> 
    using assms monoE by metis
  then show \<open>pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp> \<le> pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> y) c \<squnion> \<pp>\<close>
    using sup.mono by blast
qed

lemma seq_mono: 
  assumes prems: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> pt \<pp> c1 \<le> pt \<qq> c1\<close> \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>pt (pt \<pp> c1) c2 \<le> pt (pt \<qq> c1) c2\<close>
  using assms by auto

lemma achoice_mono: 
  assumes hyps: \<open>(pt \<pp> c1 :: 's \<Rightarrow> 'x) \<le> pt \<qq> c1\<close> \<open>pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>pt \<pp> c1 \<squnion> pt \<pp> c2 \<le> pt \<qq> c1 \<squnion> pt \<qq> c2\<close>
  using sup_mono hyps .

lemma dchoice_mono: 
  assumes hyps: \<open>(pt \<pp> c1 :: 's \<Rightarrow> 'x) \<le> pt \<qq> c1\<close> \<open>pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>pt \<pp> c1 \<sqinter> pt \<pp> c2 \<le> pt \<qq> c1 \<sqinter> pt \<qq> c2\<close>
  using inf_mono hyps .

lemma aif_mono: 
  assumes prems: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c1 :: 's \<Rightarrow> 'x) \<le> pt \<qq> c1\<close> \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2 \<le> pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<qq>) c2\<close>
  using assms by (meson inf_mono order_eq_refl sup_mono)

lemma dif_mono: 
  assumes prems: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c1 :: 's \<Rightarrow> 'x) \<le> pt \<qq> c1\<close> \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2 \<le> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<qq>) c2\<close>
  using assms by (meson inf_mono order_eq_refl sup_mono)

lemma bif_mono: 
  assumes hyps: \<open>(pt \<pp> c1 :: 's \<Rightarrow> 'x) \<le> pt \<qq> c1\<close> \<open>pt \<pp> c2 \<le> pt \<qq> c2\<close> 
  shows \<open>gi \<b> \<^bold>? pt \<pp> c1 \<^bold>: pt \<pp> c2 \<le> gi \<b> \<^bold>? pt \<qq> c1 \<^bold>: pt \<qq> c2\<close>
  unfolding lattice_if_def using assms by (meson dual_order.refl inf_mono sup.mono)

lemma pbwhile_mono: 
  assumes reqs: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c :: 's \<Rightarrow> 'x) \<le> pt \<qq> c\<close>
  shows \<open>gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<le> gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>)\<close>
proof(rule Iter_gfp2[OF mono_b_iteratee mono_b_iteratee])
  show \<open>mono (\<lambda>x. pt x c)\<close> \<open>mono (\<lambda>x. pt x c)\<close> 
    using monoI hyps by meson+
  show \<open>Iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<top> n \<le> Iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>) \<top> n\<close> for n
  proof(induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?i = \<open>Iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<top> i\<close>
    let ?j = \<open>Iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>) \<top> i\<close>
    from 2 hyps have \<open>pt ?i c \<le> pt ?j c\<close> 
      by fast
    then have \<open>gi \<b> \<^bold>? pt ?i c \<^bold>: \<pp> \<le>  gi \<b> \<^bold>? pt ?j c \<^bold>: \<qq>\<close>
      unfolding lattice_if_def using reqs by (meson dual_order.refl inf_mono sup.mono)
    then show ?case
      by (metis (mono_tags, lifting) "2.hyps"(1) Iter_succ local.above_Field)
  next
    case (3 i)
    then show ?case
      by (metis (mono_tags, lifting) INF_mono Iter_lim)
  qed
qed

lemma tbwhile_mono: 
  assumes reqs: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c :: 's \<Rightarrow> 'x) \<le> pt \<qq> c\<close>
  shows \<open>lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<le> lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>)\<close>
proof(rule iter_lfp2[OF mono_b_iteratee mono_b_iteratee])
  show \<open>mono (\<lambda>x. pt x c)\<close> \<open>mono (\<lambda>x. pt x c)\<close> 
    using monoI hyps by meson+
  show \<open>iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<bottom> n \<le> iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>) \<bottom> n\<close> for n
  proof(induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?i = \<open>iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<bottom> i\<close>
    let ?j = \<open>iter (\<lambda>x. gi \<b> \<^bold>? pt x c \<^bold>: \<qq>) \<bottom> i\<close>
    from 2 hyps have \<open>pt ?i c \<le> pt ?j c\<close> 
      by fast
    then have \<open>gi \<b> \<^bold>? pt ?i c \<^bold>: \<pp> \<le>  gi \<b> \<^bold>? pt ?j c \<^bold>: \<qq>\<close>
      unfolding lattice_if_def using reqs by (meson dual_order.refl inf_mono sup.mono)
    then show ?case
      by (metis (mono_tags, lifting) "2.hyps"(1) iter_succ local.above_Field)
  next
    case (3 i)
    then show ?case
      by (metis (mono_tags, lifting) SUP_mono iter_lim)
  qed
qed

lemma pfwhile_mono: 
  assumes reqs: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c :: 's \<Rightarrow> 'x) \<le> pt \<qq> c\<close>
  shows \<open>\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>) \<le> \<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<qq>)\<close>
proof-
  have \<open>gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>) \<le> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<qq>)\<close>
  proof(rule Iter_gfp2[OF mono_pf_iteratee mono_pf_iteratee])
    show \<open>mono (\<lambda>x. pt x c)\<close> \<open>mono (\<lambda>x. pt x c)\<close> 
      using monoI hyps by meson+
    show \<open>Iter (\<lambda>x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>) \<top> n \<le> Iter (\<lambda>x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<qq>) \<top> n\<close> for n
    proof(induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
      case 1
      then show ?case 
        by simp
    next
      case (2 i)
      let ?i = \<open>Iter (\<lambda>x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>) \<top> i\<close>
      let ?j = \<open>Iter (\<lambda>x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<qq>) \<top> i\<close>
      from 2 hyps have \<open>pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> ?i) c \<le> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> ?j) c\<close> 
        by (meson inf_sup_ord(3) le_supI le_supI2)
      then have \<open>pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> ?i) c \<sqinter> \<pp> \<le> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> ?j) c \<sqinter> \<qq>\<close>
        using reqs inf_mono by blast
      then show ?case 
        by (metis (no_types, lifting) "2.hyps"(1) Iter_succ local.above_Field)
    next
      case (3 i)
      then show ?case 
        by (metis (mono_tags, lifting) INF_mono Iter_lim)
    qed
  qed
  then show ?thesis
    by (meson order_refl sup.mono)
qed

lemma tfwhile_mono: 
  assumes reqs: \<open>\<pp> \<le> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<pp> \<le> \<qq> \<Longrightarrow> (pt \<pp> c :: 's \<Rightarrow> 'x) \<le> pt \<qq> c\<close>
  shows \<open>\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>) \<le> \<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<qq>)\<close>
proof-
  have \<open>lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>) \<le> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<qq>)\<close>
  proof(rule iter_lfp2[OF mono_tf_iteratee mono_tf_iteratee])
    show \<open>mono (\<lambda>x. pt x c)\<close> \<open>mono (\<lambda>x. pt x c)\<close> 
      using monoI hyps by meson+
    show \<open>iter (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>) \<bottom> n \<le> iter (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<qq>) \<bottom> n\<close> for n
    proof(induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
      case 1
      then show ?case 
        by simp
    next
      case (2 i)
      let ?i = \<open>iter (\<lambda>x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>) \<bottom> i\<close>
      let ?j = \<open>iter (\<lambda>x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<qq>) \<bottom> i\<close>
      from 2 hyps have \<open>pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> ?i) c \<le> pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> ?j) c\<close> 
        by (meson dual_order.refl inf_mono)
      then have \<open>pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> ?i) c \<squnion> \<pp> \<le> pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> ?j) c \<squnion> \<qq>\<close>
        using reqs sup_mono by blast
      then show ?case 
        by (metis (no_types, lifting) "2.hyps"(1) iter_succ local.above_Field)
    next
      case (3 i)
      then show ?case 
        by (metis (mono_tags, lifting) SUP_mono iter_lim)
    qed
  qed
  then show ?thesis
    by (meson order_refl inf.mono)
qed

end

locale \<r>\<p>_pt_mono = 
  \<r>\<p>_complete_lattice \<r>\<p> for \<r>\<p> :: \<open>('s \<Rightarrow> 'x :: complete_lattice) \<Rightarrow> ('s \<Rightarrow> 'r :: complete_lattice)\<close>+
  fixes pt :: \<open>('s \<Rightarrow> 'x :: complete_lattice) \<Rightarrow> ('\<b>, '\<c>) prog \<Rightarrow> ('s \<Rightarrow> 'x)\<close>
  assumes pt_mono: \<open>mono (\<lambda> \<pp>. pt \<pp> c)\<close>

context \<r>\<p>_pt_mono
begin

subsection \<open>conjunctivity\<close>

lemma seq_conj:
  assumes hyps: \<open>\<And> \<pp> \<qq>. pt \<pp> c1 \<sqinter> pt \<qq> c1 \<le> pt (\<pp> \<sqinter> \<qq>) c1\<close> \<open>\<And> \<pp> \<qq>. pt \<pp> c2 \<sqinter> pt \<qq> c2 \<le> pt (\<pp> \<sqinter> \<qq>) c2\<close>
  shows \<open>pt (pt \<pp> c1) c2 \<sqinter> pt (pt \<qq> c1) c2 \<le> pt (pt (\<pp> \<sqinter> \<qq>) c1) c2\<close>
  using assms by (metis antisym mono_inf pt_mono)

subsection \<open>disjunctivity\<close>


subsection \<open>ghost code can be removed\<close>

lemma seq_leq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (pt (pt \<pp> c1) c2) \<le> \<r>\<p> \<pp>\<close>
  using hyps by (metis dual_order.trans)

lemma seq_geq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (pt (pt \<pp> c1) c2) \<ge> \<r>\<p> \<pp>\<close>
  using hyps by (metis dual_order.trans)

lemma achoice_leq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp>\<close> \<open>\<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (pt \<pp> c1 \<squnion> pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close>
  using hyps by (metis \<r>\<p>_join le_sup_iff)

lemma achoice_geq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp> \<or> \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt \<pp> c1 \<squnion> pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close>
  using hyps \<r>\<p>_mono by (metis dual_order.trans monotoneD sup.cobounded2 sup_ge1)

lemma dchoice_leq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp> \<or> \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (pt \<pp> c1 \<sqinter> pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close>
  using hyps \<r>\<p>_mono by (metis (mono_tags, opaque_lifting) dual_order.trans inf.bounded_iff mono_inf)

lemma dchoice_geq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt \<pp> c1 \<sqinter> pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close>
  using hyps by (metis \<r>\<p>_meet inf.bounded_iff)

lemma aif_geq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<ge> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<ge> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>)\<close> 
    using hyps(1) by (metis \<r>\<p>_join sup.coboundedI1)
  moreover have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<ge> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>)\<close> 
    using hyps(2) by (metis \<r>\<p>_join sup.coboundedI2)
  ultimately show ?thesis 
    using \<r>\<p>_f_not_f_geq1 by (meson order.trans sup.boundedI)
qed

lemma aif_leq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<le> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1) \<le> \<r>\<p> \<pp>\<close>
    using hyps(1) by (metis \<r>\<p>_meet inf.bounded_iff)
  moreover have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<le> \<r>\<p> \<pp>\<close> 
    using hyps(2) by (metis \<r>\<p>_meet inf.bounded_iff)
  ultimately show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_join sup.boundedI)
qed

lemma dif_geq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<ge> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1) \<ge> \<r>\<p> \<pp>\<close> 
    using hyps(1) by (metis dual_order.trans monotoneD \<r>\<p>_mono sup.cobounded2)
  moreover have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<ge> \<r>\<p> \<pp>\<close> 
    using hyps(2) by (metis dual_order.trans monotoneD \<r>\<p>_mono sup.cobounded2)
  ultimately show ?thesis
    by (metis \<r>\<p>_meet le_infI)
qed

lemma dif_leq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp>\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<le> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<le> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>)\<close> 
    using hyps(1) by (metis \<r>\<p>_meet le_infI1)
  moreover have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<le> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>)\<close> 
    using hyps(2) by (metis \<r>\<p>_meet le_infI2)
  ultimately show ?thesis
    using \<r>\<p>_f_not_f_leq1 by (meson inf.boundedI order_trans)
qed

lemma bif_geq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> \<pp>\<close> \<open>\<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (gi \<b> \<^bold>? pt \<pp> c1 \<^bold>: pt \<pp> c2) \<ge> \<r>\<p> \<pp>\<close> 
  by (simp add: \<r>\<p>_f_not_f_geq2a hyps(1) hyps(2) lattice_if_def)

lemma bif_leq_ginduct:
  assumes hyps: \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> \<pp>\<close> \<open>\<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close> 
  shows \<open>\<r>\<p> (gi \<b> \<^bold>? pt \<pp> c1 \<^bold>: pt \<pp> c2) \<le> \<r>\<p> \<pp>\<close> 
  by (simp add: \<r>\<p>_f_not_f_leq2b hyps(1) hyps(2) lattice_if_def)

lemma gfp_\<r>\<p>_greater:
  assumes reqs: \<open>mono (f :: ('s \<Rightarrow> 'x) \<Rightarrow> ('s \<Rightarrow> 'x))\<close> 
    and hyps: \<open>\<And> \<qq>. \<r>\<p> \<qq> \<ge> \<r>\<p> \<pp> \<Longrightarrow> \<r>\<p> (f \<qq>) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (gfp f) \<ge> \<r>\<p> \<pp>\<close>  
proof-
  have \<open>\<r>\<p> (Iter f \<top> n) \<ge> \<r>\<p> \<pp>\<close> for n 
  proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    show ?case 
      by (metis Iter_zero \<r>\<p>_mono monoE top_greatest)
  next
    case (2 i)
    let ?i = \<open>Iter f \<top> i\<close>
    have \<open>\<r>\<p> (f ?i) \<ge> \<r>\<p> \<pp>\<close>
      using hyps 2(2) dual_order.trans by blast 
    then show ?case 
      by (metis Field_card_of Iter_succ UNIV_I)
  next
    case (3 i)
    let ?X = \<open>Iter f \<top> ` underS ord_rel i\<close>
    from 3 have \<open>\<forall> x \<in> ?X. \<r>\<p> \<pp> \<le> \<r>\<p> x\<close>
      by blast
    then have \<open>\<r>\<p> \<pp> \<le> \<r>\<p> (Inf ?X)\<close> 
      by (metis (no_types, lifting) INF_greatest Inf_empty \<r>\<p>_Inf \<r>\<p>_mono monoE top_greatest)
    then show ?case
      using 3(1,2) Iter_lim by metis
  qed
  then show ?thesis
    by (metis FIX_def FIX_is_gfp reqs)
qed

lemma pbwhile_geq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
proof (induct rule: gfp_\<r>\<p>_greater)
  case 1
  then show ?case 
    using mono_b_iteratee pt_mono .
next
  case (2 \<qq>)
  then have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> pt \<qq> c \<squnion> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
    using \<r>\<p>_f_not_f_geq2a by (meson dual_order.refl dual_order.trans hyps)
  then show ?case
    by (simp add: lattice_if_def)
qed

lemma lfp_\<r>\<p>_lesser:
  assumes reqs: \<open>mono (f :: ('s \<Rightarrow> 'x) \<Rightarrow> ('s \<Rightarrow> 'x))\<close> 
    and hyps: \<open>\<And> \<qq>. \<r>\<p> \<qq> \<le> \<r>\<p> \<pp> \<Longrightarrow> \<r>\<p> (f \<qq>) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (lfp f) \<le> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (iter f \<bottom> n) \<le> \<r>\<p> \<pp>\<close> for n 
  proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by (metis \<r>\<p>_mono bot.extremum iter_zero monoE)
  next
    case (2 i)
    let ?i = \<open>iter f \<bottom> i\<close>
    have \<open>\<r>\<p> (f ?i) \<le> \<r>\<p> \<pp>\<close>
      using hyps 2(2) dual_order.trans by blast 
    then show ?case 
      by (metis Field_card_of iter_succ UNIV_I)
  next
    case (3 i)
    let ?X = \<open>iter f \<bottom> ` underS ord_rel i\<close>
    from 3 have \<open>\<forall> x \<in> ?X. \<r>\<p> \<pp> \<ge> \<r>\<p> x\<close>
      by blast
    then have \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> (Sup ?X)\<close>
      by (metis (no_types, opaque_lifting) SUP_least Sup_empty \<r>\<p>_Sup \<r>\<p>_mono bot.extremum monotoneD)
    then show ?case
      using 3(1,2) iter_lim by metis
  qed
  then show ?thesis 
    by (metis Fix_def Fix_is_lfp reqs)
qed

lemma tbwhile_leq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<le> \<r>\<p> \<pp>\<close>
proof (induct rule: lfp_\<r>\<p>_lesser)
  case 1
  then show ?case 
    using mono_b_iteratee pt_mono .
next
  case (2 \<qq>)
  then have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> pt \<qq> c \<squnion> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>)) \<le> \<r>\<p> \<pp>\<close>
    using \<r>\<p>_f_not_f_leq2b by (meson hyps order_eq_refl order_trans)
  then show ?case
    by (simp add: lattice_if_def)
qed

lemma pbwhile_leq_ginduct:
  assumes reqs: \<open>gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<le> \<pp> \<squnion> lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)\<close>
    and hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<le> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<le> \<r>\<p> \<pp>\<close> 
    using tbwhile_leq_ginduct hyps .
  then show ?thesis
    using reqs by (metis \<r>\<p>_join sup.absorb_iff1)
qed

lemma tbwhile_geq_ginduct:
  assumes reqs: \<open>lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>) \<ge> \<pp> \<sqinter> gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)\<close>
    and hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<ge> \<r>\<p> \<pp>\<close> 
    using pbwhile_geq_ginduct hyps .
  then show ?thesis
    using reqs by (metis (mono_tags, lifting) \<r>\<p>_meet \<r>\<p>_mono inf.orderE monotoneD)
qed

lemma pfwhile_geq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
  proof (induct rule: gfp_\<r>\<p>_greater)
    case 1
    then show ?case 
      using mono_pf_iteratee pt_mono .
  next
    case (2 \<qq>)
    then show ?case
      by (metis (no_types, lifting) \<r>\<p>_mono dual_order.refl dual_order.trans hyps inf_greatest mono_sup \<r>\<p>_meet sup.cobounded2)
  qed
  then show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_mono inf_sup_ord(4) monoD order_trans)
qed

lemma tfwhile_leq_ginduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<le> \<r>\<p> \<pp>\<close> 
proof-
  have \<open>\<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<le> \<r>\<p> \<pp>\<close>
  proof (induct rule: lfp_\<r>\<p>_lesser)
    case 1
    then show ?case 
      using mono_tf_iteratee pt_mono .
  next
    case (2 \<qq>)
    then show ?case
      by (metis (no_types, opaque_lifting) \<r>\<p>_join \<r>\<p>_meet hyps inf.order_iff le_infE order_refl sup_least)
  qed
  then show ?thesis 
    using \<r>\<p>_mono dual_order.trans mono_inf by fastforce
qed

lemma pfwhile_leq_ginduct:
  assumes reqs: \<open>\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>) \<le> \<pp> \<squnion> lfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)\<close>
    and hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<le> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<le> \<r>\<p> \<pp>\<close>
  proof (induct rule: lfp_\<r>\<p>_lesser)
    case 1
    show ?case 
      using mono_pf_iteratee pt_mono .
  next
    case (2 \<qq>)
    then show ?case 
      by (simp add: \<r>\<p>_mono monoD)
  qed
  then show ?thesis
    using reqs by (metis (no_types, lifting) \<r>\<p>_join inf_sup_aci(5) sup.absorb_iff2)
qed

lemma tfwhile_geq_ginduct:
  assumes reqs: \<open>\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>) \<ge> \<pp> \<sqinter> gfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)\<close>
    and hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> \<pp>\<close>
  shows \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<ge> \<r>\<p> \<pp>\<close>
proof-
  have \<open>\<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<ge> \<r>\<p> \<pp>\<close> 
  proof (induct rule: gfp_\<r>\<p>_greater)
    case 1
    then show ?case 
      using mono_tf_iteratee pt_mono .
  next
    case (2 \<qq>)
    then show ?case 
      by (simp add: \<r>\<p>_mono monoD)
  qed
  then show ?thesis
    using reqs by (metis (no_types, lifting) \<r>\<p>_meet inf.absorb_iff1)
qed


section \<open>regular code preserved by ghost erasure\<close>
(*eg is intended to be instantiated by erase_ghost, defined above, though there may be other uses of the following lemmas*)
lemma seq_rinduct:
  assumes prems: \<open>cop (\<r>\<p> \<pp>) (\<r>\<p> \<qq>)\<close> 
    and hyps: 
      \<open>\<And> \<pp> \<qq>. cop (\<r>\<p> \<pp>) (\<r>\<p> \<qq>) \<Longrightarrow> cop (\<r>\<p> (pt \<pp> c1)) (\<r>\<p> (pt \<qq> (eg c1)))\<close>
      \<open>\<And> \<pp> \<qq>. cop (\<r>\<p> \<pp>) (\<r>\<p> \<qq>) \<Longrightarrow> cop (\<r>\<p> (pt \<pp> c2)) (\<r>\<p> (pt \<qq> (eg c2)))\<close>
    shows \<open>cop (\<r>\<p> (pt (pt \<pp> c1) c2)) (\<r>\<p> (pt (pt \<qq> (eg c1)) (eg c2)))\<close>
proof-
  have \<open>cop (\<r>\<p> (pt \<pp> c1)) (\<r>\<p> (pt \<qq> (eg c1)))\<close>
    using hyps(1) prems .
  with hyps(2) show ?thesis .
qed

lemma achoice_leq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt \<pp> c1 \<squnion> pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c1) \<squnion> pt \<qq> (eg c2))\<close>
  using assms \<r>\<p>_join by (metis sup_mono)

lemma dchoice_leq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt \<pp> c1 \<sqinter> pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c1) \<sqinter> pt \<qq> (eg c2))\<close>
  using assms \<r>\<p>_meet by (metis inf_mono)

lemma achoice_geq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt \<pp> c1 \<squnion> pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c1) \<squnion> pt \<qq> (eg c2))\<close>
  using assms \<r>\<p>_join by (metis sup_mono)

lemma dchoice_geq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt \<pp> c1 \<sqinter> pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c1) \<sqinter> pt \<qq> (eg c2))\<close>
  using assms \<r>\<p>_meet by (metis inf_mono)

lemma aif_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close> 
    and hyps: 
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<ge> \<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>) (eg c1) \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<qq>) (eg c2))\<close>
proof- 
  have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) \<ge> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>)\<close> \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) \<ge> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<qq>)\<close>
    using prems \<r>\<p>_meet dual_order.trans by fastforce+
  then show ?thesis
    using hyps by (metis \<r>\<p>_join sup.mono)
qed

lemma aif_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close> 
    and hyps: 
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) c1 \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) c2) \<le> \<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>) (eg c1) \<squnion> pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<qq>) (eg c2))\<close>
proof- 
  have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>) \<le> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>)\<close> \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<pp>) \<le> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> \<qq>)\<close>
    using prems \<r>\<p>_meet dual_order.trans by fastforce+
  then show ?thesis
    using hyps by (metis \<r>\<p>_join sup.mono)
qed

lemma dif_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close> 
    and hyps: 
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<ge> \<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>) (eg c1) \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<qq>) (eg c2))\<close>
proof- 
  have \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) \<ge> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>)\<close> \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) \<ge> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> \<qq>)\<close>
    using prems by (metis (no_types, lifting) \<r>\<p>_join \<r>\<p>_mono mono_sup sup.idem sup.mono)+
  then show ?thesis
    using hyps by (metis \<r>\<p>_meet inf_mono)
qed

lemma dif_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close> 
    and hyps: 
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) c1 \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) c2) \<le> \<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>) (eg c1) \<sqinter> pt (\<^bold>[gi \<b>\<^bold>] \<squnion> \<qq>) (eg c2))\<close>
proof- 
  have \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>) \<le> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>)\<close> \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> \<pp>) \<le> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> \<qq>)\<close>
    using prems by (metis (no_types, lifting) \<r>\<p>_join \<r>\<p>_mono mono_sup sup.idem sup.mono)+
  then show ?thesis
    using hyps by (metis \<r>\<p>_meet inf_mono)
qed

lemma bif_geq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<ge> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<ge> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (gi \<b> \<^bold>? pt \<pp> c1 \<^bold>: pt \<pp> c2) \<ge> \<r>\<p> (gi \<b> \<^bold>? pt \<qq> (eg c1) \<^bold>: pt \<qq> (eg c2))\<close>
  using lattice_if_mono hyps .

lemma bif_leq_rinduct:
  assumes hyps: 
      \<open>\<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<qq> (eg c1))\<close>
      \<open>\<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<qq> (eg c2))\<close>
    shows \<open>\<r>\<p> (gi \<b> \<^bold>? pt \<pp> c1 \<^bold>: pt \<pp> c2) \<le> \<r>\<p> (gi \<b> \<^bold>? pt \<qq> (eg c1) \<^bold>: pt \<qq> (eg c2))\<close>
  using lattice_if_mono hyps .

lemma gfp_\<r>\<p>_mono:
  assumes reqs: \<open>mono (f :: ('s \<Rightarrow> 'x) \<Rightarrow> ('s \<Rightarrow> 'x))\<close> \<open>mono g\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (f \<pp>) \<le> \<r>\<p> (g \<qq>)\<close>
  shows \<open>\<r>\<p> (gfp f) \<le> \<r>\<p> (gfp g)\<close>
  using assms by (metis gfp_\<r>\<p>_greater gfp_unfold)

lemma lfp_\<r>\<p>_mono:
  assumes reqs: \<open>mono (f :: ('s \<Rightarrow> 'x) \<Rightarrow> ('s \<Rightarrow> 'x))\<close> \<open>mono g\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (f \<pp>) \<le> \<r>\<p> (g \<qq>)\<close>
  shows \<open>\<r>\<p> (lfp f) \<le> \<r>\<p> (lfp g)\<close> 
  using assms by (metis lfp_\<r>\<p>_lesser lfp_unfold)

lemma pbwhile_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<ge> \<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x (eg c) \<^bold>: \<qq>))\<close>
proof (induct rule: gfp_\<r>\<p>_mono[OF mono_b_iteratee[OF pt_mono] mono_b_iteratee[OF pt_mono]])
  case (1 \<qq>' \<pp>')
  with hyps have \<open>\<r>\<p> (pt \<pp>' c) \<ge> \<r>\<p> (pt \<qq>' (eg c))\<close> .
  then show ?case 
    using prems lattice_if_mono by blast
qed

lemma pbwhile_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<le> \<r>\<p> (gfp (\<lambda> x. gi \<b> \<^bold>? pt x (eg c) \<^bold>: \<qq>))\<close>
proof (induct rule: gfp_\<r>\<p>_mono[OF mono_b_iteratee[OF pt_mono] mono_b_iteratee[OF pt_mono]])
  case (1 \<pp>' \<qq>')
  with hyps have \<open>\<r>\<p> (pt \<pp>' c) \<le> \<r>\<p> (pt \<qq>' (eg c))\<close> .
  then show ?case 
    using prems lattice_if_mono by blast
qed

lemma tbwhile_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<ge> \<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x (eg c) \<^bold>: \<qq>))\<close>
proof (induct rule: lfp_\<r>\<p>_mono[OF mono_b_iteratee[OF pt_mono] mono_b_iteratee[OF pt_mono]])
  case (1 \<qq>' \<pp>')
  with hyps have \<open>\<r>\<p> (pt \<pp>' c) \<ge> \<r>\<p> (pt \<qq>' (eg c))\<close> .
  then show ?case 
    using prems lattice_if_mono by blast
qed

lemma tbwhile_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x c \<^bold>: \<pp>)) \<le> \<r>\<p> (lfp (\<lambda> x. gi \<b> \<^bold>? pt x (eg c) \<^bold>: \<qq>))\<close>
proof (induct rule: lfp_\<r>\<p>_mono[OF mono_b_iteratee[OF pt_mono] mono_b_iteratee[OF pt_mono]])
  case (1 \<pp>' \<qq>')
  with hyps have \<open>\<r>\<p> (pt \<pp>' c) \<le> \<r>\<p> (pt \<qq>' (eg c))\<close> .
  then show ?case 
    using prems lattice_if_mono by blast
qed

lemma pfwhile_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<ge> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) (eg c) \<sqinter> \<qq>))\<close>
proof-
  have \<open>\<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<ge> \<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) (eg c) \<sqinter> \<qq>))\<close>
  proof (induct rule: gfp_\<r>\<p>_mono[OF mono_pf_iteratee[OF pt_mono] mono_pf_iteratee[OF pt_mono]])
    case (1 \<qq>' \<pp>')
    then have \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>') \<ge> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>')\<close>
      by (metis \<r>\<p>_join \<r>\<p>_mono inf_sup_absorb mono_inf sup.mono)
    with hyps have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>') c) \<ge> \<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>') (eg c))\<close> .
    then show ?case 
      using prems by (metis \<r>\<p>_meet inf_mono)
  qed
  then show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_join le_iff_sup sup_idem sup_mono)
qed

lemma pfwhile_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<le> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<squnion> gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) (eg c) \<sqinter> \<qq>))\<close>
proof-
  have \<open>\<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) c \<sqinter> \<pp>)) \<le> \<r>\<p> (gfp (\<lambda> x. pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> x) (eg c) \<sqinter> \<qq>))\<close>
  proof (induct rule: gfp_\<r>\<p>_mono[OF mono_pf_iteratee[OF pt_mono] mono_pf_iteratee[OF pt_mono]])
    case (1 \<pp>' \<qq>')
    then have \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>') \<le> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>')\<close>
      by (metis \<r>\<p>_join \<r>\<p>_mono inf_sup_absorb mono_inf sup.mono)
    with hyps have \<open>\<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<pp>') c) \<le> \<r>\<p> (pt (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<squnion> \<qq>') (eg c))\<close> .
    then show ?case 
      using prems by (metis \<r>\<p>_meet inf_mono)
  qed
  then show ?thesis 
    by (metis (no_types, lifting) \<r>\<p>_join le_iff_sup sup_idem sup_mono)
qed

lemma tfwhile_geq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<ge> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<ge> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<ge> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<ge> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) (eg c) \<squnion> \<qq>))\<close>
proof-
  have *: \<open>\<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<ge> \<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) (eg c) \<squnion> \<qq>))\<close>
  proof (induct rule: lfp_\<r>\<p>_mono[OF mono_tf_iteratee[OF pt_mono] mono_tf_iteratee[OF pt_mono]])
    case (1 \<qq>' \<pp>')
    then have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>') \<ge> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>')\<close>
      using \<r>\<p>_meet dual_order.trans by fastforce
    with hyps have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>') c) \<ge> \<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>') (eg c))\<close> .
    then show ?case 
      using prems by (metis \<r>\<p>_join sup_mono)
  qed
  have **: \<open>\<r>\<p> \<^bold>[Not \<circ> gi \<b>\<^bold>] \<le> \<r>\<p> \<^bold>[Not \<circ> gi \<b>\<^bold>]\<close> using order_refl .
  show ?thesis 
    unfolding \<r>\<p>_meet using inf_mono[OF ** *] .
qed

lemma tfwhile_leq_rinduct:
  assumes prems: \<open>\<r>\<p> \<pp> \<le> \<r>\<p> \<qq>\<close>
    and hyps: \<open>\<And> \<pp> \<qq>. \<r>\<p> \<pp> \<le> \<r>\<p> \<qq> \<Longrightarrow> \<r>\<p> (pt \<pp> c) \<le> \<r>\<p> (pt \<qq> (eg c))\<close>
  shows \<open>\<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<le> \<r>\<p> (\<^bold>[Not \<circ> gi \<b>\<^bold>] \<sqinter> lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) (eg c) \<squnion> \<qq>))\<close>
proof-
  have *: \<open>\<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) c \<squnion> \<pp>)) \<le> \<r>\<p> (lfp (\<lambda> x. pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> x) (eg c) \<squnion> \<qq>))\<close>
  proof (induct rule: lfp_\<r>\<p>_mono[OF mono_tf_iteratee[OF pt_mono] mono_tf_iteratee[OF pt_mono]])
    case (1 \<pp>' \<qq>')
    then have \<open>\<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>') \<le> \<r>\<p> (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>')\<close>
      using \<r>\<p>_meet dual_order.trans by fastforce
    with hyps have \<open>\<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<pp>') c) \<le> \<r>\<p> (pt (\<^bold>[gi \<b>\<^bold>] \<sqinter> \<qq>') (eg c))\<close> .
    then show ?case 
      using prems by (metis \<r>\<p>_join sup_mono)
  qed
  have **: \<open>\<r>\<p> \<^bold>[Not \<circ> gi \<b>\<^bold>] \<le> \<r>\<p> \<^bold>[Not \<circ> gi \<b>\<^bold>]\<close> using order_refl .
  show ?thesis 
    unfolding \<r>\<p>_meet using inf_mono[OF ** *] .
qed

end

locale \<r>\<p>_pt_full = \<r>\<p>_pt_mono +
  assumes pt_conjunctive: \<open>pt \<pp> c \<sqinter> pt \<qq> c = pt (\<pp> \<sqinter> \<qq>) c\<close>
  assumes pt_disjunctive: \<open>pt \<pp> c \<squnion> pt \<qq> c = pt (\<pp> \<squnion> \<qq>) c\<close>

(*
lemma fseq_leq_rinduct:
  assumes hyps: \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c1) \<le> \<r>\<p> (pt \<pp> (erase_ghost c1))\<close> \<open>\<And> \<pp>. \<r>\<p> (pt \<pp> c2) \<le> \<r>\<p> (pt \<pp> (erase_ghost c2))\<close>
  shows \<open>\<r>\<p> (pt (pt \<pp> c1) c2) \<le> \<r>\<p> (pt (pt \<pp> (erase_ghost c1)) (erase_ghost c2))\<close>
  using reqs hyps 

above doesn't work, consider example below

with ghost code  | without ghost code
x = 1, y = 1     | x = 1, y = 1
ghost y := 2
x = 1, y = 2     | x = 1, y = 1
if y = 2
  var x
x = any, y = 2   | x = 1, y = 1
*)




section \<open>general conservative checks\<close>
(*
primrec g_check where
  \<open>g_check gc (Command c) = gc c\<close> |
  \<open>g_check gc Skip = True\<close> |
  \<open>g_check gc (prog1\<^bold>; prog2) = (g_check gc prog1 \<and> g_check gc prog2)\<close> |
  \<open>g_check gc (prog1 \<^bold>[\<^bold>] prog2) = (g_check gc prog1 \<and> g_check gc prog2)\<close> |
  \<open>g_check gc (If \<b> prog1 prog2) = (g_check gc prog1 \<and> g_check gc prog2)\<close> |
  \<open>g_check gc (While \<b> prog) = g_check gc prog\<close> |
  \<open>g_check gc (Ghost prog) = g_check gc prog\<close>

primrec r_check where
  \<open>r_check gi \<r> rc gc (Command c) = rc c\<close> |
  \<open>r_check gi \<r> rc gc Skip = True\<close> |
  \<open>r_check gi \<r> rc gc (prog1\<^bold>; prog2) = (r_check gi \<r> rc gc prog1 \<and> r_check gi \<r> rc gc prog2)\<close> |
  \<open>r_check gi \<r> rc gc (prog1 \<^bold>[\<^bold>] prog2) = (r_check gi \<r> rc gc prog1 \<and> r_check gi \<r> rc gc prog2)\<close> |
  \<open>r_check gi \<r> rc gc (If \<b> prog1 prog2) = (\<r> \<^bold>[gi \<b>\<^bold>] \<and> r_check gi \<r> rc gc prog1 \<and> r_check gi \<r> rc gc prog2)\<close> |
  \<open>r_check gi \<r> rc gc (While \<b> prog) = (\<r> \<^bold>[gi \<b>\<^bold>] \<and> r_check gi \<r> rc gc prog)\<close> |
  \<open>r_check gi \<r> rc gc (Ghost prog) = g_check gc prog\<close>
*)



end
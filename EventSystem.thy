theory EventSystem
  imports EventSpecWhile
begin

subsection \<open>Event systems\<close>

text \<open>An event system is characterized by a partial mapping from
  events to their handlers.\<close>
type_synonym ('e,'s) event_system =
  "'e \<Rightarrow> ('s,'e,unit) event_monad option"

text \<open>Definition of reachability for event system:

  For a single event, if it is handled, execute it by invoking the
  corresponding handler, then recursively executing the list of output
  events. Otherwise simply send it to the output.

  For a list of events, recursively execute each event in sequence.
\<close>
inductive reachable :: "('e,'s) event_system \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's \<times> 'e list \<Rightarrow> bool"
  and
  reachable_list :: "('e,'s) event_system \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 's \<times> 'e list \<Rightarrow> bool" where
  reachable_None: "sys e = None \<Longrightarrow> reachable sys e s (s, [e])"
| reachable_Some: "\<lbrakk>sys e = Some p; (r, s', es) \<in> fst (p s); \<not>snd (p s);
                    reachable_list sys es s' (s'', es')\<rbrakk> \<Longrightarrow> reachable sys e s (s'', es')"

| reachable_list_Nil: "reachable_list sys [] s (s, [])"
| reachable_list_Cons: "reachable sys e s (s', es1) \<Longrightarrow> reachable_list sys es s' (s'', es2) \<Longrightarrow>
                        reachable_list sys (e # es) s (s'', es1 @ es2)"

text \<open>We only consider the scenario of non-termination due to failure
  when handling a single event.
\<close>
inductive terminates :: "('e,'s) event_system \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> bool"
  and
  terminates_list :: "('e,'s) event_system \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> bool" where
  terminates_None: "sys e = None \<Longrightarrow> terminates sys e s"
| terminates_Some: "sys e = Some p \<Longrightarrow> \<not>snd (p s) \<Longrightarrow> \<forall>(r,s',es')\<in>fst (p s). terminates_list sys es' s' \<Longrightarrow> terminates sys e s"
| terminates_list_Nil: "terminates_list sys [] s"
| terminates_list_Cons: "terminates sys e s \<Longrightarrow> \<forall>s' es'. reachable sys e s (s', es') \<longrightarrow> terminates_list sys es s' \<Longrightarrow>
                         terminates_list sys (e # es) s"

inductive_cases reachable_cases: "reachable sys e s (s', es)"
inductive_cases reachable_list_Nil_cases: "reachable_list sys [] s (s', es)"
inductive_cases reachable_list_Cons_cases: "reachable_list sys (e # es) s (s', es1)"

subsection \<open>Product systems\<close>

fun apply_fst_st :: "'t \<Rightarrow> 'a \<times> 's \<times> 'e list \<Rightarrow> 'a \<times> ('s \<times> 't) \<times> 'e list" where
  "apply_fst_st t (r, s, es) = (r, (s, t), es)"

fun apply_fst :: "('s,'e,'a) event_monad \<Rightarrow> ('s\<times>'t,'e,'a) event_monad" where
  "apply_fst c (s, t) = (let (rs, f) = c s in ((apply_fst_st t) ` rs, f))"

fun apply_snd_st :: "'s \<Rightarrow> 'a \<times> 't \<times> 'e list \<Rightarrow> 'a \<times> ('s \<times> 't) \<times> 'e list" where
  "apply_snd_st s (r, t, es) = (r, (s, t), es)"

fun apply_snd :: "('t,'e,'a) event_monad \<Rightarrow> ('s\<times>'t,'e,'a) event_monad" where
  "apply_snd c (s, t) = (let (rs, f) = c t in ((apply_snd_st s) ` rs, f))"

subsection \<open>Validity for systems\<close>

definition sValid ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool" where
  "sValid sys P e Q = (\<forall>s es1 s' es2. P s es1 \<longrightarrow> reachable sys e s (s', es2) \<longrightarrow> Q s' (es1 @ es2))"

definition sNo_fail ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> bool" where
  "sNo_fail sys P e = (\<forall>s es. P s es \<longrightarrow> terminates sys e s)"

definition sValidNF ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool" where
  "sValidNF sys P e Q = (sValid sys P e Q \<and> sNo_fail sys P e)"

definition sValid_list ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool" where
  "sValid_list sys P es Q = (\<forall>s es1 s' es2. P s es1 \<longrightarrow> reachable_list sys es s (s', es2) \<longrightarrow> Q s' (es1 @ es2))"

definition sNo_fail_list ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> bool" where
  "sNo_fail_list sys P es = (\<forall>s es'. P s es' \<longrightarrow> terminates_list sys es s)"

definition sValidNF_list ::
  "('e,'s) event_system \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> ('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool" where
  "sValidNF_list sys P es Q = (sValid_list sys P es Q \<and> sNo_fail_list sys P es)"

theorem sValid_weaken_pre:
  "(\<And>s t. P' s t \<Longrightarrow> P s t) \<Longrightarrow> sValid sys P e Q \<Longrightarrow> sValid sys P' e Q"
  unfolding sValid_def by fastforce

theorem sValidNF_weaken_pre:
  "(\<And>s t. P' s t \<Longrightarrow> P s t) \<Longrightarrow> sValidNF sys P e Q \<Longrightarrow> sValidNF sys P' e Q"
  unfolding sValidNF_def sValid_def sNo_fail_def by fastforce

theorem sValid_conj_pre:
  "sValid sys (\<lambda>s t. P \<and> Q s t) e R \<longleftrightarrow> (P \<longrightarrow> sValid sys Q e R)"
  unfolding sValid_def by auto

theorem sValidNF_conj_pre:
  "sValidNF sys (\<lambda>s t. P \<and> Q s t) e R \<longleftrightarrow> (P \<longrightarrow> sValidNF sys Q e R)"
  unfolding sValidNF_def sValid_def sNo_fail_def by auto

theorem sValid_strengthen_post:
  "(\<And>s t. Q s t \<Longrightarrow> Q' s t) \<Longrightarrow> sValid sys P e Q \<Longrightarrow> sValid sys P e Q'"
  unfolding sValid_def by fastforce

theorem sValidNF_strengthen_post:
  "(\<And>s t. Q s t \<Longrightarrow> Q' s t) \<Longrightarrow> sValidNF sys P e Q \<Longrightarrow> sValidNF sys P e Q'"
  unfolding sValidNF_def sValid_def sNo_fail_def by fastforce

theorem sValid_list_weaken_pre:
  "(\<And>s t. P' s t \<Longrightarrow> P s t) \<Longrightarrow> sValid_list sys P es Q \<Longrightarrow> sValid_list sys P' es Q"
  unfolding sValid_list_def by fastforce

theorem sValidNF_list_weaken_pre:
  "(\<And>s t. P' s t \<Longrightarrow> P s t) \<Longrightarrow> sValidNF_list sys P es Q \<Longrightarrow> sValidNF_list sys P' es Q"
  unfolding sValidNF_list_def sValid_list_def sNo_fail_list_def by fastforce

theorem sValid_list_strengthen_post:
  "(\<And>s t. Q s t \<Longrightarrow> Q' s t) \<Longrightarrow> sValid_list sys P es Q \<Longrightarrow> sValid_list sys P es Q'"
  unfolding sValid_list_def by fastforce

theorem sValidNF_list_strengthen_post:
  "(\<And>s t. Q s t \<Longrightarrow> Q' s t) \<Longrightarrow> sValidNF_list sys P es Q \<Longrightarrow> sValidNF_list sys P es Q'"
  unfolding sValidNF_list_def sValid_list_def sNo_fail_list_def by fastforce

lemma sValid_exists_pre:
  "sValid sys (\<lambda>s t. (\<exists>x. P x s t) \<and> R s t) e Q \<longleftrightarrow> (\<forall>x. sValid sys (\<lambda>s t. P x s t \<and> R s t) e Q)"
  unfolding sValid_def by auto

lemma sValidNF_exists_pre:
  "sValidNF sys (\<lambda>s t. (\<exists>x. P x s t) \<and> R s t) e Q \<longleftrightarrow> (\<forall>x. sValidNF sys (\<lambda>s t. P x s t \<and> R s t) e Q)"
  unfolding sValidNF_def sValid_def sNo_fail_def by fastforce

lemma sValid_exists_pre2:
  "sValid sys (\<lambda>s t. \<exists>x. P x s t) e Q \<longleftrightarrow> (\<forall>x. sValid sys (\<lambda>s t. P x s t) e Q)"
  unfolding sValid_def by auto

lemma sValidNF_exists_pre2:
  "sValidNF sys (\<lambda>s t. \<exists>x. P x s t) e Q \<longleftrightarrow> (\<forall>x. sValidNF sys (\<lambda>s t. P x s t) e Q)"
  unfolding sValidNF_def sValid_def sNo_fail_def by fastforce

theorem sValid_frame:
  assumes "sValid sys (\<lambda>s t. P s \<and> nil\<^sub>e t) e (\<lambda>s t. P' s \<and> Q s t)"
  shows "sValid sys (\<lambda>s t. P s \<and> R t) e (\<lambda>s t. P' s \<and> (R ^\<^sub>e Q s) t)"
  using assms unfolding sValid_def
  by (metis append_self_conv2 chop_event_def nil_event_def)

theorem sValid_frame_nil:
  assumes "sValid sys (\<lambda>s t. P s \<and> nil\<^sub>e t) e (\<lambda>s t. P' s \<and> nil\<^sub>e t)"
  shows "sValid sys (\<lambda>s t. P s \<and> R t) e (\<lambda>s t. P' s \<and> R t)"
  using assms unfolding sValid_def
  by (metis append_Nil append_Nil2 nil_event_def)

theorem sValidNF_frame:
  assumes "sValidNF sys (\<lambda>s t. P s \<and> nil\<^sub>e t) e (\<lambda>s t. P' s \<and> Q s t)"
  shows "sValidNF sys (\<lambda>s t. P s \<and> R t) e (\<lambda>s t. P' s \<and> (R ^\<^sub>e Q s) t)"
  using assms unfolding sValidNF_def sValid_def sNo_fail_def
  by (metis append_self_conv2 chop_event_def nil_event_def)

theorem sValidNF_frame_nil:
  assumes "sValidNF sys (\<lambda>s t. P s \<and> nil\<^sub>e t) e (\<lambda>s t. P' s \<and> nil\<^sub>e t)"
  shows "sValidNF sys (\<lambda>s t. P s \<and> R t) e (\<lambda>s t. P' s \<and> R t)"
  using assms unfolding sValidNF_def sValid_def sNo_fail_def
  by (metis append_Nil append_Nil2 nil_event_def)

theorem sValid_list_frame:
  assumes "sValid_list sys (\<lambda>s t. P s \<and> nil\<^sub>e t) es (\<lambda>s t. P' s \<and> Q s t)"
  shows "sValid_list sys (\<lambda>s t. P s \<and> R t) es (\<lambda>s t. P' s \<and> (R ^\<^sub>e Q s) t)"
  using assms unfolding sValid_list_def chop_event_def
  by (metis (full_types) eq_Nil_appendI nil_event_def)

theorem sValidNF_list_frame:
  assumes "sValidNF_list sys (\<lambda>s t. P s \<and> nil\<^sub>e t) es (\<lambda>s t. P' s \<and> Q s t)"
  shows "sValidNF_list sys (\<lambda>s t. P s \<and> R t) es (\<lambda>s t. P' s \<and> (R ^\<^sub>e Q s) t)"
  unfolding sValidNF_list_def sValid_list_def sNo_fail_list_def
  apply (rule conjI)
   apply auto
  apply (metis (no_types, lifting) assms nil_event_def sValidNF_list_def sValid_list_def)
  subgoal for s es s' es' apply (simp add: chop_event_def)
    using assms unfolding sValidNF_list_def sValid_list_def
    by (metis (full_types) nil_event_def self_append_conv2)
  subgoal for s es'
    using assms unfolding sValidNF_list_def sNo_fail_list_def
    by (simp add: nil_event_def)
  done

theorem sValid_None:
  assumes "sys e = None"
  shows "sValid sys (\<lambda>s t. P s (t @ [e])) e P"
  unfolding sValid_def apply auto
  apply (elim reachable_cases)
  using assms by auto

theorem sValidNF_None:
  assumes "sys e = None"
  shows "sValidNF sys (\<lambda>s t. P s (t @ [e])) e P"
  unfolding sValidNF_def sValid_def sNo_fail_def apply auto
  apply (elim reachable_cases)
  using assms apply auto
  apply (rule terminates_None) by auto

theorem sValid_None_sp:
  assumes "sys e = None"
  shows "sValid sys (\<lambda>s t. s = s0 \<and> nil\<^sub>e t) e (\<lambda>s t. s = s0 \<and> t = [e])"
  apply (rule sValid_weaken_pre)
   prefer 2 apply (rule sValid_None)
  apply (rule assms) by (auto simp add: nil_event_def)

theorem sValidNF_None_sp:
  assumes "sys e = None"
  shows "sValidNF sys (\<lambda>s t. s = s0 \<and> nil\<^sub>e t) e (\<lambda>s t. s = s0 \<and> t = [e])"
  apply (rule sValidNF_weaken_pre)
   prefer 2 apply (rule sValidNF_None)
  apply (rule assms) by (auto simp add: nil_event_def)

theorem sValid_Some:
  assumes "sys e = Some c"
    and "\<lbrace> \<lambda>s es. P s \<and> nil\<^sub>e es \<rbrace> c \<lbrace> \<lambda>_ s es. Q s es \<rbrace>"
    and "\<And>s es. Q s es \<Longrightarrow> sValid_list sys (\<lambda>s' es'. s' = s \<and> nil\<^sub>e es') es R"
  shows "sValid sys (\<lambda>s es. P s \<and> nil\<^sub>e es) e R"
proof -
  have a: "R s2 es2"
    if "P s" "((), s1, es) \<in> fst (c s)" "reachable_list sys es s1 (s2, es2)" for s s1 s2 es es2
  proof -
    have "Q s1 es"
      using that(1,2) assms(2) unfolding valid_def nil_event_def by auto
    then have "sValid_list sys (\<lambda>s' es'. s' = s1 \<and> nil\<^sub>e es') es R"
      using assms(3) by auto
    then show ?thesis
      unfolding sValid_list_def nil_event_def using that(3) by auto
  qed
  show ?thesis
    unfolding sValid_def apply auto
    apply (elim reachable_cases)
    apply (auto simp add: assms(1))
    using a unfolding nil_event_def by auto
qed

theorem sValidNF_Some:
  assumes "sys e = Some c"
    and "\<lbrace> \<lambda>s es. P s \<and> nil\<^sub>e es \<rbrace> c \<lbrace> \<lambda>_ s es. Q s es \<rbrace>!"
    and "\<And>s es. Q s es \<Longrightarrow> sValidNF_list sys (\<lambda>s' es'. s' = s \<and> nil\<^sub>e es') es R"
  shows "sValidNF sys (\<lambda>s es. P s \<and> nil\<^sub>e es) e R"
proof -
  have a1: "\<lbrace> \<lambda>s es. P s \<and> nil\<^sub>e es \<rbrace> c \<lbrace> \<lambda>_ s es. Q s es \<rbrace>" "no_fail (\<lambda>s es. P s \<and> nil\<^sub>e es) c"
    using assms(2) unfolding validNF_def by auto
  have a2: "sValid_list sys (\<lambda>s' es'. s' = s \<and> nil\<^sub>e es') es R"
           "sNo_fail_list sys (\<lambda>s' es'. s' = s \<and> nil\<^sub>e es') es" if "Q s es" for s es
    using assms(3) that unfolding sValidNF_list_def by auto
  have a3: "sValid sys (\<lambda>s es. P s \<and> nil\<^sub>e es) e R"
    apply (rule sValid_Some)
      apply (rule assms(1)) apply (rule a1(1)) by (rule a2(1))
  have a4: "terminates_list sys es s'"
    if "P s" "nil\<^sub>e (es'::'b list)" "((), s', es) \<in> fst (c s)" for s es' s' es
  proof -
    have "Q s' es"
      using that a1(1) unfolding valid_def
      by (metis append_self_conv2 case_prodD nil_event_def)
    then have "sNo_fail_list sys (\<lambda>s es'. s = s' \<and> nil\<^sub>e es') es"
      using a2(2) by auto
    then show ?thesis
      unfolding sNo_fail_list_def
      using that(2) by auto
  qed
  show ?thesis
    unfolding sValidNF_def sNo_fail_def
    apply (auto simp add: a3)
    apply (rule terminates_Some)
      apply (rule assms(1))
    using a1(2) unfolding no_fail_def apply auto[1]
    using a4 by auto
qed

theorem sValid_list_null:
  "sValid_list sys P [] P"
  unfolding sValid_list_def apply auto
  apply (elim reachable_list_Nil_cases)
  by auto

theorem sValidNF_list_null:
  "sValidNF_list sys P [] P"
  unfolding sValidNF_list_def sValid_list_def sNo_fail_list_def apply auto
   apply (elim reachable_list_Nil_cases) apply auto
  by (rule terminates_list_Nil)

theorem sValid_list_cons:
  assumes "sValid sys P e Q"
    and "sValid_list sys Q es R"
  shows "sValid_list sys P (e # es) R"
  using assms unfolding sValid_def sValid_list_def apply auto
  apply (elim reachable_list_Cons_cases) by fastforce

theorem sValidNF_list_cons:
  assumes "sValidNF sys P e Q"
    and "sValidNF_list sys Q es R"
  shows "sValidNF_list sys P (e # es) R"
  using assms unfolding sValidNF_def sValid_def sValidNF_list_def sValid_list_def apply auto
   apply (elim reachable_list_Cons_cases) apply fastforce
  unfolding sNo_fail_list_def apply auto
  apply (rule terminates_list_Cons)
   apply (meson sNo_fail_def)
  by blast

theorem sValid_list_single:
  assumes "sValid sys P e Q"
  shows "sValid_list sys P [e] Q"
  apply (rule sValid_list_cons)
  apply (rule assms) by (rule sValid_list_null)

theorem sValidNF_list_single:
  assumes "sValidNF sys P e Q"
  shows "sValidNF_list sys P [e] Q"
  apply (rule sValidNF_list_cons)
  apply (rule assms) by (rule sValidNF_list_null)

fun event_all_None :: "('e,'s) event_system \<Rightarrow> 'e list \<Rightarrow> bool" where
  "event_all_None sys [] = True"
| "event_all_None sys (e # es) = (sys e = None \<and> event_all_None sys es)"

theorem sValidNF_list_all_None:
  "event_all_None sys es \<Longrightarrow> sValidNF_list sys (\<lambda>s t. P s (t @ es)) es P"
proof (induction es)
  case Nil
  then show ?case
    unfolding sValidNF_list_def
    using sValidNF_list_def sValidNF_list_null by fastforce
next
  case (Cons e es)
  have a1: "sys e = None" "event_all_None sys es"
    using Cons(2) by auto
  have a2: "sValidNF_list sys (\<lambda>s t. P s (t @ es)) es P"
    using Cons(1) a1 by auto
  show ?case
    apply (rule sValidNF_list_cons)
    prefer 2 apply (rule a2)
    apply (rule sValidNF_weaken_pre)
     prefer 2 apply (rule sValidNF_None)
    apply (rule a1(1)) by auto
qed

theorem sValid_list_all_None:
  "event_all_None sys es \<Longrightarrow> sValid_list sys (\<lambda>s t. P s (t @ es)) es P"
  using sValidNF_list_all_None unfolding sValidNF_list_def by auto

subsection \<open>Validity for product of systems\<close>

lemma valid_apply_fst:
  assumes "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>"
  shows "\<lbrace> \<lambda>p es. P (fst p) es \<and> R (snd p) \<rbrace>
           apply_fst c
         \<lbrace> \<lambda>r p es. Q r (fst p) es \<and> R (snd p) \<rbrace>"
  unfolding valid_def apply auto
  subgoal for sl sr es r sl' sr' es' 
    apply (cases "c sl") apply auto
    using assms(1) unfolding valid_def by fastforce
  subgoal for sl sr es r sl' sr' es'
    apply (cases "c sl") by auto
  done

lemma validNF_apply_fst:
  assumes "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>!"
  shows "\<lbrace> \<lambda>p es. P (fst p) es \<and> R (snd p) \<rbrace>
           apply_fst c
         \<lbrace> \<lambda>r p es. Q r (fst p) es \<and> R (snd p) \<rbrace>!"
proof -
  have a1: "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>"
           "no_fail (\<lambda>s es. P s es) c"
    using assms(1) unfolding validNF_def by auto
  have a2: "no_fail (\<lambda>p es. P (fst p) es \<and> R (snd p)) (apply_fst c)"
    apply (auto simp add: no_fail_def)
    subgoal for sl sr es
      apply (cases "c sl") apply auto
      using a1(2) unfolding no_fail_def by fastforce
    done
  show ?thesis
    unfolding validNF_def apply auto
     apply (rule valid_apply_fst) apply (rule a1)
    using a2 by auto
qed

lemma valid_apply_snd:
  assumes "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>"
  shows "\<lbrace> \<lambda>p es. R (fst p) \<and> P (snd p) es \<rbrace>
           apply_snd c
         \<lbrace> \<lambda>r p es. R (fst p) \<and> Q r (snd p) es \<rbrace>"
  unfolding valid_def apply auto
  subgoal for sl sr es r sl' sr' es' 
    apply (cases "c sr") by auto
  subgoal for sl sr es r sl' sr' es'
    apply (cases "c sr") apply auto
    using assms(1) unfolding valid_def by fastforce
  done

lemma validNF_apply_snd:
  assumes "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>!"
  shows "\<lbrace> \<lambda>p es. R (fst p) \<and> P (snd p) es \<rbrace>
           apply_snd c
         \<lbrace> \<lambda>r p es. R (fst p) \<and> Q r (snd p) es \<rbrace>!"
proof -
  have a1: "\<lbrace> \<lambda>s es. P s es \<rbrace> c \<lbrace> \<lambda>r s es. Q r s es \<rbrace>"
           "no_fail (\<lambda>s es. P s es) c"
    using assms(1) unfolding validNF_def by auto
  have a2: "no_fail (\<lambda>p es. R (fst p) \<and> P (snd p) es) (apply_snd c)"
    apply (auto simp add: no_fail_def)
    subgoal for sl sr es
      apply (cases "c sr") apply auto
      using a1(2) unfolding no_fail_def by fastforce
    done
  show ?thesis
    unfolding validNF_def apply auto
     apply (rule valid_apply_snd) apply (rule a1)
    using a2 by auto
qed

subsection \<open>Validity for lists of systems\<close>

fun apply_idx_st :: "'s list \<Rightarrow> nat \<Rightarrow> 'a \<times> 's \<times> 'e list \<Rightarrow> 'a \<times> 's list \<times> 'e list" where
  "apply_idx_st slist i (r, s, es) = (r, slist[i := s], es)"

fun apply_idx :: "('s,'e,'a) event_monad \<Rightarrow> nat \<Rightarrow> ('s list,'e,'a) event_monad" where
  "apply_idx c i slist = (let (rs, f) = c (slist ! i) in ((apply_idx_st slist i) ` rs, f))"

lemma valid_apply_idx:
  assumes
    "\<And>s0. \<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
       c
     \<lbrace> \<lambda>_ s es. s = f s0 \<and> es = g s0 \<rbrace>"
  shows
    "\<lbrace> \<lambda>s es. s = slist \<and> es = [] \<rbrace>
       apply_idx c i
     \<lbrace> \<lambda>_ s es. s = slist[i := f (slist ! i)] \<and> es = g (slist ! i) \<rbrace>"
  unfolding valid_def apply auto
  subgoal for r s es
    apply (cases "c (slist ! i)")
    apply auto using assms(1) unfolding valid_def
    by (metis (mono_tags, lifting) case_prodD fst_conv)
  subgoal for r s es
    apply (cases "c (slist ! i)")
    apply auto using assms(1) unfolding valid_def by fastforce
  done

lemma validNF_apply_idx:
  assumes
    "\<And>s0. \<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
       c
     \<lbrace> \<lambda>_ s es. s = f s0 \<and> es = g s0 \<rbrace>!"
  shows
    "\<lbrace> \<lambda>s es. s = slist \<and> es = [] \<rbrace>
       apply_idx c i
     \<lbrace> \<lambda>_ s es. s = slist[i := f (slist ! i)] \<and> es = g (slist ! i) \<rbrace>!"
  unfolding validNF_def apply auto
  subgoal
    apply (rule valid_apply_idx)
    using assms unfolding validNF_def by auto
  subgoal
    apply (auto simp add: no_fail_def)
    apply (cases "c (slist ! i)")
    apply auto
    using assms unfolding validNF_def no_fail_def
    by (metis snd_conv)
  done

lemma valid_apply_idx2:
  assumes "\<And>i. i < N \<Longrightarrow> \<lbrace> \<lambda>s es. P i s \<and> nil\<^sub>e es \<rbrace> c \<lbrace> \<lambda>r s es. Q i r s es \<rbrace>"
    and "j < N"
  shows "\<lbrace> \<lambda>s es. length s = N \<and> (\<forall>i. i < N \<longrightarrow> P i (s ! i)) \<and> nil\<^sub>e es \<rbrace>
           apply_idx c j
         \<lbrace> \<lambda>r s es. length s = N \<and> (\<forall>i. i < N \<longrightarrow> i \<noteq> j \<longrightarrow> P i (s ! i)) \<and> Q j r (s ! j) es \<rbrace>"
  unfolding valid_def apply clarify
  subgoal for s es r s' es'
    apply (cases "c (s ! j)")
    subgoal premises pre for a b
    proof -
      from assms(1)[of j, unfolded valid_def]
      have a: "\<forall>(r, s', es2)\<in>fst (c (s ! j)). Q j r s' (es @ es2)"
        using pre assms(2) by fastforce
      show ?thesis
        using pre a assms(2) by auto
    qed
    done
  done

lemma validNF_apply_idx2:
  assumes "\<And>i. i < N \<Longrightarrow> \<lbrace> \<lambda>s es. P i s \<and> nil\<^sub>e es \<rbrace> c \<lbrace> \<lambda>r s es. Q i r s es \<rbrace>!"
    and "j < N"
  shows "\<lbrace> \<lambda>s es. length s = N \<and> (\<forall>i. i < N \<longrightarrow> P i (s ! i)) \<and> nil\<^sub>e es \<rbrace>
           apply_idx c j
         \<lbrace> \<lambda>r s es. length s = N \<and> (\<forall>i. i < N \<longrightarrow> i \<noteq> j \<longrightarrow> P i (s ! i)) \<and> Q j r (s ! j) es \<rbrace>!"
  unfolding validNF_def apply (rule conjI)
  subgoal
    apply (rule valid_apply_idx2)
    using assms unfolding validNF_def by auto
  subgoal
    apply (auto simp add: no_fail_def)
    subgoal for s es
      apply (cases "c (s ! j)")
      apply auto
      using assms unfolding validNF_def no_fail_def
      by (metis snd_conv)
    done
  done

subsection \<open>Valid and ValidNF for append\<close>

lemma reachable_list_append_cases:
  "reachable_list sys (es1 @ es2) s (s'', rs) \<Longrightarrow>
   (\<And>s' rs1 rs2. rs = rs1 @ rs2 \<Longrightarrow> reachable_list sys es1 s (s', rs1) \<Longrightarrow>
      reachable_list sys es2 s' (s'', rs2) \<Longrightarrow> P) \<Longrightarrow> P"
proof (induction es1 arbitrary: es2 s rs P)
  case Nil
  show ?case
    apply (rule Nil(2)[of "[]" rs s])
    apply auto[1]
     apply (rule reachable_list_Nil)
    using Nil(1) by auto
next
  case (Cons e es1')
  have a: "reachable_list sys (e # es1' @ es2) s (s'', rs)"
    using Cons(2) by auto
  obtain s' es1'' es2'' where b: "rs = es1'' @ es2''" "reachable sys e s (s', es1'')"
    "reachable_list sys (es1' @ es2) s' (s'', es2'')"
    using reachable_list_Cons_cases[OF a] by metis
  obtain s1' rs1' rs2' where c: "es2'' = rs1' @ rs2'" "reachable_list sys es1' s' (s1', rs1')"
    "reachable_list sys es2 s1' (s'', rs2')"
    using Cons(1)[OF b(3)] by metis
  have d: "rs = (es1'' @ rs1') @ rs2'"
    using b(1) c(1) by auto
  have e: "reachable_list sys (e # es1') s (s1', es1'' @ rs1')"
    by (rule reachable_list_Cons[OF b(2) c(2)])
  show ?case
    by (rule Cons(3)[OF d e c(3)])
qed

theorem sValid_list_append:
  assumes "sValid_list sys P es1 Q"
    and "sValid_list sys Q es2 R"
  shows "sValid_list sys P (es1 @ es2) R"
  unfolding sValid_list_def
  apply auto subgoal for s es s' es'
    apply (elim reachable_list_append_cases)
    using assms unfolding sValid_list_def by fastforce
  done

inductive_cases terminates_list_Cons_cases: "terminates_list sys (e # es) s"

lemma terminates_list_append:
  "terminates_list sys es1 s \<Longrightarrow>
   \<forall>s' es'. reachable_list sys es1 s (s', es') \<longrightarrow> terminates_list sys es2 s' \<Longrightarrow>
   terminates_list sys (es1 @ es2) s"
proof (induction es1 arbitrary: es2 s)
  case Nil
  have a: "reachable_list sys [] s (s, [])"
    by (rule reachable_list_Nil)
  show ?case
    using a Nil(2) by auto
next
  case (Cons e es1)
  have a: "terminates sys e s \<and> (\<forall>s'. (\<exists>es'. reachable sys e s (s', es')) \<longrightarrow> terminates_list sys es1 s')"
    using terminates_list_Cons_cases[OF Cons(2)] by blast
  show ?case
    apply simp
    apply (rule terminates_list_Cons)
    using a apply auto[1]
    apply clarify subgoal premises pre for s' es'
      apply (rule Cons(1))
      using a pre apply auto[1]
      apply clarify subgoal premises pre2 for s'' es''
        using reachable_list_Cons[OF pre pre2] Cons(3) by auto
      done
    done
qed

theorem sValidNF_list_append:
  assumes "sValidNF_list sys P es1 Q"
    and "sValidNF_list sys Q es2 R"
  shows "sValidNF_list sys P (es1 @ es2) R"
  unfolding sValidNF_list_def apply auto
  subgoal using assms unfolding sValidNF_list_def
    using sValid_list_append by auto
  subgoal unfolding sNo_fail_list_def
    using assms unfolding sValidNF_list_def sNo_fail_list_def apply auto
    apply (rule terminates_list_append) apply auto
    by (meson sValid_list_def)
  done

end

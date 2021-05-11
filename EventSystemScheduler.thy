theory EventSystemScheduler
  imports EventSystemWatchdog
begin

text \<open>This file contains verification of a simplified scheduler that
  does not allow switching between time tables.

  First, we verify the implementation of the scheduler, then combine
  with the implementation of the watchdog using the event system.
\<close>

subsection \<open>Abstract scheduler\<close>

record astate_scheduler =
  as_ttbl :: time_table
  window_id :: nat

definition next_partition :: "astate_scheduler \<Rightarrow> partition" where
  "next_partition st = fst (as_ttbl st ! ((window_id st + 1) mod length (as_ttbl st)))"

definition next_watchdog_pos :: "astate_scheduler \<Rightarrow> nat" where
  "next_watchdog_pos st = snd (as_ttbl st ! ((window_id st + 1) mod length (as_ttbl st)))"

definition spec_dispatch :: "astate_scheduler \<Rightarrow> astate_scheduler \<times> event list" where
  "spec_dispatch st =
    (\<lparr>as_ttbl = as_ttbl st,
      window_id = (window_id st + 1) mod length (as_ttbl st)\<rparr>,
     [PARTITION (next_partition st),
      WATCHDOG_ADD (0, next_watchdog_pos st)])"

subsection \<open>Concrete implementation of scheduler\<close>

record cstate_scheduler =
  cs_ttbl :: time_table
  window_time :: nat
  cur_window :: nat
  cur_frame_time :: nat

definition get_partition :: "nat \<Rightarrow> (cstate_scheduler, event, nat) event_monad" where
  "get_partition wid = get \<bind> (\<lambda>st. return (fst ((cs_ttbl st) ! wid)))"

definition get_duration :: "nat \<Rightarrow> (cstate_scheduler, event, nat) event_monad" where
  "get_duration wid = get \<bind> (\<lambda>st. return (snd ((cs_ttbl st) ! wid)))"

definition get_total_frame_time :: "(cstate_scheduler, event, nat) event_monad" where
  "get_total_frame_time = get \<bind> (\<lambda>st. return (frame_length (cs_ttbl st)))"

definition get_window_time :: "(cstate_scheduler, event, nat) event_monad" where
  "get_window_time = get \<bind> (\<lambda>st. return (window_time st))"

definition get_cur_window :: "(cstate_scheduler, event, nat) event_monad" where
  "get_cur_window = get \<bind> (\<lambda>st. return (cur_window st))"

definition get_cur_frame_time :: "(cstate_scheduler, event, nat) event_monad" where
  "get_cur_frame_time = get \<bind> (\<lambda>st. return (cur_frame_time st))"

definition set_window_time :: "nat \<Rightarrow> (cstate_scheduler, event, unit) event_monad" where
  "set_window_time t = modify (window_time_update (\<lambda>_. t))"

definition set_cur_window :: "nat \<Rightarrow> (cstate_scheduler, event, unit) event_monad" where
  "set_cur_window t = modify (cur_window_update (\<lambda>_. t))"

definition set_cur_frame_time :: "nat \<Rightarrow> (cstate_scheduler, event, unit) event_monad" where
  "set_cur_frame_time t = modify (cur_frame_time_update (\<lambda>_. t))"

lemma get_partition_rule [wp]:
  "\<lbrace> \<lambda>s. P (fst (cs_ttbl s ! wid)) s \<rbrace>
    get_partition wid
   \<lbrace> P \<rbrace>!"
  unfolding get_partition_def by wp

lemma get_duration_rule [wp]:
  "\<lbrace> \<lambda>s. P (snd (cs_ttbl s ! wid)) s \<rbrace>
    get_duration wid
   \<lbrace> P \<rbrace>!"
  unfolding get_duration_def by wp

lemma get_total_frame_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (frame_length (cs_ttbl s)) s \<rbrace>
    get_total_frame_time
   \<lbrace> P \<rbrace>!"
  unfolding get_total_frame_time_def by wp

lemma get_window_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (window_time s) s \<rbrace>
    get_window_time
   \<lbrace> P \<rbrace>!"
  unfolding get_window_time_def by wp

lemma get_cur_window_rule [wp]:
  "\<lbrace> \<lambda>s. P (cur_window s) s \<rbrace>
    get_cur_window
   \<lbrace> P \<rbrace>!"
  unfolding get_cur_window_def by wp

lemma get_cur_frame_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (cur_frame_time s) s \<rbrace>
    get_cur_frame_time
   \<lbrace> P \<rbrace>!"
  unfolding get_cur_frame_time_def by wp

lemma set_window_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>window_time := wtime\<rparr>) \<rbrace>
     set_window_time wtime
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_window_time_def by wp

lemma set_cur_window_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_window := window\<rparr>) \<rbrace>
     set_cur_window window
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_cur_window_def by wp

lemma set_cur_frame_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_frame_time := ftime\<rparr>) \<rbrace>
     set_cur_frame_time ftime
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_cur_frame_time_def by wp

definition update_cur_frame_time :: "(cstate_scheduler, event, unit) event_monad" where
  "update_cur_frame_time =
    get_window_time \<bind> (\<lambda>w_time.
    get_cur_frame_time \<bind> (\<lambda>f_time.
    set_cur_frame_time (f_time + w_time)))"

lemma update_cur_frame_time_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_frame_time := cur_frame_time s + window_time s\<rparr>) \<rbrace>
     update_cur_frame_time
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding update_cur_frame_time_def by wp

definition dispatch :: "(cstate_scheduler, event, unit) event_monad" where
  "dispatch =
     update_cur_frame_time \<bind> (\<lambda>_.
     get_cur_frame_time \<bind> (\<lambda>f_time.
     get_total_frame_time \<bind> (\<lambda>total_time.
     if f_time = total_time then
       get_partition 0 \<bind> (\<lambda>partition. 
       get_duration 0 \<bind> (\<lambda>duration.
       set_window_time duration \<bind> (\<lambda>_.
       set_cur_frame_time 0 \<bind> (\<lambda>_.
       set_cur_window 0 \<bind> (\<lambda>_.
       signal (PARTITION partition) \<bind> (\<lambda>_.
       signal (WATCHDOG_ADD (0, duration))))))))
     else
       get_cur_window \<bind> (\<lambda>cur_window.
       get_partition (cur_window + 1) \<bind> (\<lambda>partition.
       get_duration (cur_window + 1) \<bind> (\<lambda>duration.
       set_window_time duration \<bind> (\<lambda>_.
       set_cur_window (cur_window + 1) \<bind> (\<lambda>_.
       signal (PARTITION partition) \<bind> (\<lambda>_.
       signal (WATCHDOG_ADD (0, duration)))))))))))"

subsection \<open>Refinement relation for scheduler\<close>

definition rel :: "astate_scheduler \<Rightarrow> cstate_scheduler \<Rightarrow> bool" where
  "rel as cs \<longleftrightarrow> as_ttbl as = cs_ttbl cs \<and>
                 window_id as = cur_window cs"

definition cinv :: "cstate_scheduler \<Rightarrow> bool" where
  "cinv cs \<longleftrightarrow> is_valid_time_table (cs_ttbl cs) \<and>
               cur_window cs < length (cs_ttbl cs) \<and>
               window_time cs = snd (cs_ttbl cs ! cur_window cs) \<and>
               cur_frame_time cs = frame_time_to_window (cs_ttbl cs) (cur_window cs)"

lemma dispatch_rule':
  "\<lbrace> \<lambda>cs es. rel as cs \<and> cinv cs \<and> es = [] \<rbrace>
     dispatch
   \<lbrace> \<lambda>_ cs es. rel (fst (spec_dispatch as)) cs \<and> cinv cs \<and> es = snd (spec_dispatch as) \<rbrace>!"
proof -
  have a: "Suc (cur_window cs) mod length (cs_ttbl cs) = 0"
    if "cinv cs" "cur_frame_time cs + window_time cs = frame_length (cs_ttbl cs)" for cs
  proof -
    have a1: "frame_time_to_window (cs_ttbl cs) (Suc (cur_window cs)) = frame_length (cs_ttbl cs)"
      using that(1,2) unfolding cinv_def
      by (simp add: frame_time_to_window_next)
    have a2: "cur_window cs < length (cs_ttbl cs)"
      using that(1) unfolding cinv_def by auto
    have a3: "Suc (cur_window cs) = length (cs_ttbl cs)"
      by (metis Suc_lessI a1 cinv_def frame_time_to_window_mono_strict frame_time_to_window_total less_not_refl that(1))
    show ?thesis
      by (simp add: a3)
  qed
  have b: "Suc (cur_window cs) < length (cs_ttbl cs)"
    if "cinv cs" "cur_frame_time cs + window_time cs \<noteq> frame_length (cs_ttbl cs)" for cs
    by (metis Suc_lessI cinv_def frame_time_to_window_next frame_time_to_window_total that)
  show ?thesis
    unfolding dispatch_def apply wp apply auto
    subgoal for cs
      apply (auto simp add: rel_def spec_dispatch_def)
      using a by auto
    subgoal for cs
      by (auto simp add: rel_def cinv_def)
    subgoal for cs
      apply (auto simp add: spec_dispatch_def next_partition_def next_watchdog_pos_def)
      using a by (auto simp add: rel_def)
    subgoal for cs
      apply (auto simp add: rel_def spec_dispatch_def)
      using b by auto
    subgoal for cs
      by (auto simp add: cinv_def b frame_time_to_window_next)
    subgoal for cs
      apply (auto simp add: spec_dispatch_def next_partition_def next_watchdog_pos_def)
      using b rel_def by auto
    done
qed

definition rel_scheduler :: "astate_scheduler \<Rightarrow> cstate_scheduler \<Rightarrow> bool" where
  "rel_scheduler as cs \<longleftrightarrow> rel as cs \<and> cinv cs"

lemma dispatch_rule:
  "\<lbrace> \<lambda>cs es. rel_scheduler as cs \<and> nil\<^sub>e es \<rbrace>
     dispatch
   \<lbrace> \<lambda>_ cs es. rel_scheduler (fst (spec_dispatch as)) cs \<and> es = snd (spec_dispatch as) \<rbrace>!"
  apply (rule validNF_weaken_pre)
  apply (rule validNF_strengthen_post)
  apply (rule dispatch_rule')
  by (auto simp add: rel_scheduler_def nil_event_def)

subsection \<open>Event system\<close>

fun system :: "(event, cstate_scheduler \<times> watchdog_chain) event_system" where
  "system (DISPATCH 0) = Some (apply_fst dispatch)"
| "system (WATCHDOG_ADD (ev, n)) = Some (apply_snd (wadd_impl ev n))"
| "system WATCHDOG_TICK = Some (apply_snd wtick_impl)"
| "system _ = None"

lemma system_eval:
  "system (PARTITION n) = None"
  "system (DISPATCH 0) = Some (apply_fst dispatch)"
  "ev > 0 \<Longrightarrow> system (DISPATCH ev) = None"
  "system (WATCHDOG_ADD (ev, n)) = Some (apply_snd (wadd_impl ev n))"
  "system WATCHDOG_TICK = Some (apply_snd wtick_impl)"
  unfolding system.simps apply auto
  apply (cases ev) by auto

fun rel_total :: "astate_scheduler \<times> astate_watchdog \<Rightarrow> cstate_scheduler \<times> watchdog_chain \<Rightarrow> bool" where
  "rel_total (as, aw) p \<longleftrightarrow> rel_scheduler as (fst p) \<and> rel_watchdog aw (snd p)"
declare rel_total.simps[simp del]

theorem sValidNF_watchdog_add:
  assumes "w0 ev = None"
    and "n > 0"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (WATCHDOG_ADD (ev, n))
      (\<lambda>p es. rel_total (s0, w0(ev \<mapsto> n)) p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system_eval)
  apply (simp add: rel_total.simps)
   apply (rule validNF_apply_snd)
   apply (rule watchdog_add_rule)
    apply (rule assms(2)) apply (rule assms(1))
  unfolding nil_event_def apply auto
  apply (rule sValidNF_list_weaken_pre)
   prefer 2 apply (rule sValidNF_list_null)
  by (auto simp add: rel_total.simps)

theorem sValidNF_watchdog_add':
  assumes "w0 ev = None"
    and "n > 0"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> Q es)
      (WATCHDOG_ADD (ev, n))
      (\<lambda>p es. rel_total (s0, w0(ev \<mapsto> n)) p \<and> Q es)"
  apply (rule sValidNF_frame_nil)
  apply (rule sValidNF_watchdog_add)
  using assms by auto

lemma next_watchdog_pos_positive:
  "is_valid_time_table (as_ttbl as) \<Longrightarrow> next_watchdog_pos as > 0"
  unfolding next_watchdog_pos_def
  apply auto
  using Suc_lessD mod_less_divisor window_time_pos' by blast

theorem sValidNF_dispatch':
  assumes "w0 0 = None"
  shows
    "sValidNF system
      (\<lambda>p es. is_valid_time_table (as_ttbl s0) \<and> rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (DISPATCH 0)
      (\<lambda>p es. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> next_watchdog_pos s0)) p \<and>
              es = [PARTITION (next_partition s0)])"
proof -
  have snd_dispatch:
    "snd (spec_dispatch s0) = [PARTITION (next_partition s0), WATCHDOG_ADD (0, next_watchdog_pos s0)]"
    by (auto simp add: spec_dispatch_def)
  show ?thesis
    apply (subst sValidNF_conj_pre) apply auto
    apply (rule sValidNF_Some)
      apply (rule system_eval)
  apply (rule validNF_weaken_pre[where Q="\<lambda>p es. (rel_scheduler s0 (fst p) \<and> nil\<^sub>e es) \<and> rel_watchdog w0 (snd p)"])
    apply (rule validNF_apply_fst)
    apply (rule dispatch_rule)
   apply (auto simp add: rel_total.simps)[1]
  subgoal for p es
    apply (auto simp add: snd_dispatch)
    apply (rule sValidNF_list_cons)
     prefer 2
     apply (rule sValidNF_list_single)
     apply (rule sValidNF_watchdog_add')
      apply (rule assms(1)) apply (rule next_watchdog_pos_positive) apply auto[1]
    apply (rule sValidNF_weaken_pre)
     prefer 2 apply (rule sValidNF_None)
     apply (rule system_eval)
    by (auto simp add: nil_event_def rel_total.simps)
  done
qed

theorem sValidNF_dispatch:
  assumes "w0 0 = None"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (DISPATCH 0)
      (\<lambda>p es. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> next_watchdog_pos s0)) p \<and>
              es = [PARTITION (next_partition s0)])"
  apply (rule sValidNF_weaken_pre)
   prefer 2 apply (rule sValidNF_dispatch')
  apply (rule assms) by (auto simp add: rel_total.simps rel_scheduler_def cinv_def rel_def)

fun wtick_system_spec ::
  "astate_scheduler \<times> astate_watchdog \<Rightarrow> (astate_scheduler \<times> astate_watchdog) \<times> event set" where
  "wtick_system_spec (s0, w0) =
   (if w0 0 = Some 1 then
      ((fst (spec_dispatch s0),
        (wtick_spec w0)(0 \<mapsto> next_watchdog_pos s0)),
       (DISPATCH ` wtick_spec_ev w0 - {DISPATCH 0} \<union> {PARTITION (next_partition s0)}))
    else
      ((s0, wtick_spec w0),
       DISPATCH ` wtick_spec_ev w0))"
declare wtick_system_spec.simps [simp del]

theorem sValidNF_watchdog_tick:
  "sValidNF system
    (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
    WATCHDOG_TICK
    (\<lambda>p es. rel_total (fst (wtick_system_spec (s0, w0))) p \<and>
            distinct es \<and>
            set es = snd (wtick_system_spec (s0, w0)))"
proof -
  have pre1:
    "DISPATCH 0 \<notin> set es \<Longrightarrow>
     \<forall>e\<in>set es. \<exists>i. e = DISPATCH i \<Longrightarrow>
     sValidNF_list system (\<lambda>s' es'. P s' \<and> es' = es0) es (\<lambda>s' es'. P s' \<and> es' = es0 @ es)"
    for P es es0
    apply (rule sValidNF_list_weaken_pre)
    prefer 2 apply (rule sValidNF_list_all_None)
    apply (auto simp add: nil_event_def)
    apply (induction es) apply auto
    using system_eval(3) by fastforce
  have pre2:
    "DISPATCH 0 \<in> set es \<Longrightarrow>
     distinct es \<Longrightarrow>
     \<forall>e\<in>set es. \<exists>i. e = DISPATCH i \<Longrightarrow>
     w0 0 = None \<Longrightarrow>
     rel_scheduler s0 cs0 \<Longrightarrow>
     rel_watchdog w0 cw0 \<Longrightarrow>
     sValidNF_list system (\<lambda>s' es'. s' = (cs0, cw0) \<and> nil\<^sub>e es') es
       (\<lambda>s' es'. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> next_watchdog_pos s0)) s' \<and>
                 distinct es' \<and> set es' = set es - {DISPATCH 0} \<union> {PARTITION (next_partition s0)})"
    for cs0 cw0 s0 w0 es
  proof (induction es)
    case Nil
    then show ?case by auto
  next
    case (Cons e es)
    show ?case
    proof (cases "e = DISPATCH 0")
      case True
      have a1: "DISPATCH 0 \<notin> set es"
        using Cons(2,3) True by auto
      have a2: "\<forall>e\<in>set es. \<exists>i. e = DISPATCH i"
        using Cons(4) by auto
      let ?s0'="fst (spec_dispatch s0)"
      let ?w0'="w0(0 \<mapsto> next_watchdog_pos s0)"
      let ?es0="[PARTITION (next_partition s0)]"
      have a3: "sValidNF_list system (\<lambda>s' es'. rel_total (?s0', ?w0') s' \<and> es' = ?es0) es
                  (\<lambda>s' es'. rel_total (?s0', ?w0') s' \<and> es' = ?es0 @ es)"
        using pre1[OF a1 a2] by blast
      have a4: "distinct ([PARTITION (next_partition s0)] @ es)"
        using Cons(3) a2 by auto
      show ?thesis
        apply (subst True)
        apply (rule sValidNF_list_cons)
         apply (rule sValidNF_weaken_pre)
        prefer 2 apply (rule sValidNF_dispatch) apply (rule Cons(5))
          using Cons(6,7) apply (auto simp add: rel_total.simps)[1]
         apply (rule sValidNF_list_strengthen_post)
          prefer 2 apply (rule a3)
        using a1 a4 True by auto
    next
      case False
      have b1: "DISPATCH 0 \<in> set es"
        using Cons(2) False by auto
      have b2: "distinct es"
        using Cons(3) by auto
      have b3: "\<forall>e\<in>set es. \<exists>i. e = DISPATCH i"
        using Cons(4) by auto
      have b4: "system e = None"
        using False Cons.prems(3) system_eval(3) by force
      have b5: "sValidNF_list system
                 (\<lambda>s' es'. s' = (cs0, cw0) \<and> nil\<^sub>e es') es
                 (\<lambda>s' es'. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> next_watchdog_pos s0)) s' \<and>
                           distinct es' \<and>
                           set es' = set es - {DISPATCH 0} \<union> {PARTITION (next_partition s0)})"
        by (rule Cons(1)[OF b1 b2 b3 Cons(5,6,7)])
      have b6: "distinct t" "set t = set (e # es) - {DISPATCH 0} \<union> {PARTITION (next_partition s0)}"
        if assm_b6: "((\<lambda>t. t = [e]) ^\<^sub>e (\<lambda>es'. distinct es' \<and> set es' = set es - {DISPATCH 0} \<union> {PARTITION (next_partition s0)})) t" for t
      proof -
        obtain es' where c1: "distinct es'" "set es' = set es - {DISPATCH 0} \<union> {PARTITION (next_partition s0)}" "t = [e] @ es'"
          using assm_b6 unfolding chop_event_def by auto
        have c2: "set t = insert e (set es')"
          using c1(3) by auto
        show "distinct t"
          using Cons(3,4) c1 event.distinct(9) by auto
        show "set t = set (e # es) - {DISPATCH 0} \<union> {PARTITION (next_partition s0)}"
          using False c1(2) c2 by auto
      qed
      show ?thesis
        apply (rule sValidNF_list_cons)
        apply (rule sValidNF_None_sp)
         apply (rule b4)
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule sValidNF_list_frame)
         apply (rule b5)
        using b6 by blast
    qed
  qed
  have a: "sValidNF_list system
            (\<lambda>s' es'. s' = (cs0, cw0) \<and> nil\<^sub>e es')
             es
            (\<lambda>s' es'. rel_total (fst (wtick_system_spec (s0, w0))) s' \<and>
                      distinct es' \<and>
                      set es' = snd (wtick_system_spec (s0, w0)))"
    if "rel_scheduler s0 cs0"
       "rel_watchdog (wtick_spec w0) cw0"
       "distinct es"
       "set es = DISPATCH ` wtick_spec_ev w0" for cs0 cw0 es
  proof -
    have a1: "\<forall>e\<in>set es. \<exists>i. e = DISPATCH i"
      unfolding that wtick_spec_def by auto    
    show ?thesis
    proof (cases "w0 0 = Some 1")
      case True
      have b1: "DISPATCH 0 \<in> set es"
        using True wtick_spec_ev_def that by auto
      have b2: "wtick_spec w0 0 = None"
        by (auto simp add: wtick_spec_def True)
      show ?thesis
        apply (auto simp add: True wtick_system_spec.simps)
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule pre2[OF b1 that(3) a1 b2 that(1) that(2)])
        using True that by auto
    next
      case False
      have c1: "DISPATCH 0 \<notin> set es"
        using False wtick_spec_ev_def that by auto
      show ?thesis
        unfolding nil_event_def
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule pre1[OF c1 a1])
        using False that by (auto simp add: rel_total.simps wtick_system_spec.simps)
    qed
  qed
  show ?thesis
    apply (rule sValidNF_Some)
      apply (rule system_eval)
    apply (simp add: rel_total.simps)
     apply (rule validNF_apply_snd)
     apply (rule watchdog_tick_rule)
    using a by auto
qed

subsection \<open>Refinement for the combined system\<close>

record astate =
  a_ttbl :: time_table
  frame_time :: nat
  wchain :: astate_watchdog

definition spec_atick :: "astate \<Rightarrow> astate" where
  "spec_atick a =
    \<lparr>a_ttbl = a_ttbl a,
    frame_time = (frame_time a + 1) mod frame_length (a_ttbl a),
    wchain = wtick_spec (wchain a)\<rparr>"

definition spec_atick_ev :: "astate \<Rightarrow> event set" where
  "spec_atick_ev a =
    (if at_window_boundary (a_ttbl a) (frame_time a) then
       DISPATCH ` wtick_spec_ev (wchain a) \<union>
       {PARTITION (partition_at_time (a_ttbl a) ((frame_time a + 1) mod frame_length (a_ttbl a)))}
     else DISPATCH ` wtick_spec_ev (wchain a))"

fun arel :: "astate \<Rightarrow> astate_scheduler \<times> astate_watchdog \<Rightarrow> bool" where
  "arel a (as, aw) \<longleftrightarrow>
   (case aw 0 of
      None \<Rightarrow> False
    | Some wpos \<Rightarrow>
        a_ttbl a = as_ttbl as \<and>
        frame_time a = frame_time_to_window (as_ttbl as) (window_id as + 1) - wpos) \<and>
        wchain a 0 = None \<and> (\<forall>i>0. wchain a i = aw i)"
declare arel.simps [simp del]

fun ainv :: "astate_scheduler \<times> astate_watchdog \<Rightarrow> bool" where
  "ainv (as, aw) \<longleftrightarrow>
    is_valid_time_table (as_ttbl as) \<and>
    window_id as < length (as_ttbl as) \<and>
    (case aw 0 of
       None \<Rightarrow> False
     | Some wpos \<Rightarrow> wpos > 0 \<and> wpos \<le> snd (as_ttbl as ! window_id as))"
declare ainv.simps [simp del]

theorem spec_atick_refines:
  assumes "arel a (as, aw)"
    and "ainv (as, aw)"
  shows "arel (spec_atick a) (fst (wtick_system_spec (as, aw)))"
proof -
  have g1: "length (as_ttbl as) > 0"
    using assms(2) ainv.simps by auto
  have g2: "frame_length (as_ttbl as) > 0"
    using assms(2) valid_time_table_frame_length ainv.simps by auto
  have g3: "Suc (frame_length (as_ttbl as) - 1) = frame_length (as_ttbl as)"
    using g2 by auto
  have g4: "window_id as < length (as_ttbl as)"
    using assms(2) ainv.simps by auto
  have a: "Suc (frame_time_to_window (as_ttbl as) (Suc (window_id as)) - 1) mod frame_length (as_ttbl as) =
           frame_time_to_window (as_ttbl as) ((Suc (window_id as) mod length (as_ttbl as)) + 1) -
           snd (as_ttbl as ! (Suc (window_id as) mod length (as_ttbl as)))"
    if "frame_time a = frame_time_to_window (as_ttbl as) (Suc (window_id as)) - 1"
       "a_ttbl a = as_ttbl as"
  proof (cases "window_id as = length (as_ttbl as) - 1")
    case True
    have a1: "Suc (window_id as) = length (as_ttbl as)"
      using g1 True by auto
    have a2: "Suc (window_id as) mod length (as_ttbl as) = 0"
      using a1 by auto
    show ?thesis
      unfolding a1 a2 g1 g2 g3 frame_time_to_window_total
      apply (cases "as_ttbl as") by auto
  next
    case False
    have a1: "window_id as < length (as_ttbl as) - 1"
      using g1 g4 False by auto
    have a2: "frame_time_to_window (as_ttbl as) (Suc (window_id as)) > 0"
      using ainv.simps assms(2) frame_time_to_window_next window_time_pos by auto
    have a3: "Suc (frame_time_to_window (as_ttbl as) (Suc (window_id as)) - 1) =
              frame_time_to_window (as_ttbl as) (Suc (window_id as))"
      using a2 by auto
    have a4: "Suc (window_id as) mod length (as_ttbl as) = Suc (window_id as)"
      using One_nat_def a1 by auto
    have a5: "frame_time_to_window (as_ttbl as) (Suc (window_id as)) < frame_length (as_ttbl as)"
      by (metis a4 ainv.simps assms(2) frame_time_to_window_mono_strict frame_time_to_window_total g1 nat_mod_lem)
    have a6: "frame_time_to_window (as_ttbl as) (Suc (window_id as)) mod frame_length (as_ttbl as) =
              frame_time_to_window (as_ttbl as) (Suc (window_id as))"
      using a5 by auto
    show ?thesis
      unfolding g1 g2 g3 a3 a4 a6
      using a4 frame_time_to_window_next g1 nat_mod_lem by auto
  qed
  show ?thesis
  proof (cases "aw 0")
    case None
    then show ?thesis using assms arel.simps by auto
  next
    case (Some wpos)
    have b1: "wpos > 0" "wpos \<le> snd (as_ttbl as ! window_id as)"
      using assms(2) Some ainv.simps by auto
    have b2: "a_ttbl a = as_ttbl as"
      using assms(1) Some arel.simps by auto
    show ?thesis
    proof (cases "wpos = 1")
      case True
      then show ?thesis
        using assms unfolding Some True wtick_system_spec.simps spec_atick_def spec_dispatch_def next_watchdog_pos_def
        using a arel.simps by (auto simp add: True Some wtick_spec_def)
    next
      case False
      have c1: "wpos > 1"
        using b1 False by auto
      have c2: "wtick_spec aw 0 = Some (wpos - 1)"
        unfolding wtick_spec_def using Some c1 by auto
      have c3: "fst (wtick_system_spec (as, aw)) = (as, wtick_spec aw)"
        unfolding wtick_system_spec.simps
        using False Some by auto
      have c4: "frame_time a = frame_time_to_window (as_ttbl as) (window_id as + 1) - wpos"
        using assms(1) Some arel.simps by auto
      have c5: "frame_time_to_window (as_ttbl as) (Suc (window_id as)) \<ge> wpos"
        apply (auto simp add: frame_time_to_window_next g4)
        using b1(2) by auto
      have c6: "Suc (frame_time_to_window (as_ttbl as) (Suc (window_id as)) - wpos) =
                Suc (frame_time_to_window (as_ttbl as) (Suc (window_id as))) - wpos"
        using c5 by auto
      have c7: "Suc (frame_time_to_window (as_ttbl as) (Suc (window_id as))) - wpos < frame_length (as_ttbl as)"
        by (smt Suc_lessI Suc_less_eq2 ainv.simps assms(2) b1(1) c1 c5 c6 diff_diff_cancel diff_less
                frame_time_to_window_mono_strict frame_time_to_window_total less_diff_conv
                less_imp_diff_less less_le_trans plus_1_eq_Suc)
      show ?thesis
        unfolding spec_atick_def fst_conv c3 wtick_spec_def arel.simps
        using c1 apply (auto simp add: Some b2)
        unfolding c4 apply auto unfolding c6 using c7 apply auto
        using assms(1) unfolding arel.simps by auto
    qed
  qed
qed

theorem spec_atick_ainv:
  assumes "arel a (as, aw)"
    and "ainv (as, aw)"
  shows "ainv (fst (wtick_system_spec (as, aw)))"
  using assms ainv.simps
  apply (auto simp: spec_dispatch_def next_watchdog_pos_def wtick_spec_def wtick_system_spec.simps)
  apply (metis mod_less_divisor neq0_conv not_less_zero)
  using Suc_lessD mod_less_divisor window_time_pos' apply blast
  apply (cases "aw 0") by auto

theorem spec_atick_output:
  assumes "arel a (as, aw)"
    and "ainv (as, aw)"
  shows "spec_atick_ev a = snd (wtick_system_spec (as, aw))"
proof (cases "aw 0")
  case None
  then show ?thesis using assms arel.simps by auto
next
  case (Some wpos)
  have b1: "wpos > 0" "wpos \<le> snd (as_ttbl as ! window_id as)"
    using assms(2) Some ainv.simps by auto
  have b2: "a_ttbl a = as_ttbl as"
    using assms(1) Some arel.simps by auto
  have b3: "frame_time a = frame_time_to_window (as_ttbl as) (window_id as + 1) - wpos"
    using assms(1) Some arel.simps by auto
  have b4: "at_window_boundary (a_ttbl a) (frame_time a) \<longleftrightarrow> wpos = 1"
    unfolding b2 b3 apply (rule at_window_boundary_wpos)
    using assms(2) b1 ainv.simps by auto
  show ?thesis
  proof (cases "wpos = 1")
    case True
    have c1: "frame_time_to_window (as_ttbl as) (window_id as + 1) - wpos + 1 =
              frame_time_to_window (as_ttbl as) (window_id as + 1)"
      apply simp unfolding frame_time_to_window_next
      using True assms(2) frame_time_to_window_next window_time_pos ainv.simps by auto
    have c2: "length (as_ttbl as) > 0"
      using assms(2) ainv.simps by fastforce
    have c3: "partition_at_time (a_ttbl a) ((frame_time a + 1) mod frame_length (a_ttbl a)) =
          next_partition as"
    proof (cases "window_id as = length (as_ttbl as) - 1")
      case True
      have d1: "(window_id as + 1) mod length (as_ttbl as) = 0"
        using True
        by (metis Suc_diff_1 Suc_eq_plus1 c2 mod_self)
      have d2: "frame_time_to_window (as_ttbl as) (window_id as + 1) = frame_length (as_ttbl as)"
        by (metis Suc_diff_1 Suc_eq_plus1 True c2 frame_time_to_window_total)
      show ?thesis
        unfolding next_partition_def b3 c1 d1
        unfolding d2 b2
        apply auto
        by (metis (no_types, hide_lams) One_nat_def Suc_eq_plus1 Suc_lessD ainv.simps
              assms(2) fst_conv is_valid_time_table.elims(2) list.size(3) not_less_zero
              nth_Cons_0 partition_at_time.elims snd_conv window_time_pos)
    next
      case False
      have d1: "window_id as + 1 < length (as_ttbl as)"
        using False assms(2) ainv.simps by auto
      have d2: "frame_time_to_window (as_ttbl as) (window_id as + 1) < frame_length (as_ttbl as)"
        by (metis d1 ainv.simps assms(2) frame_time_to_window_mono_strict frame_time_to_window_total)
      have d3: "(window_id as + 1) mod length (as_ttbl as) = window_id as + 1"
        using d1 by auto
      have d4: "frame_time_to_window (as_ttbl as) (window_id as + 1) mod frame_length (as_ttbl as) =
                frame_time_to_window (as_ttbl as) (window_id as + 1)"
        using d2 by auto
      show ?thesis
        unfolding next_partition_def b2 b3 c1 d3 d4
        apply (rule partition_at_time_frame_time_to_window)
        using assms d1 ainv.simps by auto
    qed
    then show ?thesis
      unfolding spec_atick_def spec_atick_ev_def wtick_system_spec.simps snd_conv
                Some True arel.simps      
      using Some True b4 apply auto
      unfolding wtick_spec_ev_def using assms(1) unfolding arel.simps by auto
  next
    case False
    show ?thesis
      using Some False b4
      apply (auto simp add: spec_atick_def spec_atick_ev_def wtick_system_spec.simps)
      subgoal for x
        unfolding wtick_spec_ev_def using assms(1) apply (auto simp add: arel.simps)
        by (metis (mono_tags, lifting) image_eqI mem_Collect_eq neq0_conv option.distinct(1))
      subgoal for x
        unfolding wtick_spec_ev_def using assms(1) apply (auto simp add: arel.simps)
        by (metis (mono_tags, lifting) image_eqI mem_Collect_eq not_gr_zero option.inject)
      done
  qed
qed

fun arel_full :: "astate \<Rightarrow> cstate_scheduler \<times> watchdog_chain \<Rightarrow> bool" where
  "arel_full a p \<longleftrightarrow> (\<exists>as aw. arel a (as, aw) \<and> ainv (as, aw) \<and> rel_total (as, aw) p)"

theorem sValidNF_watchdog_tick_full:
  "sValidNF system
    (\<lambda>p es. arel_full a p \<and> nil\<^sub>e es)
      WATCHDOG_TICK
    (\<lambda>p es. arel_full (spec_atick a) p \<and> distinct es \<and> set es = spec_atick_ev a)"
  unfolding arel_full.simps
  apply (auto simp only: sValidNF_exists_pre)
  subgoal for as aw
    apply (auto simp add: sValidNF_conj_pre)
    apply (rule sValidNF_strengthen_post)
    prefer 2
     apply (rule sValidNF_watchdog_tick)
    subgoal for p es
      apply (intro conjI)
      subgoal  
      apply (rule exI[where x="fst (fst (wtick_system_spec (as, aw)))"])
      apply (rule exI[where x="snd (fst (wtick_system_spec (as, aw)))"])
        by (auto simp add: spec_atick_refines spec_atick_ainv)
      using spec_atick_output by auto
    done
  done

end

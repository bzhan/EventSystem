theory EventSystemSwitch
  imports EventSystemSwitchScheduler EventSystemWatchdog
begin

text \<open>This file combines verification of the full scheduler with switching
  between time tables.

  Both scheduler and watchdog sides have been verified independently.
  We now combine them together using the event system.
\<close>

context global_state
begin

subsection \<open>Event system\<close>

definition tick :: "(cstate \<times> watchdog_chain, event, unit) event_monad" where
  "tick =
    apply_fst get_next_mode \<bind> (\<lambda>nmode.
    if nmode = NEXT_TICK then
      apply_fst (set_next_mode NEXT_WINDOW) \<bind> (\<lambda>_.
      signal (WATCHDOG_REMOVE 0) \<bind> (\<lambda>_.
      signal WATCHDOG_TICK \<bind> (\<lambda>_.
      signal (DISPATCH 0))))
    else
      signal WATCHDOG_TICK)"

fun system :: "(event, cstate \<times> watchdog_chain) event_system" where
  "system (DISPATCH 0) = Some (apply_fst dispatch_all)"
| "system (WATCHDOG_ADD (ev, n)) = Some (apply_snd (wadd_impl ev n))"
| "system WATCHDOG_TICK = Some (apply_snd wtick_impl)"
| "system (WATCHDOG_REMOVE ev) = Some (apply_snd (wremove_impl ev))"
| "system TICK = Some tick"
| "system _ = None"

lemma system_eval:
  "system (PARTITION n) = None"
  "system (DISPATCH 0) = Some (apply_fst dispatch_all)"
  "ev > 0 \<Longrightarrow> system (DISPATCH ev) = None"
  "system (WATCHDOG_ADD (ev, n)) = Some (apply_snd (wadd_impl ev n))"
  "system WATCHDOG_TICK = Some (apply_snd wtick_impl)"
  "system (WATCHDOG_REMOVE ev) = Some (apply_snd (wremove_impl ev))"
  "system TICK = Some tick"
  unfolding system.simps apply auto
  apply (cases ev) by auto

fun rel_total :: "astate_scheduler \<times> astate_watchdog \<Rightarrow> cstate \<times> watchdog_chain \<Rightarrow> bool" where
  "rel_total (as, aw) p \<longleftrightarrow> rel_scheduler as (fst p) \<and> rel_watchdog aw (snd p)"
declare rel_total.simps[simp del]

lemma get_next_mode_sp:
  "\<lbrace>\<lambda>s es. rel_scheduler as s \<and> nil\<^sub>e es\<rbrace>
    get_next_mode
   \<lbrace>\<lambda>r s es. r = astate_scheduler.next_mode as \<and> rel_scheduler as s \<and> nil\<^sub>e es\<rbrace>!"
  apply wp by (auto simp add: rel_scheduler_def rel_def)

lemma set_next_mode_sp:
  "\<lbrace>\<lambda>s es. rel_scheduler as s \<and> nil\<^sub>e es\<rbrace>
    set_next_mode mode
   \<lbrace>\<lambda>_ s es. rel_scheduler (as\<lparr>astate_scheduler.next_mode := mode\<rparr>) s \<and> nil\<^sub>e es\<rbrace>!"
  apply wp apply (auto simp add: rel_scheduler_def rel_def ainv_def cur_ttbl_def)
  by (auto simp add: cinv_def c_cur_ttbl_def)

lemma tick_rule1:
  assumes "astate_scheduler.next_mode as = NEXT_TICK"
  shows
  "\<lbrace> \<lambda>p es. rel_total (as, aw) p \<and> nil\<^sub>e es \<rbrace>
     tick
   \<lbrace> \<lambda>_ p es. rel_total (as\<lparr>astate_scheduler.next_mode := NEXT_WINDOW\<rparr>, aw) p \<and>
              es = [WATCHDOG_REMOVE 0, WATCHDOG_TICK, DISPATCH 0] \<rbrace>!"
  unfolding tick_def
  apply (rule validNF_bind)
   apply (simp add: rel_total.simps)
  apply (rule validNF_weaken_pre[where Q="\<lambda>p es. (rel_scheduler as (fst p) \<and> nil\<^sub>e es) \<and> rel_watchdog aw (snd p)"])
    apply (rule validNF_apply_fst)
    apply (rule get_next_mode_sp)
  subgoal by auto
  subgoal for nmode
    apply (rule validNF_weaken_pre)
     apply (rule validNF_if_split[where Q="\<lambda>p es. rel_total (as, aw) p \<and> nil\<^sub>e es"])
      apply (rule validNF_bind)
       apply (rule validNF_weaken_pre[where Q="\<lambda>p es. (rel_scheduler as (fst p) \<and> nil\<^sub>e es) \<and> rel_watchdog aw (snd p)"])
        apply (rule validNF_apply_fst[OF set_next_mode_sp])
    apply (auto simp add: rel_total.simps)
     apply wp apply (auto simp add: nil_event_def)
    apply wp using assms by auto
  done

lemma tick_rule2:
  assumes "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows
  "\<lbrace> \<lambda>p es. rel_total (as, aw) p \<and> nil\<^sub>e es \<rbrace>
     tick
   \<lbrace> \<lambda>_ p es. rel_total (as, aw) p \<and> es = [WATCHDOG_TICK] \<rbrace>!"
  unfolding tick_def
  apply (rule validNF_bind)
     apply (simp add: rel_total.simps)
  apply (rule validNF_weaken_pre[where Q="\<lambda>p es. (rel_scheduler as (fst p) \<and> nil\<^sub>e es) \<and> rel_watchdog aw (snd p)"])
    apply (rule validNF_apply_fst)
    apply (rule get_next_mode_sp)
  subgoal by auto
  subgoal for nmode
    apply (rule validNF_weaken_pre)
    apply (rule validNF_if_split[where R="\<lambda>p es. rel_total (as, aw) p \<and> nil\<^sub>e es"])
      apply wp apply (rule validNF_apply_fst[OF set_next_mode_sp])
      apply auto apply wp using assms apply auto
    apply wp apply (auto simp add: nil_event_def)
  using assms by (auto simp add: rel_total.simps)
  done

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

theorem sValidNF_watchdog_remove:
  assumes "w0 ev \<noteq> None"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (WATCHDOG_REMOVE ev)
      (\<lambda>p es. rel_total (s0, w0(ev := None)) p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system_eval)
   apply (simp add: rel_total.simps)
  apply (rule validNF_apply_snd)
   apply (rule watchdog_remove_rule)
  unfolding nil_event_def apply auto
  apply (rule sValidNF_list_weaken_pre)
   prefer 2 apply (rule sValidNF_list_null)
  by (auto simp add: rel_total.simps)

definition next_pair :: "astate_scheduler \<Rightarrow> partition \<times> nat" where
  "next_pair st =
    (if astate_scheduler.next_mode st = NEXT_WINDOW then
       next_ttbl st ! 0
     else if window_id st = length (cur_ttbl st) - 1 \<and> astate_scheduler.next_mode st = NEXT_FRAME then
       next_ttbl st ! 0
     else if window_id st = length (cur_ttbl st) - 1 \<and> astate_scheduler.next_mode st = ONGOING then
       cur_ttbl st ! 0
     else
       cur_ttbl st ! ((window_id st + 1) mod length (cur_ttbl st)))"

lemma spec_dispatch_is_next_pair:
  "snd (spec_dispatch as) = [PARTITION (fst (next_pair as)), WATCHDOG_ADD (0, snd (next_pair as))]"
  unfolding spec_dispatch_def next_pair_def by auto

lemma next_pair_positive:
  "ainv as \<Longrightarrow> snd (next_pair as) > 0"
  unfolding ainv_def next_pair_def
  apply (cases "astate_scheduler.next_mode as = NEXT_WINDOW")
  using is_valid_time_table.elims(2) next_ttbl_def valid_time_table window_time_pos apply fastforce
  apply (cases "window_id as = length (cur_ttbl as) - 1 \<and> astate_scheduler.next_mode as = NEXT_FRAME")
  using is_valid_time_table.elims(2) next_ttbl_def valid_time_table window_time_pos apply fastforce
  apply (cases "window_id as = length (cur_ttbl as) - 1 \<and> astate_scheduler.next_mode as = ONGOING")
  using cur_ttbl_def valid_time_table window_time_pos apply fastforce
  by (smt cur_ttbl_def window_time_pos global_state_axioms length_greater_0_conv
          length_ineq_not_Nil(1) mod_less_divisor valid_time_table)

theorem sValidNF_dispatch':
  assumes "w0 0 = None"
    and "astate_scheduler.next_mode s0 \<noteq> NEXT_TICK"
  shows
    "sValidNF system
      (\<lambda>p es. ainv s0 \<and> rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (DISPATCH 0)
      (\<lambda>p es. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> snd (next_pair s0))) p \<and>
              es = [PARTITION (fst (next_pair s0))])"
  apply (subst sValidNF_conj_pre) apply auto
  apply (rule sValidNF_Some)
    apply (rule system_eval)
  apply (rule validNF_weaken_pre[where Q="\<lambda>p es. (rel_scheduler s0 (fst p) \<and> nil\<^sub>e es) \<and> rel_watchdog w0 (snd p)"])
    apply (rule validNF_apply_fst)
    apply (rule dispatch_all_rule[OF assms(2)])
   apply (auto simp add: rel_total.simps)[1]
  subgoal for p es
    apply (auto simp add: spec_dispatch_is_next_pair)
    apply (rule sValidNF_list_cons)
     prefer 2
     apply (rule sValidNF_list_single)
     apply (rule sValidNF_watchdog_add')
      apply (rule assms(1)) apply (rule next_pair_positive) apply auto[1]
    apply (rule sValidNF_weaken_pre)
     prefer 2 apply (rule sValidNF_None)
     apply (rule system_eval)
    by (auto simp add: nil_event_def rel_total.simps)
  done

theorem sValidNF_dispatch:
  assumes "w0 0 = None"
    and "astate_scheduler.next_mode s0 \<noteq> NEXT_TICK"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
      (DISPATCH 0)
      (\<lambda>p es. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> snd (next_pair s0))) p \<and>
              es = [PARTITION (fst (next_pair s0))])"
  apply (rule sValidNF_weaken_pre)
   prefer 2 apply (rule sValidNF_dispatch')
  using assms by (auto simp add: rel_scheduler_def rel_total.simps)

text \<open>Specification for watchdog tick in the event system\<close>
fun wtick_system_spec ::
  "astate_scheduler \<times> astate_watchdog \<Rightarrow> (astate_scheduler \<times> astate_watchdog) \<times> event set" where
  "wtick_system_spec (s0, w0) =
   (if w0 0 = Some 1 then
      ((fst (spec_dispatch s0),
        (wtick_spec w0)(0 \<mapsto> snd (next_pair s0))),
       (DISPATCH ` wtick_spec_ev w0) - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))})
    else
      ((s0, wtick_spec w0),
       DISPATCH ` wtick_spec_ev w0))"

theorem sValidNF_watchdog_tick:
  assumes "w0 0 = Some 1 \<longrightarrow> astate_scheduler.next_mode s0 \<noteq> NEXT_TICK"
  shows
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
     astate_scheduler.next_mode s0 \<noteq> NEXT_TICK \<Longrightarrow>
     rel_scheduler s0 cs0 \<Longrightarrow>
     rel_watchdog w0 cw0 \<Longrightarrow>
     sValidNF_list system (\<lambda>s' es'. s' = (cs0, cw0) \<and> nil\<^sub>e es') es
       (\<lambda>s' es'. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> snd (next_pair s0))) s' \<and>
                 distinct es' \<and> set es' = set es - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))})"
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
      let ?w0'="w0(0 \<mapsto> snd (next_pair s0))"
      let ?es0="[PARTITION (fst (next_pair s0))]"
      have a3: "sValidNF_list system (\<lambda>s' es'. rel_total (?s0', ?w0') s' \<and> es' = ?es0) es
                  (\<lambda>s' es'. rel_total (?s0', ?w0') s' \<and> es' = ?es0 @ es)"
        by (rule pre1[OF a1 a2])
      have a4: "distinct ([PARTITION (fst (next_pair s0))] @ es)"
        using Cons(3) a2 by auto
      show ?thesis
        apply (subst True)
        apply (rule sValidNF_list_cons)
         apply (rule sValidNF_weaken_pre)
        prefer 2 apply (rule sValidNF_dispatch) apply (rule Cons(5))
          prefer 2 using Cons(7,8) apply (auto simp add: rel_total.simps)[1]
        using Cons(6) apply auto[1]
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
                 (\<lambda>s' es'. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> snd (next_pair s0))) s' \<and>
                           distinct es' \<and> set es' = set es - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))})"
        by (rule Cons(1)[OF b1 b2 b3 Cons(5-8)])
      have b6: "distinct t" "set t = set (e # es) - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))}"
        if assm_b6: "((\<lambda>t. t = [e]) ^\<^sub>e (\<lambda>es'. distinct es' \<and> set es' = set es - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))})) t" for t
      proof -
        obtain es' where c1: "distinct es'" "set es' = set es - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))}" "t = [e] @ es'"
          using assm_b6 unfolding chop_event_def by auto
        have c2: "set t = insert e (set es')"
          using c1(3) by auto
        show "distinct t"
          using Cons(3,4) c1 event.distinct(9) by auto
        show "set t = set (e # es) - {DISPATCH 0} \<union> {PARTITION (fst (next_pair s0))}"
          using False c1(2) c2 by auto
      qed
      show ?thesis
        apply (rule sValidNF_list_cons)
         apply (rule sValidNF_None_sp)
         apply (rule b4)
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule sValidNF_list_frame)
         apply (rule b5)
        using b6(1) b6(2) by blast
    qed
  qed
  have a: "sValidNF_list system
     (\<lambda>s' es'. s' = (cs0, cw0) \<and> nil\<^sub>e es')
      es
     (\<lambda>p es. rel_total (fst (wtick_system_spec (s0, w0))) p \<and>
             distinct es \<and>
             set es = snd (wtick_system_spec (s0, w0)))"
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
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule pre2[OF b1 that(3) a1 b2 _ that(1) that(2)])
        using True that assms by auto
    next
      case False
      have c1: "DISPATCH 0 \<notin> set es"
        using False wtick_spec_ev_def that by auto
      show ?thesis
        unfolding nil_event_def
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule pre1[OF c1 a1])
        using False that by (auto simp add: rel_total.simps)
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

theorem sValidNF_watchdog_tick':
  assumes "w0 0 = None"
  shows
  "sValidNF system
    (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
    WATCHDOG_TICK
    (\<lambda>p es. rel_total (s0, wtick_spec w0) p \<and>
            distinct es \<and>
            set es = DISPATCH ` wtick_spec_ev w0)"
  apply (rule sValidNF_strengthen_post)
   prefer 2
   apply (rule sValidNF_watchdog_tick)
  using assms by auto

theorem sValidNF_dispatch_frame:
  assumes "w0 0 = None"
    and "astate_scheduler.next_mode s0 \<noteq> NEXT_TICK"
  shows
    "sValidNF system
      (\<lambda>p es. rel_total (s0, w0) p \<and> P es)
      (DISPATCH 0)
      (\<lambda>p es. rel_total (fst (spec_dispatch s0), w0(0 \<mapsto> snd (next_pair s0))) p \<and>
              (P ^\<^sub>e (\<lambda>e. e = [PARTITION (fst (next_pair s0))])) es)"
  apply (rule sValidNF_frame)
  apply (rule sValidNF_dispatch)
  using assms by auto

theorem sValidNF_tick1:
  assumes "astate_scheduler.next_mode s0 = NEXT_TICK"
    and "w0 0 \<noteq> None"
  shows
  "sValidNF system
    (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
    TICK
    (\<lambda>p es. rel_total
        (fst (spec_dispatch (s0\<lparr>astate_scheduler.next_mode := NEXT_WINDOW\<rparr>)),
        (wtick_spec (w0(0 := None)))(0 \<mapsto> snd (next_ttbl s0 ! 0))) p \<and>
        ((\<lambda>t. distinct t \<and> set t = DISPATCH ` wtick_spec_ev (w0(0 := None))) ^\<^sub>e
         (\<lambda>t. t = [PARTITION (fst (next_ttbl s0 ! 0))])) es)"
  apply (rule sValidNF_Some)
  apply (rule system_eval)
  apply (rule tick_rule1[OF assms(1)])
  subgoal for p es
    apply auto
    apply (rule sValidNF_list_cons)
    apply (rule sValidNF_weaken_pre)
      prefer 2 apply (rule sValidNF_watchdog_remove)
      apply (rule assms(2))
    apply auto
    apply (rule sValidNF_list_cons)
     apply (rule sValidNF_watchdog_tick')
     apply auto
    apply (rule sValidNF_list_single)
    apply (rule sValidNF_strengthen_post)
     prefer 2 apply (rule sValidNF_dispatch_frame)
      apply auto
    by (auto simp add: wtick_spec_def next_pair_def next_ttbl_def)
  done

theorem sValidNF_tick2:
  assumes "astate_scheduler.next_mode s0 \<noteq> NEXT_TICK"
  shows
  "sValidNF system
    (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
    TICK
    (\<lambda>p es. rel_total (fst (wtick_system_spec (s0, w0))) p \<and>
            distinct es \<and>
            set es = snd (wtick_system_spec (s0, w0)))"
  apply (rule sValidNF_Some)
  apply (rule system_eval)
   apply (rule tick_rule2[OF assms])
  subgoal for p es
    apply (auto simp del: wtick_system_spec.simps)
    apply (rule sValidNF_list_single)
    apply (rule sValidNF_weaken_pre)
     prefer 2 apply (rule sValidNF_watchdog_tick)
    using assms by auto
  done

text \<open>Specification of overall tick in the event system\<close>
fun spec_tick_system ::
  "astate_scheduler \<times> astate_watchdog \<Rightarrow> (astate_scheduler \<times> astate_watchdog) \<times> event set" where
  "spec_tick_system (s0, w0) =
   (if astate_scheduler.next_mode s0 = NEXT_TICK then
      ((fst (spec_dispatch (s0\<lparr>astate_scheduler.next_mode := NEXT_WINDOW\<rparr>)),
       (wtick_spec (w0(0 := None)))(0 \<mapsto> snd (next_ttbl s0 ! 0))),
       (DISPATCH ` wtick_spec_ev w0) - {DISPATCH 0} \<union> {PARTITION (fst (next_ttbl s0 ! 0))})
    else
      wtick_system_spec (s0, w0))"

theorem sValidNF_tick:
  assumes "w0 0 \<noteq> None"
  shows
  "sValidNF system
    (\<lambda>p es. rel_total (s0, w0) p \<and> nil\<^sub>e es)
    TICK
    (\<lambda>p es. rel_total (fst (spec_tick_system (s0, w0))) p \<and>
            distinct es \<and>
            set es = snd (spec_tick_system (s0, w0)))"
proof (cases "astate_scheduler.next_mode s0 = NEXT_TICK")
  case True
  have a: "distinct t" "set t = snd (spec_tick_system (s0, w0))"
    if assm_a: "((\<lambda>t. distinct t \<and> set t = DISPATCH ` wtick_spec_ev (w0(0 := None))) ^\<^sub>e
                (\<lambda>t. t = [PARTITION (fst (next_ttbl s0 ! 0))])) t"
      "astate_scheduler.next_mode s0 = NEXT_TICK"
    for t
  proof -
    obtain t1 where a1: "t = t1 @ [PARTITION (fst (next_ttbl s0 ! 0))]"
      "distinct t1" "set t1 = DISPATCH ` wtick_spec_ev (w0(0 := None))"
      using assm_a(1) unfolding chop_event_def by auto
    show "distinct t"
      using a1 by auto
    have a2: "snd (spec_tick_system (s0, w0)) =
      (DISPATCH ` wtick_spec_ev w0) - {DISPATCH 0} \<union> {PARTITION (fst (next_ttbl s0 ! 0))}"
      using assm_a(2) by auto
    have a3: "wtick_spec_ev (w0(0 := None)) = wtick_spec_ev w0 - {0}"
      by (auto simp add: wtick_spec_ev_def)
    have a4: "set t = set t1 \<union> {PARTITION (fst (next_ttbl s0 ! 0))}"
      unfolding a1(1) by auto
    show "set t = snd (spec_tick_system (s0, w0))"
      unfolding a2 a1(3) a4 a3 by auto
  qed
  show ?thesis
    apply (rule sValidNF_strengthen_post)
     prefer 2 apply (rule sValidNF_tick1)
    using True apply auto[1]
    using assms apply auto[1]
    by (metis (no_types, lifting) True a fst_conv spec_tick_system.simps)
next
  case False
  show ?thesis
    apply (rule sValidNF_strengthen_post)
     prefer 2 apply (rule sValidNF_tick2)
    using False by auto
qed

end

subsection \<open>Refinement for the combined system\<close>

record astate =
  a_cur_ttbl_id :: ttbl_id   \<comment> \<open>ID of current table\<close>
  frame_time :: nat          \<comment> \<open>Current time within the frame\<close>
  a_next_ttbl_id :: ttbl_id  \<comment> \<open>ID of next table (0 when not switching)\<close>
  a_next_mode :: switch_mode  \<comment> \<open>Switch mode\<close>
  wchain :: astate_watchdog  \<comment> \<open>Watchdog info (excluding 0)\<close>

context global_state
begin

definition a_cur_ttbl :: "astate \<Rightarrow> time_table" where
  "a_cur_ttbl a = time_tables (a_cur_ttbl_id a)"

definition a_next_ttbl :: "astate \<Rightarrow> time_table" where
  "a_next_ttbl a = time_tables (a_next_ttbl_id a)"

text \<open>Detect whether switching should occur at the next tick.\<close>
definition to_switch :: "astate \<Rightarrow> bool" where
  "to_switch a =
    (case a_next_mode a of
        NO_SWITCH \<Rightarrow> False
      | ONGOING \<Rightarrow> False
      | NEXT_TICK \<Rightarrow> True
      | NEXT_WINDOW \<Rightarrow> at_window_boundary (a_cur_ttbl a) (frame_time a)
      | NEXT_FRAME \<Rightarrow> frame_time a = (frame_length (a_cur_ttbl a) - 1))"

text \<open>Specification of the overall system\<close>
definition spec_atick :: "astate \<Rightarrow> astate \<times> event set" where
  "spec_atick a =
    (if to_switch a then
      (\<lparr>a_cur_ttbl_id = a_next_ttbl_id a, frame_time = 0, a_next_ttbl_id = 0, a_next_mode = ONGOING,
        wchain = wtick_spec (wchain a)\<rparr>,
       DISPATCH ` wtick_spec_ev (wchain a) \<union>
       {PARTITION (fst (a_next_ttbl a ! 0))})
     else if frame_time a = frame_length (a_cur_ttbl a) - 1 \<and> a_next_mode a = ONGOING then
      (a\<lparr>frame_time := 0, a_next_mode := NO_SWITCH,
       wchain := wtick_spec (wchain a)\<rparr>,
       DISPATCH ` wtick_spec_ev (wchain a) \<union>
       {PARTITION (fst (a_cur_ttbl a ! 0))})
     else if at_window_boundary (a_cur_ttbl a) (frame_time a) then
      (a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
       wchain := wtick_spec (wchain a)\<rparr>,
       DISPATCH ` wtick_spec_ev (wchain a) \<union>
       {PARTITION (partition_at_time (a_cur_ttbl a) ((frame_time a + 1) mod frame_length (a_cur_ttbl a)))})
     else
      (a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
       wchain := wtick_spec (wchain a)\<rparr>,
       DISPATCH ` wtick_spec_ev (wchain a)))"

fun arel :: "astate \<Rightarrow> astate_scheduler \<times> astate_watchdog \<Rightarrow> bool" where
  "arel a (as, aw) \<longleftrightarrow>
   (case aw 0 of
      None \<Rightarrow> False
    | Some wpos \<Rightarrow>
        a_cur_ttbl_id a = astate_scheduler.cur_ttbl_id as \<and>
        frame_time a = frame_time_to_window (cur_ttbl as) (window_id as + 1) - wpos \<and>
        a_next_ttbl_id a = astate_scheduler.next_ttbl_id as \<and>
        a_next_mode a = astate_scheduler.next_mode as \<and>
        wchain a 0 = None \<and> (\<forall>i>0. wchain a i = aw i))"
declare arel.simps [simp del]

fun as_inv :: "astate_scheduler \<times> astate_watchdog \<Rightarrow> bool" where
  "as_inv (as, aw) \<longleftrightarrow>
    ainv as \<and>
    (case aw 0 of
       None \<Rightarrow> False
     | Some wpos \<Rightarrow> wpos > 0 \<and> wpos \<le> snd (cur_ttbl as ! window_id as))"
declare as_inv.simps [simp del]

theorem spec_atick_refines1:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
    and "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows "arel (fst (spec_atick a)) (fst (wtick_system_spec (as, aw)))"
proof -
  have g1: "length (cur_ttbl as) > 0"
    using assms(2) by (auto simp add: ainv_def as_inv.simps)
  have g2: "frame_length (cur_ttbl as) > 0"
    using assms(2) valid_time_table_frame_length
    using cur_ttbl_def global_state.ainv_def global_state_axioms valid_time_table as_inv.simps by auto
  have g3: "Suc (frame_length (cur_ttbl as) - 1) = frame_length (cur_ttbl as)"
    using g2 by auto
  have g4: "window_id as < length (cur_ttbl as)"
    using assms(2) by (simp add: ainv_def as_inv.simps)
  have a: "Suc (frame_time_to_window (cur_ttbl as) (Suc (window_id as)) - Suc 0) mod frame_length (cur_ttbl as) =
           frame_time_to_window (cur_ttbl as) (Suc (Suc (window_id as) mod length (cur_ttbl as))) -
           snd (cur_ttbl as ! (Suc (window_id as) mod length (cur_ttbl as)))"
    if "frame_time a = frame_time_to_window (cur_ttbl as) (Suc (window_id as)) - 1"
       "a_cur_ttbl a = cur_ttbl as"
  proof (cases "window_id as = length (cur_ttbl as) - 1")
    case True
    have a1: "Suc (window_id as) = length (cur_ttbl as)"
      using g1 True by auto
    have a2: "Suc (window_id as) mod length (cur_ttbl as) = 0"
      using a1 by auto
    show ?thesis
      unfolding a1 a2 g1 g2 g3 frame_time_to_window_total
      apply (cases "cur_ttbl as")
      using g2 apply auto[1]
      by (metis One_nat_def a1 add_eq_if diff_self_eq_0 frame_time_to_window_next
                frame_time_to_window_zero g1 g3 mod_self nth_Cons_0)
  next
    case False
    have a1: "window_id as < length (cur_ttbl as) - 1"
      using g1 g4 False by auto
    have a2: "frame_time_to_window (cur_ttbl as) (Suc (window_id as)) > 0"
      using assms(2) frame_time_to_window_next window_time_pos
      using ainv_def cur_ttbl_def valid_time_table as_inv.simps by auto
    have a3: "Suc (frame_time_to_window (cur_ttbl as) (Suc (window_id as)) - 1) =
              frame_time_to_window (cur_ttbl as) (Suc (window_id as))"
      using a2 by auto
    have a4: "Suc (window_id as) mod length (cur_ttbl as) = Suc (window_id as)"
      using One_nat_def a1 by auto
    have a5: "frame_time_to_window (cur_ttbl as) (Suc (window_id as)) < frame_length (cur_ttbl as)"
      by (metis (no_types, lifting) Suc_pred' a1 as_inv.simps assms(2) cur_ttbl_def
                frame_time_to_window_mono_strict frame_time_to_window_total g1 global_state.ainv_def
                global_state_axioms not_less_eq valid_time_table)
    have a6: "frame_time_to_window (cur_ttbl as) (Suc (window_id as)) mod frame_length (cur_ttbl as) =
              frame_time_to_window (cur_ttbl as) (Suc (window_id as))"
      using a5 by auto
    show ?thesis
      unfolding g1 g2 g3 a3 a4 a6
      using a4 frame_time_to_window_next g1 nat_mod_lem
      by (metis One_nat_def a3 a6 add_diff_cancel_right')
  qed
  show ?thesis
  proof (cases "aw 0")
    case None
    then show ?thesis using assms as_inv.simps by auto
  next
    case (Some wpos)
    have b1: "wpos > 0" "wpos \<le> snd (cur_ttbl as ! window_id as)"
      using assms(2) Some as_inv.simps by auto
    have b2: "a_cur_ttbl a = cur_ttbl as"
      using assms(1) Some by (auto simp add: arel.simps cur_ttbl_def a_cur_ttbl_def)
    have b3: "frame_time a = frame_time_to_window (cur_ttbl as) (window_id as + 1) - wpos"
      using assms(1) Some by (auto simp add: arel.simps)
    have b4: "at_window_boundary (a_cur_ttbl a) (frame_time a) \<longleftrightarrow> wpos = 1"
      unfolding b2 b3 apply (rule at_window_boundary_wpos)
      using assms(2) b1 apply (auto simp add: ainv_def as_inv.simps)
      using cur_ttbl_def valid_time_table by auto
    have b5: "a_next_mode a = astate_scheduler.next_mode as"
      using assms(1) Some by (auto simp add: arel.simps)
    have b6: "is_valid_time_table (a_cur_ttbl a)"
      using assms ainv_def b2 cur_ttbl_def valid_time_table as_inv.simps by auto
    have b7: "window_id as < length (cur_ttbl as)"
      using ainv_def assms(2) as_inv.simps by auto
    have b8: "a_next_ttbl a = next_ttbl as"
      using assms(1) Some by (auto simp add: arel.simps next_ttbl_def a_next_ttbl_def)
    have b9: "is_valid_time_table (next_ttbl as)"
      using ainv_def assms(2) next_ttbl_def valid_time_table as_inv.simps by auto
    have b10: "frame_time_to_window (next_ttbl as) 1 \<le> snd (next_ttbl as ! 0)"
      apply (cases "next_ttbl as") using b9 by auto
    show ?thesis
    proof (cases "wpos = 1")
      case True
      note wpos = True
      have c1: "at_window_boundary (a_cur_ttbl a) (frame_time a)"
        using b4 True by auto
      show ?thesis
      proof (cases "a_next_mode a")
        case NO_SWITCH
        have e1: "\<not>to_switch a"
          unfolding to_switch_def using NO_SWITCH by auto
        have e2: "fst (spec_atick a) =
                    a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
                      wchain := wtick_spec (wchain a)\<rparr>"
          by (auto simp add: spec_atick_def e1 NO_SWITCH)
        have e3: "fst (wtick_system_spec (as, aw)) =
          (as\<lparr>window_id := (window_id as + 1) mod length (cur_ttbl as)\<rparr>,
           (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
          using b5 by (auto simp add: Some wpos spec_dispatch_def NO_SWITCH)
        have e4: "next_pair as = cur_ttbl as ! ((window_id as + 1) mod length (cur_ttbl as))"
          using b5 by (auto simp add: next_pair_def NO_SWITCH)
        have e5: "cur_ttbl (as\<lparr>window_id := Suc (window_id as) mod length (cur_ttbl as)\<rparr>) = cur_ttbl as"
          unfolding cur_ttbl_def by auto
        show ?thesis
          unfolding e2 e3 e4 using arel.simps apply auto
          subgoal using Some assms(1) by auto
          subgoal unfolding b3 wpos e5 b2 apply auto apply (rule a)
            using b3 wpos b2 by auto
          subgoal using Some assms(1) by auto
          subgoal using Some assms(1) by auto
          subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
          subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
          done
      next
        case NEXT_TICK
        then show ?thesis using assms(3) b5 by auto
      next
        case NEXT_WINDOW
        have e1: "to_switch a"
          unfolding to_switch_def using NEXT_WINDOW c1 by auto
        have e2: "fst (spec_atick a) = \<lparr>a_cur_ttbl_id = a_next_ttbl_id a, frame_time = 0,
                                        a_next_ttbl_id = 0, a_next_mode = ONGOING,
                                        wchain = wtick_spec (wchain a)\<rparr>"
          unfolding spec_atick_def using e1 by auto
        have e3: "fst (wtick_system_spec (as, aw)) =
            (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0,
              reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>,
             (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
          using Some True NEXT_WINDOW b5 by (auto simp add: spec_dispatch_def)
        have e4: "next_pair as = next_ttbl as ! 0"
          using next_pair_def NEXT_WINDOW b5 by auto
        show ?thesis
          unfolding e2 e3 e4 using arel.simps apply (auto simp add: cur_ttbl_def)
          using assms(1) Some apply auto[1]
          using b10 next_ttbl_def apply auto[1]
          using Some assms(1) by (auto simp add: wtick_spec_def)
      next
        case NEXT_FRAME
        show ?thesis
        proof (cases "window_id as = length (cur_ttbl as) - 1")
          case True
          have e1: "frame_time a = frame_length (a_cur_ttbl a) - 1"
            unfolding b3 True wpos apply auto
            by (metis One_nat_def Suc_diff_1 b2 b7 frame_time_to_window_total gr_zeroI not_less_zero)
          have e2: "fst (spec_atick a) = \<lparr>a_cur_ttbl_id = a_next_ttbl_id a, frame_time = 0,
                                          a_next_ttbl_id = 0, a_next_mode = ONGOING,
                                          wchain = wtick_spec (wchain a)\<rparr>"
            unfolding spec_atick_def to_switch_def e1 NEXT_FRAME b5 by auto
          have e3: "fst (wtick_system_spec (as, aw)) =
            (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0,
              reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>,
             (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
            using b5 by (auto simp add: Some wpos spec_dispatch_def NEXT_FRAME True)
          have e4: "next_pair as = next_ttbl as ! 0"
            using b5 by (auto simp add: next_pair_def NEXT_FRAME True)
          show ?thesis
            unfolding e2 e3 e4 using arel.simps apply (auto simp add: cur_ttbl_def)
            using assms(1) Some apply auto[1]
            using b10 next_ttbl_def apply auto[1]
            using Some assms(1) by (auto simp add: wtick_spec_def)
        next
          case False
          have e1: "window_id as + 1 < length (cur_ttbl as)"
            using False b7 by linarith
          have e2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) < frame_length (cur_ttbl as)"
            by (metis b2 b6 e1 frame_time_to_window_mono_strict frame_time_to_window_total)
          have e3: "frame_time a < frame_length (a_cur_ttbl a) - 1"
            unfolding b3
            by (metis add_gr_0 b2 b6 e2 frame_length.simps(1) frame_time_to_window_mono_strict
                      frame_time_to_window_zero length_greater_0_conv less_imp_diff_less
                      less_numeral_extra(1) minus_eq nat_less_cases' wpos)
          have e4: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
            using e3 by auto
          have e5: "fst (spec_atick a) = a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
                                           wchain := wtick_spec (wchain a)\<rparr>"
            using b5 e4 by (auto simp add: spec_atick_def to_switch_def NEXT_FRAME)
          have e6: "fst (wtick_system_spec (as, aw)) =
            (as\<lparr>window_id := Suc (window_id as) mod length (cur_ttbl as)\<rparr>,
             (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
            using b5 False by (auto simp add: NEXT_FRAME Some wpos spec_dispatch_def)
          have e7: "next_pair as = cur_ttbl as ! (Suc (window_id as) mod length (cur_ttbl as))"
            using b5 False by (auto simp add: next_pair_def NEXT_FRAME)
          have e8: "cur_ttbl (as\<lparr>window_id := Suc (window_id as) mod length (cur_ttbl as)\<rparr>) = cur_ttbl as"
            unfolding cur_ttbl_def by auto
          show ?thesis
            unfolding e5 e6 e7 using arel.simps apply auto
            subgoal using Some assms(1) by auto
            subgoal unfolding b3 wpos e8 b2 apply auto apply (rule a)
              using b3 wpos b2 by auto
            subgoal using Some assms(1) by auto
            subgoal using Some assms(1) by auto
            subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
            subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
            done
        qed
      next
        case ONGOING
        show ?thesis
        proof (cases "window_id as = length (cur_ttbl as) - 1")
          case True
          have e1: "frame_time a = frame_length (a_cur_ttbl a) - 1"
            unfolding b3 True wpos apply auto
            by (metis One_nat_def Suc_diff_1 b2 b7 frame_time_to_window_total gr_zeroI not_less_zero)
          have e2: "fst (spec_atick a) = a\<lparr>frame_time := 0, a_next_mode := NO_SWITCH,
                                           wchain := wtick_spec (wchain a)\<rparr>"
            unfolding spec_atick_def to_switch_def e1 ONGOING b5 by auto
          have e3: "fst (wtick_system_spec (as, aw)) =
            (as\<lparr>window_id := 0, astate_scheduler.next_mode := NO_SWITCH\<rparr>,
             (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
            using b5 by (auto simp add: Some wpos spec_dispatch_def ONGOING True)
          have e4: "next_pair as = cur_ttbl as ! 0"
            using b5 by (auto simp add: next_pair_def ONGOING True)
          show ?thesis
            unfolding e2 e3 e4 using arel.simps apply (auto simp add: cur_ttbl_def)
            using assms(1) Some apply auto[1]
            using b10 cur_ttbl_def
             apply (metis (no_types, lifting) One_nat_def Suc_diff_1 Suc_eq_plus1 True a b2 b3
                diff_is_0_eq e1 g1 g3 mod_self wpos)
            using Some assms(1) apply auto[1]
            using Some assms(1) by (auto simp add: wtick_spec_def)
        next
          case False
          have e1: "window_id as + 1 < length (cur_ttbl as)"
            using False b7 by linarith
          have e2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) < frame_length (cur_ttbl as)"
            by (metis b2 b6 e1 frame_time_to_window_mono_strict frame_time_to_window_total)
          have e3: "frame_time a < frame_length (a_cur_ttbl a) - 1"
            unfolding b3
            by (metis add_gr_0 b2 b6 e2 frame_length.simps(1) frame_time_to_window_mono_strict
                      frame_time_to_window_zero length_greater_0_conv less_imp_diff_less
                      less_numeral_extra(1) minus_eq nat_less_cases' wpos)
          have e4: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
            using e3 by auto
          have e5: "fst (spec_atick a) = a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
                                           wchain := wtick_spec (wchain a)\<rparr>"
            using b5 e4 by (auto simp add: spec_atick_def to_switch_def ONGOING)
          have e6: "fst (wtick_system_spec (as, aw)) =
            (as\<lparr>window_id := Suc (window_id as) mod length (cur_ttbl as)\<rparr>,
             (wtick_spec aw)(0 \<mapsto> snd (next_pair as)))"
            using b5 False by (auto simp add: ONGOING Some wpos spec_dispatch_def)
          have e7: "next_pair as = cur_ttbl as ! (Suc (window_id as) mod length (cur_ttbl as))"
            using b5 False by (auto simp add: next_pair_def ONGOING)
          have e8: "cur_ttbl (as\<lparr>window_id := Suc (window_id as) mod length (cur_ttbl as)\<rparr>) = cur_ttbl as"
            unfolding cur_ttbl_def by auto
          show ?thesis
            unfolding e5 e6 e7 using arel.simps apply auto
            subgoal using Some assms(1) by auto
            subgoal unfolding b3 wpos e8 b2 apply auto apply (rule a)
              using b3 wpos b2 by auto
            subgoal using Some assms(1) by auto
            subgoal using Some assms(1) by auto
            subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
            subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
            done
        qed
      qed
    next
      case False
      have d1: "\<not>at_window_boundary (a_cur_ttbl a) (frame_time a)"
        using b4 False by auto
      have d2: "at_window_boundary (a_cur_ttbl a) (frame_length (a_cur_ttbl a) - 1)"
        apply (rule at_frame_boundary_also_window_boundary)
        by (rule b6)
      have d3: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
        using d1 d2 by auto
      have d4: "\<not>to_switch a"
        unfolding to_switch_def apply (cases "a_next_mode a")
        using False d3 by (auto simp add: assms(3) b4 b5)
      have d5: "fst (spec_atick a) = a\<lparr>frame_time := (frame_time a + 1) mod frame_length (a_cur_ttbl a),
                                       wchain := wtick_spec (wchain a)\<rparr>"
        unfolding spec_atick_def using d3 d4 by auto
      have d6: "fst (wtick_system_spec (as, aw)) = (as, wtick_spec aw)"
        using Some False by auto
      have d7: "wpos > 1"
        using False b1(1) nat_neq_iff by blast
      have d8: "wtick_spec aw 0 = Some (wpos - 1)"
        unfolding wtick_spec_def using Some d7 by auto
      have d9: "frame_time_to_window (cur_ttbl as) (Suc (window_id as)) \<ge> wpos"
        apply (auto simp add: frame_time_to_window_next b7)
        using b1(2) by auto
      have d10: "frame_time_to_window (cur_ttbl as) (Suc (window_id as)) \<le> frame_length (cur_ttbl as)"
        by (metis Suc_leI b7 frame_time_to_window_mono frame_time_to_window_total)
      show ?thesis
        unfolding d5 d6 using arel.simps
        apply (auto simp add: d8)
        subgoal using Some assms(1) by auto
        subgoal unfolding b3 using b2 d10 d7 d9 by auto
        subgoal using Some assms(1) by auto
        subgoal using Some assms(1) by auto
        subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
        subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
        done
    qed
  qed
qed

theorem spec_atick_refines:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
  shows "arel (fst (spec_atick a)) (fst (spec_tick_system (as, aw)))"
proof (cases "astate_scheduler.next_mode as = NEXT_TICK")
  case True
  show ?thesis
  proof (cases "aw 0")
    case None
    then show ?thesis using assms as_inv.simps by auto
  next
    case (Some wpos)
    have a1: "a_next_mode a = NEXT_TICK"
      using Some True assms(1) by (auto simp add: arel.simps)
    have a2: "to_switch a"
      by (auto simp add: to_switch_def a1)
    have a3: "fst (spec_atick a) =
      \<lparr>a_cur_ttbl_id = a_next_ttbl_id a, frame_time = 0, a_next_ttbl_id = 0, a_next_mode = ONGOING,
       wchain = wtick_spec (wchain a)\<rparr>"
      unfolding spec_atick_def using a2 by auto
    have a4: "fst (spec_tick_system (as, aw)) =
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>,
       (wtick_spec (aw(0 := None)))(0 \<mapsto> snd (next_ttbl as ! 0)))"
      by (auto simp add: True spec_dispatch_def)
    show ?thesis
      unfolding a3 a4 using arel.simps
      apply (auto simp add: cur_ttbl_def)
      using Some assms(1) apply auto[1]
      unfolding next_ttbl_def[symmetric]
        apply (cases "next_ttbl as") apply auto
        subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
        subgoal using Some assms(1) by (auto simp add: wtick_spec_def)
        done
  qed
next
  case False
  show ?thesis
    using False assms spec_atick_refines1 by auto
qed

theorem spec_atick_ainv1:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
    and "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows "as_inv (fst (wtick_system_spec (as, aw)))"
proof (cases "aw 0")
  case None
  then show ?thesis
    using assms(2) by (auto simp add: as_inv.simps ainv_def)
next
  case (Some wpos)
  have g1: "0 < snd (cur_ttbl as ! (Suc (window_id as) mod length (cur_ttbl as)))"
    by (metis (no_types, lifting) as_inv.simps assms(2) cur_ttbl_def global_state.ainv_def
        window_time_pos global_state_axioms le_less_trans nat_Suc_less_le_imp
        unique_euclidean_semiring_numeral_class.pos_mod_bound valid_time_table zero_less_Suc)
  have g2: "0 < snd (next_ttbl as ! 0)"
    by (metis One_nat_def Suc_lessD as_inv.simps assms(2) global_state.ainv_def global_state_axioms
              is_valid_time_table.elims(2) next_ttbl_def valid_time_table window_time_pos)
  have g3: "0 < snd (cur_ttbl as ! 0)"
    using ainv_def assms(2) cur_ttbl_def valid_time_table window_time_pos as_inv.simps by fastforce
  show ?thesis
  proof (cases "wpos = 1")
    case True
    note wpos = True
    show ?thesis
    proof (cases "astate_scheduler.next_mode as")
      case NO_SWITCH
      then show ?thesis
        using assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
        subgoal by (simp add: length_ineq_not_Nil(1))
        subgoal unfolding next_pair_def using g1 by auto
        subgoal unfolding next_pair_def by (auto simp add: cur_ttbl_def)
        subgoal by (simp add: Some wpos)
        done
    next
      case NEXT_TICK
      then show ?thesis
        using assms(3) by blast
    next
      case NEXT_WINDOW
      then show ?thesis
        using assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
        subgoal using True length_ineq_not_Nil(1) valid_time_table by auto
        subgoal unfolding next_pair_def using g2 by auto
        subgoal unfolding next_pair_def by (auto simp add: next_ttbl_def)
        by (simp add: Some wpos)
    next
      case NEXT_FRAME
      show ?thesis
      proof (cases "window_id as = length (cur_ttbl as) - 1")
        case True
        then show ?thesis
          using NEXT_FRAME assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
          subgoal using valid_time_table by force
          subgoal unfolding next_pair_def True using g2 by auto
          subgoal unfolding next_pair_def True by (auto simp add: next_ttbl_def)
          by (simp add: Some wpos)
      next
        case False
        then show ?thesis
          using NEXT_FRAME assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
          subgoal unfolding next_pair_def using False g1 by auto
          subgoal unfolding next_pair_def using False by (auto simp add: cur_ttbl_def)
          by (simp add: Some wpos)
      qed
    next
      case ONGOING
      show ?thesis
      proof (cases "window_id as = length (cur_ttbl as) - 1")
        case True
        then show ?thesis
          using ONGOING assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
          subgoal unfolding next_pair_def True using g3 by auto
          subgoal unfolding next_pair_def True by (auto simp add: cur_ttbl_def)
          by (simp add: Some wpos)
      next
        case False
        then show ?thesis
          using ONGOING assms apply (auto simp add: spec_dispatch_def ainv_def cur_ttbl_def as_inv.simps)
          subgoal unfolding next_pair_def using False g1 by auto
          subgoal unfolding next_pair_def using False by (auto simp add: cur_ttbl_def)
          by (simp add: Some wpos)
      qed
    qed
  next
    case False
    have a1: "wpos > 1"
      using False assms(2) Some as_inv.simps by auto
    have a2: "wtick_spec aw 0 = Some (wpos - 1)"
      unfolding wtick_spec_def using Some a1 by auto
    show ?thesis
      using Some assms(2) False a2 by (auto simp add: ainv_def as_inv.simps)
  qed
qed

theorem spec_atick_ainv:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
  shows "as_inv (fst (spec_tick_system (as, aw)))"
proof (cases "astate_scheduler.next_mode as = NEXT_TICK")
  case True
  show ?thesis
  proof (cases "aw 0")
    case None
    then show ?thesis using assms as_inv.simps by auto
  next
    case (Some wpos)
    have a1: "a_next_mode a = NEXT_TICK"
      using Some True assms(1) by (auto simp add: arel.simps)
    have a2: "to_switch a"
      by (auto simp add: to_switch_def a1)
    have a4: "fst (spec_tick_system (as, aw)) =
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>,
       (wtick_spec (aw(0 := None)))(0 \<mapsto> snd (next_ttbl as ! 0)))"
      by (auto simp add: True spec_dispatch_def)
    show ?thesis
      unfolding a4 using assms Some apply (auto simp add: ainv_def next_ttbl_def cur_ttbl_def as_inv.simps)
      using valid_time_table apply force
      by (metis One_nat_def Suc_lessD is_valid_time_table.elims(2) valid_time_table window_time_pos)
  qed
next
  case False
  then show ?thesis
    using assms spec_atick_ainv1 by auto
qed

theorem spec_atick_output1:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
    and "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows "snd (spec_atick a) = snd (wtick_system_spec (as, aw))"
proof (cases "aw 0")
  case None
  then show ?thesis using assms as_inv.simps by auto
next
  case (Some wpos)
  have b1: "wpos > 0" "wpos \<le> snd (cur_ttbl as ! window_id as)"
    using assms(2) Some as_inv.simps by auto
  have b2: "a_cur_ttbl a = cur_ttbl as"
    using assms(1) Some by (auto simp add: arel.simps cur_ttbl_def a_cur_ttbl_def)
  have b3: "frame_time a = frame_time_to_window (cur_ttbl as) (window_id as + 1) - wpos"
    using assms(1) Some by (auto simp add: arel.simps)
  have b4: "at_window_boundary (a_cur_ttbl a) (frame_time a) \<longleftrightarrow> wpos = 1"
    unfolding b2 b3 apply (rule at_window_boundary_wpos)
    using assms(2) b1 apply (auto simp add: ainv_def as_inv.simps)
    using cur_ttbl_def valid_time_table by auto
  have b5: "a_next_mode a = astate_scheduler.next_mode as"
    using assms(1) Some by (auto simp add: arel.simps)
  have b6: "is_valid_time_table (a_cur_ttbl a)"
    using assms ainv_def b2 cur_ttbl_def valid_time_table as_inv.simps by auto
  have b7: "window_id as < length (cur_ttbl as)"
    using ainv_def assms(2) as_inv.simps by auto
  show ?thesis
  proof (cases "wpos = 1")
    case True
    note wpos = True
    have c1: "at_window_boundary (a_cur_ttbl a) (frame_time a)"
      using b4 True by auto
    have c2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) - wpos + 1 =
              frame_time_to_window (cur_ttbl as) (window_id as + 1)"
      apply simp unfolding frame_time_to_window_next
      using True assms(2) frame_time_to_window_next window_time_pos
            ainv_def b1(2) as_inv.simps by auto
    have c2: "length (cur_ttbl as) > 0"
      using assms(2) ainv_def b1(2) as_inv.simps by fastforce
    have c3: "partition_at_time (a_cur_ttbl a) ((frame_time a + 1) mod frame_length (a_cur_ttbl a)) =
              fst (cur_ttbl as ! ((window_id as + 1) mod length (cur_ttbl as)))"
    proof (cases "window_id as = length (cur_ttbl as) - 1")
      case True
      have d1: "(window_id as + 1) mod length (cur_ttbl as) = 0"
        using True
        by (metis Suc_diff_1 Suc_eq_plus1 c2 mod_self)
      have d2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) = frame_length (cur_ttbl as)"
        by (metis Suc_diff_1 Suc_eq_plus1 True c2 frame_time_to_window_total)
      show ?thesis
        unfolding b3 c1 d1
        unfolding d2 b2
        apply auto
        using b2 b6 partition_at_time_frame_time_to_window valid_time_table_frame_length wpos by fastforce
    next
      case False
      have d1: "window_id as + 1 < length (cur_ttbl as)"
        using False assms(2)
        using as_inv.simps global_state.ainv_def global_state_axioms less_diff_conv nat_less_cases' by blast
      have d2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) < frame_length (cur_ttbl as)"
        by (metis b2 b6 d1 frame_time_to_window_mono_strict frame_time_to_window_total)
      have d3: "(window_id as + 1) mod length (cur_ttbl as) = window_id as + 1"
        using d1 by auto
      have d4: "frame_time_to_window (cur_ttbl as) (window_id as + 1) mod frame_length (cur_ttbl as) =
                frame_time_to_window (cur_ttbl as) (window_id as + 1)"
        using d2 by auto
      show ?thesis
        unfolding b2 b3 c1 d3 d4
        by (metis Suc_eq_plus1 add_diff_inverse_nat add_gr_0 b2 b6 c2 d1 d4
                  frame_time_to_window_mono_strict frame_time_to_window_zero is_valid_time_table.elims(2)
                  less_numeral_extra(3) less_one partition_at_time_frame_time_to_window plus_1_eq_Suc wpos)
    qed
    show ?thesis
    proof (cases "a_next_mode a")
      case NO_SWITCH
      have e1: "\<not>to_switch a"
        unfolding to_switch_def using NO_SWITCH by auto
      have e2: "snd (spec_atick a) =
        DISPATCH ` wtick_spec_ev (wchain a) \<union>
        {PARTITION (partition_at_time (a_cur_ttbl a) ((frame_time a + 1) mod frame_length (a_cur_ttbl a)))}"
        using NO_SWITCH c1 e1 by (auto simp add: spec_atick_def)
      have e4: "next_pair as = cur_ttbl as ! ((window_id as + 1) mod length (cur_ttbl as))"
        using b5 by (auto simp add: next_pair_def NO_SWITCH)
      have e5: "snd (wtick_system_spec (as, aw)) =
        DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
        unfolding wtick_system_spec.simps Some wpos by auto
      have e6: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
        using assms(1) unfolding arel.simps Some by auto
      show ?thesis
        unfolding e2 Some wpos e5 e4
        using c3 apply auto
        unfolding wtick_spec_ev_def using e6 apply auto
        subgoal for x
          apply (rule image_eqI[where x=x]) apply auto
          by (metis One_nat_def Some neq0_conv wpos)
        done
    next
      case NEXT_TICK
      then show ?thesis
        using assms(3) b5 by auto
    next
      case NEXT_WINDOW
      have e1: "to_switch a"
        unfolding to_switch_def using NEXT_WINDOW c1 by auto
      have e2: "snd (spec_atick a) =
        DISPATCH ` wtick_spec_ev (wchain a) \<union> {PARTITION (fst (a_next_ttbl a ! 0))}"
        unfolding spec_atick_def using e1 by auto
      have e3: "next_pair as = next_ttbl as ! 0"
        using NEXT_WINDOW b5 next_pair_def by auto
      have e4: "snd (wtick_system_spec (as, aw)) =
        DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
        unfolding wtick_system_spec.simps Some wpos by auto
      have e5: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
        using assms(1) unfolding arel.simps Some by auto
      show ?thesis
        unfolding e2 e3 e4
        using Some a_next_ttbl_def assms(1) next_ttbl_def wpos apply (auto simp add: arel.simps)
        unfolding wtick_spec_ev_def using e5 by auto
    next
      case NEXT_FRAME
      show ?thesis
      proof (cases "window_id as = length (cur_ttbl as) - 1")
        case True
        have e1: "frame_time a = frame_length (a_cur_ttbl a) - 1"
          unfolding b3 True wpos apply auto
          by (metis One_nat_def Suc_diff_1 b2 b7 frame_time_to_window_total gr_zeroI not_less_zero)
        have e2: "to_switch a"
          unfolding to_switch_def using NEXT_FRAME e1 by auto
        have e3: "snd (spec_atick a) =
          DISPATCH ` wtick_spec_ev (wchain a) \<union> {PARTITION (fst (a_next_ttbl a ! 0))}"
          unfolding spec_atick_def using e1 e2 by auto
        have e4: "next_pair as = next_ttbl as ! 0"
          using NEXT_FRAME b5 next_pair_def True by auto
        have e5: "snd (wtick_system_spec (as, aw)) =
          DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
          unfolding wtick_system_spec.simps Some wpos by auto
        have e6: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
          using assms(1) unfolding arel.simps Some by auto
        show ?thesis
          unfolding e3 e4 e5 Some wpos
          using Some a_next_ttbl_def assms(1) next_ttbl_def apply (auto simp add: arel.simps)
          unfolding wtick_spec_ev_def using e6 apply auto
          subgoal for x
            apply (rule image_eqI[where x=x]) apply auto
            by (metis One_nat_def Some neq0_conv wpos)
          done
      next
        case False
        have e1: "window_id as + 1 < length (cur_ttbl as)"
          using False b7 by linarith
        have e2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) < frame_length (cur_ttbl as)"
          by (metis b2 b6 e1 frame_time_to_window_mono_strict frame_time_to_window_total)
        have e3: "frame_time a < frame_length (a_cur_ttbl a) - 1"
          unfolding b3
          by (metis add_gr_0 b2 b6 e2 frame_length.simps(1) frame_time_to_window_mono_strict
                    frame_time_to_window_zero length_greater_0_conv less_imp_diff_less
                    less_numeral_extra(1) minus_eq nat_less_cases' wpos)
        have e4: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
          using e3 by auto
        have e5: "\<not>to_switch a"
          unfolding to_switch_def using NEXT_FRAME e4 by auto
        have e6: "snd (spec_atick a) =
          DISPATCH ` wtick_spec_ev (wchain a) \<union>
          {PARTITION (partition_at_time (a_cur_ttbl a) (Suc (frame_time a) mod frame_length (a_cur_ttbl a)))}"
          using NEXT_FRAME e5 c1 by (auto simp add: spec_atick_def)
        have e7: "next_pair as = cur_ttbl as ! ((window_id as + 1) mod length (cur_ttbl as))"
          using NEXT_FRAME b5 False by (auto simp add: next_pair_def)
        have e8: "snd (wtick_system_spec (as, aw)) =
          DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
          unfolding wtick_system_spec.simps Some wpos by auto
        have e9: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
          using assms(1) unfolding arel.simps Some by auto
        show ?thesis
          unfolding e6 e7 e8 Some wpos
          using c3 apply auto
          using assms(1) e9 apply (auto simp add: wtick_spec_ev_def arel.simps)
          subgoal for x
            apply (rule image_eqI[where x=x]) apply auto
            by (metis One_nat_def Some neq0_conv wpos)
          done
      qed
    next
      case ONGOING
      show ?thesis
      proof (cases "window_id as = length (cur_ttbl as) - 1")
        case True
        have e1: "frame_time a = frame_length (a_cur_ttbl a) - 1"
          unfolding b3 True wpos apply auto
          by (metis One_nat_def Suc_diff_1 b2 b7 frame_time_to_window_total gr_zeroI not_less_zero)
        have e2: "\<not>to_switch a"
          unfolding to_switch_def using ONGOING e1 by auto
        have e3: "snd (spec_atick a) =
          DISPATCH ` wtick_spec_ev (wchain a) \<union> {PARTITION (fst (a_cur_ttbl a ! 0))}"
          unfolding spec_atick_def using e1 e2 ONGOING by auto
        have e4: "next_pair as = cur_ttbl as ! 0"
          using ONGOING b5 next_pair_def True by auto
        have e5: "snd (wtick_system_spec (as, aw)) =
          DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
          unfolding wtick_system_spec.simps Some wpos by auto
        have e6: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
          using assms(1) unfolding arel.simps Some by auto
        show ?thesis
          unfolding e3 e4 e5 Some wpos
          using Some a_cur_ttbl_def assms(1) cur_ttbl_def apply (auto simp add: arel.simps)
          unfolding wtick_spec_ev_def using e6 apply auto
          subgoal for x
            apply (rule image_eqI[where x=x]) apply auto
            by (metis One_nat_def Some neq0_conv wpos)
          done
      next
        case False
        have e1: "window_id as + 1 < length (cur_ttbl as)"
          using False b7 by linarith
        have e2: "frame_time_to_window (cur_ttbl as) (window_id as + 1) < frame_length (cur_ttbl as)"
          by (metis b2 b6 e1 frame_time_to_window_mono_strict frame_time_to_window_total)
        have e3: "frame_time a < frame_length (a_cur_ttbl a) - 1"
          unfolding b3
          by (metis add_gr_0 b2 b6 e2 frame_length.simps(1) frame_time_to_window_mono_strict
                    frame_time_to_window_zero length_greater_0_conv less_imp_diff_less
                    less_numeral_extra(1) minus_eq nat_less_cases' wpos)
        have e4: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
          using e3 by auto
        have e5: "\<not>to_switch a"
          unfolding to_switch_def using ONGOING e4 by auto
        have e6: "snd (spec_atick a) =
          DISPATCH ` wtick_spec_ev (wchain a) \<union>
          {PARTITION (partition_at_time (a_cur_ttbl a) (Suc (frame_time a) mod frame_length (a_cur_ttbl a)))}"
          using ONGOING e5 e4 c1 by (auto simp add: spec_atick_def)
        have e7: "next_pair as = cur_ttbl as ! ((window_id as + 1) mod length (cur_ttbl as))"
          using ONGOING b5 False by (auto simp add: next_pair_def)
        have e8: "snd (wtick_system_spec (as, aw)) =
          DISPATCH ` wtick_spec_ev aw - {DISPATCH 0} \<union> {PARTITION (fst (next_pair as))}"
          unfolding wtick_system_spec.simps Some wpos by auto
        have e9: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
          using assms(1) unfolding arel.simps Some by auto
        show ?thesis
          unfolding e6 e7 e8 Some wpos
          using c3 apply auto
          using assms(1) e9 apply (auto simp add: wtick_spec_ev_def arel.simps)
          subgoal for x
            apply (rule image_eqI[where x=x]) apply auto
            by (metis One_nat_def Some neq0_conv wpos)
          done
      qed
    qed
  next
    case False
    have d1: "\<not>at_window_boundary (a_cur_ttbl a) (frame_time a)"
      using b4 False by auto
    have d2: "at_window_boundary (a_cur_ttbl a) (frame_length (a_cur_ttbl a) - 1)"
      apply (rule at_frame_boundary_also_window_boundary)
      by (rule b6)
    have d3: "frame_time a \<noteq> frame_length (a_cur_ttbl a) - 1"
      using d1 d2 by auto
    have d4: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
      using assms(1) unfolding arel.simps Some by auto
    show ?thesis
      using False d3 apply (auto simp add: Some spec_atick_def d1 d3 to_switch_def)
          apply (cases "a_next_mode a") apply (auto simp add: d1 b5 assms(3))
      unfolding wtick_spec_ev_def using d4 apply auto
      subgoal for x
        apply (rule image_eqI[where x=x]) apply auto
        by (metis neq0_conv option.distinct(1))
      subgoal for x
        by (metis (full_types, lifting) Some imageI mem_Collect_eq not_gr_zero option.inject)
      subgoal for x
        apply (rule image_eqI[where x=x]) apply auto
        by (metis neq0_conv option.distinct(1))
      subgoal for x
        apply (rule image_eqI[where x=x]) apply auto
        by (metis Some neq0_conv option.inject)
      done
  qed
qed

theorem spec_atick_output:
  assumes "arel a (as, aw)"
    and "as_inv (as, aw)"
  shows "snd (spec_atick a) = snd (spec_tick_system (as, aw))"
proof (cases "astate_scheduler.next_mode as = NEXT_TICK")
  case True
  show ?thesis
  proof (cases "aw 0")
    case None
    then show ?thesis using assms(1) unfolding arel.simps by auto
  next
    case (Some wpos)
    have a1: "a_next_mode a = NEXT_TICK"
      using Some True assms(1) by (auto simp add: arel.simps)
    have a2: "to_switch a"
      by (auto simp add: to_switch_def a1)
    have a3: "snd (spec_atick a) =
      DISPATCH ` wtick_spec_ev (wchain a) \<union> {PARTITION (fst (a_next_ttbl a ! 0))}"
      by (auto simp add: spec_atick_def a2)
    have a4: "snd (spec_tick_system (as, aw)) =
      (DISPATCH ` wtick_spec_ev aw) - {DISPATCH 0} \<union> {PARTITION (fst (next_ttbl as ! 0))}"
      by (auto simp add: True)
    have a5: "wchain a 0 = None" "(\<forall>i>0. wchain a i = aw i)"
      using assms(1) unfolding arel.simps Some by auto
    have a6: "a_next_ttbl a = next_ttbl as"
      using Some a_next_ttbl_def arel.simps assms(1) next_ttbl_def by auto
    show ?thesis
      unfolding a3 a4 using a5 a6 apply (auto simp add: wtick_spec_ev_def)
      subgoal for x
        apply (rule image_eqI[where x=x])
         apply auto by (metis gt_or_eq_0 option.simps(3))
      done
  qed
next
  case False
  then show ?thesis
    using assms(1) assms(2) spec_atick_output1 by auto
qed

fun arel_full :: "astate \<Rightarrow> cstate \<times> watchdog_chain \<Rightarrow> bool" where
  "arel_full a p \<longleftrightarrow> (\<exists>as aw. arel a (as, aw) \<and> as_inv (as, aw) \<and> rel_total (as, aw) p)"

theorem sValidNF_watchdog_tick_full:
  "sValidNF system
    (\<lambda>p es. arel_full a p \<and> nil\<^sub>e es)
      TICK
    (\<lambda>p es. arel_full (fst (spec_atick a)) p \<and> distinct es \<and> set es = snd (spec_atick a))"
  unfolding arel_full.simps
  apply (auto simp only: sValidNF_exists_pre)
  subgoal for as aw
    apply (auto simp add: sValidNF_conj_pre)
    apply (rule sValidNF_strengthen_post)
    prefer 2
     apply (rule sValidNF_tick)
     apply (auto simp add: as_inv.simps)[1] apply (cases "aw 0") apply auto[1] apply auto[1]
    subgoal for p es
      apply (intro conjI)
      subgoal  
      apply (rule exI[where x="fst (fst (spec_tick_system (as, aw)))"])
        apply (rule exI[where x="snd (fst (spec_tick_system (as, aw)))"])
        using spec_atick_ainv spec_atick_refines by auto
      using spec_atick_output by auto
    done
  done

end

end

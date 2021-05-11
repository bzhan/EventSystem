section \<open>The watchdog module\<close>

theory Watchdog
  imports Main
begin

text \<open>The watchdog chain is given by a list of scheduled events,
  each event is specified by an event code, and the time it should be
  triggered, which is the number of ticks *after* the previous event is
  triggered.

  For example, the following watchdog chain:

  [(1, 10), (1, 5), (2, 0), (1, 0), (3, 5)]

  means trigger event 1 after 10 ticks, trigger event 1 (again) after another
  5 ticks, followed immediately by event 2 and event 1. Finally, trigger
  event 3 after 5 ticks after that.
\<close>

type_synonym task_id = nat

type_synonym watchdog_chain = "(task_id \<times> nat) list"

subsection \<open>Event time\<close>

text \<open>The watchdog should satisfy the property that:

  If an event (e, n) is inserted, then the event e should be triggered
  after exactly n ticks (the output after the nth tick should include e).
  
  Assume that for each event e, there is at most one entry of the form (e, _)
  in the chain. Then the chain abstract to a single integer, which is the trigger
  time for the event.
\<close>
fun event_time :: "watchdog_chain \<Rightarrow> task_id \<Rightarrow> nat option" where
  "event_time [] i = None"
| "event_time (e # es) i =
   (if fst e = i then Some (snd e)
    else case event_time es i of None \<Rightarrow> None | Some k \<Rightarrow> Some (k + snd e))"

value "event_time [(1, 5), (2, 5)] 1"
value "event_time [(1, 5), (2, 5)] 2"
value "event_time [(1, 5), (2, 5)] 3"

text \<open>Count the total time up to a certain index\<close>
fun watchdog_total_upto :: "watchdog_chain \<Rightarrow> nat \<Rightarrow> nat" where
  "watchdog_total_upto [] i = 0"
| "watchdog_total_upto ((evt_id, n) # rest) 0 = 0"
| "watchdog_total_upto ((evt_id, n) # rest) (Suc i) = n + watchdog_total_upto rest i"

value "watchdog_total_upto [(0, 1), (0, 2)] 0"
value "watchdog_total_upto [(0, 1), (0, 2)] 1"
value "watchdog_total_upto [(0, 1), (0, 2)] 2"

lemma watchdog_total_upto_0 [simp]:
  "watchdog_total_upto s 0 = 0"
  apply (cases s) by auto

lemma watchdog_total_upto_Suc:
  "i < length s \<Longrightarrow> watchdog_total_upto s (Suc i) = watchdog_total_upto s i + snd (s ! i)"
proof (induct s arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons pn tbl)
  then show ?case
    apply (cases pn) apply (cases i) by auto
qed

lemma watchdog_total_upto_take:
  "i \<le> length es \<Longrightarrow> watchdog_total_upto (take i es) i = watchdog_total_upto es i"
proof (induction es arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by auto
  next
    case (Suc i')
    show ?thesis
    proof (cases p)
      case (Pair k v)
      show ?thesis
        unfolding Pair Suc apply auto
        apply (rule Cons(1))
        using Cons(2) Suc by auto
    qed
  qed
qed

lemma event_time_Suc_None:
  "event_time (p # es) evt_id = None \<Longrightarrow> event_time es evt_id = None"
  apply auto apply (cases "fst p = evt_id") apply auto
  apply (cases "event_time es evt_id = None") by auto

lemma event_time_append1:
  "event_time es evt_id = None \<Longrightarrow>
   event_time (es @ es2) evt_id = (
     case event_time es2 evt_id of
       None \<Rightarrow> None
     | Some n \<Rightarrow> Some (n + watchdog_total_upto es (length es)))"
proof (induction es)
  case Nil
  show ?case
    apply (cases "event_time es2 evt_id") by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    have b1: "k \<noteq> evt_id"
      using Cons(2) unfolding Pair by auto
    have b2: "event_time es evt_id = None"
      using event_time_Suc_None Cons(2) by auto
    have b3: "event_time (es @ es2) evt_id =
      (case event_time es2 evt_id of
             None \<Rightarrow> None 
           | Some n \<Rightarrow> Some (n + watchdog_total_upto es (length es)))"
      using Cons(1) b2 by auto
    show ?thesis
      unfolding Pair using b1 b3
      apply (cases "event_time es2 evt_id") by auto
  qed
qed

lemma event_time_append2:
  "event_time es evt_id = Some n \<Longrightarrow>
   event_time (es @ es2) evt_id = Some n"
proof (induction es arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    show ?thesis
    proof (cases "k = evt_id")
      case True
      then show ?thesis
        unfolding Pair using Cons.prems Pair by auto
    next
      case False
      have b1: "event_time es evt_id = Some (n - v)" "n \<ge> v"
        using Cons(2) unfolding Pair using False apply auto
         apply (cases "event_time es evt_id") apply auto
        apply (cases "event_time es evt_id") by auto
      have b2: "event_time (es @ es2) evt_id = Some (n - v)"
        using Cons(1) b1 by auto
      show ?thesis
        unfolding Pair by (auto simp add: False b1 b2)
    qed
  qed
qed

lemma event_time_take_None:
  "event_time es evt_id = None \<Longrightarrow> event_time (take i es) evt_id = None"
proof (induction es arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by auto
  next
    case (Suc i')
    have a1: "event_time es evt_id = None"
      using Cons(2) event_time_Suc_None by auto
    have a2: "event_time (take i' es) evt_id = None"
      using a1 Cons(1) by auto
    show ?thesis
      unfolding Suc apply (auto simp add: a2)
      using Cons(2) by auto
  qed
qed

lemma event_time_take_Some:
  assumes "event_time (take i es) evt_id = Some n"
  shows "event_time es evt_id = Some n"
proof -
  have a1: "es = (take i es) @ (drop i es)"
    by auto
  show ?thesis
    apply (subst a1) apply (rule event_time_append2)
    using assms by auto
qed

subsection \<open>Validity properties\<close>

text \<open>Invariant to be maintained between operations:
  number of times each event ID appears is at most one.
\<close>
fun occurs_atmost_one :: "watchdog_chain \<Rightarrow> task_id \<Rightarrow> bool" where
  "occurs_atmost_one [] evt_id = True"
| "occurs_atmost_one ((k, v) # es) evt_id = 
    (if k = evt_id then event_time es evt_id = None else occurs_atmost_one es evt_id)"

text \<open>Invariant to be maintained between operations:
  if watchdog is nonempty, then the first time value is nonzero.
\<close>
definition valid_watchdog :: "watchdog_chain \<Rightarrow> bool" where
  "valid_watchdog es \<longleftrightarrow>
    (length es > 0 \<longrightarrow> snd (es ! 0) > 0) \<and>
    (\<forall>evt_id. occurs_atmost_one es evt_id)"

lemma occurs_atmost_one_None:
  "event_time es evt_id = None \<Longrightarrow> occurs_atmost_one es evt_id"
  apply (induction es) apply auto
  subgoal for i n es'
    apply (cases "event_time es' evt_id") by auto
  done

lemma occurs_atmost_one_Cons:
  "occurs_atmost_one (e # es) evt_id \<Longrightarrow> occurs_atmost_one es evt_id"
  apply (cases e) apply auto
  subgoal for i n
    apply (cases "i = evt_id")
    by (auto simp add: occurs_atmost_one_None)
  done

subsection \<open>Add position\<close>

text \<open>Preparation for watchdog_add: determine the position to add an event.\<close>
fun watchdog_add_pos :: "watchdog_chain \<Rightarrow> nat \<Rightarrow> nat" where
  "watchdog_add_pos [] n = 0"
| "watchdog_add_pos ((ev, k) # rest) n =
    (if n > k then 1 + watchdog_add_pos rest (n - k)
     else 0)"

value "watchdog_add_pos [(0, 1), (0, 2)] 1"
value "watchdog_add_pos [(0, 1), (0, 2)] 2"
value "watchdog_add_pos [(0, 1), (0, 2)] 4"

lemma watchdog_add_pos_prop1:
  "watchdog_add_pos s n \<le> length s"
  apply (induct s arbitrary: n) by auto

lemma watchdog_add_pos_prop2:
  "n > 0 \<Longrightarrow> watchdog_add_pos s n = length s \<Longrightarrow> n > watchdog_total_upto s (length s)"
proof (induct s arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons p s)
  show ?case
  proof (cases p)
    case (Pair ev k)
    have a1: "(if k < n then 1 + watchdog_add_pos s (n - k) else 0) = Suc (length s)"
      using Cons(3) unfolding Pair by auto
    have a2: "k < n"
      using a1 by (meson nat.distinct(1))
    have a3: "watchdog_add_pos s (n - k) = length s"
      using a1 a2 by auto
    have a4: "watchdog_total_upto s (length s) < n - k"
      using Cons(1) a2 a3 by auto
    show ?thesis
      apply (auto simp add: Pair) using a2 a4 by auto 
  qed
qed

lemma watchdog_add_pos_prop3:
  "n > 0 \<Longrightarrow> watchdog_add_pos s n < length s \<Longrightarrow>
   n \<le> watchdog_total_upto s (Suc (watchdog_add_pos s n)) \<and>
   n > watchdog_total_upto s (watchdog_add_pos s n)"
proof (induct s arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons p rest)
  show ?case
  proof (cases p)
    case (Pair ev k)
    show ?thesis
      apply (auto simp add: Pair)
        apply (smt Cons.hyps Cons.prems(2) One_nat_def Pair add.commute le_add_diff_inverse
                   le_neq_implies_less less_imp_le_nat list.size(4) nat_add_left_cancel_le
                   nat_neq_iff watchdog_add_pos.simps(2) zero_less_diff)
       apply (metis Cons.hyps le_add_diff_inverse le_neq_implies_less less_imp_le_nat
                   nat_add_left_cancel_less watchdog_add_pos_prop1 watchdog_add_pos_prop2 zero_less_diff)
      by (simp add: Cons.prems(1))
  qed
qed

lemma watchdog_add_fun_range:
  "n > 0 \<Longrightarrow> i < Suc (watchdog_add_pos s n) \<Longrightarrow> n > watchdog_total_upto s i \<and> i \<le> length s"
proof (induct s arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons p s)
  show ?case
  proof (cases p)
    case (Pair ev k)
    have a1: "i < Suc (if k < n then 1 + watchdog_add_pos s (n - k) else 0)"
      using Cons(3) by (auto simp add: Pair)
    show ?thesis
    proof (cases i)
      case 0
      then show ?thesis
        by (auto simp add: Pair Cons)
    next
      case (Suc i')
      have a2: "k < n"
        using a1 Suc less_one by fastforce
      have a3: "i < Suc (1 + watchdog_add_pos s (n - k))"
        using a1 a2 by auto
      have b1: "i' < Suc (watchdog_add_pos s (n - k))"
        using a3 Suc by auto
      have b2: "watchdog_total_upto s i' < n - k \<and> i' \<le> length s"
        using Cons(1)[of "n - k" i'] b1 a2 by auto
      show ?thesis
        apply (auto simp add: Pair Suc)
        using b2 by auto
    qed      
  qed
qed

lemma watchdog_add_fun_range2:
  "n > 0 \<Longrightarrow> i = Suc (watchdog_add_pos s n) \<Longrightarrow>
   (n > watchdog_total_upto s (length s) \<and> i = Suc (length s)) \<or>
   (n \<le> watchdog_total_upto s i \<and> n > watchdog_total_upto s (watchdog_add_pos s n) \<and> i \<le> length s)"
proof (induct s arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons p s)
  show ?case
  proof (cases p)
    case (Pair ev k)
    have a1: "i = Suc (if k < n then 1 + watchdog_add_pos s (n - k) else 0)"
      using Cons(3) by (auto simp add: Pair)
    show ?thesis
    proof (cases i)
      case 0
      then show ?thesis using a1 by auto
    next
      case (Suc i')
      have b1: "i' = (if k < n then 1 + watchdog_add_pos s (n - k) else 0)"
        using a1 Suc by auto
      show ?thesis
      proof (cases i')
        case 0
        have "k \<ge> n"
          using b1 0 not_le by fastforce
        then show ?thesis
          by (metis 0 Cons.prems(1,2) Suc_inject Suc_leI length_Cons Suc watchdog_add_pos_prop3 zero_less_Suc)
      next
        case (Suc i2)
        have c1: "k < n"
          using b1 Suc by (meson nat.distinct(1))
        have c2: "i' = Suc (watchdog_add_pos s (n - k))"
          using b1 c1 by auto
        have c3: "watchdog_total_upto s (length s) < n - k \<and> i' = Suc (length s) \<or> n - k \<le> watchdog_total_upto s i' \<and> i' \<le> length s"
          using Cons(1)[of "n - k" i'] c1 c2 by auto
        have c4: "k + watchdog_total_upto s (length s) < n \<longleftrightarrow> watchdog_total_upto s (length s) < n - k"
          using c1 by auto
        have c5: "i = Suc (Suc (length s)) \<longleftrightarrow> i' = Suc (length s)"
          using \<open>i = Suc i'\<close> by auto
        show ?thesis
          apply (auto simp add: c4 c5)
             apply (metis (mono_tags, lifting) Cons.prems(1) Cons.prems(2) Pair Suc_inject a1 c1 c2 c3 c4
              le_imp_less_Suc length_Cons plus_1_eq_Suc watchdog_add_pos_prop3 watchdog_total_upto.simps(3))
          using Cons.prems(2) a1 c1 c2 c3 watchdog_add_pos_prop3 apply auto[1]
           apply (simp add: Cons.prems(1) Cons.prems(2) watchdog_add_fun_range)
            apply (metis Cons.prems(1) Cons.prems(2) not_le watchdog_add_fun_range)
          using Cons.prems(1) watchdog_add_fun_range apply blast
          using a1 c2 c3 plus_1_eq_Suc by auto
      qed
    qed
  qed
qed

subsection \<open>Add function\<close>

text \<open>Add the given event to the chain. This requires modifying the event
  immediately after the added event. For example, adding (1, 7) to the
  chain [(1, 5), (1, 5)] yields [(1, 5), (1, 2), (1, 3)].

  Note events are triggered in the first-in-first-out (FIFO) order.
  For example, if the current chain is:

  [(1, 10), (1, 5), (2, 0), (3, 5)],

  then the new event (1, 15) should be added after (2, 0).
\<close>
fun watchdog_add :: "task_id \<Rightarrow> nat \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "watchdog_add evt_id n [] = [(evt_id, n)]"
| "watchdog_add evt_id n ((k, v) # es) =
    (if n > v then
       (k, v) # watchdog_add evt_id (n - v) es
     else
       (evt_id, n) # (k, v - n) # es)"

value "watchdog_add 1 15 [(1, 10), (1, 5), (2, 0), (3, 5)]"
value "watchdog_add 1 17 [(1, 10), (1, 5), (2, 0), (3, 5)]"

theorem watchdog_add_prop1:
  "n > watchdog_total_upto es (length es) \<Longrightarrow>
   watchdog_add evt_id n es = es @ [(evt_id, n - watchdog_total_upto es (length es))]"
proof (induction es arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  show ?case
  proof (cases e)
    case (Pair k v)
    have a1: "v < n"
      using Cons(2) unfolding Pair by auto
    have a2: "watchdog_total_upto es (length es) < n - v"
      using Cons(2) unfolding Pair by auto
    have a3: "watchdog_add evt_id (n - v) es = es @ [(evt_id, n - v - watchdog_total_upto es (length es))]"
      using Cons(1) a2 by auto
    show ?thesis
      unfolding Pair using a1 a3 by auto
  qed
qed

theorem watchdog_add_prop2:
  "n > 0 \<Longrightarrow> i < length es \<Longrightarrow>
   i = watchdog_add_pos es n \<Longrightarrow> 
   watchdog_add evt_id n es =
    (take i es) @ [(evt_id, n - watchdog_total_upto es i)] @
    (drop i (es[i := (fst (es ! i), snd (es ! i) - (n - watchdog_total_upto es i))]))"
proof (induction es arbitrary: i n)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  show ?case
  proof (cases e)
    case (Pair k v)
    show ?thesis
    proof (cases i)
      case 0
      have "v \<ge> n"
        using Cons(4) unfolding Pair 0
        using Cons.prems(3) Pair less_Suc_eq_0_disj old.prod.exhaust by fastforce
      then show ?thesis unfolding Pair 0 by auto
    next
      case (Suc i')
      show ?thesis
      proof (cases "v < n")
        case True
        have a1: "n - v > 0"
          using True by auto
        have a2: "i' < length es"
          using Cons(3) Suc by auto
        have a3: "i' = watchdog_add_pos es (n - v)"
          using Cons(4) unfolding Pair using True Suc by auto
        have a4: "watchdog_add evt_id (n - v) es = take i' es @
                    [(evt_id, (n - v) - watchdog_total_upto es i')] @
                    drop i' (es[i' := (fst (es ! i'), snd (es ! i') - ((n - v) - watchdog_total_upto es i'))])"
          using Cons(1)[OF a1 a2 a3] by auto
        show ?thesis
          by (simp add: Pair True a4 local.Suc)
      next
        case False
        then show ?thesis
          by (simp add: Cons.prems(3) Pair)
      qed
    qed
  qed
qed

theorem watchdog_add1:
  assumes "event_time es evt_id = None"
    and "n > 0"
  shows "event_time (watchdog_add evt_id n es) evt_id = Some n"
proof -
  let ?i="watchdog_add_pos es n"
  have a1: "(n > watchdog_total_upto es (length es) \<and> Suc ?i = Suc (length es)) \<or>
            (n \<le> watchdog_total_upto es (Suc ?i) \<and> n > watchdog_total_upto es ?i \<and> Suc ?i \<le> length es)"
    using watchdog_add_fun_range2 assms by auto
  have a2: ?thesis
    if "watchdog_total_upto es (length es) < n" "Suc ?i = Suc (length es)"
    unfolding watchdog_add_prop1[OF that(1)]
    using assms(1) that(1) event_time_append1 by auto
  have a3: ?thesis
    if "n \<le> watchdog_total_upto es (Suc ?i)" "n > watchdog_total_upto es ?i" "Suc ?i \<le> length es"
  proof -
    have b1: "?i < length es"
      using that(3) by auto
    have b2: "watchdog_add evt_id n es = take ?i es @
              [(evt_id, n - watchdog_total_upto es ?i)] @
              drop ?i (es[?i := (fst (es ! ?i), snd (es ! ?i) - (n - watchdog_total_upto es ?i))])"
      using watchdog_add_prop2[OF assms(2) b1] by auto
    have b3: "event_time (take ?i es) evt_id = None"
      using event_time_take_None assms(1) by auto
    have b4: "watchdog_total_upto (take ?i es) (length (take ?i es)) = watchdog_total_upto es ?i"
      by (metis b1 leD length_take less_or_eq_imp_le min_def watchdog_total_upto_take)
    show ?thesis
      unfolding b2 using event_time_append1[OF b3]
      unfolding b4 using that(2) by auto
  qed
  show ?thesis
    using a1 a2 a3 by auto
qed

lemma event_time_decr0_None:
  assumes "event_time es evt_id = None"
    and "length es > 0"
  shows "event_time (es[0 := (fst (es ! 0), snd (es ! 0) - k)]) evt_id = None"
proof (cases es)
  case Nil
  then show ?thesis by auto
next
  case (Cons p es')
  show ?thesis
  proof (cases p)
    case (Pair k v)
    have a1: "k \<noteq> evt_id" "event_time es' evt_id = None"
      using assms unfolding Cons Pair
      using event_time_Suc_None by auto
    show ?thesis
      unfolding Cons Pair by (auto simp add: a1)
  qed
qed

lemma event_time_decr0_Some:
  assumes "event_time es evt_id = Some a"
    and "length es > 0"
    and "k \<le> snd (es ! 0)"
  shows "event_time (es[0 := (fst (es ! 0), snd (es ! 0) - k)]) evt_id = Some (a - k)"
proof (cases es)
  case Nil
  then show ?thesis using assms(2) by auto
next
  case (Cons p es')
  show ?thesis
  proof (cases p)
    case (Pair k v)
    show ?thesis
    proof (cases "k = evt_id")
      case True
      have "v = a"
        using assms(1) unfolding Cons Pair True by auto
      then show ?thesis
        unfolding Pair Cons True by auto
    next
      case False
      have "event_time es' evt_id = Some (a - v)" "a \<ge> v"
        using assms(1) unfolding Cons Pair using False apply auto
         apply (cases "event_time es' evt_id") apply auto
        apply (cases "event_time es' evt_id") by auto
      then show ?thesis
        unfolding Pair Cons using False assms(3)
        by (simp add: Pair local.Cons)
    qed
  qed
qed

lemma watchdog_add2_helper1:
  assumes "i < length es"
    and "event_time (drop i es) evt_id = None"
  shows "event_time (drop i (es[i := (fst (es ! i), snd (es ! i) - k)])) evt_id = None"
proof -
  let ?es'="drop i es"
  have a1: "drop i (es[i := (fst (es ! i), snd (es ! i) - k)]) =
            ?es'[0 := (fst (?es' ! 0), snd (?es' ! 0) - k)]"
    by (simp add: assms(1) drop_update_swap le_eq_less_or_eq)
  show ?thesis
    unfolding a1
    apply (rule event_time_decr0_None)
    using assms by auto
qed

lemma watchdog_add2_helper2:
  assumes "i < length es"
    and "event_time (drop i es) evt_id = Some a"
    and "k \<le> snd (es ! i)"
  shows "event_time (drop i (es[i := (fst (es ! i), snd (es ! i) - k)])) evt_id = Some (a - k)"
proof -
  let ?es'="drop i es"
  have a1: "drop i (es[i := (fst (es ! i), snd (es ! i) - k)]) =
            ?es'[0 := (fst (?es' ! 0), snd (?es' ! 0) - k)]"
    by (simp add: assms(1) drop_update_swap le_eq_less_or_eq)
  show ?thesis
    unfolding a1
    apply (rule event_time_decr0_Some)
    using assms by auto
qed

theorem watchdog_add2:
  assumes "evt_id \<noteq> evt_id2"
    and "n > 0"
  shows "event_time (watchdog_add evt_id n es) evt_id2 = event_time es evt_id2"
proof -
  let ?i="watchdog_add_pos es n"
  have a1: "(n > watchdog_total_upto es (length es) \<and> Suc ?i = Suc (length es)) \<or>
            (n \<le> watchdog_total_upto es (Suc ?i) \<and> n > watchdog_total_upto es ?i \<and> Suc ?i \<le> length es)"
    using watchdog_add_fun_range2 assms by auto
  have a2: ?thesis
    if "n > watchdog_total_upto es (length es)" "Suc ?i = Suc (length es)"
    unfolding watchdog_add_prop1[OF that(1)]
    apply (cases "event_time es evt_id2 = None")
    by (auto simp add: event_time_append1 event_time_append2 assms)
  have a3: ?thesis
    if "n \<le> watchdog_total_upto es (Suc ?i)" "n > watchdog_total_upto es ?i" "Suc ?i \<le> length es"
  proof -
    have b1: "?i < length es"
      using that(3) by auto
    have b2: "watchdog_add evt_id n es = take ?i es @
                [(evt_id, n - watchdog_total_upto es ?i)] @
                drop ?i (es[?i := (fst (es ! ?i), snd (es ! ?i) - (n - watchdog_total_upto es ?i))])"
      using watchdog_add_prop2[OF assms(2) b1] by auto
    show ?thesis
    proof (cases "event_time (take ?i es) evt_id2")
      case None
      note None1 = None
      show ?thesis
      proof (cases "event_time (drop ?i es) evt_id2")
        case None
        have c1: "event_time (drop ?i (es[?i := (fst (es ! ?i), snd (es ! ?i) - k)])) evt_id2 = None" for k
          by (rule watchdog_add2_helper1[OF b1 None])
        have c2: "es = take ?i es @ drop ?i es"
          by auto
        have c3: "event_time es evt_id2 = None"
          apply (subst c2) apply (subst event_time_append1[OF None1])
          by (auto simp add: None)
        show ?thesis
          unfolding b2 event_time_append1[OF None1]
          by (auto simp add: assms(1) c1 c3)
      next
        case (Some a)
        have ineq: "n - watchdog_total_upto es ?i \<le> snd (es ! ?i)"
          using that(1) unfolding watchdog_total_upto_Suc[OF b1]
          by auto
        have ineq2: "a \<ge> n - watchdog_total_upto es ?i"
        proof -
          have c1: "drop ?i es = (es ! ?i) # drop (?i + 1) es"
            using b1 by (simp add: Cons_nth_drop_Suc)
          have "a \<ge> snd (es ! ?i)"
            using Some(1) unfolding c1 apply auto
            apply (cases "fst (es ! ?i) = evt_id2") apply auto
            apply (cases "event_time (drop (Suc ?i) es) evt_id2") by auto
          then show ?thesis
            using ineq by auto
        qed
        have c1: "event_time (drop ?i (es[?i := (fst (es ! ?i), snd (es ! ?i) - k)])) evt_id2 = Some (a - k)"
          if "k \<le> snd (es ! ?i)" for k
          by (rule watchdog_add2_helper2[OF b1 Some that])
        have c2: "es = take ?i es @ drop ?i es"
          by auto
        have c3: "watchdog_total_upto (take ?i es) (min (length es) ?i) = watchdog_total_upto es ?i"
          by (simp add: min.absorb2 watchdog_add_pos_prop1 watchdog_total_upto_take)
        have c4: "event_time es evt_id2 = Some (a + watchdog_total_upto es ?i)"
          apply (subst c2) apply (subst event_time_append1[OF None1])
          by (auto simp add: Some c3)
        show ?thesis
          unfolding b2 event_time_append1[OF None1]
          apply (auto simp add: assms(1) c1[OF ineq] c3 c4)
          using ineq2 by auto
      qed        
    next
      case (Some a)
      show ?thesis
        unfolding b2 event_time_append2[OF Some]
        using event_time_take_Some[OF Some] by auto
    qed
  qed
  show ?thesis
    using a1 a2 a3 by auto
qed

lemma watchdog_add_full:
  assumes "event_time es evt_id = None"
    and "n > 0"
  shows "event_time (watchdog_add evt_id n es) = event_time es(evt_id \<mapsto> n)"
  apply (rule ext)
  subgoal for evt_id'
    apply auto
     apply (rule watchdog_add1[OF assms])
    apply (rule watchdog_add2)
    using assms(2) by auto
  done

lemma watchdog_add_valid:
  assumes "event_time es evt_id = None"
    and "n > 0"
    and "valid_watchdog es"
  shows "valid_watchdog (watchdog_add evt_id n es)"
proof -
  have a: "\<forall>i. occurs_atmost_one es i \<Longrightarrow> event_time es evt_id = None \<Longrightarrow>
           occurs_atmost_one (watchdog_add evt_id n es) evt_id'" for evt_id'
  proof (induction es arbitrary: n)
    case Nil
    then show ?case by auto
  next
    case (Cons pair es')
    show ?case
    proof (cases pair)
      case (Pair p n')
      have a1: "\<forall>a. occurs_atmost_one es' a"
        using Cons.prems(1) occurs_atmost_one_Cons by blast
      have a2: "event_time es' evt_id = None"
        using Cons.prems(2) event_time_Suc_None by auto
      have a3: "occurs_atmost_one (watchdog_add evt_id n'' es') evt_id'" for n''
        using Cons(1) a1 a2 by auto
      show ?thesis
        unfolding Pair watchdog_add.simps
        apply (cases "n' < n")
        subgoal apply (auto simp add: a3)
          by (metis Cons(2,3) Pair event_time.simps(2) fst_conv occurs_atmost_one.simps(2)
                    option.distinct(1) watchdog_add2 zero_less_diff)
        subgoal apply auto
          using Cons.prems(2) Pair apply auto[1]
          using Cons.prems(1) Pair apply auto[1]
          apply (cases "event_time es' evt_id'")
          using Cons Pair by auto
        done
    qed
  qed
  show ?thesis
    unfolding valid_watchdog_def
    apply auto
    subgoal
      apply (cases es)
      using assms(3) by (auto simp add: valid_watchdog_def assms(2))
    subgoal for evt_id'
      using a assms by (auto simp add: valid_watchdog_def)
    done
qed

subsection \<open>Extract zero function\<close>

text \<open>Extract zero from head of watchdog chain. Helper function for watchdog_tick\<close>
fun extract_zero :: "watchdog_chain \<Rightarrow> task_id list \<times> watchdog_chain" where
  "extract_zero [] = ([], [])"
| "extract_zero (e # es) =
   (if snd e = 0 then
      let (out_es, es') = extract_zero es in
      (fst e # out_es, es')
    else
      ([], e # es))"

value "extract_zero [(0, 10), (1, 5)]"
value "extract_zero [(1, 0), (0, 10), (1, 5)]"
value "extract_zero [(1, 0), (2, 0), (0, 10), (1, 0)]"

lemma extract_zero_None:
  "event_time es evt_id = None \<Longrightarrow>
   evt_id \<notin> set (fst (extract_zero es)) \<and> event_time (snd (extract_zero es)) evt_id = None"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    have a1: "k \<noteq> evt_id"
      using Cons(2) unfolding Pair by auto
    have a2: "event_time es evt_id = None"
      using event_time_Suc_None[OF Cons(2)] by auto
    have a3: "evt_id \<notin> set (fst (extract_zero es))" "event_time (snd (extract_zero es)) evt_id = None"
      using a2 Cons(1) by auto
    show ?thesis
      unfolding Pair using a1 Cons(1) apply (auto simp add: a2)
       apply (cases "extract_zero es") using a3 apply auto
      apply (cases "extract_zero es") by auto
  qed
qed

lemma extract_zero1:
  "occurs_atmost_one es evt_id \<Longrightarrow>
   event_time es evt_id = Some 0 \<Longrightarrow>
   evt_id \<in> set (fst (extract_zero es)) \<and> event_time (snd (extract_zero es)) evt_id = None"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    have "v = 0"
      using Cons(3) unfolding Pair apply auto
      apply (cases "k = evt_id") apply auto
      apply (cases "event_time es evt_id") by auto 
    show ?thesis
    proof (cases "k = evt_id")
      case True
      have a1: "event_time es evt_id = None"
        using Cons(2) unfolding Pair using True by auto
      show ?thesis unfolding Pair using \<open>v = 0\<close> apply auto
         apply (cases "extract_zero es") using True apply auto
        apply (cases "extract_zero es") using True apply auto
        using a1 extract_zero_None snd_conv by fastforce
    next
      case False
      have a1: "event_time es evt_id = Some 0"
        using Cons(3) unfolding Pair using False apply auto
        apply (cases "event_time es evt_id") by auto
      have a2: "occurs_atmost_one es evt_id"
        using Cons(2) unfolding Pair using False by auto
      have a3: "evt_id \<in> set (fst (extract_zero es))" "event_time (snd (extract_zero es)) evt_id = None"
        using Cons(1) a1 a2 by auto
      have a4: "v = 0"
        using Cons(3) unfolding Pair using False apply auto
        apply (cases "event_time es evt_id") by auto
      show ?thesis
        unfolding Pair apply (auto simp add: a4)
         apply (cases "extract_zero es") using a3 apply auto
        apply (cases "extract_zero es") by auto
    qed
  qed
qed

lemma extract_zero2:
  "occurs_atmost_one es evt_id \<Longrightarrow>
   event_time es evt_id = Some n \<Longrightarrow>
   n > 0 \<Longrightarrow>
   evt_id \<notin> set (fst (extract_zero es)) \<and> event_time (snd (extract_zero es)) evt_id = Some n"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    show ?thesis
    proof (cases "k = evt_id")
      case True
      have a1: "v = n"
        using Cons(3) unfolding Pair using True by auto
      show ?thesis
        using True unfolding Pair using a1 Cons(4) by auto
    next
      case False
      note False1 = False
      have a1: "occurs_atmost_one es evt_id"
        using Cons(2) unfolding Pair using False by auto
      have a2: "event_time es evt_id = Some (n - v)" "n \<ge> v"
        using Cons(3) unfolding Pair using False apply auto
         apply (cases "event_time es evt_id") apply auto
        apply (cases "event_time es evt_id") by auto
      show ?thesis
      proof (cases "v = 0")
        case True
        have b1: "evt_id \<notin> set (fst (extract_zero es))" "event_time (snd (extract_zero es)) evt_id = Some n"
          using Cons(1)[OF a1] a2 Cons(4) True by auto
        show ?thesis unfolding Pair using False1 True apply auto
           apply (cases "extract_zero es") using b1 apply auto
          apply (cases "extract_zero es") by auto
      next
        case False
        show ?thesis
          unfolding Pair using False False1 a2 by auto
      qed
    qed
  qed
qed

fun count_zero :: "watchdog_chain \<Rightarrow> nat" where
  "count_zero [] = 0"
| "count_zero ((k, v) # es) = (if v = 0 then 1 + count_zero es else 0)"

lemma count_zero_length:
  "count_zero es \<le> length es"
  apply (induction es) by auto

lemma count_zero_iff:
  "i < count_zero es \<Longrightarrow> i < length es \<and> snd (es ! i) = 0"
proof (induction es arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
    apply (cases p) apply auto
    using Cons.prems count_zero_length less_le_trans apply force
    by (metis Cons.IH Cons.prems One_nat_def Suc_diff_Suc Suc_less_eq count_zero.simps(2) diff_zero
              not_gr_zero not_less_zero nth_Cons' plus_1_eq_Suc snd_conv)
qed

lemma count_zero_iff2:
  "i = count_zero es \<Longrightarrow> i = length es \<or> snd (es ! i) \<noteq> 0"
proof (induction es arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  then show ?case
    apply (cases p) by auto
qed

lemma count_zero_Suc:
  "i \<le> count_zero es \<Longrightarrow> i < length es \<Longrightarrow> snd (es ! i) = 0 \<Longrightarrow> i < count_zero es"
  using count_zero_iff2[of i es] by fastforce

lemma extract_zero_array:
  "extract_zero es = (map fst (take (count_zero es) es), drop (count_zero es) es)"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es')
  show ?case
    apply auto
      apply (metis (no_types, lifting) Cons.IH count_zero.simps(2) drop_Suc_Cons list.simps(9)
                   old.prod.case plus_1_eq_Suc surjective_pairing take_Suc_Cons)
    using count_zero_iff apply fastforce
    by (metis count_zero_iff drop_Cons' neq0_conv nth_Cons_0)
qed

subsection \<open>Decrement-head operation\<close>

text \<open>Decrement the head of the chain by n. Helper function for tick\<close>
fun decr_head :: "nat \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "decr_head n [] = []"
| "decr_head n ((k, v) # es) = (k, v - n) # es"

lemma decr_head_atmost_one:
  "occurs_atmost_one es evt_id \<Longrightarrow>
   occurs_atmost_one (decr_head n es) evt_id"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    show ?thesis
      unfolding Pair using Cons(2) unfolding Pair by auto
  qed  
qed

lemma decr_head_None:
  "event_time es evt_id = None \<Longrightarrow>
   event_time (decr_head n es) evt_id = None"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    have a1: "k \<noteq> evt_id"
      using Cons(2) unfolding Pair by auto
    have a2: "event_time es evt_id = None"
      using Cons(2) unfolding Pair using a1 apply auto
      apply (cases "event_time es evt_id") by auto
    show ?thesis
      unfolding Pair using a1 a2 by auto
  qed
qed

lemma decr_head_Some:
  "event_time es evt_id = Some a \<Longrightarrow>
   n \<le> snd (es ! 0) \<Longrightarrow>
   event_time (decr_head n es) evt_id = Some (a - n)"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons p es)
  show ?case
  proof (cases p)
    case (Pair k v)
    show ?thesis
    proof (cases "k = evt_id")
      case True
      have "v = a"
        using Cons(2) unfolding Pair using True by auto
      then show ?thesis
        unfolding Pair using True by auto
    next
      case False
      have a1: "event_time es evt_id = Some (a - v)" "v \<le> a"
        using Cons(2) unfolding Pair using False apply auto
         apply (cases "event_time es evt_id") apply auto
        apply (cases "event_time es evt_id") by auto
      show ?thesis
        using Cons(3) unfolding Pair using False a1 by auto
    qed
  qed
qed

subsection \<open>Tick operation\<close>

text \<open>Perform one tick on the watchdog chain. Return the list of
  events triggered.\<close>
definition watchdog_tick :: "watchdog_chain \<Rightarrow> task_id list \<times> watchdog_chain" where
  "watchdog_tick es = extract_zero (decr_head 1 es)"

value "watchdog_tick [(1, 10)]"
value "watchdog_tick [(1, 1), (2, 10)]"
value "watchdog_tick [(1, 1), (2, 0), (0, 5)]"

theorem watchdog_tick_None:
  assumes "event_time es evt_id = None"
  shows "evt_id \<notin> set (fst (watchdog_tick es)) \<and>
         event_time (snd (watchdog_tick es)) evt_id = None"
  unfolding watchdog_tick_def
  apply (rule extract_zero_None)
  by (rule decr_head_None[OF assms(1)])

theorem watchdog_tick_triv:
  assumes "valid_watchdog es"
  shows "event_time es evt_id \<noteq> Some 0"
proof (cases es)
  case Nil
  then show ?thesis by auto
next
  case (Cons p es')
  show ?thesis
  proof (cases p)
    case (Pair i n)
    have a: "n > 0"
      using assms(1) unfolding valid_watchdog_def Cons Pair by auto
    show ?thesis
      unfolding Cons Pair using a apply auto
      apply (cases "event_time es' evt_id")
      by auto
  qed
qed

theorem watchdog_tick1:
  assumes "valid_watchdog es"
    and "event_time es evt_id = Some 1"
  shows "evt_id \<in> set (fst (watchdog_tick es)) \<and>
         event_time (snd (watchdog_tick es)) evt_id = None"
proof -
  have a1: "event_time (decr_head 1 es) evt_id = Some (1 - 1)"
    apply (rule decr_head_Some)
    using assms(1,2) unfolding valid_watchdog_def by auto
  show ?thesis
    unfolding watchdog_tick_def
    apply (rule extract_zero1)
     apply (rule decr_head_atmost_one)
    using a1 assms(1) unfolding valid_watchdog_def by auto
qed

theorem watchdog_tick2:
  assumes "valid_watchdog es"
    and "event_time es evt_id = Some n"
    and "n > 1"
  shows "evt_id \<notin> set (fst (watchdog_tick es)) \<and>
         event_time (snd (watchdog_tick es)) evt_id = Some (n - 1)"
proof -
  have nonNil: "length es \<noteq> 0"
    using assms(2) by auto
  show ?thesis
    unfolding watchdog_tick_def
    apply (rule extract_zero2)
      apply (rule decr_head_atmost_one)
    using assms(1) unfolding valid_watchdog_def apply auto[1]
     apply (rule decr_head_Some[OF assms(2)])
    using assms(1,3) unfolding valid_watchdog_def
    using nonNil by auto
qed

lemma extract_zero_valid:
  "\<forall>i. occurs_atmost_one es i \<Longrightarrow> valid_watchdog (snd (extract_zero es))"
proof (induction es)
  case Nil
  then show ?case by (auto simp add: valid_watchdog_def)
next
  case (Cons pair es)
  show ?case
  proof (cases pair)
    case (Pair p n)
    show ?thesis
      apply (auto simp add: Cons Pair)
       apply (cases "extract_zero es")
       apply auto
      using Cons.IH Cons.prems occurs_atmost_one_Cons apply fastforce
      using Cons.prems Pair valid_watchdog_def by auto
  qed
qed

theorem watchdog_tick_valid:
  assumes "valid_watchdog es"
  shows "valid_watchdog (snd (watchdog_tick es))"
proof -
  have a: "occurs_atmost_one (decr_head 1 es) evt_id" for evt_id
    apply (rule decr_head_atmost_one)
    using assms unfolding valid_watchdog_def by auto
  show ?thesis
    unfolding watchdog_tick_def
    apply (rule extract_zero_valid)
    using a by auto
qed

theorem watchdog_tick_distinct:
  "\<forall>i. occurs_atmost_one es i \<Longrightarrow> distinct (fst (extract_zero es))"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons pair es')
  show ?case
  proof (cases pair)
    case (Pair p n)
    have a: "\<forall>a. occurs_atmost_one es' a"
      using Cons.prems occurs_atmost_one_Cons by blast
    have b: "distinct (fst (extract_zero es'))"
      using Cons(1) a by auto
    show ?thesis
      unfolding Pair
      apply (cases "extract_zero es'")
      using b apply auto
      by (metis Cons.prems Pair extract_zero_None fst_conv occurs_atmost_one.simps(2))
  qed
qed

subsection \<open>Increment-head operation\<close>

text \<open>Increment the head of the chain by n. Helper function for watchdog_remove\<close>
fun increment_head :: "nat \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "increment_head n [] = []"
| "increment_head n ((k, v) # es) = (k, v + n) # es"

value "increment_head 3 []"
value "increment_head 3 [(1, 2), (2, 0)]"

subsection \<open>Remove operation\<close>

text \<open>Remove event i from the watchdog chain. Assume event i
  occurs (exactly) once in the chain.\<close>
fun watchdog_remove :: "task_id \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "watchdog_remove i [] = []"
| "watchdog_remove i (e # es) =
    (if fst e = i then
      increment_head (snd e) es
    else e # watchdog_remove i es)"

value "watchdog_remove 1 [(1, 5), (2, 5)]"
value "watchdog_remove 1 [(2, 5), (1, 5)]"
value "watchdog_remove 1 [(2, 5), (1, 5), (0, 5)]"

text \<open>Returns the location of first occurrence of evt_id.
  Returns None if evt_id is not found.
\<close>
fun watchdog_remove_pos :: "task_id \<Rightarrow> watchdog_chain \<Rightarrow> nat option" where
  "watchdog_remove_pos evt_id [] = None"
| "watchdog_remove_pos evt_id (p # s) =
    (if fst p = evt_id then Some 0
     else case watchdog_remove_pos evt_id s of
       None \<Rightarrow> None
     | Some i \<Rightarrow> Some (i + 1))"

lemma watchdog_remove_pos_Suc: 
  "0 < length s0 \<Longrightarrow>
   watchdog_remove_pos evt_id s0 = None \<longleftrightarrow>
   watchdog_remove_pos evt_id (tl s0) = None \<and> evt_id \<noteq> fst (hd s0)"
  by (induction s0, auto, force)

lemma watchdog_remove_pos_Suc1: 
  "0 < length s0 \<Longrightarrow>
   watchdog_remove_pos evt_id (tl s0) = Some i \<and> evt_id \<noteq> fst (hd s0) \<longleftrightarrow>
   watchdog_remove_pos evt_id s0 = Some (i + 1)"
proof (induct s0)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  then show ?case apply auto
     apply (cases "watchdog_remove_pos evt_id es") by auto
qed

lemma watchdog_remove_pos_le:
  "watchdog_remove_pos evt_id s0 = Some i \<Longrightarrow> i < length s0"
proof (induct s0 arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  show ?case
    apply (cases i)
     apply auto
    using Cons.hyps Cons.prems watchdog_remove_pos_Suc1 by fastforce
qed

lemma watchdog_remove_pos_Suc2:
  "0 < length s0 \<Longrightarrow>
   watchdog_remove_pos evt_id (tl s0) = Some i \<and> evt_id \<noteq> fst (hd s0) \<and> i < length (tl s0) \<longleftrightarrow>
   watchdog_remove_pos evt_id s0 = Some (i + 1)"
proof (induct s0 arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  show ?case 
    using Cons(2) watchdog_remove_pos_Suc1[of "s#es" "evt_id" "i"] watchdog_remove_pos_le[of "evt_id" "es" "i"]
    by auto
qed

lemma es_not_empty:
  "watchdog_remove_pos evt_id (s # es) = Some (Suc n) \<Longrightarrow> 0 < length es"
proof (induct n)
  case 0
  then show ?case apply auto
    by (metis "0.prems" watchdog_remove_pos_le length_Cons list.size(3) nat_less_le)
next
  case (Suc n)
  then show ?case apply auto
    by (metis Zero_not_Suc watchdog_remove_pos.simps(1) option.distinct(1) option.inject option.simps(4))
qed


lemma watchdog_remove_pos_evtid1:
  "watchdog_remove_pos evt_id s0 = None \<longleftrightarrow> (\<forall>i<length s0. evt_id \<noteq> fst (s0 ! i))"
proof (induct s0)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  have a1: "(watchdog_remove_pos evt_id (s # es) = None) = 
  (watchdog_remove_pos evt_id (es) = None \<and> evt_id \<noteq> fst (s))"
    using Cons watchdog_remove_pos_Suc 
    by auto
  have a2: "watchdog_remove_pos evt_id (s #es) = None \<Longrightarrow> (\<forall>i<length es. evt_id \<noteq> fst (es ! i))"
    using Cons a1 
    by force
  have a3: "watchdog_remove_pos evt_id (s #es) = None \<Longrightarrow>  (\<forall>i<length (s # es). evt_id \<noteq> fst ((s # es) ! i))"
    using Cons a1 a2
    by (simp add: nth_Cons')
  show ?case
    using Cons a1 a3
    by auto
qed

lemma watchdog_remove_pos_evtid2:
  "watchdog_remove_pos evt_id s0 = Some n \<longleftrightarrow>
   (\<forall>i<n. evt_id \<noteq> fst (s0 ! i)) \<and> evt_id = fst (s0 ! n) \<and> n < length s0"
proof (induct s0 arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  show ?case
  proof(induct n)
    case 0
    then show ?case 
      apply auto
      apply (cases "watchdog_remove_pos evt_id es")
      apply simp 
      by simp
  next
    case (Suc n)
    have a1: "(watchdog_remove_pos evt_id (s # es) = Some (Suc n)) =
    (watchdog_remove_pos evt_id (es) = Some n \<and> evt_id \<noteq> fst (s) \<and> n < length es)"
      using Cons watchdog_remove_pos_Suc2
      by (metis Suc_eq_plus1 length_Cons less_Suc_eq_0_disj list.sel(1) list.sel(3))
    have a2: "0 < length es \<Longrightarrow> (watchdog_remove_pos evt_id (s # es) = Some (Suc n)) =
    ((\<forall>i<n. evt_id \<noteq> fst (es ! i)) \<and> evt_id = fst (es ! n) \<and> evt_id \<noteq> fst (s) \<and> n < length es)"
      using a1 Cons by blast
    have a3: "0 < length es \<Longrightarrow> (watchdog_remove_pos evt_id (s # es) = Some (Suc n)) =
    ((\<forall>i<(Suc n). evt_id \<noteq> fst ((s # es) ! i)) \<and> evt_id = fst ((s # es) ! (Suc n)) \<and> n < length es)"
      using a2 
      by (metis less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc)
    have a4: "(watchdog_remove_pos evt_id (s # es) = Some (Suc n)) =
    ((\<forall>i<(Suc n). evt_id \<noteq> fst ((s # es) ! i)) \<and> evt_id = fst ((s # es) ! (Suc n)) \<and> n < length es)"
      using a3 es_not_empty
      by fastforce
    have a5: "(watchdog_remove_pos evt_id (s # es) = Some (Suc n)) =
    ((\<forall>i<(Suc n). evt_id \<noteq> fst ((s # es) ! i)) \<and> evt_id = fst ((s # es) ! (Suc n)) \<and> 
    (Suc n < length (s # es)) \<and> n < length es)"
      using a4 
      using Cons.hyps a1 es_not_empty by auto
    show ?case
      using a5 Cons Suc 
      by simp
  qed
qed

lemma watchdog_remove_pos_some_fst:
  "watchdog_remove_pos evt_id s0 = Some n \<Longrightarrow> \<forall>i. i < n \<longrightarrow> fst (s0 ! i) \<noteq> fst (s0 ! n)"
proof (induct s0 arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons s es)
  then show ?case
    by (metis (no_types, lifting) watchdog_remove_pos_evtid2)
qed

definition remove_chain_pos_fun :: "nat \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "remove_chain_pos_fun i es = (
    if i \<ge> length es then
      es
    else if i = length es - 1 then
      take i es
    else
      take i es @ drop (i + 1) (es[(i + 1) := (fst (es!(i+1)), snd (es!(i+1)) + snd (es!i))]))"

value "remove_chain_pos_fun 0 [(2, 5)]"
value "remove_chain_pos_fun 1 [(2, 5), (1, 5), (0, 5)]"
value "remove_chain_pos_fun 2 [(2, 5), (1, 5), (0, 5)]"
value "remove_chain_pos_fun 3 [(2, 5), (1, 5), (0, 5)]"

lemma remove_chain_pos_prop1:
  "take (length s) ((k, v) # s) = remove_chain_pos_fun (length s) ((k, v) # s)"
proof (induct s)
  case Nil
  then show ?case apply auto
    by (simp add: remove_chain_pos_fun_def)
next
  case (Cons s es)
  then show ?case
    by (metis add_diff_cancel_left' length_Cons plus_1_eq_Suc remove_chain_pos_fun_def take_all)
qed

lemma remove_chain_pos_Suc [simp]:
  "remove_chain_pos_fun (Suc n) ((a, b) # s # es) = (a, b) # (remove_chain_pos_fun n (s # es))"
proof (induct n arbitrary: s)
  case 0
  then show ?case 
    by (simp add: remove_chain_pos_fun_def)
next
  case (Suc n)
  then show ?case 
    unfolding remove_chain_pos_fun_def
    by auto
qed

lemma remove_chain_pos_prop2:
  "(take n ((a', b') # es) @ drop n es)[n := (fst ((take n ((a', b') # es) @ drop n es) ! n), 
   snd (((a', b') # es) ! n) + snd (es ! n))] = remove_chain_pos_fun n ((a', b') # es)"
proof(induct n arbitrary: es)
  case 0
  then show ?case apply auto
    unfolding remove_chain_pos_fun_def apply auto
    by (simp add: add.commute)
next
  case (Suc n)
  then show ?case apply auto
    unfolding remove_chain_pos_fun_def apply auto
     apply (metis take_Suc_Cons)
    by (smt Cons_nth_drop_Suc Suc_leI add.commute diff_cancel2 diff_diff_cancel drop_update_swap 
        length_drop length_rev list_update_append nat_le_linear nat_less_le nth_append_length 
        plus_1_eq_Suc rev_take)
qed

definition watchdog_remove2 :: "task_id \<Rightarrow> watchdog_chain \<Rightarrow> watchdog_chain" where
  "watchdog_remove2 evt_id s =
    (case watchdog_remove_pos evt_id s of
       None \<Rightarrow> s
     | Some n \<Rightarrow> remove_chain_pos_fun n s)"

lemma watchdog_remove_pos_None:
  "watchdog_remove_pos evt_id es = None \<Longrightarrow> event_time es evt_id = None"
proof (induction es)
  case Nil
  then show ?case by auto
next
  case (Cons a es)
  then show ?case
    apply (cases "watchdog_remove_pos evt_id es")
    by auto
qed

lemma watchdog_remove_None:
  "watchdog_remove_pos evt_id s0 = None \<Longrightarrow> s0 = watchdog_remove evt_id s0"
  apply (induction s0) apply auto by fastforce

lemma watchdog_remove2_correct:
  "watchdog_remove2 evt_id s0 = watchdog_remove evt_id s0"
proof (induction s0)
  case Nil
  then show ?case
    by (auto simp add: watchdog_remove2_def)
next
  case (Cons s s0)
  show ?case
  proof (cases "fst s = evt_id")
    case True
    then show ?thesis
      apply (auto simp add: watchdog_remove2_def remove_chain_pos_fun_def)
      apply (cases s0) by auto
  next
    case False
    then show ?thesis
      apply (auto simp add: watchdog_remove2_def)
      apply (cases "watchdog_remove_pos evt_id s0")
       apply (auto simp add: watchdog_remove_None)
      by (metis Cons.IH watchdog_remove_pos.elims option.case(2) option.distinct(1) prod.collapse
                remove_chain_pos_Suc watchdog_remove2_def)
  qed
qed

lemma event_time_None_intro:
  "k < length es \<Longrightarrow> \<forall>i<k. evt_id \<noteq> fst (es ! i) \<Longrightarrow> event_time (take k es) evt_id = None"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  have a1: "take (Suc k) es = take k es @ [es ! k]"
    by (simp add: Suc.prems(1) Suc_lessD take_Suc_conv_app_nth)
  have a2: "event_time (take k es) evt_id = None"
    using Suc by auto
  show ?case
    using Suc a1 apply auto
    unfolding event_time_append1[OF a2]
    by auto
qed

lemma occurs_atmost_one_drop:
  "occurs_atmost_one es evt_id \<Longrightarrow> occurs_atmost_one (drop n es) evt_id"
  apply (induction n)
  apply auto
  by (metis drop_Nil drop_Suc hd_Cons_tl occurs_atmost_one_Cons tl_drop)

lemma event_time_incr0_None:
  assumes "event_time es evt_id = None"
  shows "event_time (es[0 := (fst (es ! 0), snd (es ! 0) + k)]) evt_id = None"
proof (cases es)
  case Nil
  then show ?thesis by auto
next
  case (Cons p es')
  show ?thesis
  proof (cases p)
    case (Pair k v)
    have a1: "k \<noteq> evt_id" "event_time es' evt_id = None"
      using assms unfolding Cons Pair
      using event_time_Suc_None by auto
    show ?thesis
      unfolding Cons Pair by (auto simp add: a1)
  qed
qed

theorem watchdog_remove_prop1:
  assumes "occurs_atmost_one es evt_id"
    and "event_time es evt_id = Some k"
  shows "event_time (watchdog_remove evt_id es) evt_id = None"
proof -
  have "watchdog_remove_pos evt_id es \<noteq> None"
    using assms watchdog_remove_pos_None by fastforce
  then obtain k where a1: "watchdog_remove_pos evt_id es = Some k"
    by auto
  then have a2: "\<forall>i<k. evt_id \<noteq> fst (es ! i)" "evt_id = fst (es ! k)" "k < length es"
    using watchdog_remove_pos_evtid2 assms(2) by auto
  have a3: "watchdog_remove evt_id es = remove_chain_pos_fun k es"
    unfolding watchdog_remove2_correct[symmetric] watchdog_remove2_def
    by (simp add: a1)
  show ?thesis
  proof (cases "k = length es - 1")
    case True
    show ?thesis
    proof -
      have b1: "watchdog_remove evt_id es = take (length es - 1) es"
        unfolding a3 remove_chain_pos_fun_def
        using a2(3) True by auto
      show ?thesis
        unfolding b1
        apply (rule event_time_None_intro)
        using a2 by (auto simp add: True)
    qed
  next
    case False
    show ?thesis
    proof -
      have c1: "watchdog_remove evt_id es =
                take k es @ drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))])"
        unfolding a3 remove_chain_pos_fun_def
        using a2(3) False by auto
      have c2: "event_time (take k es) evt_id = None"
        apply (rule event_time_None_intro)
        using a2 by auto
      have c3: "occurs_atmost_one (drop k es) evt_id"
        by (rule occurs_atmost_one_drop[OF assms(1)])
      have c4: "drop k es = es ! k # drop (Suc k) es"
        by (simp add: Cons_nth_drop_Suc a2(3))
      have c5: "event_time (drop (Suc k) es) evt_id = None"
        using c3 unfolding c4 apply (cases "es ! k")
        by (auto simp add: a2(2))
      let ?es'="drop (Suc k) es"
      have c6: "drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))]) =
                ?es'[0 := (fst (?es' ! 0), snd (?es' ! 0) + snd (es ! k))]"
        by (metis (no_types, hide_lams) a2(3) add.commute add.left_neutral add_diff_cancel_right'
              diff_le_self drop_update_swap not_less not_less_eq nth_drop)
      have c7: "event_time (drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))])) evt_id = None"
        unfolding c6 apply (rule event_time_incr0_None)
        apply (rule c5) using False a2(3) done
      show ?thesis
        unfolding c1 event_time_append1[OF c2]
        using c7 by auto
    qed
  qed
qed

lemma event_time_incr0_Some:
  assumes "event_time es evt_id = Some a"
  shows "event_time (es[0 := (fst (es ! 0), snd (es ! 0) + k)]) evt_id = Some (a + k)"
proof (cases es)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons p es')
  show ?thesis
  proof (cases p)
    case (Pair k v)
    show ?thesis
    proof (cases "k = evt_id")
      case True
      have "v = a"
        using assms(1) unfolding Cons Pair True by auto
      then show ?thesis
        unfolding Pair Cons True by auto
    next
      case False
      have "event_time es' evt_id = Some (a - v)" "a \<ge> v"
        using assms unfolding Cons Pair using False apply auto
         apply (cases "event_time es' evt_id") apply auto
        apply (cases "event_time es' evt_id") by auto
      then show ?thesis
        unfolding Pair Cons using False
        by (simp add: Pair local.Cons)
    qed
  qed
qed

theorem watchdog_remove_prop2:
  assumes "evt_id \<noteq> evt_id2"
    and "event_time es evt_id = Some k"
  shows "event_time (watchdog_remove evt_id es) evt_id2 = event_time es evt_id2"
proof -
  have "watchdog_remove_pos evt_id es \<noteq> None"
    using assms watchdog_remove_pos_None by fastforce
  then obtain k where a1: "watchdog_remove_pos evt_id es = Some k"
    by auto
  then have a2: "\<forall>i<k. evt_id \<noteq> fst (es ! i)" "evt_id = fst (es ! k)" "k < length es"
    using watchdog_remove_pos_evtid2 assms(2) by auto
  have a3: "watchdog_remove evt_id es = remove_chain_pos_fun k es"
    unfolding watchdog_remove2_correct[symmetric] watchdog_remove2_def
    by (simp add: a1)
  show ?thesis
  proof (cases "k = length es - 1")
    case True
    show ?thesis
    proof -
      have b1: "watchdog_remove evt_id es = take (length es - 1) es"
        unfolding a3 remove_chain_pos_fun_def
        using a2(3) True by auto
      show ?thesis
      proof (cases "event_time (take (length es - 1) es) evt_id2")
        case None
        have c1: "es = take (length es - 1) es @ [es ! (length es - 1)]"
          by (metis a2(3) butlast_conv_take gr_implies_not_zero last_conv_nth length_0_conv snoc_eq_iff_butlast)
        show ?thesis
          unfolding b1 None
          apply (subst c1)
          unfolding event_time_append1[OF None]
          using True a2(2) assms(1) by auto
      next
        case (Some a)
        show ?thesis
          unfolding b1 Some
          by (metis Some event_time_take_Some)
      qed
    qed
  next
    case False
    show ?thesis
    proof -
      have c1: "watchdog_remove evt_id es =
                take k es @ drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))])"
        unfolding a3 remove_chain_pos_fun_def
        using a2(3) False by auto
      have c2: "event_time (take k es) evt_id = None"
        apply (rule event_time_None_intro)
        using a2 by auto
      have c3: "event_time es evt_id2 = event_time ((take k es) @ (drop k es)) evt_id2"
        by auto
      show ?thesis
      proof (cases "event_time (take k es) evt_id2")
        case None
        note None1 = None
        let ?es'="drop (Suc k) es"
        have c4: "drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))]) =
                  ?es'[0 := (fst (?es' ! 0), snd (?es' ! 0) + snd (es ! k))]"
          by (metis (no_types, hide_lams) a2(3) add.commute add.left_neutral add_diff_cancel_right'
                diff_le_self drop_update_swap not_less not_less_eq nth_drop)
        show ?thesis
        proof (cases "event_time (drop k es) evt_id2")
          case None
          have d1: "event_time es evt_id2 = None"
            by (metis None None1 append_take_drop_id event_time_append1 option.simps(4))
          show ?thesis
            unfolding c1 d1
            apply (subst event_time_append1[OF None1])
            apply (subst c4)
            by (metis (no_types, lifting) Cons_nth_drop_Suc None a2(3)
                  event_time_Suc_None event_time_incr0_None option.case_eq_if)
        next
          case (Some n)
          have e1: "event_time es evt_id2 = Some (n + watchdog_total_upto (take k es) (length (take k es)))"
            unfolding c3
            apply (subst event_time_append1[OF None1])
            using Some by auto
          have e2: "drop k es = es ! k # drop (Suc k) es"
            by (simp add: Cons_nth_drop_Suc a2(3))
          have e3: "fst (es ! k) \<noteq> evt_id2"
            using a2(2) assms(1) by auto
          have e4: "n \<ge> snd (es ! k) \<and> event_time (drop (Suc k) es) evt_id2 = Some (n - snd (es ! k))"
            using Some unfolding e2
            apply (auto simp add: e3)
            by (cases "event_time (drop (Suc k) es) evt_id2", auto)+
          have e5: "event_time (drop (Suc k) (es[Suc k := (fst (es ! Suc k), snd (es ! Suc k) + snd (es ! k))])) evt_id2 = Some (n - snd (es ! k) + snd (es ! k))"
            unfolding c4
            apply (rule event_time_incr0_Some)
            using e4 apply auto done
          show ?thesis
            unfolding c1 e1
            apply (subst event_time_append1[OF None])
            using Some apply (auto simp add: e5)
            using e4 by auto
        qed
      next
        case (Some a)
        then show ?thesis
          unfolding c1
          by (metis event_time_append2 event_time_take_Some)
      qed
    qed
  qed
qed

lemma event_time_to_watchdog_remove_pos_None:
  "event_time es evt_id = None \<Longrightarrow> watchdog_remove_pos evt_id es = None"
  apply (induction es)
   apply auto
  subgoal for p n es'
    apply (cases "event_time es' evt_id")
    by auto
  done

theorem watchdog_remove_same:
  assumes "event_time es evt_id = None"
  shows "watchdog_remove evt_id es = es"
  unfolding watchdog_remove2_correct[symmetric] watchdog_remove2_def
  by (simp add: assms event_time_to_watchdog_remove_pos_None)

theorem watchdog_remove_prop1':
  assumes "occurs_atmost_one es evt_id"
  shows "event_time (watchdog_remove evt_id es) evt_id = None"
  by (metis assms event_time_to_watchdog_remove_pos_None option.exhaust option.simps(4)
            watchdog_remove2_correct watchdog_remove2_def watchdog_remove_prop1)

theorem watchdog_remove_prop2':
  assumes "evt_id \<noteq> evt_id2"
  shows "event_time (watchdog_remove evt_id es) evt_id2 = event_time es evt_id2"
  using assms watchdog_remove_prop2 watchdog_remove_same by fastforce

theorem watchdog_remove_valid:
  assumes "valid_watchdog es"
  shows "valid_watchdog (watchdog_remove evt_id es)"
proof -
  have a: "occurs_atmost_one es evt_id' \<Longrightarrow>
           occurs_atmost_one (watchdog_remove evt_id es) evt_id'" for evt_id'
  proof (induction es)
    case Nil
    then show ?case by auto
  next
    case (Cons pair es')
    have a1: "occurs_atmost_one es' evt_id'"
      using Cons.prems occurs_atmost_one_Cons by blast
    have a2: "occurs_atmost_one (watchdog_remove evt_id es') evt_id'"      
      using Cons(1) a1 by auto
    show ?case
    proof (cases pair)
      case (Pair p n)
      show ?thesis
        apply (auto simp add: Cons Pair a2)
          apply (metis a1 increment_head.simps occurs_atmost_one.elims(2) occurs_atmost_one.simps(2))
        using Cons(2) unfolding Pair apply auto
         apply (subst watchdog_remove_prop2')
           apply auto
        by (metis increment_head.elims occurs_atmost_one.simps(2))
    qed
  qed
  show ?thesis
    unfolding valid_watchdog_def
    apply auto
    subgoal
      apply (cases es)
       apply simp subgoal for pair es'
        apply (cases pair)
        subgoal for p n
          apply auto
           apply (metis (no_types, lifting) add_eq_0_iff_both_eq_0 assms(1) event_time.simps(2) gr0I
                    increment_head.elims nth_Cons_0 snd_conv watchdog_tick_triv)
          using assms(1) valid_watchdog_def by auto
        done
      done
    subgoal for evt_id'
      apply (rule a)
      using assms(1) unfolding valid_watchdog_def by auto
    done
qed

end

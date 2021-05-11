theory EventSystemWatchdog
  imports EventSystemExBase
begin

subsection \<open>Implementations of basic operations\<close>

definition get_chain_pos :: "nat \<Rightarrow> (watchdog_chain, event, nat) event_monad" where
  "get_chain_pos i = (
     get \<bind>
     (\<lambda>st. return (snd (st ! i))))"

theorem get_chain_pos_rule [wp]:
  "\<lbrace> \<lambda>s e. Q (snd (s ! i)) s e \<rbrace>
    get_chain_pos i
   \<lbrace> Q \<rbrace>!"
  unfolding get_chain_pos_def by wp

definition get_chain_pos_id :: "nat \<Rightarrow> (watchdog_chain, event, task_id) event_monad" where
  "get_chain_pos_id i = (
     get \<bind>
     (\<lambda>st. return (fst (st ! i))))"

theorem get_chain_pos_id_rule [wp]:
  "\<lbrace> \<lambda>s e. Q (fst (s ! i)) s e \<rbrace>
    get_chain_pos_id i
   \<lbrace> Q \<rbrace>!"
  unfolding get_chain_pos_id_def by wp

definition get_chain_length :: "(watchdog_chain, event, nat) event_monad" where
  "get_chain_length = (
     get \<bind>
     (\<lambda>st. return (length st)))"

theorem get_chain_length_rule [wp]:
  "\<lbrace> \<lambda>s e. Q (length s) s e \<rbrace>
     get_chain_length
   \<lbrace> Q \<rbrace>!"
  unfolding get_chain_length_def by wp

definition set_chain_pos :: "nat \<Rightarrow> nat \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "set_chain_pos i k = (
     modify (\<lambda>es. es[i := (fst (es ! i), k)]))"

theorem set_chain_pos_rule [wp]:
  "\<lbrace> \<lambda>s e. Q () (s[i := (fst (s ! i), k)]) e \<rbrace>
    set_chain_pos i k
   \<lbrace> Q \<rbrace>!"
  unfolding set_chain_pos_def by wp

definition insert_chain_pos :: "nat \<Rightarrow> task_id \<Rightarrow> nat \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "insert_chain_pos i evt_id n = (
    modify (\<lambda>es. (take i es) @ [(evt_id, n)] @ drop i es))"

theorem insert_chain_pos_rule [wp]:
  "\<lbrace> \<lambda>s e. Q () (take i s @ [(evt_id, n)] @ drop i s) e \<rbrace>
    insert_chain_pos i evt_id n
   \<lbrace> Q \<rbrace>!"
  unfolding insert_chain_pos_def by wp

definition remove_first :: "(watchdog_chain, event, unit) event_monad" where
  "remove_first = modify (\<lambda>es. tl es)"

theorem remove_first_rule [wp]:
  "\<lbrace> \<lambda>s e. Q () (tl s) e \<rbrace>
     remove_first
   \<lbrace> Q \<rbrace>!"
  unfolding remove_first_def by wp

subsection \<open>Imperative version of watchdog_add\<close>

text \<open>
  While loop keeps track of current position in the list and remaining ticks.
\<close>
definition watchdog_add_impl' :: "task_id \<Rightarrow> nat \<Rightarrow> (watchdog_chain, event, nat \<times> nat) event_monad" where
  "watchdog_add_impl' evt_id n = whileLoop (\<lambda>r s. snd r > 0) (\<lambda>r.
     get_chain_length \<bind> (\<lambda>len.
     if fst r \<ge> len then
       insert_chain_pos (fst r) evt_id (snd r) \<bind> (\<lambda>_.
       return (fst r + 1, 0))   \<comment> \<open>Add at end\<close>
     else
       get_chain_pos (fst r) \<bind> (\<lambda>w.
       (if snd r > w then
          return (fst r + 1, snd r - w)  \<comment> \<open>Add at later iteration\<close>
        else
          set_chain_pos (fst r) (w - snd r) \<bind> (\<lambda>_.
          insert_chain_pos (fst r) evt_id (snd r) \<bind> (\<lambda>_.
          return (fst r + 1, 0))))))) (0, n)"  \<comment> \<open>Add at current iteration\<close>

definition watchdog_add_impl :: "task_id \<Rightarrow> nat \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "watchdog_add_impl evt_id n = (watchdog_add_impl' evt_id n) \<bind> (\<lambda>_. return ())"


text \<open>Functional array implementation of watchdog_add.

  The parameters are:
  evt_id - ID of event to be added
  n - initial amount of ticks
  s - current state of watchdog chain
  i - number of iterations of execute

  Returns pair of remaining amount of ticks and state of watchdog chain after i iterations
\<close>
fun watchdog_add_fun :: "task_id \<Rightarrow> nat \<Rightarrow> watchdog_chain \<Rightarrow> nat \<Rightarrow> nat \<times> watchdog_chain" where
  "watchdog_add_fun evt_id n s 0 = (n, s)"
| "watchdog_add_fun evt_id n s (Suc i) = (
    let (n', s') = watchdog_add_fun evt_id n s i in
      if n' = 0 then
        (n', s')  \<comment> \<open>Imperative code should have terminated\<close>
      else if i \<ge> length s' then
        (0, s' @ [(evt_id, n')])  \<comment> \<open>Add at the end\<close>
      else if n' > snd (s' ! i) then
        (n' - snd (s' ! i), s')  \<comment> \<open>Add at later iteration\<close>
      else
        (0, take i s' @ [(evt_id, n')] @ drop i (s'[i := (fst (s' ! i), snd (s' ! i) - n')])))"  \<comment> \<open>Add at current iteration\<close>

lemma watchdog_add_fun_correct:
  "(n > watchdog_total_upto s i \<longrightarrow> i \<le> length s \<longrightarrow>
     watchdog_add_fun evt_id n s i = (n - watchdog_total_upto s i, s)) \<and>  \<comment> \<open>not inserting at step i\<close>
   (n > watchdog_total_upto s (length s) \<longrightarrow> i = Suc (length s) \<longrightarrow>
     watchdog_add_fun evt_id n s i = (0, s @ [(evt_id, n - watchdog_total_upto s (length s))])) \<and>  \<comment> \<open>inserting at the end\<close>
   (n > 0 \<longrightarrow> n \<le> watchdog_total_upto s i \<longrightarrow> i \<le> length s \<longrightarrow> i = Suc (watchdog_add_pos s n) \<longrightarrow>
     watchdog_add_fun evt_id n s i = (0,
       take (i - 1) s @ [(evt_id, n - watchdog_total_upto s (i - 1))] @
       drop (i - 1) (s[i - 1 := (fst (s ! (i - 1)), snd (s ! (i - 1)) - (n - watchdog_total_upto s (i - 1)))])))"  \<comment> \<open>inserting at middle\<close>
proof (induct i arbitrary: n s)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have s1: "watchdog_add_fun evt_id n s (Suc i) = (n - watchdog_total_upto s (Suc i), s)"
    if "n > watchdog_total_upto s (Suc i)" "Suc i \<le> length s"
  proof -
    let ?n' = "fst (watchdog_add_fun evt_id n s i)"
    let ?s' = "snd (watchdog_add_fun evt_id n s i)"
    have a1: "n > watchdog_total_upto s i"
      using that by (auto simp add: watchdog_total_upto_Suc)
    have a2: "?n' = n - watchdog_total_upto s i"
      using Suc a1 that(2) by auto
    have a3: "?n' \<noteq> 0"
      using a1 a2 by auto
    have a4: "?s' = s"
      using a1 Suc that(2) by auto
    have a5: "\<not>i \<ge> length ?s'"
      using a4 that(2) by auto
    have a6: "?n' > snd (?s' ! i)"
      using that(1) a2 a4 a5 by (auto simp add: watchdog_total_upto_Suc) 
    show ?thesis
      apply (auto simp add: a3 a5 a6 case_prod_beta)
      using a5 
      unfolding a2 a4 
      by (auto simp add: watchdog_total_upto_Suc)
  qed
  have s2: "watchdog_add_fun evt_id n s (Suc i) = (0, s @ [(evt_id, n - watchdog_total_upto s (length s))])"
    if "n > watchdog_total_upto s (length s)" "Suc i = Suc (length s)"
  proof -
    let ?n' = "fst (watchdog_add_fun evt_id n s i)"
    let ?s' = "snd (watchdog_add_fun evt_id n s i)"
    have a1: "n > watchdog_total_upto s i"
      using that by auto
    have a2: "i \<le> length s \<longrightarrow> ?n' = n - watchdog_total_upto s i"
      using a1 Suc by auto
    have a3: "i \<le> length s \<longrightarrow> ?s' = s"
      using a1 Suc by auto
    show ?thesis
    proof (cases "?n' = 0")
      case True
      have b1: "i > length s"
        using a1 a2 True by auto
      show ?thesis
        using b1 that(2) by auto
    next
      case False
      have b1: "?s' = s"
        using a3 that(2) by auto
      have b2: "i \<ge> length ?s'"
        using b1 that(2) by auto
      have b3: "?n' = n - watchdog_total_upto s i"
        using that(2) a2 by auto
      show ?thesis
        apply (auto simp add: case_prod_beta \<open>?n' \<noteq> 0\<close> b2)
        unfolding b3 b1 using that(2) by auto
    qed
  qed
  have s3: "watchdog_add_fun evt_id n s (Suc i) = (0,
              take i s @ [(evt_id, n - watchdog_total_upto s i)] @
              drop i (s[i := (fst (s ! i), snd (s ! i) - (n - watchdog_total_upto s i))]))"
    if assum_s3: "n > 0" "n \<le> watchdog_total_upto s (Suc i)" "Suc i \<le> length s"
                 "Suc i = Suc (watchdog_add_pos s n)"
  proof -
    let ?n' = "fst (watchdog_add_fun evt_id n s i)"
    let ?s' = "snd (watchdog_add_fun evt_id n s i)"
    have "i = watchdog_add_pos s n"
      using assum_s3(4) by auto
    then have "i \<le> length s"
      using watchdog_add_pos_prop1 by auto
    have a1a: "watchdog_total_upto s i < n"
      by (metis (full_types) Suc_inject le_neq_implies_less that(1) that(4)
             watchdog_add_pos_prop1 watchdog_add_pos_prop2 watchdog_add_pos_prop3)
    have a1b: "i < length s"
      using that(3) by auto
    have a2: "?n' = n - watchdog_total_upto s i"
      using a1a a1b Suc by auto
    have a3: "?s' = s"
      using a1a a1b Suc by auto
    have a4: "?n' \<noteq> 0"
      using a2 a1a by auto
    have a5: "\<not>i \<ge> length ?s'"
      using a3 a1b by auto
    have a6: "\<not>?n' > snd (?s' ! i)"
      unfolding a2 a3 using assum_s3(2) a3 a5
      by (auto simp add: watchdog_total_upto_Suc)
    show ?thesis
      apply (auto simp add: case_prod_beta a4 a5 a6)
      unfolding a2 a3 by auto
  qed
  show ?case
    using s1 s2 s3 by auto
qed

lemma watchdog_add_fun_prop1:
  assumes "n > 0"
    and "i = Suc (watchdog_add_pos s0 n)"
  shows "fst (watchdog_add_fun evt_id n s0 i) = 0"
proof -
  have a1: "(n > watchdog_total_upto s0 (length s0) \<and> i = Suc (length s0)) \<or>
        (n \<le> watchdog_total_upto s0 i \<and> i \<le> length s0)"
    using watchdog_add_fun_range2 assms(1-2) by auto
  have a2: ?thesis
    if "n > watchdog_total_upto s0 (length s0)" "i = Suc (length s0)"
    using watchdog_add_fun_correct[of s0 i n evt_id] that by auto
  have a3: ?thesis
    if "n \<le> watchdog_total_upto s0 i" "i \<le> length s0"
    using watchdog_add_fun_correct[of s0 i n evt_id] assms(1,2) that by auto
  show ?thesis
    using a1 a2 a3 by auto
qed

lemma watchdog_add_fun_prop2:
  assumes "n > 0"
    and "i < Suc (watchdog_add_pos s0 n)"
  shows "fst (watchdog_add_fun evt_id n s0 i) > 0"
proof -
  have a1: "watchdog_total_upto s0 i < n \<and> i \<le> length s0"
    using watchdog_add_fun_range assms by auto
  then have a2: "watchdog_add_fun evt_id n s0 i = (n - watchdog_total_upto s0 i, s0)"
    using watchdog_add_fun_correct by auto
  show ?thesis
    using a1 a2 by auto
qed

lemma watchdog_add_impl_rule':
  assumes "n > 0"
  shows
    "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
      watchdog_add_impl' evt_id n
     \<lbrace> \<lambda>r s es. fst r = Suc (watchdog_add_pos s0 n) \<and> s = snd (watchdog_add_fun evt_id n s0 (fst r)) \<and> es = e0 \<rbrace>!"
  unfolding watchdog_add_impl'_def
  apply (rule validNF_whileLoop[where I="\<lambda>r s e. watchdog_add_fun evt_id n s0 (fst r) = (snd r, s) \<and>
                                                 fst r \<le> Suc (watchdog_add_pos s0 n) \<and> e = e0" and
                                      R="measure (\<lambda>(r,s). Suc (watchdog_add_pos s0 n) - fst r)"])
  subgoal for s es
    by auto
  subgoal for r s0'
    apply wp
    apply auto
    using assms watchdog_add_fun_prop1[of n "fst r" s0 evt_id]
     apply fastforce
    by (metis assms diff_less_mono fst_conv le_SucE lessI neq0_conv watchdog_add_fun_prop1)
  subgoal
    by (rule wf_measure)
  subgoal for r s es
    apply auto
    by (metis assms fst_conv le_neq_implies_less less_numeral_extra(3) watchdog_add_fun_prop2)
  done

lemma watchdog_add_fun_correct2:
  assumes "n > 0"
  shows "snd (watchdog_add_fun evt_id n s (Suc (watchdog_add_pos s n))) = Watchdog.watchdog_add evt_id n s"
proof -
  let ?i="watchdog_add_pos s n"
  have a1: "(n > watchdog_total_upto s (length s) \<and> ?i = length s) \<or>
        (n \<le> watchdog_total_upto s (Suc ?i) \<and> n > watchdog_total_upto s ?i \<and> Suc ?i \<le> length s)"
    using watchdog_add_fun_range2[OF assms] by auto
  have a2: ?thesis if "n > watchdog_total_upto s (length s)" "?i = length s"
    using watchdog_add_fun_correct[of s "Suc ?i" n evt_id] watchdog_add_prop1 that by auto
  have a3: ?thesis if "n \<le> watchdog_total_upto s (Suc ?i)" "n > watchdog_total_upto s ?i" "Suc ?i \<le> length s"
    using watchdog_add_fun_correct[of s "Suc ?i" n evt_id] watchdog_add_prop2 that by auto
  show ?thesis
    using a1 a2 a3 by blast
qed

lemma watchdog_add_impl_rule2':
  assumes "n > 0"
  shows
    "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
      watchdog_add_impl' evt_id n
     \<lbrace> \<lambda>r s es. s = Watchdog.watchdog_add evt_id n s0 \<and> es = e0 \<rbrace>!"
  apply (rule validNF_strengthen_post[OF watchdog_add_impl_rule'])
  using watchdog_add_fun_correct2 assms by auto

lemma watchdog_add_impl_rule2:
  assumes "n > 0"
  shows
    "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
      watchdog_add_impl evt_id n
     \<lbrace> \<lambda>_ s es. s = Watchdog.watchdog_add evt_id n s0 \<and> es = e0 \<rbrace>!"
  unfolding watchdog_add_impl_def
  apply wp apply (rule watchdog_add_impl_rule2')
  using assms apply auto by wp

subsection \<open>Imperative version of watchdog_tick\<close>

definition decr_head_impl :: "nat \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "decr_head_impl n = (
     get_chain_pos 0 \<bind> (\<lambda>k.
     set_chain_pos 0 (k - n) \<bind> (\<lambda>_.
     return ())))"

theorem decr_head_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
     decr_head_impl n
   \<lbrace> \<lambda>r s es. s = decr_head n s0 \<and> es = e0 \<rbrace>!"
  unfolding decr_head_impl_def
  apply wp
  apply (cases s0) by auto

text \<open>
  While loop keeps track of whether to continue iteration.
\<close>
definition extract_zero_impl :: "(watchdog_chain, event, bool) event_monad" where
  "extract_zero_impl = whileLoop (\<lambda>k s. k) (\<lambda>k.
     get_chain_length \<bind> (\<lambda>len.
     if len = 0 then
       return False
     else
       get_chain_pos 0 \<bind> (\<lambda>k.
       if k = 0 then
         get_chain_pos_id 0 \<bind> (\<lambda>evt_id.
         signal (DISPATCH evt_id) \<bind> (\<lambda>_.
         remove_first \<bind> (\<lambda>_.
         return True)))
       else
         return False))) True"

text \<open>Functional array implementation of extract_zero\<close>
fun extract_zero_fun :: "watchdog_chain \<Rightarrow> nat \<Rightarrow> event list \<times> bool \<times> watchdog_chain" where
  "extract_zero_fun s 0 = ([], True, s)"
| "extract_zero_fun s (Suc i) = (
    let (es, r, s') = extract_zero_fun s i in
      if \<not>r then
        (es, r, s')
      else case s' of
             [] \<Rightarrow> (es, False, s')
           | p # s2 \<Rightarrow> if snd p = 0 then (es @ [DISPATCH (fst p)], True, s2)
                       else (es, False, s'))"

lemma extract_zero_fun_prop1:
  "extract_zero_fun s0 i = (e, True, s) \<Longrightarrow> s = drop i s0 \<and> i \<le> count_zero s0"
proof (induction i arbitrary: s0 e s)
  case 0
  then show ?case by auto
next
  case (Suc i)
  show ?case
  proof (cases "extract_zero_fun s0 i")
    case (fields es r s')
    show ?thesis
    proof (cases "r = True")
      case True
      have a1: "s' = drop i s0 \<and> i \<le> count_zero s0"
        using Suc(1)[OF fields[unfolded True]] by auto
      show ?thesis
      proof (cases s')
        case Nil
        then show ?thesis
          using Suc(2) fields True by auto
      next
        case (Cons p s2)
        show ?thesis
          using Suc(2) apply (auto simp add: fields True Cons)
          subgoal apply (cases "snd p = 0") apply auto
            using Cons a1 by (metis Cons_nth_drop_Suc length_Cons length_drop list.inject zero_less_Suc zero_less_diff)
          subgoal apply (cases "snd p = 0")
             apply auto using Cons a1
            by (metis Cons_nth_drop_Suc Suc_leI count_zero_iff2 le_neq_implies_less length_Cons
                      length_drop nth_Cons_0 zero_less_Suc zero_less_diff)
          done
      qed
    next
      case False
      then show ?thesis
        using Suc(2) by (auto simp add: fields)
    qed
  qed
qed

lemma extract_zero_fun_prop2:
  "i \<le> count_zero s0 \<Longrightarrow> extract_zero_fun s0 i = (map (\<lambda>p. DISPATCH (fst p)) (take i s0), True, drop i s0)"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have a1: "extract_zero_fun s0 i = (map (\<lambda>p. DISPATCH (fst p)) (take i s0), True, drop i s0)"
    using Suc by auto
  have a2: "i < count_zero s0"
    using Suc by auto
  have a3: "i < length s0" "snd (s0 ! i) = 0"
    using count_zero_iff a2 by auto
  have a4: "drop i s0 \<noteq> []" "snd ((drop i s0) ! 0) = 0"
    using a3 by auto
  have a5: "take (Suc i) s0 = take i s0 @ [s0 ! i]"
    by (simp add: a3(1) take_Suc_conv_app_nth)
  show ?case
    apply (auto simp add: a1) apply (cases "drop i s0")
    subgoal using a4 by auto
    subgoal for p s2
      apply (auto simp add: a4 a5 nth_via_drop)
      apply (simp add: a3(1) drop_Suc_nth)
      using a4(2) by auto
    done
qed

lemma extract_zero_fun_prop3:
  "extract_zero_fun s0 (Suc (count_zero s0)) =
   (map (\<lambda>p. DISPATCH (fst p)) (take (count_zero s0) s0), False, drop (count_zero s0) s0)"
proof -
  let ?i="count_zero s0"
  have a1: "extract_zero_fun s0 ?i = (map (\<lambda>p. DISPATCH (fst p)) (take ?i s0), True, drop ?i s0)"
    using extract_zero_fun_prop2 by auto
  have a2: "?i = length s0 \<or> snd (s0 ! ?i) \<noteq> 0"
    using count_zero_iff2 by auto
  show ?thesis
    apply (auto simp add: a1)
    apply (cases "drop ?i s0") apply auto
    using a2 nth_via_drop by fastforce
qed

lemma extract_zero_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    extract_zero_impl
   \<lbrace> \<lambda>r s es. \<not>r \<and> extract_zero_fun s0 (Suc (count_zero s0)) = (es, r, s) \<rbrace>!"
  unfolding extract_zero_impl_def
  apply (rule validNF_whileLoop[where
          I="\<lambda>r s es. \<exists>i. i \<le> Suc (count_zero s0) \<and> extract_zero_fun s0 i = (es, r, s)" and
          R="measure (\<lambda>(r,s). length s + (if r then 1 else 0))"])
  subgoal
    apply (rule exI[where x=0]) by auto
  subgoal for r s0'
    apply wp
    subgoal for s e apply auto
      subgoal for i
        apply (rule exI[where x="Suc i"])
        apply auto
        by (auto simp add: extract_zero_fun_prop1)
      subgoal for i
        apply (rule exI[where x="Suc i"])
        apply (auto simp add: extract_zero_fun_prop1)
        apply (cases s) by auto
      subgoal for i
        apply (rule exI[where x="Suc i"])
        apply (auto simp add: extract_zero_fun_prop1)
        apply (cases s) by auto
      done
    done
  subgoal
    by (rule wf_measure)
  subgoal for r s es
    using extract_zero_fun_prop2 le_Suc_eq by fastforce
  done

lemma extract_zero_fun_correct:
  "extract_zero_fun s0 (Suc (count_zero s0)) =
   (map DISPATCH (fst (extract_zero s0)), False, snd (extract_zero s0))"
  unfolding extract_zero_fun_prop3 extract_zero_array by auto

lemma extract_zero_impl_rule2:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    extract_zero_impl
   \<lbrace> \<lambda>r s es. \<not>r \<and> s = snd (extract_zero s0) \<and> es = map DISPATCH (fst (extract_zero s0)) \<rbrace>!"
  apply (rule validNF_strengthen_post[OF extract_zero_impl_rule])
  using extract_zero_fun_correct by auto

definition watchdog_tick_impl :: "(watchdog_chain, event, unit) event_monad" where
  "watchdog_tick_impl = (
    decr_head_impl 1 \<bind> (\<lambda>_.
    extract_zero_impl \<bind> (\<lambda>_. return ())))"

lemma watchdog_tick_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     watchdog_tick_impl
   \<lbrace> \<lambda>_ s es. s = snd (Watchdog.watchdog_tick s0) \<and>
              es = map DISPATCH (fst (Watchdog.watchdog_tick s0)) \<rbrace>!"
  unfolding watchdog_tick_impl_def
  apply wp
    apply (rule decr_head_impl_rule)
   apply (rule validNF_strengthen_post)
  apply (rule validNF_bind)
     apply (rule extract_zero_impl_rule2)
  apply (rule validNF_weaken_pre)
     apply (rule validNF_return)
  by (auto simp add: Watchdog.watchdog_tick_def)

subsection \<open>Imperative version of watchdog_remove\<close>

text \<open>Imperative code\<close>
definition find_chain_pos_impl :: "task_id \<Rightarrow> (watchdog_chain, event, bool \<times> nat) event_monad" where
  "find_chain_pos_impl evt_id = whileLoop (\<lambda>r s. (snd r < length s \<and> fst r = False)) (\<lambda>r.
     get_chain_pos_id (snd r) \<bind> (\<lambda>w. 
     if evt_id = w then
       return (True, snd r + 1)
     else
       return (False, snd r + 1))) (False, 0)"

text \<open>Corresponding functional code\<close>
fun find_chain_pos_fun :: "task_id \<Rightarrow> watchdog_chain \<Rightarrow> nat \<Rightarrow> bool" where
  "find_chain_pos_fun evt_id s 0 = False"
| "find_chain_pos_fun evt_id s (Suc i) = (
    let b' = find_chain_pos_fun evt_id s i in
      if b' \<or> i \<ge> length s then
        b'    \<comment> \<open>Imperative code should have terminated\<close>
      else if fst (s ! i) = evt_id then
        True  \<comment> \<open>Found at other position\<close>
      else
        False)"   \<comment> \<open>Repeat the iteration\<close>

lemma find_chain_pos_Suc:
  "n < length s0 \<Longrightarrow>
   find_chain_pos_fun evt_id s0 n = False \<and> evt_id \<noteq> fst (s0 ! n) \<longleftrightarrow>
   find_chain_pos_fun evt_id s0 (Suc n) = False"
  by (induction n, auto)

lemma find_chain_pos_evtid:
  "n \<le> length s0 \<Longrightarrow>
   find_chain_pos_fun evt_id s0 n = False \<longleftrightarrow> (\<forall>i < n. evt_id \<noteq> fst (s0 ! i))"
proof (induct n arbitrary: s0)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof (cases s0)
    case Nil
    then show ?thesis
      using Suc.prems(1) by auto
  next
    case (Cons s es)
    show ?thesis
      using Suc.hyps less_Suc_eq local.Suc(2) by auto
  qed
qed

lemma find_chain_some_n:
  assumes "n < length s0"
    shows "watchdog_remove_pos evt_id s0 = Some n \<longleftrightarrow> 
    (evt_id = fst (s0 ! n) \<and> find_chain_pos_fun evt_id s0 (n) = False)"
  using assms find_chain_pos_evtid watchdog_remove_pos_evtid2 by auto

lemma find_chain_some_nSuc:
  "watchdog_remove_pos evt_id s0 = Some n \<longleftrightarrow>
   (find_chain_pos_fun evt_id s0 (Suc n) = True \<and> find_chain_pos_fun evt_id s0 (n) = False)"
proof (induct n)
  case 0
  then show ?case apply auto
     apply (simp add: find_chain_some_n)
    by (simp add: find_chain_some_n)
next
  case (Suc n)
  then show ?case 
  proof -
    have "(watchdog_remove_pos evt_id s0 = Some (Suc n)) = (evt_id = fst (s0 ! Suc n) \<and> Suc n < length s0 \<and> 
      \<not> find_chain_pos_fun evt_id s0 (Suc n))"
      by (metis find_chain_some_n watchdog_remove_pos_le)
    then show ?thesis
      using not_le by force
  qed
qed

lemma find_chain_some_snd:
  "watchdog_remove_pos evt_id s0 = Some n \<Longrightarrow> i \<le> Suc n \<Longrightarrow> find_chain_pos_fun evt_id s0 i \<Longrightarrow> i = Suc n"
proof (induct n)
  case 0
  then show ?case 
    using le_eq_less_or_eq by fastforce
next
  case (Suc n)
  then show ?case 
    by (metis find_chain_pos_fun.simps(2) find_chain_some_nSuc le_Suc_eq nat_induct_at_least)
qed

lemma find_chain_pos_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
    find_chain_pos_impl evt_id
   \<lbrace> \<lambda>r s es. (case watchdog_remove_pos evt_id s0 of
                 None \<Rightarrow> fst r = False \<and> snd r = length s0
               | Some i \<Rightarrow> fst r = True \<and> snd r = Suc i) \<and>
              s = s0 \<and> es = e0 \<rbrace>!"
  unfolding find_chain_pos_impl_def
  apply (rule validNF_whileLoop[where I="\<lambda>r s e. find_chain_pos_fun evt_id s0 (snd r) = fst r \<and>
                                                 (case watchdog_remove_pos evt_id s0 of
                                                    None \<Rightarrow> snd r \<le> length s0
                                                  | Some i \<Rightarrow> snd r \<le> Suc i) \<and> s = s0 \<and> e = e0" and
                                      R="measure (\<lambda>(r,s). length s0 - snd r)"])
  subgoal for s es
    apply (cases "watchdog_remove_pos evt_id s0") by auto
  subgoal for r0 s0
    apply wp subgoal for s e
      apply (cases "watchdog_remove_pos evt_id s0") apply auto
      apply (metis find_chain_some_nSuc le_SucE)
      using find_chain_some_nSuc le_Suc_eq by auto
    done
  subgoal
    apply (cases "watchdog_remove_pos evt_id s0") by auto
  subgoal for r s e
    apply (cases "watchdog_remove_pos evt_id s0") apply auto
    apply (metis find_chain_pos_fun.simps(1) find_chain_some_nSuc option.simps(3) zero_induct)
    apply (metis find_chain_pos_fun.simps(1) find_chain_some_nSuc option.simps(3) zero_induct)
    apply (metis (full_types) find_chain_pos_fun.simps(1) find_chain_some_nSuc option.distinct(1) zero_induct)
    apply (simp add: find_chain_some_snd)
    apply (metis (mono_tags, hide_lams) Suc_leI find_chain_some_nSuc le_antisym not_less order_trans watchdog_remove_pos_le)
    using watchdog_remove_pos_le apply fastforce
    by (simp add: find_chain_some_snd)
done

definition remove_chain_pos_impl :: "nat \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "remove_chain_pos_impl i = (
    get_chain_length \<bind> (\<lambda>len.
    if i \<ge> len then
      return ()
    else if i = len - 1 then
        modify (\<lambda>es. take i es) \<bind> (\<lambda>_.
        return ())
    else
      get_chain_pos i \<bind> (\<lambda>n.
      get_chain_pos (i + 1) \<bind> (\<lambda>k.
      modify (\<lambda>es. (take i es) @ (drop (i + 1) es)) \<bind> (\<lambda>_.
      set_chain_pos i (n + k) \<bind> (\<lambda>_.
      return ()))))))"

theorem remove_chain_pos_impl_rule:
 "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
       remove_chain_pos_impl n
     \<lbrace> \<lambda>r s es. s = remove_chain_pos_fun n s0 \<and> es = e0 \<rbrace>!"
  unfolding remove_chain_pos_impl_def
  apply wp
  apply (cases s0) apply auto
     apply (simp add: remove_chain_pos_fun_def)
  using remove_chain_pos_prop1 apply auto
  using remove_chain_pos_prop2 
    apply (simp add: remove_chain_pos_fun_def) 
   apply (simp add: remove_chain_pos_prop1)
  by (simp add: remove_chain_pos_prop2)

definition watchdog_remove_impl :: "task_id \<Rightarrow> (watchdog_chain, event, unit) event_monad" where
  "watchdog_remove_impl evt_id = (
    find_chain_pos_impl evt_id \<bind> (\<lambda>r.
    if fst r then
      remove_chain_pos_impl (snd r - 1)
    else return ()))"

lemma watchdog_remove_impl_rule':
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
    watchdog_remove_impl evt_id
   \<lbrace> \<lambda>r s es. s = watchdog_remove2 evt_id s0 \<and> es = e0 \<rbrace>!"
  unfolding watchdog_remove_impl_def
  apply (rule validNF_bind)
   apply (rule find_chain_pos_impl_rule)
  subgoal for r
  proof (cases "watchdog_remove_pos evt_id s0")
    case None
    then show ?thesis
      apply auto
      subgoal apply (rule validNF_weaken_pre)
        unfolding remove_chain_pos_impl_def apply wp by auto
      subgoal
        apply wp
        by (auto simp add: watchdog_remove2_def)
      done
  next
    case (Some n)
    then show ?thesis
      apply auto
      subgoal
        apply (subst validNF_conj_pre) apply auto
        apply (rule validNF_strengthen_post)
         apply (rule remove_chain_pos_impl_rule)
        by (auto simp add: watchdog_remove2_def)
      subgoal apply (rule validNF_weaken_pre)
        unfolding remove_chain_pos_impl_def apply wp by auto
      done
  qed
  done

lemma watchdog_remove_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = e0 \<rbrace>
    watchdog_remove_impl evt_id
   \<lbrace> \<lambda>r s es. s = watchdog_remove evt_id s0 \<and> es = e0 \<rbrace>!"
  using watchdog_remove_impl_rule' watchdog_remove2_correct 
  by auto

subsection \<open>Refinement proofs for watchdog\<close>

type_synonym astate_watchdog =
  "task_id \<Rightarrow> nat option"

definition rel_watchdog :: "astate_watchdog \<Rightarrow> watchdog_chain \<Rightarrow> bool" where
  "rel_watchdog as cs \<longleftrightarrow> valid_watchdog cs \<and> as = event_time cs"

theorem watchdog_add_rule':
  assumes "0 < n"
    and "as evt_id = None"
  shows
  "\<lbrace> \<lambda>cs es. \<exists>cs'. rel_watchdog as cs' \<and> cs = cs' \<and> es = e0 \<rbrace>
     watchdog_add_impl evt_id n
   \<lbrace> \<lambda>_ cs es. rel_watchdog (as(evt_id \<mapsto> n)) cs \<and> es = e0 \<rbrace>!"
  apply (rule validNF_ex_pre)
  subgoal for cs'
    apply (subst validNF_conj_pre)
    apply auto
    apply (rule validNF_strengthen_post)
    apply (rule watchdog_add_impl_rule2[OF assms(1)])
    apply (auto simp add: rel_watchdog_def)
    apply (rule watchdog_add_valid) using assms apply auto
    apply (subst watchdog_add_full[OF _ assms(1)])
    using assms(2) by auto
  done

theorem watchdog_add_rule:
  assumes "n > 0"
    and "as evt_id = None"
  shows
  "\<lbrace> \<lambda>cs es. rel_watchdog as cs \<and> nil\<^sub>e es \<rbrace>
     watchdog_add_impl evt_id n
   \<lbrace> \<lambda>_ cs es. rel_watchdog (as(evt_id \<mapsto> n)) cs \<and> nil\<^sub>e es \<rbrace>!"
  apply (rule validNF_weaken_pre)
  unfolding nil_event_def
   apply (rule watchdog_add_rule')
  by (auto simp add: assms)


definition spec_watchdog_tick :: "astate_watchdog \<Rightarrow> astate_watchdog" where
  "spec_watchdog_tick as =
    (\<lambda>ev. case as ev of None \<Rightarrow> None
                       | Some n \<Rightarrow> if n > 1 then Some (n - 1) else None)"

definition spec_watchdog_tick_ev :: "astate_watchdog \<Rightarrow> task_id set" where
  "spec_watchdog_tick_ev as = {ev. as ev = Some 1}"

theorem watchdog_tick_full:
  assumes "rel_watchdog as cs"
  shows "set (fst (watchdog_tick cs)) = spec_watchdog_tick_ev as"
        "rel_watchdog (spec_watchdog_tick as) (snd (watchdog_tick cs))"
proof -
  have valid: "valid_watchdog cs"
    using assms unfolding rel_watchdog_def by auto
  have a: "evt_id \<in> set (fst (watchdog_tick cs)) \<longleftrightarrow> evt_id \<in> spec_watchdog_tick_ev as" for evt_id
    apply (cases "event_time cs evt_id = None")
    using assms apply (auto simp add: watchdog_tick_None spec_watchdog_tick_ev_def rel_watchdog_def)[1]
    apply (cases "event_time cs evt_id = Some 0")
    apply (auto simp add: watchdog_tick_triv[OF valid])[1]
    apply (cases "event_time cs evt_id = Some 1")
    using assms apply (auto simp add: watchdog_tick1 spec_watchdog_tick_ev_def rel_watchdog_def)[1]
    using assms by (auto simp add: watchdog_tick2[OF valid] spec_watchdog_tick_ev_def rel_watchdog_def)
  show "rel_watchdog (spec_watchdog_tick as) (snd (watchdog_tick cs))"
    apply (auto simp add: rel_watchdog_def)
    apply (rule watchdog_tick_valid[OF valid])
    apply (rule ext) subgoal for evt_id
      apply (cases "event_time cs evt_id = None")
      subgoal
        apply (auto simp add: watchdog_tick_None spec_watchdog_tick_def rel_watchdog_def)
        apply (cases "as evt_id") using assms rel_watchdog_def by auto
      apply (cases "event_time cs evt_id = Some 0")
      subgoal by (auto simp add: watchdog_tick_triv[OF valid])[1]
      apply (cases "event_time cs evt_id = Some 1")
      subgoal
        apply (auto simp add: watchdog_tick1[OF valid] spec_watchdog_tick_def)
        apply (cases "as evt_id") using assms rel_watchdog_def by auto
      apply (auto simp add: watchdog_tick2[OF valid] spec_watchdog_tick_def)
      apply (cases "as evt_id") using assms rel_watchdog_def by auto
    done
  show "set (fst (watchdog_tick cs)) = spec_watchdog_tick_ev as"
    using a by auto
qed

lemma watchdog_tick_event_distinct:
  assumes "rel_watchdog as cs"
  shows "distinct (map DISPATCH (fst (watchdog_tick cs)))"
proof -
  have a: "distinct (fst (watchdog_tick cs))"
    unfolding watchdog_tick_def
    apply (rule watchdog_tick_distinct)
    using assms(1) unfolding rel_watchdog_def valid_watchdog_def
    using decr_head_atmost_one by auto
  have b: "distinct es \<Longrightarrow> distinct (map DISPATCH es)" for es
    apply (induction es) by auto
  show ?thesis
    using a b by auto
qed

theorem watchdog_tick_rule':
  "\<lbrace> \<lambda>cs es. \<exists>cs'. rel_watchdog as cs' \<and> cs = cs' \<and> es = [] \<rbrace>
     watchdog_tick_impl
   \<lbrace> \<lambda>_ cs es. rel_watchdog (spec_watchdog_tick as) cs \<and>
               distinct es \<and>
               set es = DISPATCH ` (spec_watchdog_tick_ev as) \<rbrace>!"
  apply (rule validNF_ex_pre)
  subgoal for cs'
    apply (subst validNF_conj_pre)
    apply auto
    apply (rule validNF_strengthen_post)
     apply (rule watchdog_tick_impl_rule)
    apply (rule conjI)
    by (auto simp add: watchdog_tick_full watchdog_tick_event_distinct)
  done

theorem watchdog_tick_rule:
  "\<lbrace> \<lambda>cs es. rel_watchdog as cs \<and> nil\<^sub>e es \<rbrace>
     watchdog_tick_impl
   \<lbrace> \<lambda>_ cs es. rel_watchdog (spec_watchdog_tick as) cs \<and>
               distinct es \<and>
               set es = DISPATCH ` (spec_watchdog_tick_ev as) \<rbrace>!"
  apply (rule validNF_weaken_pre) unfolding nil_event_def
  apply (rule watchdog_tick_rule')
  by auto

theorem watchdog_remove_full:
  assumes "rel_watchdog as cs"
  shows "rel_watchdog (as(evt_id := None)) (watchdog_remove evt_id cs)"
proof -
  have valid: "valid_watchdog cs"
    using assms unfolding rel_watchdog_def by auto
  show ?thesis
    apply (auto simp add: rel_watchdog_def)
    apply (rule watchdog_remove_valid[OF valid])
    apply (rule ext) subgoal for evt_id'
      apply (cases "evt_id = evt_id'")
      subgoal apply auto apply (subst watchdog_remove_prop1')
        using assms by (auto simp add: valid_watchdog_def rel_watchdog_def)
      apply auto apply (subst watchdog_remove_prop2')
      using assms by (auto simp add: rel_watchdog_def)
    done
qed

theorem watchdog_remove_rule':
  "\<lbrace> \<lambda>cs es. \<exists>cs'. rel_watchdog as cs' \<and> cs = cs' \<and> es = e0 \<rbrace>
     watchdog_remove_impl evt_id
   \<lbrace> \<lambda>_ cs es. rel_watchdog (as(evt_id := None)) cs \<and> es = e0 \<rbrace>!"
  apply (rule validNF_ex_pre)
  subgoal for cs'
    apply (subst validNF_conj_pre)
    apply auto
    apply (rule validNF_strengthen_post)
     apply (rule watchdog_remove_impl_rule)
    apply auto
    apply (rule watchdog_remove_full)
    by (auto simp add: watchdog_remove_valid)
  done

theorem watchdog_remove_rule:
  "\<lbrace> \<lambda>cs es. rel_watchdog as cs \<and> nil\<^sub>e es \<rbrace>
     watchdog_remove_impl evt_id
   \<lbrace> \<lambda>_ cs es. rel_watchdog (as(evt_id := None)) cs \<and> nil\<^sub>e es \<rbrace>!"
  apply (rule validNF_weaken_pre) unfolding nil_event_def
   apply (rule watchdog_remove_rule')
  by auto

end

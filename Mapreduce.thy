theory Mapreduce
  imports EventSystem
begin


subsection \<open>Events\<close>

datatype event =
  QUERY "nat \<times> nat list"
| RESPOND nat
| TICK
| INIT

subsection \<open>Implementation of server\<close>

record server =
  input :: "nat list"
  index :: nat
  cursum :: nat
  returned :: bool

text \<open>Add a query\<close>
definition query_impl :: "nat list \<Rightarrow> (server, event, unit) event_monad" where
  "query_impl xs = put (\<lparr>input = xs, index = 0, cursum = 0, returned = False\<rparr>)"

theorem query_impl_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     query_impl xs
   \<lbrace> \<lambda>_ s es. s = \<lparr>input = xs, index = 0, cursum = 0, returned = False\<rparr> \<and> es = [] \<rbrace>!"
  unfolding query_impl_def apply wp by auto

text \<open>Implementation of tick: if there is a job present,
  nondeterministically advance one index.\<close>
definition tick_node_impl :: "(server, event, unit) event_monad" where
  "tick_node_impl = (get \<bind> (\<lambda>s.
   (if \<not>returned s then
      if index s = length (input s) then
        signal (RESPOND (cursum s)) \<bind> (\<lambda>_. put (s\<lparr>returned := True\<rparr>))
      else
        put (s\<lparr>index := index s + 1, cursum := cursum s + input s ! (index s)\<rparr>)
    else
      skip) \<squnion> skip))"

definition tick_node_fun :: "server \<Rightarrow> server \<times> event list" where
  "tick_node_fun s =
    (if \<not>returned s then
       if index s = length (input s) then
         (s\<lparr>returned := True\<rparr>, [RESPOND (cursum s)])
       else
         (s\<lparr>index := index s + 1, cursum := cursum s + input s ! (index s)\<rparr>, [])
     else
       (s, []))"

lemma tick_node_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. (s = fst (tick_node_fun s0) \<and> es = snd (tick_node_fun s0)) \<or>
              (s = s0 \<and> es = []) \<rbrace>!"
  unfolding tick_node_impl_def
  apply (rule validNF_bind)
   apply (rule validNF_get_post)
  subgoal for s'
    apply (subst validNF_conj_pre) apply (rule impI)
    apply (rule validNF_nondet2)
    subgoal apply wp by (auto simp add: tick_node_fun_def)
    subgoal by wp
    done
  done

fun node_inv :: "nat list \<times> bool \<Rightarrow> server \<Rightarrow> bool" where
  "node_inv (xs, b) s = (
    if b then returned s else
    input s = xs \<and> index s \<le> length xs \<and> \<not>returned s \<and>
    cursum s = sum (\<lambda>i. input s ! i) {0 ..< index s})"

definition sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list xs = sum (\<lambda>i. xs ! i) {0 ..< length xs}"

lemma tick_node_fun_inv:
  assumes "node_inv (xs, False) s"
  shows "(node_inv (xs, False) (fst (tick_node_fun s)) \<and> snd (tick_node_fun s) = []) \<or>
         (node_inv (xs, True) (fst (tick_node_fun s)) \<and> snd (tick_node_fun s) = [RESPOND (sum_list xs)])"
  using assms unfolding node_inv.simps tick_node_fun_def sum_list_def by auto

lemma tick_node_rule2:
  "node_inv (xs, False) s0 \<Longrightarrow>
   \<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. (node_inv (xs, False) s \<and> es = []) \<or>
              (node_inv (xs, True) s \<and> es = [RESPOND (sum_list xs)]) \<rbrace>!"
  apply (rule validNF_strengthen_post)
   apply (rule tick_node_rule)
  using tick_node_fun_inv by auto

lemma tick_node_rule3:
  "\<lbrace> \<lambda>s es. node_inv (xs, False) s \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. (node_inv (xs, False) s \<and> es = []) \<or>
              (node_inv (xs, True) s \<and> es = [RESPOND (sum_list xs)]) \<rbrace>!"
  apply (rule validNF_weaken_pre[where Q="\<lambda>s es. \<exists>s0. node_inv (xs, False) s0 \<and> s = s0 \<and> es = []"])
   apply (rule validNF_ex_pre)
  subgoal for s0 apply (subst validNF_conj_pre)
    using tick_node_rule2 by auto
  by auto

lemma tick_node_rule4:
  "node_inv (xs, True) s0 \<Longrightarrow>
   \<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. node_inv (xs, True) s \<and> es = [] \<rbrace>!"
  apply (rule validNF_strengthen_post)
   apply (rule tick_node_rule)
  by (auto simp add: tick_node_fun_def)

lemma tick_node_rule5:
  "\<lbrace> \<lambda>s es. node_inv (xs, True) s \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. node_inv (xs, True) s \<and> es = [] \<rbrace>!"
  apply (rule validNF_weaken_pre[where Q="\<lambda>s es. \<exists>s0. node_inv (xs, True) s0 \<and> s = s0 \<and> es = []"])
  apply (rule validNF_ex_pre)
  subgoal for s0 apply (subst validNF_conj_pre)
    using tick_node_rule4 by auto
  by auto

lemma tick_node_rule6:
  "\<lbrace> \<lambda>s es. node_inv (xs, b) s \<and> es = [] \<rbrace>
     tick_node_impl
   \<lbrace> \<lambda>_ s es. (node_inv (xs, b) s \<and> es = []) \<or> (b = False \<and> node_inv (xs, True) s \<and> es = [RESPOND (sum_list xs)]) \<rbrace>!"
  apply (cases b)
  using tick_node_rule3 tick_node_rule5 by auto

record client =
  num_received :: nat
  acc :: nat
  alldone :: bool

text \<open>Implementation of respond\<close>
definition respond_impl :: "nat \<Rightarrow> nat \<Rightarrow> (client, event, unit) event_monad" where
  "respond_impl N a = (get \<bind> (\<lambda>s.
    put (s\<lparr>acc := acc s + a, num_received := num_received s + 1\<rparr>)) \<bind> (\<lambda>_.
    get \<bind> (\<lambda>s.
    if num_received s = N then
      put (s\<lparr>alldone := True\<rparr>)
    else
      skip)))"

definition respond_fun :: "nat \<Rightarrow> nat \<Rightarrow> client \<Rightarrow> client" where
  "respond_fun N a s = (let s' = s\<lparr>acc := acc s + a, num_received := num_received s + 1\<rparr> in
                    if num_received s' = N then s'\<lparr>alldone := True\<rparr> else s')"

theorem validNF_respond:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     respond_impl N a
   \<lbrace> \<lambda>_ s es. s = respond_fun N a s0 \<and> es = [] \<rbrace>!"
  unfolding respond_impl_def
  apply wp by (auto simp add: respond_fun_def)

text \<open>Implementation of init\<close>
definition init_impl :: "nat \<Rightarrow> nat list list \<Rightarrow> (client, event, unit) event_monad" where
  "init_impl N data = (
    whileLoop (\<lambda>i _. i < N)
      (\<lambda>i. signal (QUERY (i, data ! i)) \<bind> (\<lambda>_.
           return (Suc i))) 0) \<bind> (\<lambda>_. return ())"

subsection \<open>Verify the event system\<close>

definition tick_impl :: "nat \<Rightarrow> (server list \<times> client, event, unit) event_monad" where
  "tick_impl N = (
    whileLoop (\<lambda>i _. i < N)
      (\<lambda>i. apply_fst (apply_idx tick_node_impl i) \<bind> (\<lambda>_.
           return (Suc i))) 0) \<bind> (\<lambda>_. return ())"

fun system :: "nat \<Rightarrow> nat list list \<Rightarrow> (event, server list \<times> client) event_system" where
  "system N data (QUERY (i, xs)) = Some (apply_fst (apply_idx (query_impl xs) i))"
| "system N data (RESPOND a) = Some (apply_snd (respond_impl N a))"
| "system N data TICK = Some (tick_impl N)"
| "system N data INIT = Some (apply_snd (init_impl N data))"

definition server_inv :: "nat \<Rightarrow> nat list list \<Rightarrow> bool list \<Rightarrow> server list \<Rightarrow> bool" where
  "server_inv N data bs ss =
    (length bs = N \<and> length ss = N \<and>
    (\<forall>i. i < N \<longrightarrow> node_inv (data ! i, bs ! i) (ss ! i)))"

fun tick_events :: "nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> event list" where
  "tick_events N bs bs' xss 0 = []"
| "tick_events N bs bs' xss (Suc i) =
    (if \<not>bs ! i \<and> bs' ! i then tick_events N bs bs' xss i @ [RESPOND (sum_list (xss ! i))]
     else tick_events N bs bs' xss i)"

lemma tick_events_cong:
  "\<forall>i<r. bs1 ! i = bs2 ! i \<Longrightarrow> tick_events N bs bs1 xss r = tick_events N bs bs2 xss r"
  apply (induction r) by auto

definition dominates :: "nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool" where
  "dominates N bs bs' = (\<forall>i<N. bs ! i \<longrightarrow> bs' ! i)"

lemma tick_rule:
  "\<lbrace> \<lambda>p es. server_inv N xss bs (fst p) \<and> snd p = c0 \<and> nil\<^sub>e es \<rbrace>
     tick_impl N
   \<lbrace> \<lambda>_ p es. \<exists>bs'. server_inv N xss bs' (fst p) \<and> dominates N bs bs' \<and> snd p = c0 \<and> es = tick_events N bs bs' xss N \<rbrace>!"
  unfolding tick_impl_def
  apply (rule validNF_bind) prefer 2 apply (rule validNF_return)
  apply (rule validNF_whileLoop[where
        I="\<lambda>i p es. i \<le> N \<and> (\<exists>bs'. server_inv N xss bs' (fst p) \<and>
              length bs' = N \<and> dominates N bs bs' \<and> (\<forall>j\<ge>i. bs ! j = bs' ! j) \<and>
              snd p = c0 \<and> es = tick_events N bs bs' xss i)" and
        R="measure (\<lambda>(i,p). (N - i))"])
  subgoal for p es
    apply (rule conjI) apply simp
    apply (rule exI[where x=bs])
    by (auto simp add: nil_event_def server_inv_def dominates_def)
  subgoal for r s
    apply (rule validNF_bind) prefer 2
     apply (rule validNF_return)
    apply (rule validNF_weaken_pre[where
          Q="\<lambda>p es. r < N \<and> (\<exists>bs'. (length bs' = N \<and> dominates N bs bs' \<and>
                (\<forall>i\<ge>r. bs ! i = bs' ! i)) \<and>
                (server_inv N xss bs' (fst p) \<and> es = tick_events N bs bs' xss r) \<and> snd p = c0)"])
     prefer 2 subgoal by auto
    apply (subst validNF_conj_pre) apply (rule impI)
    apply (rule validNF_ex_pre) subgoal premises pre for bs'
      apply (subst validNF_conj_pre) apply (rule impI)
      apply (subst server_inv_def)
      apply (rule validNF_strengthen_post)
       apply (rule validNF_apply_fst)
       apply (rule validNF_frame)
       apply (rule validNF_weaken_pre[where
            Q="\<lambda>p es. length p = N \<and> (\<forall>i. i < N \<longrightarrow> node_inv (xss ! i, bs' ! i) (p ! i)) \<and> nil\<^sub>e es"])
        prefer 2 subgoal by (auto simp add: nil_event_def)
       apply (rule validNF_apply_idx2)
      unfolding nil_event_def apply (rule tick_node_rule6)
      apply (rule pre)
      subgoal for r' s' es'
        unfolding chop_event_def apply clarify subgoal for es1 es2
          apply (elim disjE)
          subgoal
            apply (intro conjI)
            subgoal using pre by auto
            subgoal apply (rule exI[where x=bs'])
              by (auto simp add: server_inv_def)
            subgoal using pre by auto
            done
          subgoal
            apply (intro conjI)
            subgoal using pre by auto
            subgoal apply (rule exI[where x="bs'[r := True]"])
              apply (intro conjI)
              subgoal unfolding server_inv_def
                apply (rule conjI) apply simp
                apply clarify subgoal for i apply (cases "i = r")
                  subgoal by auto
                  subgoal by auto
                  done
                done
              subgoal by auto
              subgoal by (metis dominates_def nth_list_update pre)
              subgoal by auto
              subgoal by auto
              subgoal unfolding tick_events.simps
                using pre by (auto simp add: tick_events_cong)
              done
            subgoal using pre by auto
            done
          done
        done
      done
    done
  subgoal by auto
  subgoal by auto
  done

lemma sValidNF_Respond:
  "sValidNF (system N data)
    (\<lambda>p es. P (fst p) \<and> snd p = c \<and> nil\<^sub>e es)
    (RESPOND a)
    (\<lambda>p es. P (fst p) \<and> snd p = respond_fun N a c \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where P="\<lambda>p es. (P (fst p) \<and> snd p = c) \<and> nil\<^sub>e es"])
  apply simp
  apply (rule sValidNF_Some)
  apply (rule system.simps)
  apply (rule validNF_weaken_pre)
  apply (rule validNF_apply_snd[where R="\<lambda>s. P s"])
    apply (rule validNF_respond)
   apply (auto simp add: nil_event_def)
  apply (rule sValidNF_list_strengthen_post)
  prefer 2 
   apply (rule sValidNF_list_null)
  by auto

fun sum_tick_events :: "nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_tick_events N bs bs' xss 0 = 0"
| "sum_tick_events N bs bs' xss (Suc i) =
    (if \<not>bs ! i \<and> bs' ! i then sum_tick_events N bs bs' xss i + sum_list (xss ! i)
     else sum_tick_events N bs bs' xss i)"

fun count_tick_events :: "nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> nat" where
  "count_tick_events N bs bs' xss 0 = 0"
| "count_tick_events N bs bs' xss (Suc i) =
    (if \<not>bs ! i \<and> bs' ! i then count_tick_events N bs bs' xss i + 1
     else count_tick_events N bs bs' xss i)"

lemma sValidNF_Respond_tick_events:
  assumes "num_received c \<ge> N \<longleftrightarrow> alldone c"
  shows
  "sValidNF_list (system N data)
    (\<lambda>p es. P (fst p) \<and> snd p = c \<and> nil\<^sub>e es)
    (tick_events N bs bs' data i)
    (\<lambda>p es. P (fst p) \<and> snd p = c\<lparr>acc := acc c + sum_tick_events N bs bs' data i,
         num_received := num_received c + count_tick_events N bs bs' data i,
         alldone := alldone c \<or> (\<exists>i'\<le>i. num_received c + count_tick_events N bs bs' data i' = N)\<rparr> \<and> nil\<^sub>e es)"
proof (induction i)
  case 0
  then show ?case 
    apply auto
    apply (rule sValidNF_list_strengthen_post) prefer 2
     apply (rule sValidNF_list_null)
    using assms by auto
next
  case (Suc i)
  show ?case
    apply (cases "\<not>bs ! i \<and> bs' ! i")
    subgoal apply auto
      apply (rule sValidNF_list_append)
       apply (rule Suc)
      apply (rule sValidNF_list_single)
      apply (rule sValidNF_strengthen_post)
      prefer 2
      apply (rule sValidNF_Respond)
      apply (auto simp add: respond_fun_def Let_def)
      subgoal premises pre for es
      proof -
        have "num_received c + count_tick_events N bs bs' data (Suc i) = N"
          using pre by auto
        then have "\<exists>i'\<le>Suc i. num_received c + count_tick_events N bs bs' data i' = N"
          by auto
        then show ?thesis
          by auto
      qed
      subgoal premises pre for es
      proof -
        have "num_received c + count_tick_events N bs bs' data (Suc i) \<noteq> N"
          using pre by auto
        then have "(\<exists>i'\<le>i. num_received c + count_tick_events N bs bs' data i' = N) \<longleftrightarrow>
                   (\<exists>i'\<le>Suc i. num_received c + count_tick_events N bs bs' data i' = N)"
          using le_Suc_eq by blast
        then show ?thesis
          by auto
      qed
      done
    subgoal premises pre
    proof -
      have "count_tick_events N bs bs' data (Suc i) = count_tick_events N bs bs' data i"
        using pre by auto
      then have a: "(\<exists>i'\<le>i. num_received c + count_tick_events N bs bs' data i' = N) \<longleftrightarrow>
                 (\<exists>i'\<le>Suc i. num_received c + count_tick_events N bs bs' data i' = N)"
        by (metis le_Suc_eq pl_pl_rels)
      show ?thesis
        apply (auto simp add: pre)
        apply (rule sValidNF_list_strengthen_post)
         prefer 2 apply (rule Suc)
        using a by auto
    qed
    done
qed

lemma sValidNF_Tick:
  assumes "num_received c0 \<ge> N \<longleftrightarrow> alldone c0"
  shows
  "sValidNF (system N data)
    (\<lambda>p es. server_inv N data bs (fst p) \<and> snd p = c0 \<and> nil\<^sub>e es)
    TICK
    (\<lambda>p es. \<exists>bs'. server_inv N data bs' (fst p) \<and> dominates N bs bs' \<and>
        snd p = c0\<lparr>acc := acc c0 + sum_tick_events N bs bs' data N,
                   num_received := num_received c0 + count_tick_events N bs bs' data N,
                   alldone := alldone c0 \<or> (\<exists>i'\<le>N. num_received c0 + count_tick_events N bs bs' data i' = N)\<rparr> \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where P="\<lambda>p es. (server_inv N data bs (fst p) \<and> snd p = c0) \<and> nil\<^sub>e es"])
  apply simp
  apply (rule sValidNF_Some)
  apply (rule system.simps)
   apply (subst conj_assoc)
  apply (rule tick_rule)
  subgoal for p es
    apply clarify subgoal for bs'
      apply (rule sValidNF_list_strengthen_post) prefer 2
       apply (rule sValidNF_list_weaken_pre[where P="\<lambda>p es. server_inv N data bs' (fst p) \<and> snd p = c0 \<and> nil\<^sub>e es"])
      apply auto[1]
      apply (rule sValidNF_Respond_tick_events[OF assms])
      subgoal for p' es'
        apply (rule exI[where x=bs'])
        by auto
      done
    done
  done

fun system_inv :: "nat \<Rightarrow> nat list list \<Rightarrow> server list \<times> client \<Rightarrow> bool" where
  "system_inv N data (ss, c) =
    (\<exists>bs. server_inv N data bs ss \<and>
          num_received c = sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< N} \<and>
          acc c = sum (\<lambda>i. if bs ! i then sum_list (data ! i) else 0) {0 ..< N} \<and>
          alldone c = (num_received c \<ge> N))"

lemma dominates_num_received':
  assumes "dominates N bs bs'"
  shows
    "k \<le> N \<Longrightarrow>
     sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< k} + count_tick_events N bs bs' data k =
     sum (\<lambda>i. if bs' ! i then 1 else 0) {0 ..< k}"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  show ?case
    apply auto
    subgoal using Suc by auto
    subgoal using Suc by auto
    subgoal using assms(1) unfolding dominates_def
      using Suc by simp
    done
qed

lemma dominates_num_received:
  "dominates N bs bs' \<Longrightarrow>
   sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< N} + count_tick_events N bs bs' data N =
   sum (\<lambda>i. if bs' ! i then 1 else 0) {0 ..< N}"
  using dominates_num_received' by auto

lemma dominates_acc':
  assumes "dominates N bs bs'"
  shows
    "k \<le> N \<Longrightarrow>
      sum (\<lambda>i. if bs ! i then sum_list (data ! i) else 0) {0 ..< k} + sum_tick_events N bs bs' data k =
      sum (\<lambda>i. if bs' ! i then sum_list (data ! i) else 0) {0 ..< k}"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  show ?case
    apply auto
    subgoal using Suc by auto
    subgoal using Suc by auto
    subgoal using assms(1) unfolding dominates_def
      using Suc by simp
    done
qed

lemma dominates_acc:
  "dominates N bs bs' \<Longrightarrow>
   sum (\<lambda>i. if bs ! i then sum_list (data ! i) else 0) {0 ..< N} + sum_tick_events N bs bs' data N =
   sum (\<lambda>i. if bs' ! i then sum_list (data ! i) else 0) {0 ..< N}"
  using dominates_acc' by auto

lemma count_tick_events_mono:
  "count_tick_events N bs bs' data i \<le> count_tick_events N bs bs' data (a + i)"
  apply (induction a) by auto 

lemma count_tick_events_mono2:
  "i \<le> j \<Longrightarrow> count_tick_events N bs bs' data i \<le> count_tick_events N bs bs' data j"
  using count_tick_events_mono
  by (metis add.commute nat_le_iff_add)

lemma count_tick_events_dense:
  "a \<le> count_tick_events N bs bs' data j \<Longrightarrow> \<exists>i\<le>j. a = count_tick_events N bs bs' data i"
proof (induction j)
  case 0
  then show ?case by auto
next
  case (Suc j)
  have "a \<le> count_tick_events N bs bs' data j + 1"
    using Suc(2) apply (cases "\<not> bs ! j \<and> bs' ! j") by auto
  have "a \<le> count_tick_events N bs bs' data j + 1"
    using Suc(2) apply (cases "\<not> bs ! j \<and> bs' ! j") by auto
  then have "a = count_tick_events N bs bs' data j + 1 \<or> a \<le> count_tick_events N bs bs' data j"
    by auto
  then show ?case
    apply (elim disjE)
    subgoal apply (rule exI[where x="Suc j"])
      by (metis Suc.prems add_diff_cancel_left' add_le_cancel_right count_tick_events.simps(2)
                diff_is_0_eq' le_numeral_extra(4) plus_1_eq_Suc zero_neq_one)
    subgoal using Suc(1)
      by (meson le_SucI)
    done
qed

lemma count_tick_events_dense2:
  assumes "N > num_received c0"
    and "N \<le> num_received c0 + count_tick_events N bs bs' data N"
  shows "\<exists>i\<le>N. N = num_received c0 + count_tick_events N bs bs' data i"
proof -
  have a: "N - num_received c0 \<le> count_tick_events N bs bs' data N"
    using assms by auto
  then obtain i where b: "i \<le> N" "N - num_received c0 = count_tick_events N bs bs' data i"
    using count_tick_events_dense by blast
  then have c: "N = num_received c0 + count_tick_events N bs bs' data i"
    using assms by auto
  show ?thesis
    using b c by auto
qed

lemma count_tick_events_incr:
  "(N \<le> num_received c0 \<or> (\<exists>i'\<le>N. num_received c0 + count_tick_events N bs bs' data i' = N)) \<longleftrightarrow>
   (N \<le> num_received c0 + count_tick_events N bs bs' data N)"
  apply (rule iffI, elim disjE)
  subgoal by auto
  subgoal using count_tick_events_mono2
    by (metis add_left_mono)
  subgoal using count_tick_events_dense2
    by (metis not_le_imp_less)
  done

lemma sValidNF_Tick2:
  "sValidNF (system N data)
    (\<lambda>p es. system_inv N data p \<and> nil\<^sub>e es)
    TICK
    (\<lambda>p es. system_inv N data p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where
        P="\<lambda>p es. \<exists>bs c0. (num_received c0 \<ge> N \<longleftrightarrow> alldone c0) \<and>
            num_received c0 = sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< N} \<and>
            acc c0 = sum (\<lambda>i. if bs ! i then sum_list (data ! i) else 0) {0 ..< N} \<and>
            server_inv N data bs (fst p) \<and>
            snd p = c0 \<and> nil\<^sub>e es"])
  subgoal for p es
    apply (cases p) by auto
  apply (subst sValidNF_exists_pre2) apply (rule allI)
  apply (subst sValidNF_exists_pre2) apply (rule allI)
  apply (subst sValidNF_conj_pre) apply (rule impI)
  apply (subst sValidNF_conj_pre) apply (rule impI)
  apply (subst sValidNF_conj_pre) apply (rule impI)
  subgoal premises pre for bs c0
    apply (rule sValidNF_strengthen_post) prefer 2
     apply (rule sValidNF_Tick[OF pre(1)])
    subgoal for p es
      apply (cases p) subgoal for ss c
        apply clarify subgoal for bs'
          unfolding system_inv.simps
          apply (rule exI[where x=bs'])
          apply (intro conjI)
          subgoal by auto
          subgoal apply (auto simp add: pre(2))
            apply (rule dominates_num_received) by auto
          subgoal apply (auto simp add: pre(3))
            apply (rule dominates_acc) by auto
          subgoal apply simp
            using pre(1) count_tick_events_incr by blast
          done
        done
      done
    done
  done

subsection \<open>Final results\<close>

theorem validNF_init:
  "\<lbrace> \<lambda>c es. c = c0 \<and> es = [] \<rbrace>
     init_impl N data
   \<lbrace> \<lambda>_ c es. c = c0 \<and> es = map (\<lambda>i. QUERY (i, data ! i)) [0 ..< N] \<rbrace>!"
  unfolding init_impl_def
  apply (rule validNF_bind) prefer 2
   apply (rule validNF_return)
  apply (rule validNF_whileLoop[where I="\<lambda>r c es. c = c0 \<and> r \<le> N \<and> es = map (\<lambda>i. QUERY (i, data ! i)) [0 ..< r]" and
                                      R="measure (\<lambda>(r,c). (N - r))"])
  subgoal for c es by auto
  subgoal for r s apply wp by auto
  subgoal by auto
  subgoal for r s es by auto
  done

theorem sValidNF_Query:
  "sValidNF (system N data)
    (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es)
    (QUERY (i, data ! i))
    (\<lambda>p es. p = (ss[i := \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>], c0) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
    apply (rule validNF_apply_fst[where R="\<lambda>s. s = c0"])
    apply (rule validNF_apply_idx[OF query_impl_rule])
  apply (auto simp add: nil_event_def)[1]
  apply auto by (rule sValidNF_list_null)

theorem sValidNF_list_queries:
  assumes "length ss = N"
  shows
  "j \<le> N \<Longrightarrow>
   sValidNF_list (system N data)
    (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es)
      (map (\<lambda>i. QUERY (i, data ! i)) [0..<j])
    (\<lambda>p es. p = (map (\<lambda>i. if i < j then \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>
                          else ss ! i) [0..<N], c0) \<and> nil\<^sub>e es)"
proof (induction j)
  case 0
  then show ?case
    using assms apply (auto simp add: map_nth)
    by (rule sValidNF_list_null)
next
  case (Suc j)
  have a: "map (\<lambda>i. QUERY (i, data ! i)) [0..<Suc j] = map (\<lambda>i. QUERY (i, data ! i)) [0..<j] @ [QUERY (j, data ! j)]"
    by auto
  have b: "sValidNF_list (system N data) (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es) (map (\<lambda>i. QUERY (i, data ! i)) [0..<j])
   (\<lambda>p es. p = (map (\<lambda>i. if i < j then \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr> else ss ! i) [0..<N], c0) \<and>
          nil\<^sub>e es)"
    using Suc by auto
  show ?case
    unfolding a apply (rule sValidNF_list_append)
     apply (rule b)
    apply (rule sValidNF_list_single)
    apply (rule sValidNF_strengthen_post) prefer 2
     apply (rule sValidNF_Query)
    apply auto
    apply (rule nth_equalityI)
     apply auto subgoal for es i
      apply (cases "i = j") by auto
    done
qed

theorem sValidNF_list_queries':
  assumes "length ss = N"
  shows
  "sValidNF_list (system N data)
    (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es)
    (map (\<lambda>i. QUERY (i, data ! i)) [0..<N])
    (\<lambda>p es. p = (map (\<lambda>i. \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>) [0..<N], c0) \<and> nil\<^sub>e es)"
proof -
  have a: "sValidNF_list (system N data)
    (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es)
      (map (\<lambda>i. QUERY (i, data ! i)) [0..<N])
    (\<lambda>p es. p = (map (\<lambda>i. if i < N then \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>
                          else ss ! i) [0..<N], c0) \<and> nil\<^sub>e es)"
    using sValidNF_list_queries[OF assms, where j=N] by auto
  have b: "map (\<lambda>i. if i < N then \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>
                    else ss ! i) [0..<N] = map (\<lambda>i. \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>) [0 ..< N]"
    apply (rule nth_equalityI)
    by auto
  show ?thesis
    using a b by auto
qed

fun init_state :: "nat \<Rightarrow> server list \<times> client \<Rightarrow> bool" where
  "init_state N (ss, c) \<longleftrightarrow> length ss = N \<and> c = \<lparr>num_received = 0, acc = 0, alldone = False\<rparr>"

theorem sValidNF_init:
  assumes "length ss = N"
  shows
  "sValidNF (system N data)
    (\<lambda>p es. p = (ss, c0) \<and> nil\<^sub>e es)
     INIT
    (\<lambda>p es. p = (map (\<lambda>i. \<lparr>input = data ! i, index = 0, cursum = 0, returned = False\<rparr>) [0 ..< N], c0) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
    apply (rule validNF_apply_snd[where R="\<lambda>s. s = ss"])
    apply (rule validNF_init)
   apply (auto simp add: nil_event_def)
  using sValidNF_list_queries'[OF assms] unfolding nil_event_def by auto

theorem sValidNF_init_inv:
  assumes "N > 0"
  shows
  "sValidNF (system N data)
    (\<lambda>p es. init_state N p \<and> nil\<^sub>e es)
     INIT
    (\<lambda>p es. system_inv N data p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where P="\<lambda>p es. \<exists>ss c. init_state N (ss, c) \<and> p = (ss, c) \<and> nil\<^sub>e es"])
   apply auto[1]
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_conj_pre) apply clarify
  subgoal premises pre for ss c
    apply (rule sValidNF_strengthen_post)
     prefer 2 apply (rule sValidNF_init)
    using pre apply auto[1]
    subgoal for p es
      apply auto apply (rule exI[where x="map (\<lambda>i. False) [0..<N]"])
      using pre assms by (auto simp add: server_inv_def)
    done
  done

theorem system_inv_sum:
  assumes "system_inv N data (ss, c)"
    and "alldone c"
  shows "acc c = sum (\<lambda>i. sum_list (data ! i)) {0 ..< N}"
proof -
  obtain bs where a: "server_inv N data bs ss"
    "num_received c = sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< N}"
    "acc c = sum (\<lambda>i. if bs ! i then sum_list (data ! i) else 0) {0 ..< N}"
    "alldone c = (num_received c \<ge> N)"
    using assms by auto
  have b: "(\<forall>i<j. bs ! i) \<longleftrightarrow> sum (\<lambda>i. if bs ! i then 1 else 0) {0 ..< j} \<ge> j" for j
    apply (induction j)
    apply auto using not_less_less_Suc_eq by auto
  have c: "\<forall>i<N. bs ! i"
    using a(2,4) assms(2) b by auto
  show ?thesis
    using a(3) c by auto
qed

theorem system_inv_all':
  assumes "N > 0"
  shows
  "sValidNF_list (system N data)
    (\<lambda>p es. init_state N p \<and> nil\<^sub>e es)
    (INIT # replicate n TICK)
    (\<lambda>p es. system_inv N data p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_list_cons)
  apply (rule sValidNF_init_inv[OF assms])
  apply (induction n)
  subgoal apply auto by (rule sValidNF_list_null)
  subgoal for n
    apply auto apply (rule sValidNF_list_cons)
     apply (rule sValidNF_Tick2)
    by auto
  done

theorem system_inv_all:
  assumes "N > 0"
  shows
  "sValidNF_list (system N data)
    (\<lambda>p es. init_state N p \<and> nil\<^sub>e es)
    (INIT # replicate n TICK)
    (\<lambda>p es. (alldone (snd p) \<longrightarrow> acc (snd p) = sum (\<lambda>i. sum_list (data ! i)) {0 ..< N}) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_list_strengthen_post)
  prefer 2 apply (rule system_inv_all'[OF assms])
  using system_inv_sum by auto

end

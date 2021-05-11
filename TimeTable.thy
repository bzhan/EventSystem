section \<open>Time tables\<close>

theory TimeTable
  imports Main
begin

text \<open>Partitions and IDs for time tables are both specified by natural
  numbers.\<close>
type_synonym partition = nat
type_synonym ttbl_id = nat

text \<open>Each time table is specified by a list of windows, each window
  specifies the partition id and the length of the window.

  For example, [(1, 10), (2, 15), (1, 5)] means a frame has a total length
  of 30 ticks. The first 10 ticks in partition 1, next 15 ticks in
  partition 2, and the last 5 ticks in partition 1.
\<close>
type_synonym time_table = "(partition \<times> nat) list"

text \<open>Returns the total frame length of the time table.\<close>
fun frame_length :: "time_table \<Rightarrow> nat" where
  "frame_length [] = 0"
| "frame_length ((p, n) # fs) = n + frame_length fs"

text \<open>Amount of time spent at partition in one frame.\<close>
fun partition_time :: "time_table \<Rightarrow> partition \<Rightarrow> nat" where
  "partition_time [] p' = 0"
| "partition_time ((p, n) # fs) p' = (if p = p' then n + partition_time fs p' else partition_time fs p')"

text \<open>Returns the partition for the t'th tick of the time table.
  If t is greater than or equal to the total frame time, return undefined.\<close>
fun partition_at_time :: "time_table \<Rightarrow> nat \<Rightarrow> partition" where
  "partition_at_time [] t = undefined"
| "partition_at_time ((p, n) # fs) t = (if t < n then p else partition_at_time fs (t - n))"

text \<open>Whether the given time is at a window boundary.
  If t is  equal to the window time minus one, return False.\<close>
fun at_window_boundary :: "time_table \<Rightarrow> nat \<Rightarrow> bool" where
  "at_window_boundary [] t = False"
| "at_window_boundary ((p, n) # fs) t = (if t < n then t = (n - 1) else at_window_boundary fs (t - n))"


text \<open>Id of the current window, given the total amount of time spent in frame.\<close>
fun cur_window_id :: "time_table \<Rightarrow> nat \<Rightarrow> nat" where
  "cur_window_id [] t = undefined"
| "cur_window_id ((p, n) # fs) t = (if t < n then 0 else cur_window_id fs (t - n) + 1)"

text \<open>Amount of time spent in the current window.\<close>
fun cur_window_time :: "time_table \<Rightarrow> nat \<Rightarrow> nat" where
  "cur_window_time [] t = undefined"
| "cur_window_time ((p, n) # fs) t = (if t < n then t else cur_window_time fs (t - n))"

text \<open>Time to the next window boundary.\<close>
fun time_to_next_window :: "time_table \<Rightarrow> nat \<Rightarrow> nat" where
  "time_to_next_window tbl t = (
    let window_id = cur_window_id tbl t;
        window_time = cur_window_time tbl t
     in
       snd (tbl ! window_id) - window_time)"

text \<open>Amount of time until the start of next frame.\<close>
fun time_to_next_frame :: "time_table \<Rightarrow> nat \<Rightarrow> nat" where
  "time_to_next_frame tbl t = frame_length tbl - t"

text \<open>Whether a time table contains frames of length zero. This condition
  may be needed in some of the future proofs.\<close>
fun is_valid_time_table' :: "time_table \<Rightarrow> bool" where
  "is_valid_time_table' [] = True"
| "is_valid_time_table' ((p, n) # fs) \<longleftrightarrow> (n \<noteq> 0 \<and> is_valid_time_table' fs)"

fun is_valid_time_table :: "time_table \<Rightarrow> bool" where
  "is_valid_time_table ttbl \<longleftrightarrow> length ttbl > 1 \<and> is_valid_time_table' ttbl"

lemma valid_time_table_frame_length:
  assumes "is_valid_time_table ttbl"
  shows "frame_length ttbl > 0"
proof (cases ttbl)
  case Nil
  then show ?thesis
    using assms by auto
next
  case (Cons a fs)
  show ?thesis
  proof (cases a)
    case (Pair p n)
    have "n > 0"
      using assms unfolding Cons Pair by auto
    then show ?thesis
      unfolding Cons Pair by simp
  qed
qed

lemma window_time_pos':
  "is_valid_time_table' tbl \<Longrightarrow> i < length tbl \<Longrightarrow> snd (tbl ! i) > 0"
  apply (induction tbl arbitrary: i) apply auto
  using less_Suc_eq_0_disj by fastforce

lemma window_time_pos:
  "is_valid_time_table tbl \<Longrightarrow> i < length tbl \<Longrightarrow> snd (tbl ! i) > 0"
  using window_time_pos' by auto

text \<open>Returns the total frame time up to (but not including) window k.\<close>
fun frame_time_to_window :: "time_table \<Rightarrow> nat \<Rightarrow> nat" where
  "frame_time_to_window [] i = 0"
| "frame_time_to_window ((p, n) # tbl) 0 = 0"
| "frame_time_to_window ((p, n) # tbl) (Suc i) = n + frame_time_to_window tbl i"

lemma frame_time_to_window_zero [simp]:
  "frame_time_to_window tbl 0 = 0"
  apply (cases tbl) by auto

lemma frame_time_to_window_total:
  "frame_time_to_window tbl (length tbl) = frame_length tbl"
  apply (induction tbl) by auto

lemma frame_time_to_window_mono:
  "a \<le> b \<Longrightarrow> frame_time_to_window tbl a \<le> frame_time_to_window tbl b"
proof (induct b arbitrary: a tbl)
  case 0
  then show ?case by auto
next
  case (Suc b)
  show ?case
  proof (cases tbl)
    case Nil
    then show ?thesis by auto
  next
    case (Cons x list)
    then show ?thesis
      apply (cases x)
      subgoal for p n
        apply (cases a) apply auto
        subgoal for a'
          apply (rule Suc(1)) using Suc(2) by auto
        done
      done
  qed
qed

lemma frame_time_to_window_next:
  "i < length tbl \<Longrightarrow> frame_time_to_window tbl (Suc i) = frame_time_to_window tbl i + snd (tbl ! i)"
proof (induct tbl arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons pn tbl)
  then show ?case
    apply (cases pn)
    subgoal for p n
      apply auto apply (cases i) by auto
    done
qed

lemma frame_time_to_window_mono_strict:
  assumes "is_valid_time_table tbl"
    and "a < b"
    and "a < length tbl"
  shows "frame_time_to_window tbl a < frame_time_to_window tbl b"
proof -
  have a1: "Suc a \<le> b"
    using assms(2) by auto
  have a2: "frame_time_to_window tbl (Suc a) \<le> frame_time_to_window tbl b"
    using a1 frame_time_to_window_mono by auto
  have a3: "frame_time_to_window tbl a < frame_time_to_window tbl (Suc a)"
    unfolding frame_time_to_window_next[OF assms(3)]
    using assms(1,3) window_time_pos by auto
  show ?thesis
    using a2 a3 by auto
qed

lemma frame_time_to_window_inj:
  assumes "is_valid_time_table tbl"
    and "a \<le> length tbl"
    and "b \<le> length tbl"
    and "frame_time_to_window tbl a = frame_time_to_window tbl b"
  shows "a = b"
  by (metis assms frame_time_to_window_mono_strict less_le_trans less_not_refl3 linorder_neqE_nat)

lemma at_window_boundary_wpos:
  "is_valid_time_table' tbl \<Longrightarrow> wid < length tbl \<Longrightarrow> wpos > 0 \<Longrightarrow> wpos \<le> snd (tbl ! wid) \<Longrightarrow>
   at_window_boundary tbl (frame_time_to_window tbl (wid + 1) - wpos) \<longleftrightarrow> wpos = 1"
proof (induction tbl arbitrary: wid)
  case Nil
  then show ?case by auto
next
  case (Cons pair tbl')
  show ?case
  proof (cases pair)
    case (Pair p n)
    have a: "n > 0"
      using Cons(2) unfolding Pair by auto
    show ?thesis
    proof (cases wid)
      case 0
      show ?thesis
        unfolding 0 Pair using a apply auto
        using Cons.prems(4) Pair 0 apply auto[1]
        by (simp add: Cons.prems(3))
    next
      case (Suc wid')
      have b1: "is_valid_time_table' tbl'"
        using Cons(2) unfolding Pair by auto
      have b2: "wpos \<le> snd (tbl' ! wid')"
        using Cons(5) unfolding Pair Suc by auto
      have b3: "wid' < length tbl'"
        using Cons(3) unfolding Pair Suc by auto
      have b4: "at_window_boundary tbl' (frame_time_to_window tbl' (wid' + 1) - wpos) = (wpos = 1)"
        using Cons(1)[OF b1 b3 Cons(4) b2] by auto
      show ?thesis
        unfolding Pair Suc using b4 apply auto
        unfolding frame_time_to_window_next[OF b3]
        using b2 by linarith
    qed
  qed
qed

lemma partition_at_time_frame_time_to_window:
  "is_valid_time_table' tbl \<Longrightarrow> wid < length tbl \<Longrightarrow> partition_at_time tbl (frame_time_to_window tbl wid) = fst (tbl ! wid)"
proof (induction tbl arbitrary: wid)
  case Nil
  then show ?case by auto
next
  case (Cons pair tbl')
  show ?case
  proof (cases pair)
    case (Pair p n)
    have a: "n > 0"
      using Cons(2) unfolding Pair by auto
    show ?thesis
    proof (cases wid)
      case 0
      then show ?thesis unfolding Pair using a by auto
    next
      case (Suc wid')
      have b: "partition_at_time tbl' (frame_time_to_window tbl' wid') = fst (tbl' ! wid')"
        apply (rule Cons(1))
        using Cons(2,3) unfolding Pair Suc by auto
      show ?thesis
        unfolding Pair Suc using b by auto
    qed
  qed
qed

lemma at_frame_boundary_also_window_boundary:
  assumes "is_valid_time_table tbl"
  shows "at_window_boundary tbl (frame_length tbl - 1)"
proof -
  have a: "at_window_boundary tbl (frame_time_to_window tbl (length tbl - 1 + 1) - 1)"
    apply (subst at_window_boundary_wpos)
    using assms apply auto
    by (simp add: Suc_leI window_time_pos)
  show ?thesis
    using a unfolding frame_time_to_window_total[symmetric]
    by (metis One_nat_def Suc_pred add.right_neutral add_Suc_right assms is_valid_time_table.elims(2)
              length_greater_0_conv less_imp_le list.size(3) not_le zero_less_Suc)
qed

text \<open>Three switch modes: switch at next tick, switch at next window,
  and switch at next time frame.\<close>
datatype switch_mode = NO_SWITCH | NEXT_TICK | NEXT_WINDOW | NEXT_FRAME | ONGOING

text \<open>Global state contains a list of time tables, indexed by ID.
  We require that all time tables with valid ID (less than 256) are valid.
\<close>
locale global_state =
  fixes time_tables :: "ttbl_id \<Rightarrow> time_table"
  assumes valid_time_table: "\<And>n. n < 256 \<Longrightarrow> is_valid_time_table (time_tables n)"

end

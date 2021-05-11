theory EventSystemSwitchScheduler
  imports EventSystemExBase
begin                        

subsection \<open>Abstract scheduler\<close>

record astate_scheduler =
  cur_ttbl_id :: ttbl_id    \<comment> \<open>ID of current table\<close>
  window_id :: nat          \<comment> \<open>Current window in the frame\<close>
  reset :: bool             \<comment> \<open>Reset state for intermediate computations\<close>
  next_ttbl_id :: ttbl_id   \<comment> \<open>ID of next table (0 when not switching\<close>
  next_mode :: switch_mode  \<comment> \<open>Switch mode\<close>

definition init_astate :: astate_scheduler where
  "init_astate = \<lparr>cur_ttbl_id = 0, window_id = 0, reset = False, next_ttbl_id = 0, next_mode = NO_SWITCH\<rparr>"

context global_state
begin

definition cur_ttbl :: "astate_scheduler \<Rightarrow> time_table" where
  "cur_ttbl st = time_tables (cur_ttbl_id st)"

definition next_ttbl :: "astate_scheduler \<Rightarrow> time_table" where
  "next_ttbl st = time_tables (next_ttbl_id st)"

definition cur_frame_length :: "astate_scheduler \<Rightarrow> nat" where
  "cur_frame_length st = frame_length (cur_ttbl st)"

text \<open>Invariant for abstract scheduler\<close>
definition ainv :: "astate_scheduler \<Rightarrow> bool" where
  "ainv st \<longleftrightarrow>
     \<not>reset st \<and>
     cur_ttbl_id st < 256 \<and>
     next_ttbl_id st < 256 \<and>
     window_id st < length (cur_ttbl st)"

text \<open>Specification for executing a dispatch.\<close>
definition spec_dispatch :: "astate_scheduler \<Rightarrow> astate_scheduler \<times> event list" where
  "spec_dispatch st =
    (if next_mode st = NEXT_WINDOW then
       (\<lparr>cur_ttbl_id = next_ttbl_id st, window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>, 
        [PARTITION (fst (next_ttbl st ! 0)),
         WATCHDOG_ADD (0, snd (next_ttbl st ! 0))])
     else if window_id st = length (cur_ttbl st) - 1 \<and> next_mode st = NEXT_FRAME then
       (\<lparr>cur_ttbl_id = next_ttbl_id st, window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>, 
        [PARTITION (fst (next_ttbl st ! 0)),
         WATCHDOG_ADD (0, snd (next_ttbl st ! 0))])
     else if window_id st = length (cur_ttbl st) - 1 \<and> next_mode st = ONGOING then
       (st\<lparr>window_id := 0, next_mode := NO_SWITCH\<rparr>,
        [PARTITION (fst (cur_ttbl st ! 0)),
         WATCHDOG_ADD (0, snd (cur_ttbl st ! 0))])
     else
       (st\<lparr>window_id := (window_id st + 1) mod length (cur_ttbl st)\<rparr>,
        [PARTITION (fst (cur_ttbl st ! ((window_id st + 1) mod length (cur_ttbl st)))),
         WATCHDOG_ADD (0, snd (cur_ttbl st ! ((window_id st + 1) mod length (cur_ttbl st))))]))"

text \<open>Specification for executing a switch command.

  If there is no existing switch, store the next table and switch mode.
  Otherwise do nothing.
\<close>
definition spec_switch :: "ttbl_id \<Rightarrow> switch_mode \<Rightarrow> astate_scheduler \<Rightarrow> astate_scheduler" where
  "spec_switch nxt_tbl nxt_mode st =
    (if nxt_tbl \<ge> 256 then
       st
     else if nxt_mode \<noteq> NO_SWITCH then
       if cur_ttbl_id st = nxt_tbl \<and> next_mode st \<noteq> NO_SWITCH then
         st\<lparr>next_ttbl_id := nxt_tbl, next_mode := NO_SWITCH\<rparr>
       else 
         st\<lparr>next_ttbl_id := nxt_tbl, next_mode := nxt_mode\<rparr>
     else
       st)"

end

subsection \<open>Concrete scheduler\<close>

record cstate =
  cur_ttbl_id :: ttbl_id    \<comment> \<open>ID of current table\<close>
  window_time :: nat        \<comment> \<open>Length of current window\<close>
  cur_frame_time :: nat     \<comment> \<open>Current time within the frame\<close>
  cur_window :: nat         \<comment> \<open>Current window in the frame\<close>
  total_frame_time :: nat   \<comment> \<open>Total length of frame\<close>
  next_ttbl_id :: ttbl_id   \<comment> \<open>ID of next table (0 when not switching)\<close>
  next_mode :: switch_mode  \<comment> \<open>Switch mode\<close>

definition get_cur_ttbl_id :: "(cstate, event, ttbl_id) event_monad" where
  "get_cur_ttbl_id = get \<bind> (\<lambda>st. return (cur_ttbl_id st))"

definition get_window_time :: "(cstate, event, nat) event_monad" where
  "get_window_time = get \<bind> (\<lambda>st. return (window_time st))"

definition get_cur_frame_time :: "(cstate, event, nat) event_monad" where
  "get_cur_frame_time = get \<bind> (\<lambda>st. return (cur_frame_time st))"

definition get_cur_window :: "(cstate, event, nat) event_monad" where
  "get_cur_window = get \<bind> (\<lambda>st. return (cur_window st))"

definition get_total_frame_time :: "(cstate, event, nat) event_monad" where
  "get_total_frame_time = get \<bind> (\<lambda>st. return (total_frame_time st))"

definition get_next_ttbl_id :: "(cstate, event, ttbl_id) event_monad" where
  "get_next_ttbl_id = get \<bind> (\<lambda>st. return (next_ttbl_id st))"

definition get_next_mode :: "(cstate, event, switch_mode) event_monad" where
  "get_next_mode = get \<bind> (\<lambda>st. return (next_mode st))"

definition set_cur_ttbl_id :: "ttbl_id \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_cur_ttbl_id ttbl = modify (cur_ttbl_id_update (\<lambda>_. ttbl))"

definition set_window_time :: "nat \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_window_time t = modify (window_time_update (\<lambda>_. t))"

definition set_cur_frame_time :: "nat \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_cur_frame_time t = modify (cur_frame_time_update (\<lambda>_. t))"

definition set_cur_window :: "nat \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_cur_window n = modify (cur_window_update (\<lambda>_. n))"

definition set_total_frame_time :: "nat \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_total_frame_time t = modify (total_frame_time_update (\<lambda>_. t))"

definition set_next_ttbl_id :: "ttbl_id \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_next_ttbl_id ttbl = modify (next_ttbl_id_update (\<lambda>_. ttbl))"

definition set_next_mode :: "switch_mode \<Rightarrow> (cstate, event, unit) event_monad" where
  "set_next_mode mode = modify (next_mode_update (\<lambda>_. mode))"


context global_state
begin

text \<open>Get partition and duration for a given window\<close>
definition get_partition :: "ttbl_id \<Rightarrow> nat \<Rightarrow> nat" where
  "get_partition tbl_id wid = fst (time_tables tbl_id ! wid)"

definition get_duration :: "ttbl_id \<Rightarrow> nat \<Rightarrow> nat" where
  "get_duration tbl_id wid = snd (time_tables tbl_id ! wid)"

definition get_frame_time :: "ttbl_id \<Rightarrow> nat" where
  "get_frame_time tbl_id = frame_length (time_tables tbl_id)"

text \<open>Initial state.

  We assume the initial time table is the zeroth time table in the global state.
\<close>
definition init_cstate :: cstate where
  "init_cstate = \<lparr>cur_ttbl_id = 0, window_time = get_duration 0 0,
    cur_frame_time = 0, cur_window = 0, total_frame_time = get_frame_time 0, next_ttbl_id = 0,
    next_mode = NO_SWITCH\<rparr>"

text \<open>Concrete switch operation\<close>
fun switch :: "ttbl_id \<Rightarrow> switch_mode \<Rightarrow> (cstate, event, unit) event_monad" where
  "switch nxt_tbl nxt_mode =
    (if nxt_tbl \<ge> 256 then
      return ()
     else 
      get_next_mode \<bind> (\<lambda>mode. 
      get_cur_ttbl_id \<bind> (\<lambda>cur_ttbl. 
      get_next_ttbl_id \<bind> (\<lambda>nxt_ttbl.
      if (nxt_mode \<noteq> NO_SWITCH) then 
        set_next_ttbl_id nxt_tbl \<bind> (\<lambda>_.
        if (cur_ttbl = nxt_tbl \<and> mode \<noteq> NO_SWITCH) then 
          set_next_mode NO_SWITCH 
        else 
          set_next_mode nxt_mode)
      else
        return ()))))"

lemma get_cur_ttbl_id_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (cur_ttbl_id s) s \<rbrace>
     get_cur_ttbl_id
   \<lbrace> P \<rbrace>!"
  unfolding get_cur_ttbl_id_def by wp

lemma get_window_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (window_time s) s \<rbrace>
     get_window_time
   \<lbrace> P \<rbrace>!"
  unfolding get_window_time_def by wp

lemma get_cur_frame_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (cur_frame_time s) s \<rbrace>
     get_cur_frame_time
   \<lbrace> P \<rbrace>!"
  unfolding get_cur_frame_time_def by wp

lemma get_cur_window_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (cur_window s) s \<rbrace>
     get_cur_window
   \<lbrace> P \<rbrace>!"
  unfolding get_cur_window_def by wp

lemma get_total_frame_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (total_frame_time s) s \<rbrace>
     get_total_frame_time
   \<lbrace> P \<rbrace>!"
  unfolding get_total_frame_time_def by wp

lemma get_next_ttbl_id_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (next_ttbl_id s) s \<rbrace>
     get_next_ttbl_id
   \<lbrace> P \<rbrace>!"
  unfolding get_next_ttbl_id_def by wp

lemma get_next_mode_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (next_mode s) s \<rbrace> 
     get_next_mode
   \<lbrace> P \<rbrace>!"
  unfolding get_next_mode_def by wp

lemma set_cur_ttbl_id_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_ttbl_id := cur_id\<rparr>) \<rbrace>
     set_cur_ttbl_id cur_id
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_cur_ttbl_id_def by wp

lemma set_window_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>window_time := wtime\<rparr>) \<rbrace>
     set_window_time wtime
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_window_time_def by wp

lemma set_cur_frame_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_frame_time := ftime\<rparr>) \<rbrace>
     set_cur_frame_time ftime
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_cur_frame_time_def by wp

lemma set_cur_window_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_window := window\<rparr>) \<rbrace>
     set_cur_window window
   \<lbrace> \<lambda>_ s. P s \<rbrace>!"
  unfolding set_cur_window_def by wp

lemma set_total_frame_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>total_frame_time := tftime\<rparr>) \<rbrace>
     set_total_frame_time tftime
   \<lbrace> \<lambda>r s. P s \<rbrace>!"
  unfolding set_total_frame_time_def by wp

lemma set_next_ttbl_id_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>next_ttbl_id := nxt_tbl\<rparr>) \<rbrace>
     set_next_ttbl_id nxt_tbl
   \<lbrace> \<lambda>r s. P s \<rbrace>!"
  unfolding set_next_ttbl_id_def by wp

lemma set_next_mode_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>next_mode := nxt_mode\<rparr>) \<rbrace>
     set_next_mode nxt_mode
   \<lbrace> \<lambda>r s. P s \<rbrace>!"
  unfolding set_next_mode_def by wp

lemma switch_NF_rule [wp]:
  "\<lbrace> \<lambda>s. if nxt_tbl \<ge> 256 then P s
         else (if nxt_mode \<noteq> NO_SWITCH
               then if (cur_ttbl_id s = nxt_tbl \<and> next_mode s \<noteq> NO_SWITCH)
                    then P (s\<lparr>next_ttbl_id := nxt_tbl, next_mode := NO_SWITCH\<rparr>) 
                    else P (s\<lparr>next_ttbl_id := nxt_tbl, next_mode := nxt_mode\<rparr>)
         else P s) \<rbrace>
     switch nxt_tbl nxt_mode
   \<lbrace> \<lambda>r s. P s \<rbrace>!"
  apply (unfold switch.simps) 
  apply wp by auto

definition update_cur_frame_time :: "(cstate, event, unit) event_monad" where
  "update_cur_frame_time = doE
     w_time \<leftarrow> get_window_time;
     f_time \<leftarrow> get_cur_frame_time;
     set_cur_frame_time (f_time + w_time)
   odE"

lemma update_cur_frame_time_NF_rule [wp]:
  "\<lbrace> \<lambda>s. P (s\<lparr>cur_frame_time := cur_frame_time s + window_time s\<rparr>) \<rbrace>
     update_cur_frame_time
   \<lbrace> \<lambda>r. P \<rbrace>!"
  unfolding update_cur_frame_time_def by wp

subsection \<open>Refinement\<close>

text \<open>Refinement relation between abstract and concrete scheduler.\<close>
definition rel :: "astate_scheduler \<Rightarrow> cstate \<Rightarrow> bool" where
  "rel as cs \<longleftrightarrow> astate_scheduler.cur_ttbl_id as = cstate.cur_ttbl_id cs \<and>
                 astate_scheduler.window_id as = cur_window cs \<and>
                 (if astate_scheduler.reset as then window_time cs = 0 else window_time cs \<noteq> 0) \<and>
                 astate_scheduler.next_ttbl_id as = cstate.next_ttbl_id cs \<and>
                 astate_scheduler.next_mode as = cstate.next_mode cs"

definition c_cur_ttbl :: "cstate \<Rightarrow> time_table" where
  "c_cur_ttbl st = time_tables (cur_ttbl_id st)"

text \<open>Main invariant for concrete scheduler, to be held before and after
  each dispatch.
\<close>
definition cinv :: "cstate \<Rightarrow> bool" where
  "cinv cs \<longleftrightarrow> cur_ttbl_id cs < 256 \<and>
               next_ttbl_id cs < 256 \<and>
               cur_window cs < length (c_cur_ttbl cs) \<and>
               total_frame_time cs = frame_length (c_cur_ttbl cs) \<and>
               window_time cs = get_duration (cur_ttbl_id cs) (cur_window cs) \<and>
               cur_frame_time cs = frame_time_to_window (c_cur_ttbl cs) (cur_window cs)"

text \<open>Auxiliary invariant to be held during the computation.\<close>
definition cinv2 :: "cstate \<Rightarrow> bool" where
  "cinv2 cs \<longleftrightarrow> cur_ttbl_id cs < 256 \<and>
                next_ttbl_id cs < 256 \<and>
                cur_window cs < length (c_cur_ttbl cs) \<and>
                total_frame_time cs = frame_length (c_cur_ttbl cs) \<and>
                (if window_time cs = 0 then cur_frame_time cs = 0 \<and> cur_window cs = 0
                 else window_time cs = get_duration (cur_ttbl_id cs) (cur_window cs) \<and>
                      cur_frame_time cs = frame_time_to_window (c_cur_ttbl cs) (cur_window cs + 1))"

lemma cinv_duration_nonzero:
  assumes "cinv cs"
  shows "snd (time_tables (cur_ttbl_id cs) ! cur_window cs) \<noteq> 0"
proof -
  have "is_valid_time_table (time_tables (cstate.cur_ttbl_id cs))"
    apply (rule valid_time_table)
    using cinv_def assms by auto
  also have "cur_window cs < length (time_tables (cstate.cur_ttbl_id cs))"
    using cinv_def assms c_cur_ttbl_def by auto
  ultimately show ?thesis
    using window_time_pos by auto
qed

subsection \<open>Dispatch\<close>

text \<open>Due to the length of the dispatch function, we prove it in several
  sections: dispatch_part1, dispatch_part2, dispatch_part3. The overall
  implementation is dispatch_all.
\<close>
definition dispatch_part1 :: "(cstate, event, unit) event_monad" where
  "dispatch_part1 = get_next_mode \<bind> (\<lambda>mode.
    
    \<comment>\<open>If switching at next window\<close>
    (if (mode = NEXT_WINDOW) then
      set_window_time 0 \<bind> (\<lambda>_.
      set_cur_frame_time 0 \<bind> (\<lambda>_.
      set_cur_window 0 \<bind> (\<lambda>_.
      get_next_ttbl_id \<bind> (\<lambda>next_ttbl_id.
      set_cur_ttbl_id next_ttbl_id \<bind> (\<lambda>_.
      get_cur_ttbl_id \<bind> (\<lambda>cur_tbl.
      set_total_frame_time (get_frame_time cur_tbl) \<bind> (\<lambda>_.
      set_next_mode ONGOING \<bind> (\<lambda>_.
      set_next_ttbl_id 0))))))))
    else 
      return ())
    \<bind> (\<lambda>_.
  
    \<comment> \<open>Update total frame time\<close>
    update_cur_frame_time))"

definition dispatch_part_a1 :: "astate_scheduler \<Rightarrow> astate_scheduler" where
  "dispatch_part_a1 st =
   (if astate_scheduler.next_mode st = NEXT_WINDOW then
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id st,
       window_id = 0,
       reset = True,
       next_ttbl_id = 0,
       next_mode = ONGOING\<rparr>)
    else st)"

lemma dispatch_part1_rule:
  assumes "\<not>reset as"
  shows
  "\<lbrace> \<lambda>cs es. cinv cs \<and> rel as cs \<and> P es \<rbrace>
     dispatch_part1
   \<lbrace> \<lambda>_ cs es. cinv2 cs \<and> rel (dispatch_part_a1 as) cs \<and> P es \<rbrace>!"
  unfolding dispatch_part1_def apply wp apply auto
  unfolding rel_def rel_def dispatch_part_a1_def apply auto
  subgoal for cs e
    apply (auto simp add: cinv2_def cinv_def c_cur_ttbl_def)
    using valid_time_table apply auto[1]
    using get_frame_time_def
     apply fastforce
    using get_frame_time_def by blast
  subgoal for cs e
    apply (auto simp add: cinv2_def cinv_def c_cur_ttbl_def get_duration_def cinv_duration_nonzero)
    by (simp add: frame_time_to_window_next)
  done


definition dispatch_part2 :: "(cstate, event, unit) event_monad" where
  "dispatch_part2 =
     get_next_mode \<bind> (\<lambda>mode.
        (if mode = NEXT_FRAME then
          set_window_time 0 \<bind> (\<lambda>_.
          set_cur_frame_time 0 \<bind> (\<lambda>_.
          set_cur_window 0 \<bind> (\<lambda>_.
          get_next_ttbl_id \<bind> (\<lambda>next_ttbl_id.
          set_cur_ttbl_id next_ttbl_id \<bind> (\<lambda>_.
          get_cur_ttbl_id \<bind> (\<lambda>cur_tbl.
          set_total_frame_time (get_frame_time cur_tbl) \<bind> (\<lambda>_.
          set_next_mode ONGOING \<bind> (\<lambda>_.
          set_next_ttbl_id 0 ))))))))
        else if mode = ONGOING then
          set_next_mode NO_SWITCH
        else
          return ()) \<bind> (\<lambda>_.
        get_cur_ttbl_id \<bind> (\<lambda>cur_tbl.
        set_window_time 0 \<bind> (\<lambda>_.
        set_cur_frame_time 0 \<bind> (\<lambda>_.
        set_cur_window 0)))))"

text \<open>Expect to be called only when frame time equals total frame time.\<close>
definition dispatch_part_a2 :: "astate_scheduler \<Rightarrow> astate_scheduler" where
  "dispatch_part_a2 st =
   (if astate_scheduler.next_mode st = NEXT_FRAME then
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id st,
        window_id = 0,
        reset = True,
        astate_scheduler.next_ttbl_id = 0,
        next_mode = ONGOING\<rparr>)
    else if astate_scheduler.next_mode st = ONGOING then
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.cur_ttbl_id st,
        window_id = 0,
        reset = True,
        astate_scheduler.next_ttbl_id = astate_scheduler.next_ttbl_id st,
        next_mode = NO_SWITCH\<rparr>)
    else
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.cur_ttbl_id st,
        window_id = 0,
        reset = True,
        astate_scheduler.next_ttbl_id = astate_scheduler.next_ttbl_id st,
        next_mode = astate_scheduler.next_mode st\<rparr>))"

lemma dispatch_part2_rule:
  "\<lbrace> \<lambda>cs es. cinv2 cs \<and> rel as cs \<and> P es \<rbrace>
     dispatch_part2
   \<lbrace> \<lambda>_ cs es. cinv2 cs \<and> rel (dispatch_part_a2 as) cs \<and>
               cur_window cs = 0 \<and> window_time cs = 0 \<and> cur_frame_time cs = 0 \<and> P es\<rbrace>!"
  unfolding dispatch_part2_def apply wp
  apply (auto simp add: rel_def dispatch_part_a2_def)
  using valid_time_table
  apply (auto simp add: cinv2_def c_cur_ttbl_def get_frame_time_def)
  by fastforce


definition dispatch_part3 :: "(cstate, event, unit) event_monad" where
  "dispatch_part3 = 
    get_cur_frame_time \<bind> (\<lambda>f_time.
    get_total_frame_time \<bind> (\<lambda>total_time.
    if f_time = 0 \<or> f_time = total_time then
      ((if (f_time = total_time) then
        (dispatch_part2) else return ()) \<bind> (\<lambda>_.
      get_cur_ttbl_id \<bind> (\<lambda>cur_tbl.
      set_window_time (get_duration cur_tbl 0) \<bind> (\<lambda>_.
      signal (PARTITION (get_partition cur_tbl 0))) \<bind> (\<lambda>_.
      signal (WATCHDOG_ADD (0, get_duration cur_tbl 0))))))
    else  
      get_cur_ttbl_id \<bind> (\<lambda>cur_tbl.
      get_cur_window \<bind> (\<lambda>cur_window.
      set_cur_window (cur_window + 1) \<bind> (\<lambda>_.
      set_window_time (get_duration cur_tbl (cur_window + 1)) \<bind> (\<lambda>_.
      signal (PARTITION (get_partition cur_tbl (cur_window + 1))) \<bind> (\<lambda>_.
      signal (WATCHDOG_ADD (0, get_duration cur_tbl (cur_window + 1))))))))))"

definition dispatch_part_a3 :: "astate_scheduler \<Rightarrow> astate_scheduler \<times> event list" where
  "dispatch_part_a3 st =
    (if astate_scheduler.window_id st = length (cur_ttbl st) - 1 then
       ((dispatch_part_a2 st)\<lparr>reset := False\<rparr>,
        [PARTITION (fst (cur_ttbl (dispatch_part_a2 st) ! 0)),
         WATCHDOG_ADD (0, snd (cur_ttbl (dispatch_part_a2 st) ! 0))])
     else if astate_scheduler.reset st then
       (st\<lparr>reset := False\<rparr>, [PARTITION (fst (cur_ttbl st ! 0)), WATCHDOG_ADD (0, snd (cur_ttbl st ! 0))])
     else (st\<lparr>window_id := window_id st + 1\<rparr>,
           [PARTITION (fst (cur_ttbl st ! (window_id st + 1))),
            WATCHDOG_ADD (0, snd (cur_ttbl st ! (window_id st + 1)))]))"

lemma dispatch_part2_rule'':
  assumes "window_id as = length (cur_ttbl as) - 1"
  shows
  "\<lbrace> \<lambda>cs es. cinv2 cs \<and> rel as cs \<and> es = [] \<rbrace>
     dispatch_part2
   \<lbrace> \<lambda>_ cs es. cinv (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>) \<and>
            rel (fst (dispatch_part_a3 as)) (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>) \<and> 
            es @ [PARTITION (get_partition (cstate.cur_ttbl_id cs) 0),
                  WATCHDOG_ADD (0, get_duration (cstate.cur_ttbl_id cs) 0)] = snd (dispatch_part_a3 as) \<rbrace>!"
proof -
  have a: "dispatch_part_a3 as =
    ((dispatch_part_a2 as)\<lparr>reset := False\<rparr>,
     [PARTITION (fst (cur_ttbl (dispatch_part_a2 as) ! 0)),
      WATCHDOG_ADD (0, snd (cur_ttbl (dispatch_part_a2 as) ! 0))])"
    unfolding dispatch_part_a3_def using assms by auto
  show ?thesis
    apply (rule validNF_strengthen_post)
    apply (rule validNF_weaken_pre)
      apply (rule dispatch_part2_rule[where as=as and P="\<lambda>e. e = []"])
     apply auto[1]
    subgoal for r cs e
      apply simp apply (intro conjI)
      subgoal by (auto simp add: cinv_def cinv2_def c_cur_ttbl_def)
      subgoal apply (auto simp add: rel_def cinv2_def c_cur_ttbl_def a)
        using get_duration_def window_time_pos global_state_axioms valid_time_table by auto
      subgoal by (auto simp add: cinv2_def cinv_def c_cur_ttbl_def cur_ttbl_def rel_def a get_partition_def get_duration_def)
      done
    done
qed

lemma dispatch_part2_rule':
  "\<lbrace> \<lambda>cs es. window_id as = length (cur_ttbl as) - 1 \<and> cinv2 cs \<and> rel as cs \<and> es = [] \<rbrace>
     dispatch_part2
   \<lbrace> \<lambda>_ cs es. cinv (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>) \<and>
            rel (fst (dispatch_part_a3 as)) (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>) \<and> 
            (es @ [PARTITION (get_partition (cstate.cur_ttbl_id cs) 0)]) @
                 [WATCHDOG_ADD (0, get_duration (cstate.cur_ttbl_id cs) 0)] = snd (dispatch_part_a3 as) \<rbrace>!"
  unfolding validNF_conj_pre
  using dispatch_part2_rule'' by auto

lemma dispatch_part3_rule:
  "\<lbrace> \<lambda>cs es. cinv2 cs \<and> rel as cs \<and> es = []\<rbrace>
     dispatch_part3
   \<lbrace> \<lambda>_ cs es. cinv cs \<and> rel (fst (dispatch_part_a3 as)) cs \<and> es = snd (dispatch_part_a3 as)\<rbrace>!"
proof -
  have 2: "cinv (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>)"
    if "cinv2 cs" and "cur_frame_time cs = 0" for cs
    using that
    by (smt add_gr_0 c_cur_ttbl_def cstate.select_convs cstate.surjective cstate.update_convs(2)
            frame_time_to_window_mono_strict frame_time_to_window_zero global_state.cinv2_def
            global_state.cinv_def global_state_axioms gr0I is_valid_time_table.elims(2)
            less_numeral_extra(2) less_numeral_extra(3) valid_time_table)
  have 4: "length (cur_ttbl as) > 1" if "cinv2 cs" "rel as cs" for cs
    using global_state.cinv2_def global_state.cur_ttbl_def global_state_axioms rel_def that(1) that(2) valid_time_table by auto
  have 5: "cur_window cs = length (c_cur_ttbl cs) - 1"
    if "cinv2 cs" "rel as cs" "cur_frame_time cs = total_frame_time cs" for cs
  proof -
    note that1 = that
    have a1: "cur_window cs < length (c_cur_ttbl cs)"
      using cinv2_def nat_le_linear not_le that(1) by blast
    have a2: "is_valid_time_table (c_cur_ttbl cs)"
      using c_cur_ttbl_def cinv2_def that(1) valid_time_table by auto
    have a3: False if "Suc (cur_window cs) < length (c_cur_ttbl cs)"
    proof -
      have "frame_time_to_window (c_cur_ttbl cs) (Suc (cur_window cs)) < frame_time_to_window (c_cur_ttbl cs) (length (c_cur_ttbl cs))"
        by (rule frame_time_to_window_mono_strict[OF a2 that that])
      then show ?thesis
        using that1 cinv2_def frame_time_to_window_total 
        by (metis Suc_eq_plus1 gr_implies_not0 less_not_refl2)
    qed
    show ?thesis
      using a1 a3 by fastforce
  qed
  have 6: "rel (fst (dispatch_part_a3 as)) (cs\<lparr>window_time := get_duration (cstate.cur_ttbl_id cs) 0\<rparr>)"
    if "cinv2 cs" "rel as cs" "cur_frame_time cs = 0" for cs
  proof -
    have a1: "window_time cs = 0" "cur_window cs = 0"
      using that(1,3) unfolding cinv2_def
       apply (metis Suc_eq_plus1 c_cur_ttbl_def frame_time_to_window_mono_strict less_add_same_cancel2
                    less_numeral_extra(1) not_less_zero plus_1_eq_Suc valid_time_table)
      by (metis Suc_eq_plus1 Suc_leI cinv2_def diff_Suc_1 diff_less frame_time_to_window_mono_strict
                global_state.c_cur_ttbl_def global_state_axioms less_numeral_extra(1) not_le
                that(1) that(3) valid_time_table zero_less_Suc)
    have a2: "window_id as = 0"
      using a1(2) that(2) unfolding rel_def by auto
    have a3: "reset as"
      using that(2) unfolding rel_def that(3)
      by (meson a1(1))
    have a4: "fst (dispatch_part_a3 as) = as\<lparr>reset := False\<rparr>"
      unfolding dispatch_part_a3_def
      using a2 4[OF that(1,2)] a3 by auto
    show ?thesis
      using that(2) unfolding a4 rel_def
      using 2 a2 astate_scheduler.ext_inject cinv_duration_nonzero cstate.surjective
            get_duration_def that(1) that(3) by force
  qed
  have 7: "rel (fst (dispatch_part_a3 as))
     (cs\<lparr>cur_window := cur_window cs + 1, window_time := get_duration (cstate.cur_ttbl_id cs) (cur_window cs + 1)\<rparr>)"
    "[PARTITION (get_partition (cstate.cur_ttbl_id cs) (cur_window cs + 1)),
      WATCHDOG_ADD (0, get_duration (cstate.cur_ttbl_id cs) (cur_window cs + 1))] = snd (dispatch_part_a3 as)"
    if "cinv2 cs" "rel as cs" "\<not> (cur_frame_time cs = 0 \<or> cur_frame_time cs = total_frame_time cs)" for cs
  proof -
    have a1: "cur_window cs < length (c_cur_ttbl cs)"
      using that(1) unfolding cinv2_def by auto
    have a2: "window_time cs = get_duration (cstate.cur_ttbl_id cs) (cur_window cs)"
       "cur_frame_time cs = frame_time_to_window (c_cur_ttbl cs) (cur_window cs + 1)"
      using that(1,3) unfolding cinv2_def
      apply meson
      using cinv2_def that(1) that(3) by presburger
    have a3: "cur_window cs + 1 \<noteq> length (c_cur_ttbl cs)"
      using a2(2) that(3)
      using cinv2_def frame_time_to_window_total that(1) by auto
    have a4: "\<not>reset as"
      using cinv2_def rel_def that(1) that(2) that(3) by auto
    have a5: "fst (dispatch_part_a3 as) = as\<lparr>window_id := window_id as + 1\<rparr>"
      using a3 a4 that(2)
      by (smt Suc_eq_plus1 add_diff_inverse_nat 4[OF that(1,2)] astate_scheduler.surjective
              astate_scheduler.update_convs(2) c_cur_ttbl_def cur_ttbl_def dispatch_part_a3_def
              fst_conv length_0_conv length_greater_0_conv less_one less_trans plus_1_eq_Suc rel_def)
    have a6: "snd (dispatch_part_a3 as) = [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
                                           WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))]"
      using a3 a4 that(2)
      by (smt Suc_eq_plus1 add_diff_inverse_nat 4[OF that(1,2)] c_cur_ttbl_def cur_ttbl_def dispatch_part_a3_def
              length_0_conv length_greater_0_conv less_one less_trans plus_1_eq_Suc rel_def snd_conv)
    show "rel (fst (dispatch_part_a3 as))
     (cs\<lparr>cur_window := cur_window cs + 1, window_time := get_duration (cstate.cur_ttbl_id cs) (cur_window cs + 1)\<rparr>)"
      using a4 that(2) unfolding a5 rel_def apply auto
      using a3 c_cur_ttbl_def get_duration_def global_state.cinv2_def
            window_time_pos global_state_axioms that(1) valid_time_table by auto
    show "[PARTITION (get_partition (cstate.cur_ttbl_id cs) (cur_window cs + 1)),
           WATCHDOG_ADD (0, get_duration (cstate.cur_ttbl_id cs) (cur_window cs + 1))] = snd (dispatch_part_a3 as)"
      unfolding a6 apply (auto simp add: get_partition_def get_duration_def cur_ttbl_def)
      using rel_def that(2) by auto
  qed
  show ?thesis
    unfolding dispatch_part3_def
    apply (rule validNF_bind)
     prefer 2 apply (rule validNF_bind)
      prefer 2 apply (rule validNF_if_split)
    apply (rule validNF_bind)
        prefer 2 apply (rule validNF_bind)
         prefer 2 apply (rule validNF_bind)
          prefer 2 apply (rule validNF_signal)
    apply (rule validNF_bind)
          prefer 2 apply (rule validNF_signal)
    apply (rule set_window_time_NF_rule)
    apply (rule get_cur_ttbl_id_NF_rule)
    apply (rule validNF_if_split)
        apply (rule dispatch_part2_rule')
       apply (rule validNF_return)
      apply wp apply wp apply wp
    subgoal for cs e
      apply (intro conjI)
      subgoal apply (intro impI conjI)
        subgoal using 5 c_cur_ttbl_def cur_ttbl_def rel_def by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal using 2 by auto
        subgoal using 6 by auto
        subgoal using 4 cinv2_def cur_ttbl_def dispatch_part_a3_def rel_def
        proof -
          assume a1: "cur_frame_time cs = 0 \<or> cur_frame_time cs = total_frame_time cs"
          assume a2: "cur_frame_time cs \<noteq> total_frame_time cs"
          assume a3: "cinv2 cs \<and> rel as cs \<and> e = []"
          then have "window_time cs = 0"
            using a2 a1
            by (smt One_nat_def Suc_lessD add_gr_0 4 c_cur_ttbl_def cur_ttbl_def
                    frame_time_to_window_mono_strict frame_time_to_window_zero global_state.cinv2_def
                    global_state_axioms less_numeral_extra(1) less_numeral_extra(3) rel_def valid_time_table)
          then have f4: "reset as"
            using a3 by (metis (no_types) rel_def)
          have "1 < length (c_cur_ttbl cs)"
            using a3 by (metis (no_types) 4 c_cur_ttbl_def cur_ttbl_def rel_def)
          then show ?thesis
            using f4 a3
            by (simp add: c_cur_ttbl_def cinv2_def cur_ttbl_def dispatch_part_a3_def get_partition_def get_duration_def rel_def)
        qed
        done
      subgoal apply (intro impI conjI)
        subgoal apply (auto simp add: cinv_def cinv2_def c_cur_ttbl_def)
           apply (metis Suc_eq_plus1 Suc_lessI c_cur_ttbl_def frame_time_to_window_total not_less_zero)
          using Suc_eq_plus1 c_cur_ttbl_def by presburger
        subgoal using 7(1) by blast
        subgoal using 7(2) by auto
        done
      done
    done
qed


definition dispatch_all :: "(cstate, event, unit) event_monad" where
  "dispatch_all = dispatch_part1 \<bind> (\<lambda>_. dispatch_part3)"

lemma dispatch_all_rule':
  "\<lbrace> \<lambda>cs es. \<not>reset as \<and> cinv cs \<and> rel as cs \<and> es = [] \<rbrace>
     dispatch_all
   \<lbrace> \<lambda>_ cs es. cinv cs \<and> rel (fst (dispatch_part_a3 (dispatch_part_a1 as))) cs 
      \<and> es = snd (dispatch_part_a3 (dispatch_part_a1 as)) \<rbrace>!"
  unfolding dispatch_all_def
  apply (subst validNF_conj_pre)
  apply auto
  apply (rule validNF_bind)
  apply (rule dispatch_part1_rule) apply auto
  by (rule dispatch_part3_rule)

subsection \<open>Equivalence with spec_dispatch\<close>

lemma spec_dispatch_equal_next_window:
  assumes "astate_scheduler.next_mode as = NEXT_WINDOW"
    and "ainv as"
  shows "spec_dispatch as = dispatch_part_a3 (dispatch_part_a1 as)"
proof -
  have a1: "spec_dispatch as =
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0, reset = False, next_ttbl_id = 0,
        next_mode = ONGOING\<rparr>,
       [PARTITION (fst (next_ttbl as ! 0)), WATCHDOG_ADD (0, snd (next_ttbl as ! 0))])"
    unfolding spec_dispatch_def using assms(1) by auto
  have a2: "dispatch_part_a1 as =
      \<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0, reset = True, next_ttbl_id = 0,
       next_mode = ONGOING\<rparr>"
    unfolding dispatch_part_a1_def using assms(1) by auto
  have a3: "length (time_tables (astate_scheduler.next_ttbl_id as)) > 1"
    using ainv_def assms(2) valid_time_table by auto
  have a4: "dispatch_part_a3 (dispatch_part_a1 as) =
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as, window_id = 0, reset = False, next_ttbl_id = 0,
        next_mode = ONGOING\<rparr>,
       [PARTITION (fst (next_ttbl as ! 0)), WATCHDOG_ADD (0, snd (next_ttbl as ! 0))])"
    unfolding a2 dispatch_part_a3_def using a3 by (auto simp add: cur_ttbl_def next_ttbl_def)
  show ?thesis
    using a1 a4 by auto
qed

lemma spec_dispatch_equal_next_frame:
  assumes "astate_scheduler.next_mode as = NEXT_FRAME"
    and "ainv as"
  shows "spec_dispatch as = dispatch_part_a3 (dispatch_part_a1 as)"
proof -
  have a1: "spec_dispatch as =
      (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as,
        window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>, 
       [PARTITION (fst (next_ttbl as ! 0)),
        WATCHDOG_ADD (0, snd (next_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that by auto
  have a2: "dispatch_part_a1 as = as"
    unfolding dispatch_part_a1_def using assms(1) by auto
  have a3: "dispatch_part_a3 (dispatch_part_a1 as) =
     (\<lparr>astate_scheduler.cur_ttbl_id = astate_scheduler.next_ttbl_id as,
       window_id = 0, reset = False, next_ttbl_id = 0, next_mode = ONGOING\<rparr>, 
      [PARTITION (fst (next_ttbl as ! 0)),
       WATCHDOG_ADD (0, snd (next_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding a2 dispatch_part_a3_def
    by (auto simp add: that assms(1) dispatch_part_a2_def cur_ttbl_def next_ttbl_def)
  have a4: "spec_dispatch as =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that apply auto
    by (metis Euclidean_Division.mod_less One_nat_def Suc_lessI ainv_def assms(2) diff_Suc_1)+
  have a5: "dispatch_part_a3 (dispatch_part_a1 as) =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding a2 dispatch_part_a3_def
    using that assms(2) ainv_def by auto
  show ?thesis
    apply (cases "window_id as = length (cur_ttbl as) - 1")
    using a1 a3 apply auto[1]
    using a4 a5 by auto
qed

lemma spec_dispatch_equal_no_switch:
  assumes "astate_scheduler.next_mode as = NO_SWITCH"
    and "ainv as"
  shows "spec_dispatch as = dispatch_part_a3 (dispatch_part_a1 as)"
proof -
  have a1: "spec_dispatch as =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that apply auto
    by (metis Euclidean_Division.mod_less One_nat_def Suc_lessI ainv_def assms(2) diff_Suc_1)+
  have a2: "dispatch_part_a1 as = as"
    using assms(1) dispatch_part_a1_def by auto
  have a3: "dispatch_part_a3 as =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding dispatch_part_a3_def using assms(2) that by (auto simp add: ainv_def)
  have a4: "spec_dispatch as =
     (as\<lparr>window_id := 0\<rparr>,
      [PARTITION (fst (cur_ttbl as ! 0)),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that apply auto
    by (metis One_nat_def assms(2) diff_Suc_1 global_state.ainv_def global_state_axioms mod_self not0_implies_Suc not_less_zero)+
  have a5: "dispatch_part_a3 as =
     (as\<lparr>window_id := 0\<rparr>,
      [PARTITION (fst (cur_ttbl as ! 0)),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding dispatch_part_a3_def using assms(1,2) that
    by (auto simp add: dispatch_part_a2_def ainv_def cur_ttbl_def)
  show ?thesis
    apply (cases "window_id as = length (cur_ttbl as) - 1")
    using a2 a4 a5 apply auto[1]
    using a1 a2 a3 by auto
qed

lemma spec_dispatch_equal_ongoing:
  assumes "astate_scheduler.next_mode as = ONGOING"
    and "ainv as"
  shows "spec_dispatch as = dispatch_part_a3 (dispatch_part_a1 as)"
proof -
  have a1: "spec_dispatch as =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that apply auto
    by (metis Euclidean_Division.mod_less One_nat_def Suc_lessI ainv_def assms(2) diff_Suc_1)+
  have a2: "dispatch_part_a1 as = as"
    using assms(1) dispatch_part_a1_def by auto
  have a3: "dispatch_part_a3 as =
     (as\<lparr>window_id := window_id as + 1\<rparr>,
      [PARTITION (fst (cur_ttbl as ! (window_id as + 1))),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! (window_id as + 1)))])" if "window_id as \<noteq> length (cur_ttbl as) - 1"
    unfolding dispatch_part_a3_def using assms(2) that by (auto simp add: ainv_def)
  have a4: "spec_dispatch as =
     (as\<lparr>window_id := 0, astate_scheduler.next_mode := NO_SWITCH\<rparr>,
      [PARTITION (fst (cur_ttbl as ! 0)),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding spec_dispatch_def using assms(1) that by auto
  have a5: "dispatch_part_a3 as =
     (as\<lparr>window_id := 0, astate_scheduler.next_mode := NO_SWITCH\<rparr>,
      [PARTITION (fst (cur_ttbl as ! 0)),
       WATCHDOG_ADD (0, snd (cur_ttbl as ! 0))])" if "window_id as = length (cur_ttbl as) - 1"
    unfolding dispatch_part_a3_def using assms(1,2) that
    by (auto simp add: dispatch_part_a2_def ainv_def cur_ttbl_def)
  show ?thesis
    apply (cases "window_id as = length (cur_ttbl as) - 1")
    using a2 a4 a5 apply auto[1]
    using a1 a2 a3 by auto
qed

lemma spec_dispatch_equal:
  assumes "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
    and "ainv as"
  shows "spec_dispatch as = dispatch_part_a3 (dispatch_part_a1 as)"
  using assms spec_dispatch_equal_next_frame spec_dispatch_equal_next_window
        spec_dispatch_equal_no_switch spec_dispatch_equal_ongoing switch_mode.exhaust by blast

subsection \<open>Overall refinement relation\<close>

definition rel_scheduler :: "astate_scheduler \<Rightarrow> cstate \<Rightarrow> bool" where
  "rel_scheduler as cs \<longleftrightarrow> ainv as \<and> cinv cs \<and> rel as cs"

lemma ainv_spec_dispatch:
  assumes "ainv as"
  shows "ainv (fst (spec_dispatch as))"
proof -
  have "time_tables (astate_scheduler.next_ttbl_id as) \<noteq> []"
    using ainv_def assms valid_time_table by fastforce
  then show ?thesis
    unfolding spec_dispatch_def using assms
    apply (auto simp add: ainv_def cur_ttbl_def)
    by (simp add: length_ineq_not_Nil(1))
qed

lemma dispatch_all_rule'':
  assumes "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows
  "\<lbrace> \<lambda>cs es. ainv as \<and> cinv cs \<and> rel_scheduler as cs \<and> es = [] \<rbrace>
     dispatch_all
   \<lbrace> \<lambda>_ cs es. cinv cs \<and> rel_scheduler (fst (spec_dispatch as)) cs \<and> es = snd (spec_dispatch as) \<rbrace>!"
  apply (subst validNF_conj_pre)
  apply auto
  apply (rule validNF_strengthen_post)
  apply (rule validNF_weaken_pre)
    apply (rule dispatch_all_rule'[of as])
  subgoal unfolding rel_scheduler_def ainv_def by auto
  using spec_dispatch_equal[OF assms]
  unfolding rel_scheduler_def apply auto
  unfolding spec_dispatch_equal[OF assms, symmetric]
  apply (rule ainv_spec_dispatch) by auto

lemma dispatch_all_rule:
  assumes "astate_scheduler.next_mode as \<noteq> NEXT_TICK"
  shows
  "\<lbrace> \<lambda>cs es. rel_scheduler as cs \<and> nil\<^sub>e es \<rbrace>
     dispatch_all
   \<lbrace> \<lambda>_ cs es. rel_scheduler (fst (spec_dispatch as)) cs \<and> es = snd (spec_dispatch as) \<rbrace>!"
  apply (rule validNF_weaken_pre)
  apply (rule validNF_strengthen_post)
   apply (rule dispatch_all_rule''[OF assms])
  unfolding rel_scheduler_def nil_event_def by auto

end

end

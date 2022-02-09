theory Cache
  imports EventSystem
begin


subsection \<open>Events\<close>

datatype event =
  ReqS nat | ReqE nat | Inv nat | InvAck nat | SendS nat | SendE nat

datatype state =
  Invalid | Shared | Exclusive

subsection \<open>Implementation of server\<close>

record server =
  invset :: "bool list"
  shrset :: "bool list"
  curptr :: "nat option"
  grantE :: bool

record client =
  st :: state

text \<open>
  Handler for send shared - change status to shared.
\<close>
definition SendS_impl :: "(client, event, unit) event_monad" where
  "SendS_impl = (
    get \<bind> (\<lambda>s.
    put (s\<lparr>st := Shared\<rparr>)))"

theorem SendS_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    SendS_impl
   \<lbrace> \<lambda>_ s es. s = s0\<lparr>st := Shared\<rparr> \<and> es = [] \<rbrace>!"
  unfolding SendS_impl_def apply wp by auto

text \<open>
  Handler for send exclusive - change status to exclusive.
\<close>
definition SendE_impl :: "(client, event, unit) event_monad" where
  "SendE_impl = (
    get \<bind> (\<lambda>s.
    put (s\<lparr>st := Exclusive\<rparr>)))"

theorem SendE_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    SendE_impl
   \<lbrace> \<lambda>_ s es. s = s0\<lparr>st := Exclusive\<rparr> \<and> es = [] \<rbrace>!"
  unfolding SendE_impl_def apply wp by auto

text \<open>
  Handler for invalidate - change status to invalid, then send acknowledgement.
\<close>
definition Inv_impl :: "nat \<Rightarrow> (client, event, unit) event_monad" where
  "Inv_impl i = (
    get \<bind> (\<lambda>s.
    put (s\<lparr>st := Invalid\<rparr>) \<bind> (\<lambda>_.
    signal (InvAck i))))"

theorem Inv_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    Inv_impl i
   \<lbrace> \<lambda>_ s es. s = s0\<lparr>st := Invalid\<rparr> \<and> es = [InvAck i] \<rbrace>!"
  unfolding Inv_impl_def apply wp by auto

text \<open>
  Implementation of grant:
  if invset array becomes all empty, send the appropriate grant.
\<close>
definition grant_impl :: "nat \<Rightarrow> (server, event, unit) event_monad" where
  "grant_impl N = (
    get \<bind> (\<lambda>s.
    if curptr s = None then skip else
      if (\<forall>i. i < N \<longrightarrow> \<not>invset s ! i) then
        if grantE s then
          signal (SendE (the (curptr s))) \<bind> (\<lambda>_.
          put (s\<lparr>curptr := None, shrset := (shrset s)[the (curptr s) := True]\<rparr>))
        else
          signal (SendS (the (curptr s))) \<bind> (\<lambda>_.
          put (s\<lparr>curptr := None, shrset := (shrset s)[the (curptr s) := True]\<rparr>))
      else skip))"

definition grant :: "nat \<Rightarrow> server \<Rightarrow> server" where
  "grant N s =
    (case curptr s of None \<Rightarrow> s | Some j \<Rightarrow>
      if (\<forall>i. i < N \<longrightarrow> \<not>invset s ! i) then
        s\<lparr>curptr := None, shrset := (shrset s)[j := True]\<rparr>
      else s)"

definition grant_ev :: "nat \<Rightarrow> server \<Rightarrow> event list" where
  "grant_ev N s =
    (case curptr s of None \<Rightarrow> [] | Some j \<Rightarrow>
      if (\<forall>i. i < N \<longrightarrow> \<not>invset s ! i) then
        if grantE s then [SendE j] else [SendS j]
      else [])"

theorem grant_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    grant_impl N
   \<lbrace> \<lambda>_ s es. s = grant N s0 \<and> es = grant_ev N s0 \<rbrace>!"
  unfolding grant_impl_def grant_def grant_ev_def
  apply wp by auto

text \<open>
  Handler for invack - update the invset array. Then possibly send
  the appropriate grant.
\<close>
definition Invack_impl :: "nat \<Rightarrow> nat \<Rightarrow> (server, event, unit) event_monad" where
  "Invack_impl N i = (
    get \<bind> (\<lambda>s.
    put (s\<lparr>invset := (invset s)[i := False]\<rparr>) \<bind> (\<lambda>_.
    grant_impl N)))"

theorem Invack_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    Invack_impl N i
   \<lbrace> \<lambda>_ s es. s = grant N (s0\<lparr>invset := (invset s0)[i := False]\<rparr>) \<and>
              es = grant_ev N (s0\<lparr>invset := (invset s0)[i := False]\<rparr>) \<rbrace>!"
  unfolding Invack_impl_def
  apply (rule validNF_bind)
   prefer 2 apply (rule validNF_bind)
    prefer 2 apply (rule grant_rule)
   apply wp apply (rule validNF_weaken_pre)
  apply wp by auto      

definition sendInv_impl :: "nat \<Rightarrow> (server, event, nat) event_monad" where
  "sendInv_impl N = (
    whileLoop (\<lambda>i _. i < N)
      (\<lambda>i. get \<bind> (\<lambda>s.
             if shrset s ! i then
               signal (Inv i) \<bind> (\<lambda>_.
               put (s\<lparr>shrset := (shrset s)[i := False], invset := (invset s)[i := True]\<rparr>) \<bind> (\<lambda>_.
               return (Suc i)))
             else
               return (Suc i))) 0)"

fun sendInv :: "nat \<Rightarrow> nat \<Rightarrow> server \<Rightarrow> server" where
  "sendInv N 0 s = s"
| "sendInv N (Suc i) s =
   (let s' = sendInv N i s in
     if shrset s' ! i then
       s'\<lparr>shrset := (shrset s')[i := False], invset := (invset s')[i := True]\<rparr>
     else s')"

fun sendInv_ev :: "nat \<Rightarrow> nat \<Rightarrow> server \<Rightarrow> event list" where
  "sendInv_ev N 0 s = []"
| "sendInv_ev N (Suc i) s =
   (let s' = sendInv N i s;
        es' = sendInv_ev N i s
    in
      if shrset s' ! i then
        es' @ [Inv i]
      else es')"

theorem sendInv_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    sendInv_impl N
   \<lbrace> \<lambda>i s es. i = N \<and> s = sendInv N N s0 \<and> es = sendInv_ev N N s0 \<rbrace>!"
  unfolding sendInv_impl_def
  apply (rule validNF_whileLoop[where
            I="\<lambda>i s es. i \<le> N \<and> s = sendInv N i s0 \<and> es = sendInv_ev N i s0" and
            R="measure (\<lambda>(r,s). N - r)"])
  subgoal for s es by auto
  subgoal for i s'
    apply wp by (auto simp add: Let_def)
  subgoal by auto
  subgoal for i s es by auto
  done

definition set_curptr :: "nat \<Rightarrow> bool \<Rightarrow> server \<Rightarrow> server" where
  "set_curptr i gE s = (s\<lparr>grantE := gE, curptr := Some i\<rparr>)"

lemma set_curptr_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
     modify (set_curptr i gE)
   \<lbrace> \<lambda>_ s es. s = set_curptr i gE s0 \<and> es = [] \<rbrace>!"
  apply wp unfolding set_curptr_def by auto

text \<open>
  Handler for request shared. If some node has exclusive access, send
  invalidate messages.
\<close>
definition ReqS_impl :: "nat \<Rightarrow> nat \<Rightarrow> (server, event, unit) event_monad" where
  "ReqS_impl N i = (
    get \<bind> (\<lambda>s.
    if grantE s then
      sendInv_impl N \<bind> (\<lambda>_.
      modify (set_curptr i False) \<bind> (\<lambda>_.
      grant_impl N))
    else
      signal (SendS i) \<bind> (\<lambda>_.
      put(s\<lparr>shrset := (shrset s)[i := True]\<rparr>))))"

theorem ReqS_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    ReqS_impl N i
   \<lbrace> \<lambda>_ s es. s = (if grantE s0 then
                     grant N (set_curptr i False (sendInv N N s0))
                   else
                     s0\<lparr>shrset := (shrset s0)[i := True]\<rparr>) \<and>
              es = (if grantE s0 then sendInv_ev N N s0 @ grant_ev N (set_curptr i False (sendInv N N s0))
                    else [SendS i]) \<rbrace>!"
  unfolding ReqS_impl_def apply (rule validNF_bind)
   apply (rule validNF_get_post)
  subgoal for r
    apply (cases "grantE r") apply auto
    subgoal
      apply (rule validNF_bind) apply (subst validNF_conj_pre)
       apply (rule impI) apply (rule sendInv_rule)
      apply (rule validNF_bind)
       apply (subst validNF_conj_pre) apply (rule impI)
       apply (rule validNF_frame2)
       apply (rule set_curptr_rule)
      apply (rule validNF_strengthen_post)
       apply (rule validNF_frame2)
       apply (rule grant_rule)
      by auto
    subgoal unfolding validNF_def valid_def no_fail_def by auto
    subgoal unfolding validNF_def valid_def no_fail_def by auto
    subgoal apply wp by auto
    done
  done

text \<open>
  Handler for request exclusive. Always send invalidate messages.
\<close>
definition ReqE_impl :: "nat \<Rightarrow> nat \<Rightarrow> (server, event, unit) event_monad" where
  "ReqE_impl N i = (
    sendInv_impl N \<bind> (\<lambda>_.
    modify (set_curptr i True) \<bind> (\<lambda>_.
    grant_impl N)))"

theorem ReqE_rule:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    ReqE_impl N i
   \<lbrace> \<lambda>_ s es. s = grant N (set_curptr i True (sendInv N N s0)) \<and>
              es = sendInv_ev N N s0 @ grant_ev N (set_curptr i True (sendInv N N s0)) \<rbrace>!"
  unfolding ReqE_impl_def
  apply (rule validNF_bind)
   apply (rule sendInv_rule)
  subgoal for N'
    apply (subst validNF_conj_pre) apply (rule impI)
    apply (rule validNF_bind)
     apply (rule validNF_frame2)
     apply (rule set_curptr_rule)
    apply (rule validNF_strengthen_post)
     apply (rule validNF_frame2)
     apply (rule grant_rule)
    by auto
  done

subsection \<open>Verify the event system\<close>

fun system :: "nat \<Rightarrow> (event, server \<times> client list) event_system" where
  "system N (ReqS i) = Some (apply_fst (ReqS_impl N i))"
| "system N (ReqE i) = Some (apply_fst (ReqE_impl N i))"
| "system N (Inv i) = Some (apply_snd (apply_idx (Inv_impl i) i))"
| "system N (InvAck i) = Some (apply_fst (Invack_impl N i))"
| "system N (SendS i) = Some (apply_snd (apply_idx SendS_impl i))"
| "system N (SendE i) = Some (apply_snd (apply_idx SendE_impl i))"

theorem sValidNF_SendS:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (SendS i)
    (\<lambda>p es. p = (s0, clist[i := (clist ! i)\<lparr>st := Shared\<rparr>]) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
  apply (rule validNF_apply_snd[where R="\<lambda>s. s = s0"])
    apply (rule validNF_apply_idx[OF SendS_rule])
   apply (auto simp add: nil_event_def)
  by (rule sValidNF_list_null)

theorem sValidNF_SendE:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (SendE i)
    (\<lambda>p es. p = (s0, clist[i := (clist ! i)\<lparr>st := Exclusive\<rparr>]) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
  apply (rule validNF_apply_snd[where R="\<lambda>s. s = s0"])
    apply (rule validNF_apply_idx[OF SendE_rule])
   apply (auto simp add: nil_event_def)
  by (rule sValidNF_list_null)

fun apply_grant :: "nat \<Rightarrow> server \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "apply_grant N s1 (s, clist) =
    (case curptr s1 of None \<Rightarrow> (s, clist) | Some j \<Rightarrow>
      if (\<forall>i. i < N \<longrightarrow> \<not>invset s1 ! i) then
        if grantE s1 then (s, clist[j := (clist ! j)\<lparr>st := Exclusive\<rparr>])
        else (s, clist[j := (clist ! j)\<lparr>st := Shared\<rparr>])
      else (s, clist))"

lemma sValidNF_list_apply_grant:
  "sValidNF_list (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (grant_ev N s1)
    (\<lambda>p es. p = apply_grant N s1 (s0, clist) \<and> nil\<^sub>e es)"
  apply (cases "curptr s1")
  subgoal
    apply (auto simp add: grant_ev_def)
    by (rule sValidNF_list_null)
  subgoal for j
    apply (auto simp add: grant_ev_def)
    subgoal
      apply (rule sValidNF_list_single)
      by (rule sValidNF_SendE)
    subgoal
      apply (rule sValidNF_list_single)
      by (rule sValidNF_SendS)
    subgoal
      by (rule sValidNF_list_null)
    subgoal
      by (rule sValidNF_list_null)
    done
  done

declare apply_grant.simps [simp del]

fun sInvAck :: "nat \<Rightarrow> nat \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "sInvAck N i (s0, clist) =
   (let s1 = s0\<lparr>invset := (invset s0)[i := False]\<rparr> in
     apply_grant N s1 (grant N s1, clist))"

theorem sValidNF_InvAck:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (InvAck i)
    (\<lambda>p es. p = sInvAck N i (s0, clist) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
  apply (rule system.simps)
   apply (rule validNF_weaken_pre)
    apply (rule validNF_apply_fst[where R="\<lambda>s. s = clist"])
    apply (rule Invack_rule)
   apply (auto simp add: nil_event_def)[1]
  apply (auto simp add: Let_def)
  by (rule sValidNF_list_apply_grant)

declare sInvAck.simps [simp del]

fun sInv :: "nat \<Rightarrow> nat \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "sInv N i (s0, clist) =
    sInvAck N i (s0, clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>])"

theorem sValidNF_Inv:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (Inv i)
    (\<lambda>p es. p = sInv N i (s0, clist) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
  apply (rule validNF_apply_snd[where R="\<lambda>s. s = s0"])
  apply (rule validNF_apply_idx[OF Inv_rule])
   apply (auto simp add: nil_event_def)
  apply (rule sValidNF_list_single)
  by (rule sValidNF_InvAck[unfolded nil_event_def])

declare sInv.simps [simp del]

\<comment> \<open>Here s1 is the initial server state for generating the sendInv events.
    (s, clist) is the server/client state the events are applied to\<close>
fun apply_sendInv :: "nat \<Rightarrow> nat \<Rightarrow> server \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "apply_sendInv N 0 s1 (s, clist) = (s, clist)"
| "apply_sendInv N (Suc i) s1 (s, clist) =
   (let s1' = sendInv N i s1;
        (s', clist') = apply_sendInv N i s1 (s, clist)
    in
      if shrset s1' ! i then
        sInv N i (s', clist')
      else
        (s', clist'))"

lemma sValidNF_list_sendInv:
  "sValidNF_list (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (sendInv_ev N i s1)
    (\<lambda>p es. p = apply_sendInv N i s1 (s0, clist) \<and> nil\<^sub>e es)"
proof (induction i)
  case 0
  then show ?case
    by (auto intro: sValidNF_list_null)
next
  case (Suc i)
  show ?case
    apply simp apply (intro conjI impI)
    subgoal apply (rule sValidNF_list_append)
      apply (rule Suc)
      apply (rule sValidNF_list_single)
      apply (cases "apply_sendInv N i s1 (s0, clist)")
      apply auto
      by (rule sValidNF_Inv)
    subgoal
      by (rule Suc)
    done
qed

declare apply_sendInv.simps [simp del]

fun sReq :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "sReq N i b (s0, clist) =
    (let s1 = set_curptr i b (sendInv N N s0);
         s2 = grant N s1
     in
       apply_grant N s1 (apply_sendInv N N s0 (s2, clist)))"

fun sReqE :: "nat \<Rightarrow> nat \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "sReqE N i (s0, clist) = sReq N i True (s0, clist)"

theorem sValidNF_ReqE:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (ReqE i)
    (\<lambda>p es. p = sReqE N i (s0, clist) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
  apply (rule validNF_weaken_pre)
    apply (rule validNF_apply_fst[where R="\<lambda>s. s = clist"])
    apply (rule ReqE_rule)
   apply (auto simp add: nil_event_def)[1]
  subgoal for p es
    apply (cases p) apply auto
    apply (rule sValidNF_list_append)
     apply (rule sValidNF_list_sendInv)
    apply (simp only: Let_def)
    apply (cases "apply_sendInv N N s0 (grant N (set_curptr i True (sendInv N N s0)), clist)")
    apply auto
    by (rule sValidNF_list_apply_grant)
  done

declare sReqE.simps [simp del]

fun sReqS :: "nat \<Rightarrow> nat \<Rightarrow> server \<times> client list \<Rightarrow> server \<times> client list" where
  "sReqS N i (s0, clist) =
    (if grantE s0 then
       sReq N i False (s0, clist)
     else
       (s0\<lparr>shrset := (shrset s0)[i := True]\<rparr>, clist[i := (clist ! i)\<lparr>st := Shared\<rparr>]))"

theorem sValidNF_ReqS:
  "sValidNF (system N)
    (\<lambda>p es. p = (s0, clist) \<and> nil\<^sub>e es)
    (ReqS i)
    (\<lambda>p es. p = sReqS N i (s0, clist) \<and> nil\<^sub>e es)"
  apply (rule sValidNF_Some)
    apply (rule system.simps)
   apply (rule validNF_weaken_pre)
    apply (rule validNF_apply_fst[where R="\<lambda>s. s = clist"])
    apply (rule ReqS_rule)
   apply (auto simp add: nil_event_def)[1]
  subgoal for p es
    apply (cases p) apply auto
    subgoal
      apply (rule sValidNF_list_append)
       apply (rule sValidNF_list_sendInv)
      apply (simp only: Let_def)
      apply (cases "apply_sendInv N N s0 (grant N (set_curptr i False (sendInv N N s0)), clist)")
      apply auto
      by (rule sValidNF_list_apply_grant)
    subgoal
      apply (rule sValidNF_list_single)
      by (rule sValidNF_SendS)
    done
  done

subsection \<open>Functional correctness\<close>

fun system_inv1 :: "nat \<Rightarrow> server \<times> client list \<Rightarrow> bool" where
  "system_inv1 N (s, clist) =
    (length (shrset s) = N \<and> length (invset s) = N \<and> length clist = N \<and>
     (case curptr s of None \<Rightarrow> True | Some j \<Rightarrow> j < N) \<and>
     (\<forall>i<N. (st (clist ! i) = Shared \<or> st (clist ! i) = Exclusive) \<longrightarrow>
            (shrset s ! i \<or> invset s ! i)))"

lemma sendInv_inv':
  "i \<le> N \<Longrightarrow> system_inv1 N (s, clist) \<Longrightarrow>
   system_inv1 N (sendInv N i s, clist)"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have a: "i < N" using Suc(2) by auto
  have b: "length (shrset (sendInv N i s)) = N" using Suc by auto
  have c: "length (invset (sendInv N i s)) = N" using Suc by auto
  show ?case
    unfolding sendInv.simps Let_def
    apply (cases "shrset (sendInv N i s) ! i")
    subgoal using b c apply auto
      subgoal using Suc by auto
      subgoal using Suc by auto
      subgoal for i' apply (cases "i' = i")
        using Suc by (auto simp add: b c)
      subgoal for i' apply (cases "i' = i")
        using Suc by (auto simp add: b c)
      done
    using Suc by auto
qed

lemma sendInv_inv:
  "system_inv1 N (s, clist) \<Longrightarrow> system_inv1 N (sendInv N N s, clist)"
  using sendInv_inv' by auto

lemma set_curptr_inv:
  "i < N \<Longrightarrow> system_inv1 N (s, clist) \<Longrightarrow> system_inv1 N (set_curptr i b s, clist)"
  by (auto simp add: set_curptr_def)

lemma grant_inv:
  "system_inv1 N (s, clist) \<Longrightarrow>
   system_inv1 N (grant N s, clist)"
  apply (cases "curptr s")
  subgoal by (auto simp add: grant_def)
  subgoal for j
    apply (auto simp add: grant_def)
    subgoal for i apply (cases "i = j") by auto
    subgoal for i apply (cases "i = j") by auto
    done
  done

lemma grant_inv2:
  "curptr s = Some j \<Longrightarrow> j < N \<Longrightarrow> length (shrset s) = N \<Longrightarrow>
   \<forall>i. i < N \<longrightarrow> \<not>invset s ! i \<Longrightarrow>
   shrset (grant N s) ! j"
  by (auto simp add: grant_def)

lemma apply_grant_inv:
  "curptr s1 = Some j \<Longrightarrow>
   (\<forall>i. i < N \<longrightarrow> \<not>invset s1 ! i) \<longrightarrow> shrset s ! j \<Longrightarrow>
   system_inv1 N (s, clist) \<Longrightarrow>
   system_inv1 N (apply_grant N s1 (s, clist))"
  apply (auto simp add: apply_grant.simps)
  subgoal for i apply (cases "i = j") by auto
  subgoal for i apply (cases "i = j") by auto
  subgoal for i apply (cases "i = j") by auto
  subgoal for i apply (cases "i = j") by auto
  done

lemma sInv_inv1:
  assumes "curptr s = Some j"
    and "system_inv1 N (s, clist)"
  shows "system_inv1 N (sInv N i (s, clist))"
proof -
  let ?s'="s\<lparr>invset := (invset s)[i := False]\<rparr>"
  have *: "j < N"
    using assms by auto
  have a: "curptr ?s' = Some j"
    using assms(1) by auto
  have b: "system_inv1 N (apply_grant N ?s' (grant N ?s', clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>]))"
  proof (cases "\<forall>i. i < N \<longrightarrow> \<not>invset ?s' ! i")
    case True
    have b1: "grant N ?s' = ?s'\<lparr>curptr := None, shrset := (shrset ?s')[j := True]\<rparr>"
      unfolding grant_def a using True by auto
    show ?thesis 
      apply (rule apply_grant_inv[where j=j])
      subgoal using assms(1) by auto
      subgoal unfolding b1 using * assms(2) by auto
      subgoal apply (rule grant_inv)
        using assms(2) apply auto
        subgoal for j apply (cases "i = j") by auto
        subgoal for j apply (cases "i = j") by auto
        done
      done
  next
    case False
    have b2: "grant N ?s' = ?s'"
      unfolding grant_def a using False by auto
    have b3: "apply_grant N ?s' (?s', clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>]) =
              (?s', clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>])"
      unfolding apply_grant.simps a using False by auto
    show ?thesis
      unfolding b2 b3
      using assms(2) apply auto
      subgoal for j apply (cases "i = j") by auto
      subgoal for j apply (cases "i = j") by auto
      done
  qed
  then show ?thesis
    by (auto simp add: sInv.simps sInvAck.simps Let_def)
qed

lemma sInv_inv2:
  assumes "curptr s = None"
    and "system_inv1 N (s, clist)"
  shows "system_inv1 N (sInv N i (s, clist))"
proof -
  let ?s'="s\<lparr>invset := (invset s)[i := False]\<rparr>"
  have a: "curptr ?s' = None"
    using assms(1) by auto
  have b: "grant N ?s' = ?s'"
    by (auto simp add: grant_def assms(1) a)
  have c: "apply_grant N ?s' (?s', clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>]) =
           (?s', clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>])"
    by (auto simp add: apply_grant.simps assms(1))
  show ?thesis
    apply (auto simp add: sInv.simps sInvAck.simps Let_def)
    unfolding b c 
    using assms(2) apply auto
    subgoal for j apply (cases "i = j") by auto
    subgoal for j apply (cases "i = j") by auto
    done
qed

lemma sInv_inv:
  "system_inv1 N (s, clist) \<Longrightarrow> system_inv1 N (sInv N i (s, clist))"
  apply (cases "curptr s")
  using sInv_inv1 sInv_inv2 by auto

lemma apply_sendInv_inv:
  "system_inv1 N (s, clist) \<Longrightarrow>
   system_inv1 N (apply_sendInv N i s1 (s, clist))"
proof (induction i)
  case 0
  then show ?case
    by (auto simp add: apply_sendInv.simps)
next
  case (Suc i)
  show ?case
    unfolding apply_sendInv.simps Let_def
    apply (cases "shrset (sendInv N i s1) ! i")
    subgoal apply auto
      apply (cases "apply_sendInv N i s1 (s, clist)")
      by (metis Suc.IH Suc.prems sInv_inv)
    using Suc by auto
qed

lemma sendInv_shrset_same:
  assumes "system_inv1 N (s0, clist)"
  shows "j \<ge> i \<Longrightarrow> shrset (sendInv N i s0) ! j = shrset s0 ! j \<and> invset (sendInv N i s0) ! j = invset s0 ! j"
  apply (induction i) by (auto simp add: Let_def)

\<comment> \<open>The following lemmas prove results about shrset and invset\<close>
lemma sendInv_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not>invset s0 ! i"
  shows "i \<le> N \<Longrightarrow> \<forall>j<i. \<not>shrset (sendInv N i s0) ! j \<and> invset (sendInv N i s0) ! j = shrset s0 ! j"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  let ?s'="sendInv N i s0"
  have a: "system_inv1 N (?s', clist)"
    apply (rule sendInv_inv')
    using assms(1) Suc(2) by auto
  have b: ?case if "shrset ?s' ! i"
  proof -
    have b1: "sendInv N (Suc i) s0 = ?s'\<lparr>shrset := (shrset ?s')[i := False], invset := (invset ?s')[i := True]\<rparr>"
      using that by (auto simp add: Let_def)
    have b2: "i < length (shrset ?s')"
      using Suc a by auto
    have b3: "i < length (invset ?s')"
      using Suc a by auto
    show ?case
      apply clarify subgoal for j
        apply (cases "j = i")
        subgoal unfolding b1 using b2 b3 apply auto
          using assms(1) sendInv_shrset_same that by blast
        subgoal
          using b2 b3 Suc by (auto simp add: Let_def)
        done
      done
  qed
  have c: ?case if "\<not>shrset ?s' ! i"
  proof -
    have b1: "sendInv N (Suc i) s0 = ?s'"
      using that by auto
    show ?thesis
      apply clarify subgoal for j
        apply (cases "j = i")
        apply (metis that assms Suc.prems b1 le_refl less_le_trans sendInv_shrset_same)
        by (metis Suc.IH Suc.prems Suc_leD b1 less_antisym)
      done
  qed
  show ?case
    using b c by blast
qed

lemma set_curptr_sendInv_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not>invset s0 ! i"
    and "j < N"
  shows "invset (set_curptr i b (sendInv N N s0)) ! j = shrset s0 ! j"
        "\<not>shrset (set_curptr i b (sendInv N N s0)) ! j"
proof -
  have a: "invset (set_curptr i b (sendInv N N s0)) ! j = invset (sendInv N N s0) ! j"
    by (auto simp add: set_curptr_def)
  have a2: "shrset (set_curptr i b (sendInv N N s0)) ! j = shrset (sendInv N N s0) ! j"
    by (auto simp add: set_curptr_def)
  show "invset (set_curptr i b (sendInv N N s0)) ! j = shrset s0 ! j"
    unfolding a using sendInv_shrset
    by (meson assms order_refl)
  show "\<not>shrset (set_curptr i b (sendInv N N s0)) ! j"
    unfolding a2 using sendInv_shrset
    by (metis assms order_refl)
qed

lemma grant_shrset_Some:
  assumes "system_inv1 N (s0, clist)"
    and "curptr s0 = Some i"
  shows "j < N \<longrightarrow> invset (grant N s0) ! j = invset s0 ! j"
        "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> shrset (grant N s0) ! j = shrset s0 ! j"
        "shrset (grant N s0) ! i \<longleftrightarrow> (shrset s0 ! i \<or> (\<forall>k<N. \<not>invset (grant N s0) ! k))"
proof -
  have *: "i < N"
    using assms(1,2) by auto
  show a: "j < N \<longrightarrow> invset (grant N s0) ! j = invset s0 ! j" for j
    using assms(2) by (auto simp add: grant_def)
  show b: "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> shrset (grant N s0) ! j = shrset s0 ! j" for j
    using assms(2) by (auto simp add: grant_def)
  have c: "shrset (grant N s0) ! i \<longleftrightarrow> (shrset s0 ! i \<or> (\<forall>k<N. \<not>invset s0 ! k))"
    using assms(1,2) * by (auto simp add: grant_def)
  show "shrset (grant N s0) ! i \<longleftrightarrow> (shrset s0 ! i \<or> (\<forall>k<N. \<not>invset (grant N s0) ! k))"
    unfolding c by (auto simp add: a)
qed

lemma grant_shrset_None:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not>invset s0 ! i"
    and "curptr s0 = None"
  shows "j < N \<longrightarrow> invset (grant N s0) ! j = invset s0 ! j"
        "j < N \<longrightarrow> shrset (grant N s0) ! j = shrset s0 ! j"
  using assms by (auto simp add: grant_def)

lemma grant_sendInv_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not>invset s0 ! i"
    and "i < N"
  shows "j < N \<longrightarrow> invset (grant N (set_curptr i b (sendInv N N s0))) ! j = shrset s0 ! j"
        "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> \<not>shrset (grant N (set_curptr i b (sendInv N N s0))) ! j"
        "if \<forall>k<N. \<not> invset (grant N (set_curptr i b (sendInv N N s0))) ! k
         then shrset (grant N (set_curptr i b (sendInv N N s0))) ! i \<and>
              curptr (grant N (set_curptr i b (sendInv N N s0))) = None
         else \<not>shrset (grant N (set_curptr i b (sendInv N N s0))) ! i \<and>
              curptr (grant N (set_curptr i b (sendInv N N s0))) = Some i"
proof -
  let ?s'="set_curptr i b (sendInv N N s0)"
  have a1: "curptr ?s' = Some i"
    by (auto simp add: set_curptr_def)
  have a2: "system_inv1 N (?s', clist)"
    apply (rule set_curptr_inv[OF assms(3)])
    apply (rule sendInv_inv) by (rule assms(1))
  have b1: "j < N \<longrightarrow> invset (grant N ?s') ! j = invset ?s' ! j"
           "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> shrset (grant N ?s') ! j = shrset ?s' ! j"
    using grant_shrset_Some[OF a2 a1] by auto
  show "j < N \<longrightarrow> invset (grant N ?s') ! j = shrset s0 ! j"
    using b1(1) assms(1) assms(2) set_curptr_sendInv_shrset(1) by blast
  show "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> \<not>shrset (grant N ?s') ! j"
    using assms(1) assms(2) b1(2) set_curptr_sendInv_shrset(2) by blast
  show "if \<forall>k<N. \<not> invset (grant N ?s') ! k then
          shrset (grant N ?s') ! i \<and> curptr (grant N ?s') = None
        else
          \<not>shrset (grant N ?s') ! i \<and> curptr (grant N ?s') = Some i"
  proof -
    have c1: "length (shrset (set_curptr i b (sendInv N N s0))) = N"
      using a2 by auto
    show ?thesis
      apply (auto simp add: grant_def a1 c1 assms(3))
      using set_curptr_sendInv_shrset(2)[OF assms(1,2,3)] by auto
  qed
qed

\<comment> \<open>apply_grant does not change either invset or shrset\<close>
lemma apply_grant_shrset:
  "invset (fst (apply_grant N s1 p)) ! k = invset (fst p) ! k"
  "shrset (fst (apply_grant N s1 p)) ! k = shrset (fst p) ! k"
  "curptr (fst (apply_grant N s1 p)) = curptr (fst p)"
  by (cases p, simp add: apply_grant.simps; cases "curptr s1", auto)+

lemma sInv_shrset:
  assumes "system_inv1 N (s, clist)"
    and "i < N"
    and "k < N"
    and "if \<forall>j<N. \<not>invset s ! j then shrset s ! k \<and> curptr s = None
         else \<not>shrset s ! k \<and> curptr s = Some k"
    and "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset s ! j"
  shows "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> invset (fst (sInv N i (s, clist))) ! j = invset s ! j"
        "\<not>invset (fst (sInv N i (s, clist))) ! i"
        "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset (fst (sInv N i (s, clist))) ! j"
        "if \<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j then
           shrset (fst (sInv N i (s, clist))) ! k \<and> curptr (fst (sInv N i (s, clist))) = None
         else
           \<not>shrset (fst (sInv N i (s, clist))) ! k \<and> curptr (fst (sInv N i (s, clist))) = Some k"
proof -
  let ?s'="s\<lparr>invset := (invset s)[i := False]\<rparr>"
  let ?clist'="clist[i := (clist ! i)\<lparr>st := Invalid\<rparr>]"
  let ?s2="grant N ?s'"
  let ?s3="apply_grant N ?s' (grant N ?s', ?clist')"
  have c: "invset ?s2 ! j = invset ?s' ! j" for j
    unfolding grant_def
    apply (cases "curptr (s\<lparr>invset := (invset s)[i := False]\<rparr>)") by auto
  have c2: "shrset ?s2 ! j = shrset s ! j" if "curptr s = None" for j
    unfolding grant_def using that by auto
  have c3: "j \<noteq> k \<longrightarrow> shrset ?s2 ! j = shrset s ! j" if "curptr s = Some k" for j
    unfolding grant_def using that by auto
  have d: "invset (fst ?s3) ! j = invset ?s2 ! j" for j
    unfolding apply_grant.simps
    apply (cases "curptr (s\<lparr>invset := (invset s)[i := False]\<rparr>)") by auto
  have c4: "shrset ?s2 ! k" "curptr ?s2 = None"
    if "curptr s = Some k" "(\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j)"
  proof -
    have c41: "\<forall>j<N. \<not> invset (s\<lparr>invset := (invset s)[i := False]\<rparr>) ! j"
      using that(2) unfolding sInv.simps sInvAck.simps Let_def d c by auto
    show "shrset ?s2 ! k"
      unfolding grant_def using that(1) c41 assms(1,3) by auto
    show "curptr ?s2 = None"
      unfolding grant_def using that(1) c41 assms(1,3) by auto
  qed
  have c5: "shrset ?s2 ! k \<and> curptr ?s2 = None"
    if "\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j" "\<forall>j<N. \<not>invset s ! j"
    unfolding grant_def using assms(4) that(2) by auto
  have c6: "shrset ?s2 ! k \<and> curptr ?s2 = None"
    if "\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j" "\<not>(\<forall>j<N. \<not>invset s ! j)"
    by (simp add: assms(4) c4(1) c4(2) that(1) that(2))
  have c7: "\<not>shrset ?s2 ! k \<and> curptr ?s2 = Some k"
    if "\<not>(\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j)"
  proof -
    have c71: "\<not>(\<forall>j<N. \<not>invset s ! j)"
      using that apply (auto simp add: sInv.simps sInvAck.simps Let_def d c)
      by (metis (full_types) assms(2) list_update_id)
    have c72: "curptr (s\<lparr>invset := (invset s)[i := False]\<rparr>) = Some k"
      using c71 assms(4) by auto
    have c73: "\<not>(\<forall>j<N. \<not>(invset s)[i := False] ! j)"
      using that by (auto simp add: sInv.simps sInvAck.simps Let_def d c)
    have c74: "grant N (s\<lparr>invset := (invset s)[i := False]\<rparr>) = s\<lparr>invset := (invset s)[i := False]\<rparr>"
      by (auto simp add: grant_def c72 c73)
    show ?thesis
      apply (auto simp add: c74) using c71 assms(4) by auto
  qed
  have d2: "shrset (fst ?s3) ! j = shrset ?s2 ! j" for j
    unfolding apply_grant.simps
    apply (cases "curptr (s\<lparr>invset := (invset s)[i := False]\<rparr>)") by auto
  have d3: "curptr (fst ?s3) = curptr ?s2"
    unfolding apply_grant.simps
    apply (cases "curptr (s\<lparr>invset := (invset s)[i := False]\<rparr>)") by auto
  have c8: "shrset (fst ?s3) ! k \<and> curptr (fst ?s3) = None"
    if "\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j"
    unfolding d2 d3 using c5 c6 that by blast
  have c9: "\<not>shrset (fst ?s3) ! k \<and> curptr (fst ?s3) = Some k"
    if "\<not>(\<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j)"
    unfolding d2 d3 using c7 that by blast
  show "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> invset (fst (sInv N i (s, clist))) ! j = invset s ! j"
    by (auto simp add: sInv.simps sInvAck.simps Let_def d c)
  show "\<not>invset (fst (sInv N i (s, clist))) ! i"
    using assms by (auto simp add: sInv.simps sInvAck.simps Let_def d c)
  show "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset (fst (sInv N i (s, clist))) ! j"
    apply clarify unfolding sInv.simps sInvAck.simps Let_def d2
    apply (cases "curptr s") apply (simp add: assms(5) c2)
    by (metis assms(4) assms(5) c2 c3)
  show "if \<forall>j<N. \<not>invset (fst (sInv N i (s, clist))) ! j then
          shrset (fst (sInv N i (s, clist))) ! k \<and> curptr (fst (sInv N i (s, clist))) = None
        else
          \<not>shrset (fst (sInv N i (s, clist))) ! k \<and> curptr (fst (sInv N i (s, clist))) = Some k"
    by (metis c8 c9 sInv.simps sInvAck.simps)
qed

lemma sInv_shrset':
  assumes "system_inv1 N p"
    and "i < N"
    and "k < N"
    and "if \<forall>j<N. \<not>invset (fst p) ! j then shrset (fst p) ! k \<and> curptr (fst p) = None
         else \<not>shrset (fst p) ! k \<and> curptr (fst p) = Some k"
    and "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset (fst p) ! j"
  shows "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> invset (fst (sInv N i p)) ! j = invset (fst p) ! j"
        "\<not>invset (fst (sInv N i p)) ! i"
        "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset (fst (sInv N i p)) ! j"
        "if \<forall>j<N. \<not>invset (fst (sInv N i p)) ! j then
           shrset (fst (sInv N i p)) ! k \<and> curptr (fst (sInv N i p)) = None
         else
           \<not>shrset (fst (sInv N i p)) ! k \<and> curptr (fst (sInv N i p)) = Some k"
proof -
  obtain a b where a: "fst p = a" "p = (a, b)"
    by force
  show "j < N \<longrightarrow> j \<noteq> i \<longrightarrow> invset (fst (sInv N i p)) ! j = invset (fst p) ! j"
    unfolding a(1) unfolding a(2)
    apply (rule sInv_shrset) using assms unfolding a(1) unfolding a(2) by auto
  show "\<not>invset (fst (sInv N i p)) ! i"
    unfolding a(1) unfolding a(2)
    apply (rule sInv_shrset) using assms unfolding a(1) unfolding a(2) by auto
  show "j < N \<longrightarrow> j \<noteq> k \<longrightarrow> \<not>shrset (fst (sInv N i p)) ! j"
    unfolding a(1) unfolding a(2)
    apply (rule sInv_shrset) using assms unfolding a(1) unfolding a(2) by auto
  show "if \<forall>j<N. \<not>invset (fst (sInv N i p)) ! j then
          shrset (fst (sInv N i p)) ! k \<and> curptr (fst (sInv N i p)) = None
        else
          \<not>shrset (fst (sInv N i p)) ! k \<and> curptr (fst (sInv N i p)) = Some k"
    unfolding a(1) unfolding a(2)
    apply (rule sInv_shrset) using assms unfolding a(1) unfolding a(2) by auto
qed

lemma apply_sendInv_shrset:
  assumes "system_inv1 N (s2, clist)"
    and "system_inv1 N (s0, clist)"
    and "\<forall>i<N. invset s2 ! i = shrset s0 ! i"
    and "k < N"
    and "if \<forall>i<N. \<not>invset s2 ! i then shrset s2 ! k \<and> curptr s2 = None
         else \<not>shrset s2 ! k \<and> curptr s2 = Some k"
    and "\<forall>i<N. i \<noteq> k \<longrightarrow> \<not>shrset s2 ! i"
  shows "j \<le> N \<Longrightarrow>
    (i < j \<longrightarrow> \<not>invset (fst (apply_sendInv N j s0 (s2, clist))) ! i) \<and>
    (i \<ge> j \<longrightarrow> i < N \<longrightarrow> invset (fst (apply_sendInv N j s0 (s2, clist))) ! i = shrset s0 ! i) \<and>
    (i < N \<longrightarrow> i \<noteq> k \<longrightarrow> \<not>shrset (fst (apply_sendInv N j s0 (s2, clist))) ! i) \<and>
    (if \<forall>i<N. \<not>invset (fst (apply_sendInv N j s0 (s2, clist))) ! i then
       shrset (fst (apply_sendInv N j s0 (s2, clist))) ! k \<and> curptr (fst (apply_sendInv N j s0 (s2, clist))) = None
     else
       \<not>shrset (fst (apply_sendInv N j s0 (s2, clist))) ! k \<and> curptr (fst (apply_sendInv N j s0 (s2, clist))) = Some k)"
proof (induction j)
  case 0
  show ?case
    unfolding apply_sendInv.simps fst_conv
    using assms by auto
next
  case (Suc j)
  let ?s'="sendInv N j s0"
  let ?s2="apply_sendInv N j s0 (s2, clist)"
  have *: "j < N"
    using Suc(2) by auto
  have b: "system_inv1 N ?s2"
    by (intro apply_sendInv_inv assms(1))
  have b2: "i < j \<longrightarrow> \<not> invset (fst ?s2) ! i"
    "j \<le> i \<longrightarrow> i < N \<longrightarrow> invset (fst ?s2) ! i = shrset s0 ! i"
    "i < N \<longrightarrow> i \<noteq> k \<longrightarrow> \<not> shrset (fst ?s2) ! i"
    "if \<forall>i<N. \<not> invset (fst ?s2) ! i then shrset (fst ?s2) ! k \<and> curptr (fst ?s2) = None
     else \<not> shrset (fst ?s2) ! k \<and> curptr (fst ?s2) = Some k"
    using Suc * by auto
  have ?case if "shrset ?s' ! j"
  proof -
    have **: "shrset s0 ! j"
      using sendInv_shrset_same[OF assms(2), where i=j and j=j] that by auto
    have a: "apply_sendInv N (Suc j) s0 (s2, clist) = sInv N j ?s2"
      unfolding apply_sendInv.simps Let_def using that by auto
    have c: "i < N \<longrightarrow> i \<noteq> j \<longrightarrow> invset (fst (sInv N j ?s2)) ! i = invset (fst ?s2) ! i"
      using sInv_shrset'(1)[OF b * assms(4) b2(4) b2(3)] by auto
    have c2: "\<not> invset (fst (sInv N j ?s2)) ! j"
      using sInv_shrset'(2)[OF b * assms(4) b2(4) b2(3)] by auto
    have c3: "i < N \<longrightarrow> i \<noteq> k \<longrightarrow> \<not> shrset (fst (sInv N j ?s2)) ! i"
      using sInv_shrset'(3)[OF b * assms(4) b2(4) b2(3)] by auto
    have c4: "if \<forall>i<N. \<not> invset (fst (sInv N j ?s2)) ! i then
                shrset (fst (sInv N j ?s2)) ! k \<and> curptr (fst (sInv N j ?s2)) = None
              else
                \<not>shrset (fst (sInv N j ?s2)) ! k \<and> curptr (fst (sInv N j ?s2)) = Some k"
      using sInv_shrset'(4)[OF b * assms(4) b2(4) b2(3)] by auto
    show ?case
      apply (intro conjI)
         apply (metis Suc.IH Suc.prems a c c2 le_def le_less_Suc_eq less_le_trans less_or_eq_imp_le)
        apply (simp add: a b2(2) c)
      using a c3 apply auto[1]
      using a c4 by auto
  qed
  moreover have ?case if "\<not>shrset ?s' ! j"
  proof -
    have **: "\<not>shrset s0 ! j"
      using sendInv_shrset_same[OF assms(2), where i=j and j=j] that by auto
    have a: "apply_sendInv N (Suc j) s0 (s2, clist) = apply_sendInv N j s0 (s2, clist)"
      unfolding apply_sendInv.simps Let_def using that by auto
    show ?case
      apply (rule conjI)
       apply (metis "*" "**" Suc.IH a dual_order.strict_implies_order le_refl less_SucE)
      using "*" Suc.IH Suc_leD a less_or_eq_imp_le by presburger
  qed
  ultimately show ?case
    by blast
qed

lemma apply_sendInv_shrset':
  assumes "system_inv1 N (s2, clist)"
    and "system_inv1 N (s0, clist)"
    and "\<forall>i<N. invset s2 ! i = shrset s0 ! i"
    and "k < N"
    and "if \<forall>i<N. \<not>invset s2 ! i then shrset s2 ! k \<and> curptr s2 = None
         else \<not>shrset s2 ! k \<and> curptr s2 = Some k"
    and "\<forall>i<N. i \<noteq> k \<longrightarrow> \<not>shrset s2 ! i"
  shows "i < N \<Longrightarrow> \<not>invset (fst (apply_sendInv N N s0 (s2, clist))) ! i"
    "i < N \<Longrightarrow> i \<noteq> k \<Longrightarrow> \<not>shrset (fst (apply_sendInv N N s0 (s2, clist))) ! i"
    "if \<forall>i<N. \<not>invset (fst (apply_sendInv N N s0 (s2, clist))) ! i then
       shrset (fst (apply_sendInv N N s0 (s2, clist))) ! k \<and> curptr (fst (apply_sendInv N N s0 (s2, clist))) = None
     else
       \<not>shrset (fst (apply_sendInv N N s0 (s2, clist))) ! k \<and> curptr (fst (apply_sendInv N N s0 (s2, clist))) = Some k"
  using apply_sendInv_shrset[OF assms] by auto

lemma sReq_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "k < N \<Longrightarrow> \<not>invset (fst (sReq N i b (s0, clist))) ! k"
        "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not>shrset (fst (sReq N i b (s0, clist))) ! k"
        "shrset (fst (sReq N i b (s0, clist))) ! i"
        "curptr (fst (sReq N i b (s0, clist))) = None"
proof -
  let ?s'="grant N (set_curptr i b (sendInv N N s0))"
  have a: "system_inv1 N (?s', clist)"
    by (meson assms(1) assms(3) grant_inv sendInv_inv set_curptr_inv)
  have b: "\<forall>k<N. invset ?s' ! k = shrset s0 ! k"
    using assms grant_sendInv_shrset(1) by blast
  have c: "if \<forall>k<N. \<not> invset ?s' ! k then shrset ?s' ! i \<and> curptr ?s' = None
           else \<not> shrset ?s' ! i \<and> curptr ?s' = Some i"
    using assms(1) assms(2) assms(3) grant_sendInv_shrset(3) by blast
  have d: "\<forall>k<N. k \<noteq> i \<longrightarrow> \<not> shrset ?s' ! k"
    by (meson assms(1) assms(2) assms(3) grant_sendInv_shrset(2))
  have e: "k < N \<Longrightarrow> \<not> invset (fst (apply_sendInv N N s0 (?s', clist))) ! k"
          "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not> shrset (fst (apply_sendInv N N s0 (?s', clist))) ! k" for k
    using apply_sendInv_shrset'[OF a assms(1) b assms(3) c d] by auto
  show "k < N \<Longrightarrow> \<not>invset (fst (sReq N i b (s0, clist))) ! k"
    unfolding sReq.simps Let_def
    apply (subst apply_grant_shrset) by (rule e(1))
  show "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not>shrset (fst (sReq N i b (s0, clist))) ! k"
    unfolding sReq.simps Let_def
    apply (subst apply_grant_shrset) by (rule e(2))
  show "shrset (fst (sReq N i b (s0, clist))) ! i"
    unfolding sReq.simps Let_def
    apply (subst apply_grant_shrset)
    using a apply_sendInv_shrset'(3) assms(1) assms(3) b c d e(1) by presburger
  show "curptr (fst (sReq N i b (s0, clist))) = None"
    unfolding sReq.simps Let_def
    apply (subst apply_grant_shrset)
    using a apply_sendInv_shrset'(3) assms(1) assms(3) b c d e(1) by presburger
qed

lemma sReq_inv:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "system_inv1 N (sReq N i b (s0, clist))"
proof -
  let ?s1="set_curptr i b (sendInv N N s0)"
  let ?s2="grant N ?s1"
  let ?s3="apply_sendInv N N s0 (?s2, clist)"
  have a: "curptr ?s1 = Some i"
    unfolding set_curptr_def by auto
  have b: "shrset (fst ?s3) ! i"
    by (metis apply_grant_shrset(2) assms(1) assms(2) assms(3) sReq.simps sReq_shrset(3))
  have c: "system_inv1 N ?s3"
    by (intro apply_sendInv_inv grant_inv set_curptr_inv[OF assms(3)] sendInv_inv assms(1))
  show ?thesis
    apply (cases "apply_sendInv N N s0 (?s2, clist)") apply auto
    apply (rule apply_grant_inv[where j=i])
    using a b c by auto
qed

lemma sReqE_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "k < N \<Longrightarrow> \<not>invset (fst (sReqE N i (s0, clist))) ! k"
        "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not>shrset (fst (sReqE N i (s0, clist))) ! k"
        "shrset (fst (sReqE N i (s0, clist))) ! i"
        "curptr (fst (sReqE N i (s0, clist))) = None"
  unfolding sReqE.simps using sReq_shrset[OF assms] by auto

lemma sReqE_inv1:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "system_inv1 N (sReqE N i (s0, clist))"
  unfolding sReqE.simps using sReq_inv[OF assms] by auto

lemma sReqS_shrset:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "k < N \<Longrightarrow> \<not>invset (fst (sReqS N i (s0, clist))) ! k"
        "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> shrset (fst (sReqS N i (s0, clist))) ! k = (if grantE s0 then False else shrset s0 ! k)"
        "shrset (fst (sReqS N i (s0, clist))) ! i"
  unfolding sReqS.simps
  subgoal apply (cases "grantE s0")
    using assms sReq_shrset(1) apply presburger
    using assms by auto
  subgoal apply (cases "grantE s0")
    using assms sReq_shrset(2) apply presburger
    using assms by auto
  subgoal apply (cases "grantE s0")
    using assms sReq_shrset(3) apply presburger
    using assms by auto
  done

lemma sReqS_inv1:
  assumes "system_inv1 N (s0, clist)"
    and "\<forall>i<N. \<not> invset s0 ! i"
    and "i < N"
  shows "system_inv1 N (sReqS N i (s0, clist))"
  unfolding sReqS.simps apply (cases "grantE s0")
  subgoal unfolding if_P sReq.simps using sReq_inv[OF assms] by auto
  subgoal unfolding if_not_P
    using assms apply auto
    subgoal for i' apply (cases "i = i'") by auto
    subgoal for i' apply (cases "i = i'") by auto
    done
  done

fun system_inv2 :: "nat \<Rightarrow> server \<times> client list \<Rightarrow> bool" where
  "system_inv2 N (s0, clist) =
    ((\<forall>i<N. \<not>invset s0 ! i) \<and>
     (grantE s0 \<longrightarrow> (\<forall>i j. i < N \<longrightarrow> j < N \<longrightarrow> i \<noteq> j \<longrightarrow> \<not>shrset s0 ! i \<or> \<not>shrset s0 ! j)))"

lemma sReqE_inv2:
  assumes "system_inv1 N (s0, clist)"
    and "system_inv2 N (s0, clist)"
    and "i < N"
  shows "system_inv2 N (sReqE N i (s0, clist))"
proof -
  let ?p="sReqE N i (s0, clist)"
  have a: "\<forall>i<N. \<not>invset s0 ! i"
    using assms(2) by auto
  have b: "\<forall>i<N. \<not>invset (fst ?p) ! i"
    using sReqE_shrset(1)[OF assms(1) a assms(3)] by auto
  have c: "k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not> shrset (fst ?p) ! k" for k
    using sReqE_shrset(2)[OF assms(1) a assms(3)] by auto
  show ?thesis
    apply (cases "sReqE N i (s0, clist)")
    using b c by auto
qed

lemma grant_grantE [simp]:
  "grantE (grant N s) = grantE s"
  apply (auto simp add: grant_def) apply (cases "curptr s") apply auto
   apply (cases "\<forall>i<N. \<not> invset s ! i") apply auto
  apply (cases "curptr s") by auto

lemma apply_grant_grantE [simp]:
  "grantE (fst (apply_grant N s1 p)) = grantE (fst p)"
  apply (cases p) subgoal for s clist
  apply (auto simp add: apply_grant.simps) apply (cases "curptr s1") apply auto
   apply (cases "\<forall>i<N. \<not> invset s1 ! i") apply auto
     apply (cases "grantE s1") apply auto apply (cases "curptr s1") by auto
  done

lemma sInvAck_grantE [simp]:
  "grantE (fst (sInvAck N i (s, clist))) = grantE s"
  by (auto simp add: sInvAck.simps Let_def)

lemma sInv_grantE [simp]:
  "grantE (fst (sInv N i p)) = grantE (fst p)"
  apply (cases p) by (auto simp add: sInv.simps)

lemma sReq_grantE:
  "grantE (fst (sReq N i b (s0, clist))) = b"
proof -
  let ?s'="set_curptr i b (sendInv N N s0)"
  let ?s2="grant N ?s'"
  have a: "grantE ?s' = b"
    unfolding set_curptr_def by auto
  have b: "grantE ?s2 = b"
    unfolding grant_def apply (cases "curptr ?s'") using a by auto
  have c: "i \<le> N \<Longrightarrow> grantE (fst (apply_sendInv N i s0 (grant N ?s', clist))) = b" for i
    apply (induction i) using b by (auto simp add: apply_sendInv.simps)
  show ?thesis
    unfolding sReq.simps Let_def using c by auto
qed

lemma sReqS_inv2:
  assumes "system_inv1 N (s0, clist)"
    and "system_inv2 N (s0, clist)"
    and "i < N"
  shows "system_inv2 N (sReqS N i (s0, clist))"
proof -
  let ?p="sReqS N i (s0, clist)"
  have a: "\<forall>i<N. \<not>invset s0 ! i"
    using assms(2) by auto
  have b: "\<forall>i<N. \<not>invset (fst ?p) ! i"
    using sReqS_shrset(1)[OF assms(1) a assms(3)] by auto
  have c: "grantE s0 \<Longrightarrow> k < N \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not> shrset (fst ?p) ! k" for k
    using sReqS_shrset(2)[OF assms(1) a assms(3)] by auto
  have d: "\<not>grantE (fst ?p)"
    unfolding sReqS.simps apply (cases "grantE s0") 
    using sReq_grantE by auto
  show ?thesis
    apply (cases "sReqS N i (s0, clist)")
    using b c d by auto
qed

subsection \<open>Overall result\<close>

fun system_inv :: "nat \<Rightarrow> server \<times> client list \<Rightarrow> bool" where
  "system_inv N (s, clist) \<longleftrightarrow>
   system_inv1 N (s, clist) \<and> system_inv2 N (s, clist)"

definition system_init :: "nat \<Rightarrow> server \<times> client list" where
  "system_init N = (
    \<lparr>invset = map (\<lambda>_. False) [0 ..< N],
     shrset = map (\<lambda>_. False) [0 ..< N],
     curptr = None, grantE = False\<rparr>,
    map (\<lambda>_. \<lparr>st = Invalid\<rparr>) [0 ..< N])"

lemma system_init_inv:
  "system_inv N (system_init N)"
  by (auto simp add: system_init_def)

lemma sReqE_inv:
  assumes "system_inv N (s0, clist)"
    and "i < N"
  shows "system_inv N (sReqE N i (s0, clist))"
proof -
  have a: "system_inv1 N (s0, clist)" "system_inv2 N (s0, clist)"
    using assms(1) by auto
  have b: "system_inv2 N (sReqE N i (s0, clist))"
    apply (rule sReqE_inv2) using a assms(2) by auto
  have c: "\<forall>i<N. \<not> invset s0 ! i"
    using a by auto
  have d: "system_inv1 N (sReqE N i (s0, clist))"
    apply (rule sReqE_inv1) using a c assms(2) by auto
  show ?thesis
    by (metis b d system_inv.elims(3))
qed

lemma sReqS_inv:
  assumes "system_inv N (s0, clist)"
    and "i < N"
  shows "system_inv N (sReqS N i (s0, clist))"
proof -
  have a: "system_inv1 N (s0, clist)" "system_inv2 N (s0, clist)"
    using assms(1) by auto
  have b: "system_inv2 N (sReqS N i (s0, clist))"
    apply (rule sReqS_inv2) using a assms(2) by auto
  have c: "\<forall>i<N. \<not> invset s0 ! i"
    using a by auto
  have d: "system_inv1 N (sReqS N i (s0, clist))"
    apply (rule sReqS_inv1) using a c assms(2) by auto
  show ?thesis
    by (metis b d system_inv.elims(3))
qed

theorem sValidNF_ReqE_inv:
  assumes "i < N"
  shows
  "sValidNF (system N)
    (\<lambda>p es. system_inv N p \<and> nil\<^sub>e es)
    (ReqE i)
    (\<lambda>p es. system_inv N p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where P="\<lambda>p es. \<exists>s clist. system_inv N (s, clist) \<and> p = (s, clist) \<and> nil\<^sub>e es"])
   apply auto[1]
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_conj_pre) apply clarify
  subgoal premises pre for s clist
    apply (rule sValidNF_strengthen_post) prefer 2
     apply (rule sValidNF_ReqE)
    using sReqE_inv[OF pre assms(1)] by auto
  done

theorem sValidNF_ReqS_inv:
  assumes "i < N"
  shows
  "sValidNF (system N)
    (\<lambda>p es. system_inv N p \<and> nil\<^sub>e es)
    (ReqS i)
    (\<lambda>p es. system_inv N p \<and> nil\<^sub>e es)"
  apply (rule sValidNF_weaken_pre[where P="\<lambda>p es. \<exists>s clist. system_inv N (s, clist) \<and> p = (s, clist) \<and> nil\<^sub>e es"])
   apply auto[1]
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_exists_pre2) apply clarify
  apply (subst sValidNF_conj_pre) apply clarify
  subgoal premises pre for s clist
    apply (rule sValidNF_strengthen_post) prefer 2
     apply (rule sValidNF_ReqS)
    using sReqS_inv[OF pre assms(1)] by auto
  done

end

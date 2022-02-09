theory EventSpecWhile
  imports AutoCorres.AutoCorres
begin

text \<open>Remove notation to fix conflicts\<close>
no_notation NonDetMonad.valid   ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
no_notation NonDetMonad.validNF   ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
no_notation NonDetMonad.invariant ("_ \<lbrace>_\<rbrace>" [59,0] 60)
no_notation Monad_Syntax.bind (infixl "\<bind>" 54)

subsection \<open>Event monad\<close>

text \<open>An event monad is similar to a non-deterministic monad, except
  also outputting a list of events. This list is appended during bind.
\<close>
type_synonym ('s,'e,'a) event_monad = "'s \<Rightarrow> ('a \<times> 's \<times> 'e list) set \<times> bool"

definition skip :: "('s,'e,unit) event_monad" where
  "skip = (\<lambda>s. ({((),s,[])}, False))"

definition return :: "'a \<Rightarrow> ('s,'e,'a) event_monad" where
  "return a = (\<lambda>s. ({(a,s,[])}, False))"

definition signal :: "'e \<Rightarrow> ('s,'e,unit) event_monad" where
  "signal e = (\<lambda>s. ({((),s,[e])}, False))"

fun prepend_event :: "'e list \<Rightarrow> 'b \<times> 's \<times> 'e list \<Rightarrow> 'b \<times> 's \<times> 'e list" where
  "prepend_event e1 (b,s2,e2) = (b,s2,e1 @ e2)"

fun bind_cont :: "('a \<Rightarrow> ('s,'e,'b) event_monad) \<Rightarrow> 'a \<times> 's \<times> 'e list \<Rightarrow>
                   ('b \<times> 's \<times> 'e list) set \<times> bool" where
  "bind_cont g (a,s1,e1) = (let (rs2, f2) = g a s1 in (prepend_event e1 ` rs2, f2))"

definition bind :: "('s,'e,'a) event_monad \<Rightarrow> ('a \<Rightarrow> ('s,'e,'b) event_monad) \<Rightarrow>
                    ('s,'e,'b) event_monad" (infixl "\<bind>" 60) where
  "bind f g = (\<lambda>s. let (rs1, f1) = f s in
                   let rss2 = bind_cont g ` rs1 in
                    (\<Union>(fst ` rss2), f1 \<or> True \<in> (snd ` rss2)))"

definition get :: "('s,'e,'s) event_monad" where
  "get = (\<lambda>s. ({(s,s,[])}, False))"

definition put :: "'s \<Rightarrow> ('s,'e,unit) event_monad" where
  "put s = (\<lambda>_. ({((),s,[])}, False))"

definition modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('s,'e,unit) event_monad" where
  "modify f = (get \<bind> (\<lambda>s. put (f s)))"

definition nondet :: "('s,'e,'a) event_monad \<Rightarrow> ('s,'e,'a) event_monad \<Rightarrow> ('s,'e,'a) event_monad"
  (infixr "\<squnion>" 60) where
  "f \<squnion> g = (\<lambda>s. let (rs1, f1) = f s; (rs2, f2) = g s in (rs1 \<union> rs2, f1 \<or> f2))"

subsection \<open>Loops\<close>

inductive_set whileLoop_results ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s,'e,'r) event_monad) \<Rightarrow>
   (('r \<times> 's) \<times> (('r \<times> 's \<times> 'e list) option)) set" for C B where
  "\<lbrakk> \<not> C r s \<rbrakk> \<Longrightarrow> ((r, s), Some (r, s, [])) \<in> whileLoop_results C B"  (* termination *)
| "\<lbrakk> C r s; snd (B r s) \<rbrakk> \<Longrightarrow> ((r, s), None) \<in> whileLoop_results C B"  (* failure on first iteration *)
| "\<lbrakk> C r s; (r', s', e1) \<in> fst (B r s); ((r', s'), None) \<in> whileLoop_results C B \<rbrakk>
    \<Longrightarrow> ((r, s), None) \<in> whileLoop_results C B"  (* failure on remaining iterations *)
| "\<lbrakk> C r s; (r', s', e1) \<in> fst (B r s); ((r', s'), Some (r'', s'', e2)) \<in> whileLoop_results C B \<rbrakk>
    \<Longrightarrow> ((r, s), Some (r'', s'', e1 @ e2)) \<in> whileLoop_results C B"  (* success *)

inductive whileLoop_terminates ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s,'e,'r) event_monad) \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B where
  "\<not> C r s \<Longrightarrow> whileLoop_terminates C B r s"
| "\<lbrakk> C r s; \<forall>(r',s',e1) \<in> fst (B r s). whileLoop_terminates C B r' s' \<rbrakk>
    \<Longrightarrow> whileLoop_terminates C B r s"

definition whileLoop ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s,'e,'r) event_monad) \<Rightarrow> 'r \<Rightarrow> ('s,'e,'r) event_monad" where
  "whileLoop C B = (\<lambda>r s.
     ({(r',s',es). ((r, s), Some (r',s',es)) \<in> whileLoop_results C B},
      ((r, s), None) \<in> whileLoop_results C B \<or> (\<not>whileLoop_terminates C B r s)))"


subsection \<open>Setup syntax\<close>

text \<open>We set up syntax for event monads, just like in NonDetMonad.thy\<close>

print_ast_translation \<open>
  let
    fun monad_tr_event _ [t1, Ast.Appl [Ast.Constant @{type_syntax prod}, 
         t2, Ast.Appl [Ast.Constant @{type_syntax prod}, t3, 
        Ast.Appl [Ast.Constant @{type_syntax list}, t4]]]] =
      if t3 = t1
      then Ast.Appl [Ast.Constant @{type_syntax "event_monad"}, t1, t4, t2]
      else raise Match
  in [(@{type_syntax "fun"}, monad_tr_event)] end
\<close>

text \<open>We use @{text K_bind} to syntactically indicate the
  case where the return argument of the left side of a @{term bind}
  is ignored\<close>

nonterminal
  dobinds and dobind and nobind

syntax
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do ((_);//(_))//od)" 100)
syntax (xsymbols)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)

translations
  "_do (_dobinds b bs) e"  == "_do b (_do bs e)"
  "_do (_nobind b) e"      == "b >>= (CONST K_bind e)"


subsection \<open>Hoare logic\<close>

definition valid ::
  "('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> ('s,'e,'a) event_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
  where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> = (\<forall>s es1. P s es1 \<longrightarrow> (\<forall>(r,s',es2) \<in> fst (f s). Q r s' (es1 @ es2)))"

definition no_fail :: "('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> ('s,'e,'a) event_monad \<Rightarrow> bool" where
  "no_fail P m = (\<forall>s t. P s t \<longrightarrow> \<not>(snd (m s)))"

definition validNF ::
  "('s \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> ('s,'e,'a) event_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
  where
  "validNF P f Q = (valid P f Q \<and> no_fail P f)"

theorem valid_weaken_pre [wp_pre]:
  "\<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace> \<Longrightarrow> (\<And>s e. P s e \<Longrightarrow> Q s e) \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>"
  unfolding valid_def by blast

theorem validNF_weaken_pre [wp_pre]:
  "\<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>! \<Longrightarrow> (\<And>s e. P s e \<Longrightarrow> Q s e) \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def by blast

theorem valid_strengthen_post:
  "\<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace> \<Longrightarrow> (\<And>r s e. Q r s e \<Longrightarrow> R r s e) \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>"
  unfolding valid_def by blast

theorem validNF_strengthen_post:
  "\<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>! \<Longrightarrow> (\<And>r s e. Q r s e \<Longrightarrow> R r s e) \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def by blast

theorem valid_skip [wp]:
  "\<lbrace> \<lambda>s es. P () s es \<rbrace> skip \<lbrace> P \<rbrace>"
  unfolding valid_def skip_def by auto

theorem validNF_skip [wp]:
  "\<lbrace> \<lambda>s es. P () s es \<rbrace> skip \<lbrace> P \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def skip_def by auto

theorem valid_return [wp]:
  "\<lbrace> \<lambda>s. P x s \<rbrace> return x \<lbrace> P \<rbrace>"
  unfolding valid_def return_def by auto

theorem validNF_return [wp]:
  "\<lbrace> \<lambda>s. P x s \<rbrace> return x \<lbrace> P \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def return_def by auto

theorem valid_signal [wp]:
  "\<lbrace> \<lambda>s es. P () s (es @ [e]) \<rbrace> signal e \<lbrace> P \<rbrace>"
  unfolding valid_def signal_def by auto

theorem validNF_signal [wp]:
  "\<lbrace> \<lambda>s es. P () s (es @ [e]) \<rbrace> signal e \<lbrace> P \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def signal_def by auto

theorem valid_get [wp]:
  "\<lbrace> \<lambda>s. P s s \<rbrace> get \<lbrace> P \<rbrace>"
  unfolding valid_def get_def by auto

theorem validNF_get [wp]:
  "\<lbrace> \<lambda>s. P s s \<rbrace> get \<lbrace> P \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def get_def by auto

theorem validNF_get_post:
  "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace>
    get
   \<lbrace> \<lambda>r s es. r = s0 \<and> s = s0 \<and> es = [] \<rbrace>!"
  apply wp by auto

theorem valid_put [wp]:
  "\<lbrace> \<lambda>s. P () x \<rbrace> put x \<lbrace> P \<rbrace>"
  unfolding valid_def put_def by auto

theorem validNF_put [wp]:
  "\<lbrace> \<lambda>s. P () x \<rbrace> put x \<lbrace> P \<rbrace>!"
  unfolding validNF_def valid_def no_fail_def put_def by auto

theorem valid_bind [wp]:
  fixes f :: "('s,'e,'a) event_monad"
    and g :: "'a \<Rightarrow> ('s,'e,'b) event_monad"
  assumes f: "\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>"
    and g: "\<And>x. \<lbrace> B x \<rbrace> g x \<lbrace> C \<rbrace>"
  shows "\<lbrace> A \<rbrace> f \<bind> g \<lbrace> C \<rbrace>"
proof -
  have a: "C a s2 (e1 @ e1' @ e2')" if "A s1 e1" "f s1 = (fs, fterm)" "(x, s1', e1') \<in> fs"
    "g x s1' = (gs, gterm)" "(a, s2, e2') \<in> gs" "e2 = e1' @ e2'" for s1 e1 fs fterm x s1' e1' gs gterm a s2 e2' e2
  proof -
    have "B x s1' (e1 @ e1')"
      using f unfolding valid_def using that(1,2,3) by fastforce
    then have "C a s2 ((e1 @ e1') @ e2')"
      using g unfolding valid_def using that(4,5) by fastforce
    then show ?thesis
      by auto
  qed
  show ?thesis
    unfolding valid_def
    apply auto
    subgoal for s1 e1 a s2 e2
      apply (auto simp add: bind_def)
      apply (cases "f s1")
      apply auto
      subgoal for fs fterm x s1' e1'
        apply (cases "g x s1'")
        apply auto
        subgoal for gs gterm e2'
          using a by auto
        done
      done
    done
qed

theorem validNF_bind [wp]:
  fixes f :: "('s,'e,'a) event_monad"
    and g :: "'a \<Rightarrow> ('s,'e,'b) event_monad"
  assumes f: "\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>!"
    and g: "\<And>x. \<lbrace> B x \<rbrace> g x \<lbrace> C \<rbrace>!"
  shows "\<lbrace> A \<rbrace> f \<bind> g \<lbrace> C \<rbrace>!"
proof -
  have a1: "\<lbrace> A \<rbrace> f \<lbrace> B \<rbrace>" "no_fail A f"
    using f unfolding validNF_def by auto
  have a2: "\<lbrace> B x \<rbrace> g x \<lbrace> C \<rbrace>" "no_fail (B x) (g x)" for x
    using g unfolding validNF_def by auto
  have a3: "\<not>snd (g x s1')"
    if "A s1 e1" "f s1 = (fs, fterm)" "(x, s1', e1') \<in> fs"
    for s1 e1 fs fterm x s1' e1'
  proof -
    have "B x s1' (e1 @ e1')"
      using a1 unfolding valid_def using that(1,2,3) by fastforce
    then show ?thesis
      using a2(2) unfolding no_fail_def by auto
  qed
  show ?thesis
    unfolding validNF_def no_fail_def
    apply (auto simp add: valid_bind[OF a1(1) a2(1)])
    apply (auto simp add: bind_def)
    subgoal for s1 e1
      apply (cases "f s1")
      apply auto
      using a1(2) unfolding no_fail_def apply auto
      subgoal for fs fterm x s1' e1'
        apply (cases "g x s1'")
        apply auto
        using a3[of s1 e1 fs fterm x s1' e1'] by auto
      done
    done
qed

theorem valid_modify [wp]:
  "\<lbrace> \<lambda>s. P () (f s) \<rbrace> modify f \<lbrace> P \<rbrace>"
  unfolding modify_def by wp

theorem validNF_modify [wp]:
  "\<lbrace> \<lambda>s. P () (f s) \<rbrace> modify f \<lbrace> P \<rbrace>!"
  unfolding modify_def by wp

theorem valid_nondet [wp]:
  assumes "\<lbrace> P1 \<rbrace> f \<lbrace> Q \<rbrace>"
    and "\<lbrace> P2 \<rbrace> g \<lbrace> Q \<rbrace>"
  shows "\<lbrace> \<lambda>s es. P1 s es \<and> P2 s es \<rbrace> f \<squnion> g \<lbrace> Q \<rbrace>"
  using assms unfolding valid_def nondet_def
  apply auto subgoal for s es r s' b
    apply (cases "f s") apply (cases "g s") apply auto
    by fastforce+
  done

theorem validNF_nondet [wp]:
  assumes "\<lbrace> P1 \<rbrace> f \<lbrace> Q \<rbrace>!"
    and "\<lbrace> P2 \<rbrace> g \<lbrace> Q \<rbrace>!"
  shows "\<lbrace> \<lambda>s es. P1 s es \<and> P2 s es \<rbrace> f \<squnion> g \<lbrace> Q \<rbrace>!"
  unfolding validNF_def fail_def
  apply (rule conjI)
  subgoal
    apply (rule valid_nondet)
    using assms unfolding validNF_def by auto
  subgoal
    using assms unfolding validNF_def no_fail_def nondet_def
    apply auto subgoal for s es
      apply (cases "f s") apply (cases "g s") by auto
    done
  done

theorem valid_nondet2:
  assumes "\<lbrace> P \<rbrace> f \<lbrace> Q1 \<rbrace>"
    and "\<lbrace> P \<rbrace> g \<lbrace> Q2 \<rbrace>"
  shows "\<lbrace> P \<rbrace> f \<squnion> g \<lbrace> \<lambda>r s es. Q1 r s es \<or> Q2 r s es \<rbrace>"
  using assms unfolding valid_def nondet_def
  apply auto subgoal for s es r s' b
    apply (cases "f s") apply (cases "g s") apply auto
    by fastforce+
  done

theorem validNF_nondet2 [wp]:
  assumes "\<lbrace> P \<rbrace> f \<lbrace> Q1 \<rbrace>!"
    and "\<lbrace> P \<rbrace> g \<lbrace> Q2 \<rbrace>!"
  shows "\<lbrace> P \<rbrace> f \<squnion> g \<lbrace> \<lambda>r s es. Q1 r s es \<or> Q2 r s es \<rbrace>!"
  unfolding validNF_def fail_def
  apply (rule conjI)
  subgoal
    apply (rule valid_nondet2)
    using assms unfolding validNF_def by auto
  subgoal
    using assms unfolding validNF_def no_fail_def nondet_def
    apply auto subgoal for s es
      apply (cases "f s") apply (cases "g s") by auto
    done
  done

theorem valid_whileLoop':
  assumes "\<And>r. \<lbrace> \<lambda>s es. I r s es \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>"
  shows "\<lbrace> \<lambda>s es. I r s es \<rbrace>
            whileLoop C B r
         \<lbrace> \<lambda>r s es. I r s es \<and> \<not>C r s \<rbrace>"
proof -
  have "I r' s' (es1 @ es2) \<and> \<not> C r' s'"
    if assum_a: "I r s es1" "(r', s', es2) \<in> fst (whileLoop C B r s)" for s es1 r' s' es2
  proof -
    obtain vb where a1: "((r, s), vb) \<in> whileLoop_results C B" "vb = Some (r', s', es2)"
      using assum_a(2) unfolding whileLoop_def by auto
    from a1 assum_a(1) show ?thesis
    proof (induct arbitrary: es1 es2 rule: whileLoop_results.induct)
      case (1 r s)
      then show ?case by auto
    next
      case (2 r s)
      then show ?case by auto
    next
      case (3 r s r' s' e1)
      then show ?case by auto
    next
      case (4 r s r2' s2' e1 r'' s'' e2)
      have a1: "r'' = r'" "s'' = s'" "e1 @ e2 = es2"
        using 4(5) by auto
      have a2: "I r2' s2' (es1 @ e1)"
        using 4(1,2,6) assms unfolding valid_def by blast
      have a3: "I r' s' ((es1 @ e1) @ e2) \<and> \<not> C r' s'"
        using 4(4) a1 a2 by blast
      then show ?case
        using a1 by auto
    qed
  qed
  then show ?thesis 
    unfolding valid_def apply clarify
    subgoal for s es1 r' s' es2
      by auto
    done
qed

theorem valid_whileLoop [wp]:
  assumes init: "\<And>s es. P s es \<Longrightarrow> I r s es"
    and inv_step: "\<And>r. \<lbrace> \<lambda>s es. I r s es \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>"
    and final: "\<And>r s es. I r s es \<and> \<not>C r s \<Longrightarrow> Q r s es"
  shows "\<lbrace> P \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
  apply (rule valid_weaken_pre)
   apply (rule valid_strengthen_post)
    apply (rule valid_whileLoop'[OF inv_step])
  using init final by auto

theorem validNF_whileLoop':
  assumes "\<And>r0 s0. \<lbrace> \<lambda>s es. I r0 s es \<and> C r0 s \<and> s = s0 \<rbrace>
                    B r0
                  \<lbrace> \<lambda>r' s' es'. I r' s' es' \<and> ((r', s'), (r0, s0)) \<in> R \<rbrace>!"
    and "wf R"
  shows "\<lbrace> \<lambda>s es. I r s es \<rbrace>
            whileLoop C B r
         \<lbrace> \<lambda>r s es. I r s es \<and> \<not>C r s \<rbrace>!"
proof -
  have a1: "\<lbrace> \<lambda>s es. I r s es \<and> C r s \<rbrace> B r \<lbrace> \<lambda>r' s' es'. I r' s' es' \<rbrace>"
           "no_fail (\<lambda>s es. I r s es \<and> C r s) (B r)" for r
    unfolding valid_def apply auto
    subgoal for s es1 r' s' es'
      using assms(1)[of r s] unfolding validNF_def valid_def
      by auto
    subgoal
      using assms(1)[of r] unfolding validNF_def no_fail_def
      by auto
    done
  have a2: "((r, s), vb) \<in> whileLoop_results C B \<Longrightarrow> vb = None \<Longrightarrow> I r s es \<Longrightarrow> False" for s es vb
  proof (induct arbitrary: es rule: whileLoop_results.induct)
    case (2 r s)
    then show ?case
      using a1(2) unfolding no_fail_def by auto
  next
    case (3 r s r' s' e1)
    then show ?case
      using a1(1) unfolding valid_def by fastforce 
  qed (auto)
  have wf_pair': "(\<And>r s. \<forall>r' s'. ((r', s'), (r, s)) \<in> R \<longrightarrow> P (r', s') \<Longrightarrow> P (r, s)) \<Longrightarrow> P (r, s)" for P r s
    using wf_induct[OF assms(2)] by (metis old.prod.exhaust)
  have wf_pair: "(\<And>r s. \<forall>r' s'. ((r', s'), (r, s)) \<in> R \<longrightarrow> P r' s' \<Longrightarrow> P r s) \<Longrightarrow> P r s" for P r s
    using wf_pair'[of "\<lambda>(r,s). P r s"] by auto
  have a3: "I r s es \<Longrightarrow> whileLoop_terminates C B r s" for es r s
  proof (induction arbitrary: es rule: wf_pair)
    case (1 r s)
    show ?case
    proof (cases "C r s")
      case True
      have b1: "whileLoop_terminates C B r' s'" if "(r', s', es') \<in> fst (B r s)" for r' s' es'
      proof -
        have c1: "I r' s' (es @ es')" "((r', s'), (r, s)) \<in> R"
          using assms(1)[of r s] unfolding validNF_def valid_def
          using 1(2) True that(1) by blast+
        show ?thesis
          using c1 1(1) by auto
      qed
      show ?thesis
        apply (rule whileLoop_terminates.intros(2))
        by (auto simp add: True b1)
    next
      case False
      then show ?thesis
        by (rule whileLoop_terminates.intros(1))
    qed
  qed
  show ?thesis
    unfolding validNF_def
    apply (auto simp add: valid_whileLoop'[OF a1(1)])
    unfolding no_fail_def whileLoop_def snd_conv
    using a2 a3 by auto
qed

theorem validNF_whileLoop [wp]:
  assumes init: "\<And>s es. P s es \<Longrightarrow> I r s es"
    and inv_step:
      "\<And>r0 s0. \<lbrace> \<lambda>s es. I r0 s es \<and> C r0 s \<and> s = s0 \<rbrace>
                 B r0
               \<lbrace> \<lambda>r' s' es'. I r' s' es' \<and> ((r', s'), (r0, s0)) \<in> R \<rbrace>!"
    and wf: "wf R"
    and final: "\<And>r s es. I r s es \<and> \<not>C r s \<Longrightarrow> Q r s es"
  shows "\<lbrace> P \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>!"
  apply (rule validNF_weaken_pre)
   apply (rule validNF_strengthen_post)
    apply (rule validNF_whileLoop'[OF inv_step wf])
  using init final by auto

theorem valid_if_split [wp_split]:
  fixes f :: "('s,'e,'a) event_monad"
  and g :: "('s,'e,'a) event_monad"
  assumes "P \<Longrightarrow> \<lbrace> Q \<rbrace> f \<lbrace> S \<rbrace>" "\<not>P \<Longrightarrow> \<lbrace> R \<rbrace> g \<lbrace> S \<rbrace>"
  shows "\<lbrace> \<lambda>s e. (P \<longrightarrow> Q s e) \<and> (\<not>P \<longrightarrow> R s e)\<rbrace>
          if P then f else g
         \<lbrace> S \<rbrace>"
  using assms by simp

theorem validNF_if_split [wp_split]:
  fixes f :: "('s,'e,'a) event_monad"
  and g :: "('s,'e,'a) event_monad"
  assumes "P \<Longrightarrow> \<lbrace> Q \<rbrace> f \<lbrace> S \<rbrace>!" "\<not>P \<Longrightarrow> \<lbrace> R \<rbrace> g \<lbrace> S \<rbrace>!"
  shows "\<lbrace> \<lambda>s e. (P \<longrightarrow> Q s e) \<and> (\<not>P \<longrightarrow> R s e)\<rbrace>
          if P then f else g
         \<lbrace> S \<rbrace>!"
  using assms by simp

lemma validNF_conj_pre:
  "\<lbrace> \<lambda>r s. b \<and> P r s \<rbrace> c \<lbrace> Q \<rbrace>! \<longleftrightarrow> (b \<longrightarrow> \<lbrace> P \<rbrace> c \<lbrace> Q \<rbrace>!)"
  unfolding validNF_def no_fail_def apply auto
   apply (auto simp add: valid_def) by blast

lemma validNF_ex_pre:
  "(\<And>x. \<lbrace> \<lambda>s e. P x s e \<rbrace> c \<lbrace> Q \<rbrace>!) \<Longrightarrow> \<lbrace> \<lambda>s e. \<exists>x. P x s e \<rbrace> c \<lbrace> Q \<rbrace>!"
  unfolding validNF_def no_fail_def valid_def by blast+

subsection \<open>Operations on sequences of events\<close>

definition nil_event :: "'e list \<Rightarrow> bool" ("nil\<^sub>e") where
  "nil\<^sub>e = (\<lambda>es. es = [])"

definition chop_event :: "('e list \<Rightarrow> bool) \<Rightarrow> ('e list \<Rightarrow> bool) \<Rightarrow> ('e list \<Rightarrow> bool)" (infixr "^\<^sub>e" 75) where
  "A ^\<^sub>e B = (\<lambda>es. \<exists>es1 es2. A es1 \<and> B es2 \<and> es = es1 @ es2)"

lemma valid_frame:
  assumes "\<lbrace> \<lambda>s t. P s \<and> nil\<^sub>e t \<rbrace> c \<lbrace> \<lambda>r s t. P' r s \<and> Q s t \<rbrace>"
  shows "\<lbrace> \<lambda>s t. P s \<and> R t \<rbrace> c \<lbrace> \<lambda> r s t. P' r s \<and> (R ^\<^sub>e Q s) t \<rbrace>"
proof -
  have a: "P' r s'" "(R ^\<^sub>e Q s') (es @ es')"
    if "(r, s', es') \<in> fst (c s)" "P s" "R es" for s es r s' es'
  proof -
    have a1: "P s \<and> nil\<^sub>e []"
      using that(2) by (auto simp add: nil_event_def)
    have a2: "\<forall>(r, s', es2)\<in>fst (c s). P' r s' \<and> Q s' ([] @ es2)"
      using assms unfolding valid_def using a1 by blast
    show "P' r s'"
      using a2 that(1) by auto
    show "(R ^\<^sub>e Q s') (es @ es')"
      apply (auto simp add: chop_event_def)
      apply (rule exI[where x=es])
      using a2 that(1,3) by auto
  qed
  show ?thesis
    unfolding valid_def using a by auto
qed

lemma validNF_frame:
  assumes "\<lbrace> \<lambda>s t. P s \<and> nil\<^sub>e t \<rbrace> c \<lbrace> \<lambda>r s t. P' r s \<and> Q s t \<rbrace>!"
  shows "\<lbrace> \<lambda>s t. P s \<and> R t \<rbrace> c \<lbrace> \<lambda> r s t. P' r s \<and> (R ^\<^sub>e Q s) t \<rbrace>!"
  unfolding validNF_def apply auto
  subgoal using assms valid_frame
    unfolding validNF_def by fastforce
  subgoal using assms
    unfolding validNF_def no_fail_def
    by (simp add: nil_event_def)
  done

lemma valid_frame2:
  assumes "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace> c
           \<lbrace> \<lambda>r s es. Q r s \<and> es = g s0 \<rbrace>"
  shows "\<lbrace> \<lambda>s es. s = s0 \<and> es = es0 \<rbrace> c
         \<lbrace> \<lambda>r s es. Q r s \<and> es = es0 @ g s0 \<rbrace>"
  unfolding valid_def apply auto
  subgoal for s r s'
    using assms unfolding valid_def by fastforce
  subgoal for s r s'
    using assms unfolding valid_def by fastforce
  done

lemma validNF_frame2:
  assumes "\<lbrace> \<lambda>s es. s = s0 \<and> es = [] \<rbrace> c
           \<lbrace> \<lambda>r s es. Q r s \<and> es = g s0 \<rbrace>!"
  shows "\<lbrace> \<lambda>s es. s = s0 \<and> es = es0 \<rbrace> c
         \<lbrace> \<lambda>r s es. Q r s \<and> es = es0 @ g s0 \<rbrace>!"
  unfolding validNF_def apply auto
  subgoal using assms valid_frame2
    unfolding validNF_def by fastforce
  subgoal using assms
    unfolding validNF_def no_fail_def by auto
  done

end

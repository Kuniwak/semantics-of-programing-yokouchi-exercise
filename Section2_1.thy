theory Section2_1 imports Main begin

section "Exercise 2.1"

type_alias var = nat


datatype expr =
  NatLit nat |
  Var var |
  Plus expr expr |
  LAbs "var list" expr |
  LApp expr "expr list"


fun varSubst :: "expr \<Rightarrow> (var \<times> expr) list \<Rightarrow> expr" where
  varSubstNatLit_iff: "varSubst (NatLit n) _ = (NatLit n)" |
  varSubstVarNil_iff: "varSubst (Var v') [] = (Var v')" |
  varSubstVarCons_iff: "varSubst (Var v') ((v, e)#vs) = (if v = v' then e else varSubst (Var v') vs)" |
  varSubstPlus_iff: "varSubst (Plus l r) ss = (Plus (varSubst l ss) (varSubst r ss))" |
  varSubstLAbs_iff: "varSubst (LAbs vs b) ss = (LAbs vs (varSubst b ss))" |
  varSubstLApp_iff: "varSubst (LApp f ps) ss = (LApp (varSubst f ss) (map (\<lambda>p. varSubst p ss) ps))"


lemma pairConsI[intro]: "\<lbrakk> \<forall>i < length xs. zs!i = (xs!i, ys!i) \<rbrakk> \<Longrightarrow> (\<forall>i < length (x#xs). ((x, y)#zs)!i = ((x#xs)!i, (y#ys)!i))"
  using less_Suc_eq_0_disj by auto


inductive_set B :: "(expr \<times> expr) set" where
  BNatLitI: "(NatLit n, NatLit n) \<in> B" |
  BVarI: "(Var v, Var v) \<in> B" |
  BPlusI: "\<lbrakk> (l, l') \<in> B; (r, r') \<in> B \<rbrakk> \<Longrightarrow> (Plus l r, Plus l' r') \<in> B" |
  BLAbsI: "\<lbrakk> (b, b') \<in> B \<rbrakk> \<Longrightarrow> (LAbs vs b, LAbs vs b') \<in> B" |
  BLAppI: "\<lbrakk>
    (f, LAbs vs b) \<in> B;
    length vs = length ps;
    \<forall>i. i < length vs \<longrightarrow> ((ss!i) = (vs!i, ps!i));
    length ss = length vs;
    e = varSubst b ss
  \<rbrakk> \<Longrightarrow> (LApp f ps, e) \<in> B"
  

theorem "((LApp (LAbs [0] (Var 0)) [NatLit 1]), NatLit 1) \<in> B"
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(force)
  apply(intro allI)
  apply(intro impI)
  apply(clarsimp)
  apply(rule nth_Cons_0)
  apply(simp)
  apply(subst varSubstVarCons_iff)
  apply(simp)
  done
  

theorem "(LApp (LApp (LAbs [0] (Var 0)) [LAbs [0] (Var 0)]) [NatLit 2], NatLit 2) \<in> B"
  apply(rule BLAppI)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(simp)
  apply(rule nth_Cons_0)
  apply(simp)
  apply(subst varSubstVarCons_iff)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(rule nth_Cons_0)
  apply(simp)
  apply(subst varSubstVarCons_iff)
  apply(simp)
  done


definition LId :: "expr" where
  "LId \<equiv> (LAbs [0] (Var 0))"


theorem "(LApp LId [e], e) \<in> B"
  apply(unfold LId_def)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(subgoal_tac "\<forall>i<length [0]. [(0, e)] ! i = ([0] ! i, [e] ! i)")
  apply(assumption)
  apply(auto)
  done


definition f :: "expr" where
  "f \<equiv> LAbs [0, 1, 2] (Plus (Var 0) (Plus (Var 1) (Var 2)))"


definition g :: "expr" where
  "g \<equiv> LAbs [0] (LAbs [1] (LAbs [2] (Plus (Var 0) (Plus (Var 1) (Var 2)))))"


lemma f_fullBetaConv: "(LApp f [NatLit 1, NatLit 2, NatLit 3], (Plus (NatLit 1) (Plus (NatLit 2) (NatLit 3)))) \<in> B"
  apply(unfold f_def)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(simp)
  apply(rule BPlusI)
  apply(rule BVarI)
  apply(rule BPlusI)
  apply(rule BVarI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(rule pairConsI)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  done


lemma g_fullBetaConv: "(LApp (LApp (LApp g [NatLit 1]) [NatLit 2]) [NatLit 3], (Plus (NatLit 1) (Plus (NatLit 2) (NatLit 3)))) \<in> B"
  apply(unfold g_def)
  apply(rule BLAppI)
  apply(rule BLAppI)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(simp)
  apply(rule BLAbsI)
  apply(rule BLAbsI)
  apply(rule BPlusI)
  apply(rule BVarI)
  apply(rule BPlusI)
  apply(rule BVarI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(subst varSubstLAbs_iff)
  apply(rule refl)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  done


theorem "\<exists>x. (LApp f [NatLit 1, NatLit 2, NatLit 3], x) \<in> B \<and> (LApp (LApp (LApp g [NatLit 1]) [NatLit 2]) [NatLit 3], x) \<in> B"
  apply(rule_tac x="Plus (NatLit 1) (Plus (NatLit 2) (NatLit 3))" in exI)
  apply(intro conjI)
  apply(rule f_fullBetaConv)
  apply(rule g_fullBetaConv)
  done



fun vars :: "expr \<Rightarrow> var set" where
  varsNarLit_iff: "vars (NatLit _) = {}" |
  varsVar_iff: "vars (Var v) = {v}" |
  varsPlus_iff: "vars (Plus l r) = vars l \<union> vars r" |
  varsLAbs_iff: "vars (LAbs as b) = vars b \<union> set as" |
  varsLApp_iff: "vars (LApp fn ps) = vars fn \<union> (\<Union> (vars ` set ps))"


fun fv :: "expr \<Rightarrow> var set" where
  fvNatLit_iff: "fv (NatLit _) = {}" |
  fvVar_iff: "fv (Var v) = {v}" |
  fvPlus_iff: "fv (Plus l r) = (fv l) \<union> (fv r)" |
  fvLAbs_iff: "fv (LAbs vs b) = (fv b) - (set vs)" |
  fvLApp_iff: "fv (LApp fn as) = (fv fn) \<union> (\<Union> (fv ` set as))"


theorem "0 \<notin> fv (LAbs [0] (Var 0))"
  apply(simp)
  done


theorem "1 \<in> fv (LAbs [0] (Var 1))"
  apply(simp)
  done


theorem "0 \<in> fv (Plus (Var 0) (LApp (LAbs [0] (Var 0)) [NatLit 0]))"
  apply(simp)
  done


fun closed :: "expr \<Rightarrow> bool" where
  "closed e = (fv e = {})"


fun binded :: "var \<Rightarrow> expr \<Rightarrow> bool" where
  bindedNatLit_iff: "binded _ (NatLit _) = False" |
  bindedVar_iff: "binded _ (Var _) = False" |
  bindedPlus_iff: "binded v (Plus l r) = (binded v l \<or> binded v r)" |
  bindedLAbs_iff: "binded v (LAbs as b) = (v \<in> set as \<or> binded v b)" |
  bindedLApp_iff: "binded v (LApp fn ps) = (binded v fn \<or> (\<exists>p \<in> set ps. binded v p))"


inductive_set E :: "expr set" where
  ENatLitI: "NatLit _ \<in> E" |
  EVarI: "Var _ \<in> E" |
  EPlusI: "\<lbrakk> l \<in> E; r \<in> E \<rbrakk> \<Longrightarrow> Plus l r \<in> E" |
  ELAbsI: "\<lbrakk> b \<in> E; \<forall>v \<in> set vs. \<not>binded v b \<rbrakk> \<Longrightarrow> LAbs vs b \<in> E" |
  ELAppI: "\<lbrakk> f \<in> E; \<forall>p \<in> set ps. p \<in> E \<rbrakk> \<Longrightarrow> LApp f ps \<in> E"


inductive_cases ELAbsE: "LAbs vs b \<in> E"


theorem "\<lbrakk> e \<in> E \<rbrakk> \<Longrightarrow> fv e \<subseteq> vars e"
  apply(erule E.induct)
  apply(auto)
  done


theorem "LAbs [0] (Var 0) \<in> E"
  apply(rule ELAbsI)
  apply(rule EVarI)
  apply(intro ballI)
  apply(subst bindedVar_iff)
  apply(rule notI)
  apply(assumption)
  done


lemma listSingletonI: "x \<in> set [x]"
  apply(subst set_simps)
  apply(rule Set.insertI1)
  done


theorem "(LAbs [0] (LAbs [0] (Var 0))) \<notin> E"
  apply(rule notI)
  apply(erule ELAbsE)
  apply(drule_tac x=0 in bspec)
  apply(rule listSingletonI)
  apply(subst (asm) bindedLAbs_iff)
  apply(erule notE)
  apply(rule disjI1)
  apply(rule listSingletonI)
  done


fun betaSet :: "expr \<Rightarrow> expr set" where
  "betaSet e = B\<^sup>+ `` {e}"


theorem "NatLit n \<in> betaSet (NatLit n)"
  apply(auto)
  apply(subst trancl_unfold)
  apply(rule UnI1)
  apply(rule BNatLitI)
  done


theorem "NatLit 1 \<in> betaSet (LApp (LAbs [0] (Var 0)) [NatLit 1])"
  apply(auto)
  apply(subst trancl_unfold)
  apply(rule UnI1)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  done


(* \<beta>簡約が2回必要なのに1回の分岐に入ったみた *)
theorem "NatLit 1 \<in> betaSet (LApp LId [LApp LId [NatLit 1]])"
  apply(auto)
  apply(subst trancl_unfold)
  apply(rule UnI1) (* \<beta>簡約1回の分岐に入る *)
  apply(rule BLAppI)
  apply(unfold LId_def)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  (* goal: False *)
  oops
  

theorem "NatLit 1 \<in> betaSet (LApp LId [LApp LId [NatLit 1]])"
  apply(auto)
  apply(subst trancl_unfold)
  apply(rule UnI2) (* \<beta>簡約1回のルートを避ける *)
  apply(rule relcomp.relcompI)
  apply(subst trancl_unfold)
  apply(rule UnI1) (* \<beta>簡約2回のルートへ入る *)
  apply(rule BLAppI)
  apply(unfold LId_def)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(rule refl)
  apply(subst varSubstVarCons_iff)
  apply(simp)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(rule BVarI)
  apply(simp)
  apply(rule pairConsI)
  apply(simp)
  apply(simp)
  apply(simp)
  done


(* TODO: 練習問題の = の意味が怪しいがこれ以上\<beta>変換できない的な意味なら、それぞれがただ1つのこれ以上
   \<beta>変換できない式をもつ的な条件を加えてあげないと存在限量の主張が題意に対して弱すぎる気がする *)
theorem "\<lbrakk> e \<in> E \<rbrakk> \<Longrightarrow> \<exists>e' \<in> betaSet e. {e'} = betaSet e'"
  oops
end
theory Section2 imports Main begin

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


inductive_set B :: "(expr \<times> expr) set" where
  BNatLitI: "(NatLit n, NatLit n) \<in> B" |
  BVarI: "(Var v, Var v) \<in> B" |
  BPlusI: "(Plus l r, Plus l r) \<in> B" |
  BLAbsI: "(LAbs vs b, LAbs vs b) \<in> B" |
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


definition f :: "expr" where
  "f \<equiv> LAbs [0, 1, 2] (Plus (Var 0) (Plus (Var 1) (Var 2)))"


definition g :: "expr" where
  "g \<equiv> LAbs [0] (LAbs [1] (LAbs [2] (Plus (Var 0) (Plus (Var 1) (Var 2)))))"


lemma append_split: "xs = xs'@[x'] \<Longrightarrow>
    (\<forall>i. i < length xs \<longrightarrow> P i (xs!i)) =
    (P ((length xs) - 1) x' \<and> (\<forall>i'. i' < length xs' \<longrightarrow> P i' (xs'!i')))"
  apply(erule ssubst)
  apply(auto)
  apply(drule_tac x=i' in spec)
  apply(simp add: nth_append)
  by (metis less_antisym nth_append nth_append_length)


lemma f_fullBetaConv: "(LApp f [NatLit 1, NatLit 2, NatLit 3], (Plus (NatLit 1) (Plus (NatLit 2) (NatLit 3)))) \<in> B"
  apply(unfold f_def)
  apply(rule BLAppI)
  apply(rule BLAbsI)
  apply(simp)
  apply(subgoal_tac "\<forall>i<length [0, 1, 2].
       [(0, NatLit 1), (1, NatLit 2), (2, NatLit 3)] ! i =
       ([0, 1, 2] ! i,
        [NatLit 1, NatLit 2, NatLit 3] ! i)")
  apply(assumption)
  apply(subst append_split)
  apply(simp)
  apply(subst append_split)
  apply(simp)
  apply(subst append_split)
  apply(simp)
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
  apply(simp)
  apply(subgoal_tac "[(0, NatLit 1)]! 0 = (0, NatLit (Suc 0))")
  apply(assumption)
  apply(simp)
  apply(simp)
  apply(subst varSubstLAbs_iff)
  apply(subst varSubstLAbs_iff)
  apply(subst varSubstPlus_iff)
  apply(subst varSubstVarCons_iff)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(subgoal_tac "[(Suc 0, NatLit 2)]!0 = (Suc 0, NatLit 2)")
  apply(assumption)
  apply(simp)
  apply(simp)
  apply(subst varSubstLAbs_iff)
  apply(subst varSubstPlus_iff)
  apply(subst varSubstNatLit_iff)
  apply(rule refl)
  apply(simp)
  apply(simp)
  apply(subgoal_tac "[(2, NatLit 3)]!0 = (2, NatLit 3)")
  apply(assumption)
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
end
open HolKernel boolLib bossLib Parse bagTheory listTheory
val _ = new_theory "compositionality";

val _ = add_rule
  {term_name = "Contract", fixity = Closefix,
  pp_elements = [TOK "(", TM, TOK ",", TM, TOK ")"], paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val _ = add_rule
  {term_name = "Assertional", fixity = Closefix,
  pp_elements = [TOK "Assertional(", TM, TOK ")"], paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 450),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "◁"],
                  term_name = "Impl"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 550),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊑"],
                  term_name = "Refines"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 580),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊓"],
                  term_name = "And"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infixl 581,
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "ₓ"],
                  term_name = "Composition"}


Datatype:
  Term = Impl C S | Assertional S | Refines S S ;
  C    = Q α | Composition C C ;
  S    = P (α set) | And S S | Contract S S | Parallell S S
End

Definition C_M:
    C_M (Q α)     = {α}
  ∧ C_M (c1 ₓ c2) = (C_M c1) ∩ (C_M c2)
End

Definition S_M:
    (S_M (P α)             = {α})
  ∧ (S_M (s1 ⊓ s2)         = (S_M s1) ∩ (S_M s2))
  ∧ (S_M (s1, s2)          = {b | ∀b'. C_M b' ∈ S_M s1 ⇒ C_M b' ∩ b ∈ S_M s2})
  ∧ (S_M (Parallell s1 s2) = {a ∩ b | a ∈ (S_M s1) ∧ b ∈ (S_M s2)})
End

Definition T_M:
    (T_M (c ◁ s)      ⇔ C_M c ∈ S_M s)
  ∧ (T_M (s1 ⊑ s2)     ⇔ S_M s1 ⊆ S_M s2)
End

Theorem IMPL_AX_THM:
  ∀c s. T_M (c ◁ s) ⇔ C_M c ∈ S_M s 
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem COMP_ASSOC_THM:
  ∀c1 c2 c3 s. T_M (c1 ₓ c2 ₓ c3 ◁ s) ⇔ T_M (c1 ₓ (c2 ₓ c3) ◁ s)
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[pred_setTheory.INTER_ASSOC]
QED

Theorem COMP_COMM_THM:
  ∀c1 c2 s. T_M (c1 ₓ c2 ◁ s) ⇔ T_M (c2 ₓ c1 ◁ s)
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[pred_setTheory.INTER_COMM]
QED

Theorem ELEM_IN_AND_THM:
  ∀e s1 s2. e ∈ S_M s1 ∧ e ∈ S_M s2 ⇒ e ∈ S_M (s1 ⊓ s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_THM:
  ∀c s1 s2. T_M (c ◁ s1) ∧ T_M (c ◁ s2) ⇒ T_M (c ◁ s1 ⊓ s2)
Proof
  rw[] >>
  metis_tac[IMPL_AX_THM, ELEM_IN_AND_THM]
QED

Theorem AND_ELIM_1_THM:
  ∀c s1 s2. T_M (c ◁ s1 ⊓ s2) ⇒ T_M (c ◁ s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_ELIM_2_THM:
  ∀c s1 s2. T_M (c ◁ s1 ⊓ s2) ⇒ T_M (c ◁ s1)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem REFINEMENT_THM:
  ∀c s1 s2. T_M (c ◁ s1) ∧ T_M (s1 ⊑ s2) ⇒ T_M (c ◁ s2)
Proof
  EVAL_TAC >>
  metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.SUBSET_TRANS]
QED

Theorem CONTRACT_ELIM_THM:
  ∀c1 c2 s1 s2. T_M (c1 ◁ s1) ∧ T_M(c2 ◁ (s1, s2)) ⇒ T_M (c1 ₓ c2 ◁ s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem SPEC_CONTRACT_INTRO_THM:
  ∀c2 s1 s2. (∀q0. T_M (q0 ◁ s1) ⇒ T_M (q0 ₓ c2 ◁ s2)) ⇒ T_M (c2 ◁ (s1,s2))
Proof
  EVAL_TAC >>
  rw[]
QED

Inductive G:
    (∀(t:α Term) Γ. (t <: Γ) ⇒ G Γ t) (* ax *)
  ∧ (∀t1 t2 Γ. G Γ t1 ∧ (T_M t1 ⇒ T_M t2) ⇒ G Γ t2) (* lower-level-imp *)
  ∧ (∀t1 t2 t3 Γ. G Γ t1 ∧ G Γ t2 ∧ (T_M t1 ∧ T_M t2 ⇒ T_M t3) ⇒ G Γ t3) (* lower-level-imp *)
  ∧ (∀q0 c s1 s2 Γ. G (BAG_INSERT (q0 ◁ s1) Γ) ((q0 ₓ c) ◁ s2) ⇒ G Γ (c ◁ (s1, s2))) (* contract *)
  ∧ (∀c1 c2 s Γ. G Γ (c1 ◁ s) ∧ BAG_IN (Assertional s) Γ ⇒ G Γ (c1 ₓ c2 ◁ s)) 
  ∧ (∀t1 t2 Γ . G Γ t1 ⇒ G (BAG_INSERT t2 Γ) t1) (* closure *)
End

val [G_AX, G_LOWER_IMP, G_LOWER_IMP2, G_CONTRACT_AX, G_ASSERTION, G_CLOSURE] = CONJUNCTS G_rules;

Theorem G_REFINEMENT_THM:
  ∀c s1 s2 Γ. G Γ (c ◁ s1) ∧ (BAG_IN (s1 ⊑ s2) Γ) ⇒ G Γ (c ◁ s2)
Proof
  rw[] >>
  ‘G Γ (s1 ⊑ s2)’ by metis_tac[G_AX] >>
  ASSUME_TAC REFINEMENT_THM >>
  metis_tac[G_LOWER_IMP] >>
  metis_tac[G_AX, REFINEMENT_THM, G_LOWER_IMP]
QED

Theorem G_CONTRACT_ELIM_THM:
  ∀c1 c2 s1 s2 Γ. G Γ (c1 ◁ s1) ∧ G Γ (c2 ◁ (s1, s2)) ⇒ G Γ (c1 ₓ c2 ◁ s2)
Proof
  rw[] >>
  metis_tac[G_LOWER_IMP, CONTRACT_ELIM_THM]
QED

val comp_rules = [ELEM_IN_AND_THM,
                  AND_THM,
                  AND_ELIM_1_THM,
                  AND_ELIM_2_THM,
                  CONTRACT_ELIM_THM,
                  SPEC_CONTRACT_INTRO_THM,
                  REFINEMENT_THM,
                  G_AX,
                  G_LOWER_IMP,
                  G_LOWER_IMP2,
                  G_CONTRACT_AX,
                  G_ASSERTION,
                  G_REFINEMENT_THM,
                  G_CONTRACT_ELIM_THM,
                  G_CLOSURE,
                  BAG_IN_BAG_INSERT,
                  COMP_ASSOC_THM,
                  COMP_COMM_THM];

Theorem PAPER_EXAMPLE:
  let
    Γ = {|Assertional a; a ⊑ a1; (a ⊓ g1) ⊑ a2; g2 ⊑ g|}
  in
    G Γ (c1 ◁ (a1, g1)) ∧ G Γ (c2 ◁ (a2, g2)) ⇒ G Γ (c1 ₓ c2 ◁ (a, g))
Proof
  rw[] >>
  metis_tac comp_rules
QED

Theorem FUEL_LEVEL_DISPLAY_CONTROLLER:
    Γ = {|g_I ⊑ a_A;
          g_ADC ⊑ a_I; g_A ⊑ a_DAC;
          g_T ⊑ a_ADC; g_DAC ⊑ a_D;|}
    ∧ G Γ (c_I ◁ (a_I, g_I)) ∧ G Γ (c_A ◁ (a_A, g_A)) (* Program components *)
    ∧ G Γ (c_ADC ◁ (a_ADC, g_ADC)) ∧ G Γ (c_DAC ◁ (a_DAC, g_DAC)) (* Controller components *)
    ∧ G Γ (c_T ◁ (a_T, g_T)) ∧ G Γ (c_D ◁ (a_D, g_D)) (* Additional system components *)
  ⇒ G Γ ((c_T ₓ c_ADC ₓ c_I ₓ c_A ₓ c_DAC ₓ c_D) ◁ (a_T, g_D))
Proof
  rw[] >>
  metis_tac comp_rules
QED

val _ = export_theory();

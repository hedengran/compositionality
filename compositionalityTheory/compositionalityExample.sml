open HolKernel boolLib bossLib Parse bagTheory listTheory compositionalityTheory

val comp_rules = [CONTRACT_ELIM_THM,
                  CONTRACT_INTRO_THM,
                  REFINEMENT_THM,
                  COMP_ASSOC_THM,
                  COMP_COMM_THM,
                  Assertional_AX];

Theorem PAPER_EXAMPLE:
  Assertional(a) ∧
  a ⊑ a1 ∧
  a ⊓ g1 ⊑ a2 ∧
  g2 ⊑ g ∧
  c1 ◁ (a1, g1) ∧
  c2 ◁ (a2, g2)
  ⇒
  c1 ₓ c2 ◁ (a, g)
Proof
  rw[] >>
  sg ‘∀q0. (q0 ◁ a) ⇒ q0 ₓ c1 ₓ c2 ◁ g’ >>
  rw[]
  >- (‘q0 ₓ c1 ◁ a’ by metis_tac[Assertional_AX] >>
     ‘q0 ₓ c1 ◁ a1’ by metis_tac[REFINEMENT_THM] >>
     ‘q0 ◁ a1’ by metis_tac[REFINEMENT_THM] >>
     ‘q0 ₓ c1 ◁ g1’ by metis_tac[CONTRACT_ELIM_THM] >>
     ‘q0 ₓ c1 ◁ a ⊓ g1’ by metis_tac[AND_THM] >>
     ‘q0 ₓ c1 ◁ a2’ by metis_tac[REFINEMENT_THM] >>
     ‘q0 ₓ c1 ₓ c2 ◁ g2’ by metis_tac[CONTRACT_ELIM_THM] >>
     ‘q0 ₓ c1 ₓ c2 ◁ g’ by metis_tac[REFINEMENT_THM])
   >> metis_tac[CONTRACT_INTRO_THM, COMP_COMM_THM, COMP_ASSOC_THM]
QED

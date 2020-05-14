open HolKernel boolLib bossLib Parse bagTheory gentzen_compositionalityTheory

val [G_ax, G_down, G_and_i, G_and_el1, G_and_el2, G_contract_i, G_contract_el, G_assertional, G_refinement, G_comp_assoc, G_comp_comm] = CONJUNCTS G_rules;

Theorem PAPER_EXAMPLE:
  let
    Γ = {|Assertional(a); a ⊑ a1; a ⊓ g1 ⊑ a2; g2 ⊑ g|}
  in
    G Γ (c1 ◁ (a1, g1)) ∧ G Γ (c2 ◁ (a2, g2)) ⇒ G Γ (c1 ₓ c2 ◁ (a, g))
  let
    Γ = {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}
  in
    G Γ (x1 ◁ (A1, G1)) ∧ G Γ (x2 ◁ (A2, G2)) ⇒ G Γ ((x1 ₓ x2) ◁ (A0, G0))
Proof
  rw[] >>
  metis_tac[G_rules]
QED

Theorem FUEL_LEVEL_DISPLAY_CONTROLLER:
  let
    Γ = {|g_I ⊑ a_A; g_ADC ⊑ a_I; g_A ⊑ a_DAC; g_T ⊑ a_ADC; g_DAC ⊑ a_D;|}
  in
      G Γ (c_I ◁ (a_I, g_I))       (* Interface *)
    ∧ G Γ (c_A ◁ (a_A, g_A))       (* Applet *)
    ∧ G Γ (c_ADC ◁ (a_ADC, g_ADC)) (* ADC *)
    ∧ G Γ (c_DAC ◁ (a_DAC, g_DAC)) (* DAC *)
    ∧ G Γ (c_T ◁ (a_T, g_T))       (* Tank *)
    ∧ G Γ (c_D ◁ (a_D, g_D))       (* Display *)
  ⇒ G Γ ((c_T ₓ c_ADC ₓ c_I ₓ c_A ₓ c_DAC ₓ c_D) ◁ (a_T, g_D))
Proof
  rw[] >>
  metis_tac[G_rules]
QED

Theorem PAPER_EXAMPLE_MANUAL:
  let
    Γ = {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}
  in
    G Γ (x1 ◁ (A1, G1)) ∧ G Γ (x2 ◁ (A2, G2)) ⇒ G Γ ((x1 ₓ x2) ◁ (A0, G0))
Proof
  rw[] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (C0 ◁ A0)’ by metis_tac[G_ax, BAG_IN_BAG_INSERT] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (A0 ⊑ A1)’ by metis_tac[G_ax, BAG_IN_BAG_INSERT] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (C0 ◁ A1)’ by metis_tac[G_refinement] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (C0 ◁ A1)’ by metis_tac[G_rules] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (x1 ◁ (A1, G1))’ by metis_tac[G_rules] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ x1) ◁ G1)’ by metis_tac[G_contract_el] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (Assertional(A0))’ by metis_tac[G_ax, BAG_IN_BAG_INSERT] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ x1) ◁ A0)’ by metis_tac[G_assertional] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ x1) ◁ (A0 ⊓ G1))’ by metis_tac[G_and_i] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((A0 ⊓ G1) ⊑ A2)’ by metis_tac[G_ax, BAG_IN_BAG_INSERT] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ x1) ◁ A2)’ by metis_tac[G_refinement] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (x2 ◁ (A2, G2))’ by metis_tac[G_down] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (((C0 ₓ x1) ₓ x2) ◁ G2)’ by metis_tac[G_contract_el] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (G2 ⊑ G0)’ by metis_tac[G_ax, BAG_IN_BAG_INSERT] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (((C0 ₓ x1) ₓ x2) ◁ G0)’ by metis_tac[G_refinement] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) (((C0 ₓ x1) ₓ x2) ◁ G0)’ by metis_tac[G_refinement] >>
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ (x1 ₓ x2)) ◁ G0)’ by metis_tac[G_comp_assoc] >>
  ‘G {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|} ((x1 ₓ x2) ◁ (A0, G0))’ by metis_tac[G_contract_i]
QED


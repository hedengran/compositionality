open HolKernel boolLib bossLib Parse bagTheory ax_compositionality

Theorem Paper_example:
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
  ‘G (BAG_INSERT (C0 ◁ A0) {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|}) ((C0 ₓ (x1 ₓ x2)) ◁ G0)’ by metis_tac[G_comp_assoc1] >>
  ‘G {|Assertional(A0); A0 ⊑ A1; (A0 ⊓ G1) ⊑ A2; G2 ⊑ G0|} ((x1 ₓ x2) ◁ (A0, G0))’ by metis_tac[G_contract_i]
QED

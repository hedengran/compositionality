
open HolKernel boolLib bossLib Parse bagTheory
val _ = new_theory "gentzen_compositionality";

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
                  term_name = "Implements"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 550),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊑"],
                  term_name = "Refines"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 580),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊓"],
                  term_name = "Conjunction"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infixl 581,
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "ₓ"],
                  term_name = "Composition"}

Datatype:
  Term = Implements C S | Assertional S | Refines S S
  ;
  C = Q α | Composition C C
  ;
  S = P (α set) | Conjunction S S | Contract S S | Parallell S S
End

Inductive G:
    (∀(t:α Term) Γ. (t <: Γ) ⇒ G Γ t) (* ax *)
  ∧ (∀t1 (t2:α Term) Γ . G Γ t1 ⇒ G (BAG_INSERT t2 Γ) t1) (* *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ s1) ∧ G Γ (c ◁ s2) ⇒ G Γ (c ◁ (s1 ⊓ s2))) (* and-introduction *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ (s1 ⊓ s2)) ⇒ G Γ (c ◁ s1)) (* and-elimination-1 *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ (s1 ⊓ s2)) ⇒ G Γ (c ◁ s2)) (* and-elimination-2 *)
  ∧ (∀q0 c s1 s2 Γ. G (BAG_INSERT (q0 ◁ s1) Γ) ((q0 ₓ c) ◁ s2) ⇒ G Γ (c ◁ (s1,s2))) (* contract-introduction *)
  ∧ (∀c1 c2 s1 s2 Γ. G Γ (c1 ◁ s1) ∧ G Γ (c2 ◁ (s1, s2)) ⇒ G Γ ((c1 ₓ c2) ◁ s2)) (* contract-elimination *)
  ∧ (∀c1 c2 s Γ. G Γ (c1 ◁ s) ∧ G Γ Assertional(s) ⇒ G Γ ((c1 ₓ c2) ◁ s)) (* assertional *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ s1) ∧ G Γ (s1 ⊑ s2) ⇒ G Γ (c ◁ s2)) (* refinement *)
  ∧ (∀c1 c2 c3 s Γ. G Γ (c1 ₓ c2 ₓ c3 ◁ s) ⇒ G Γ (c1 ₓ (c2 ₓ c3) ◁ s)) (* comp-assoc *)
  ∧ (∀c1 c2 s Γ. G Γ (c1 ₓ c2 ◁ s) ⇒ G Γ (c2 ₓ c1 ◁ s) (* comp-comm *)
End

val [G_ax, G_down, G_and_i, G_and_el1, G_and_el2, G_contract_i, G_contract_el, G_assertional, G_refinement, G_comp_assoc1, G_comp_assoc2] = CONJUNCTS G_rules;

Theorem Conjunction_refinement:
  ∀c s1 s2 s3 Γ. G Γ (c ◁ s1 ⊓ s2) ∧ G Γ (s2 ⊑ s3) ⇒ G Γ (c ◁ (s1 ⊓ s3))
Proof
  metis_tac[G_rules]
QED

Theorem PAPER_EXAMPLE:
  let
    Γ = {|Assertional(a); a ⊑ a1; a ⊓ g1 ⊑ a2; g2 ⊑ g|}
  in
    G Γ (c1 ◁ (a1, g1)) ∧ G Γ (c2 ◁ (a2, g2)) ⇒ G Γ (c1 ₓ c2 ◁ (a, g))
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

val _ = export_theory();

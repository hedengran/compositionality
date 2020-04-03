open HolKernel boolLib bossLib Parse bagTheory
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
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "-:"],
                  term_name = "Implements"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "◁"],
                  term_name = "Implements"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊑"],
                  term_name = "Refines"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "⊓"],
                  term_name = "And"}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [TOK "ₓ"],
                  term_name = "Comp"}

Datatype:
  Term = Implements C S | Assertional S | Refines S S
  ;
  C = Q α | Comp C C
  ;
  S = P (α set) | And S S | Contract S S | Parallell S S
End

Definition C_M:
    C_M (Q α) = {α}
  ∧ C_M (Comp c1 c2) = (C_M c1) ∩ (C_M c2)
End



(* TODO Contract, Parallell *)
Definition S_M:
    (S_M (P α) = {α})
  ∧ (S_M (And s1 s2) = (S_M s1) ∩ (S_M s2))
End

Theorem S_M_refl_And_thm:
  ∀s. S_M s = S_M (And s s)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem S_M_both_And_thm:
  ∀e s1 s2. e ∈ S_M s1 ∧ e ∈ S_M s2 ⇒ e ∈ S_M (And s1 s2)
Proof
  EVAL_TAC >>
  rw[]
QED


Inductive Impls:
      (∀(c:α C). Impls c (P {C_M c}))
    ∧ (∀c s1 s2. Impls c s1 ∧ (S_M s1) ⊆ (S_M s2) ⇒ Impls c s2)
End

val [Impls_ax, Impls_sub] = CONJUNCTS Impls_rules;

Theorem Impls_c_in_s_thm:
  ∀c s. Impls c s ⇒ {C_M c} ∈ S_M s
Proof
  Induct_on ‘Impls’ >>
  rw[]
    >- EVAL_TAC
    >- metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem l_lw:
  ∀c s1 s2. Impls c s1 ∧ Impls c s2 ⇒ Impls c (And s1 s2)
Proof
  Induct_on ‘Impls’
  rw[]
    EVAL_TAC

    ‘Impls c (P {C_M c})’ by metis_tac[Impls_ax]
QED

(*
ax
and-introduction
and-elimination-1
and-elimination-2
contract-introduction
contract-elimination
assertional
refinement
*)
Inductive G:
    (∀(t:α Term) Γ. (t <: Γ) ⇒ G Γ t) (* ax *)
  ∧ (∀t1 (t2:α Term) Γ . G Γ t1 ⇒ G (BAG_INSERT T2 Γ) t1) (* *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ s1) ∧ G Γ (c ◁ s2) ⇒ G Γ (c ◁ (And s1 s2))) (* and-introduction *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ (And s1 s2)) ⇒ G Γ (c ◁ s1)) (* and-elimination-1 *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ (And s1 s2)) ⇒ G Γ (c ◁ s2)) (* and-elimination-2 *)
  ∧ (∀q0 c s1 s2 Γ. G (BAG_INSERT (q0 ◁ s1) Γ) ((q0 ₓ c) ◁ s2) ⇒ G Γ (c ◁ (s1,s2))) (* contract-introduction *)
  ∧ (∀c1 c2 s1 s2 Γ. G Γ (c1 ◁ s1) ∧ G Γ (c2 ◁ (s1, s2)) ⇒ G Γ ((c1 ₓ c2) ◁ s2)) (* contract-elimination *)
  ∧ (∀c1 c2 s Γ. G Γ (c1 ◁ s) ∧ G Γ Assertional(s) ⇒ G Γ ((c1 ₓ c2) ◁ s)) (* assertional *)
  ∧ (∀c s1 s2 Γ. G Γ (c ◁ s1) ∧ G Γ (s1 ⊑ s2) ⇒ G Γ (c ◁ s2)) (* refinement *)
  ∧ (∀c1 c2 c3 s Γ. G Γ (((c1 ₓ c2) ₓ c3) ◁ s) ⇒ G Γ ((c1 ₓ (c2 ₓ c3)) ◁ s)) (* comp-assoc-1 *)
  ∧ (∀c1 c2 c3 s Γ. G Γ ((c1 ₓ (c2 ₓ c3)) ◁ s) ⇒ G Γ (((c1 ₓ c2) ₓ c3) ◁ s)) (* comp-assoc-2 *)
End

val [G_ax, G_down, G_and_i, G_and_el1, G_and_el2, G_contract_i, G_contract_el, G_assertional, G_refinement, G_comp_assoc1, G_comp_assoc2] = CONJUNCTS G_rules;

Theorem Conjunction_refinement:
  ∀c s1 s2 s3. G Γ (c ◁ (s1 ⊓ s2)) ∧ G Γ ((s2 ⊑ s3)) ⇒ G Γ (c ◁ (s1 ⊓ s3))
Proof metis_tac[G_rules]
QED

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


val _ = export_theory();

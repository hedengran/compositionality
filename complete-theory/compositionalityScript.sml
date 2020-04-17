
open HolKernel boolLib bossLib Parse pred_setTheory boolTheory bagTheory
val _ = new_theory "compositionality";

val _ = add_rule
  {term_name = "Contract", fixity = Closefix,
  pp_elements = [TOK "(", TM, TOK ",", TM, TOK ")"], paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

(*
val _ = add_rule
  {term_name = "Assertional", fixity = Closefix,
  pp_elements = [TOK "Assertional(", TM, TOK ")"], paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};
*)

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
  ∧ (S_M (And s1 s2)       = (S_M s1) ∩ (S_M s2))
  ∧ (S_M (Contract s1 s2)  = {b | ∀b'. C_M b' ∈ S_M s1 ⇒ C_M b' ∩ b ∈ S_M s2})
  ∧ (S_M (Parallell s1 s2) = {a ∩ b | a ∈ (S_M s1) ∧ b ∈ (S_M s2)})
End

Definition T_M:
    (T_M (Impl c s)      ⇔ C_M c ∈ S_M s)
  ∧ (T_M (Refines s1 s2) ⇔ S_M s1 ⊆ S_M s2)
End

Theorem IMPL_AX_THM:
  ∀c s. T_M (Impl c s) ⇔ C_M c ∈ S_M s 
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem COMP_ASSOC_THM:
  ∀c1 c2 c3 s. T_M (Impl (Composition (Composition c1 c2) c3) s) ⇔ T_M (Impl (Composition c1 (Composition c2 c3)) s)
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[pred_setTheory.INTER_ASSOC]
QED

Theorem ELEM_IN_AND_THM:
  ∀e s1 s2. e ∈ S_M s1 ∧ e ∈ S_M s2 ⇒ e ∈ S_M (And s1 s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_THM:
  ∀c s1 s2. T_M (Impl c s1) ∧ T_M (Impl c s2) ⇒ T_M (Impl c (And s1 s2))
Proof
  rw[] >>
  metis_tac[IMPL_AX_THM, ELEM_IN_AND_THM]
QED

Theorem AND_ELIM_1_THM:
  ∀c s1 s2. T_M (Impl c (And s1 s2)) ⇒ T_M (Impl c s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_ELIM_2_THM:
  ∀c s1 s2. T_M (Impl c (And s1 s2)) ⇒ T_M (Impl c s1)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem REFINEMENT_THM:
  ∀c s1 s2. T_M (Impl c s1) ∧ T_M (Refines s1 s2) ⇒ T_M (Impl c s2)
Proof
  EVAL_TAC >>
  metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.SUBSET_TRANS]
QED

Theorem CONTRACT_ELIM_THM:
  ∀c1 c2 s1 s2. T_M (Impl c1 s1) ∧ T_M(Impl c2 (s1, s2)) ⇒ T_M (Impl (Composition c1 c2) s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem SPEC_CONTRACT_INTRO_THM:
  ∀c2 s1 s2. (∀q0. T_M (Impl q0 s1) ⇒ T_M (Impl (Composition q0 c2) s2)) ⇒ T_M (Impl c2 (s1,s2))
Proof
  EVAL_TAC >>
  rw[]
QED

(*
define new and operator as part of term grammar
*)

Inductive G:
    (∀(t:α Term) Γ. (t <: Γ) ⇒ G Γ t) (* ax *)
  ∧ (∀t1 t2 Γ. G Γ t1 ∧ (T_M t1 ⇒ T_M t2) ⇒ G Γ t2) (* lower-level-imp *)
  ∧ (∀q0 c s1 s2 Γ. G (BAG_INSERT (Impl q0 s1) Γ) (Impl (Composition q0 c) s2) ⇒ G Γ (Impl c (s1, s2))) (* contract *)
  ∧ (∀c1 c2 s Γ. G Γ (Impl c1 s) ∧ BAG_IN (Assertional s) Γ ⇒ G Γ (Impl (Composition c1 c2) s)) 
  ∧ (∀t1 t2 Γ . G Γ t1 ⇒ G (BAG_INSERT t2 Γ) t1) (* closure *)
End

val [G_AX, G_LOWER_IMP, G_CONTRACT_AX, G_ASSERTION, G_CLOSURE] = CONJUNCTS G_rules;

Theorem G_REFINEMENT_THM:
  ∀c s1 s2 Γ. G Γ ((Impl c s1)) ∧ (BAG_IN (Refines s1 s2) Γ) ⇒ G Γ (Impl c s2)
Proof
  rw[] >>
  ‘G Γ (Refines s1 s2)’ by metis_tac[G_AX] >>
  ASSUME_TAC REFINEMENT_THM >>
  metis_tac[G_LOWER_IMP] >>
  metis_tac[G_AX, REFINEMENT_THM, G_LOWER_IMP]
QED

(*
Theorem G_CONTRACT_INTRO_THM:
  ∀q0 c s1 s2 Γ. G ((Impl q0 s1) INSERT Γ) (Impl (Composition q0 c) s2) ⇒ G Γ (Impl c (s1, s2))
Proof
  rw[]
  ‘G ((Impl q0 s1) INSERT Γ) (Impl q0 s1)’ by metis_tac[G_AX, pred_setTheory.IN_INSERT]
  ASSUME_TAC SPEC_CONTRACT_INTRO_THM
  metis_tac[G_LOWER_IMP]
QED
*)

val comp_rules = [ELEM_IN_AND_THM,
                  AND_THM,
                  AND_ELIM_1_THM,
                  AND_ELIM_2_THM,
                  CONTRACT_ELIM_THM,
                  SPEC_CONTRACT_INTRO_THM,
                  REFINEMENT_THM,
                  G_AX,
                  G_LOWER_IMP,
                  G_CONTRACT_AX,
                  G_ASSERTION,
                  G_REFINEMENT_THM,
                  G_CLOSURE,
                  BAG_IN_BAG_INSERT,
                  COMP_ASSOC_THM];


(*
Context menu

Pallet
*)

Theorem TEST:
  let
    Γ = {|Assertional a; Refines a a1; Refines (And a g1) a2; Refines g2 g|}
  in
    G Γ (Impl c1 (a1, g1)) ∧ G Γ (Impl c2 (a2, g2)) ⇒ G Γ (Impl (Composition c1 c2) (a, g))
Proof
  rw[] >>
  ‘G {|Assertional a; Refines a a1; Refines (And a g1) a2; Refines g2 g|} (Impl (Composition c1 c2) (a, g))’ by metis_tac comp_rules
QED

val _ = export_theory();

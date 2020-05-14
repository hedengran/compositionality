open HolKernel boolLib bossLib Parse bagTheory listTheory
val _ = new_theory "compositionality";

Datatype:
  C         = Q α | Composition C C
            ;
  S         = P (α set) | Conjunction S S | Contract S S | Parallell S S
End

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

Definition C_M:
    C_M (Q α)     = α
  ∧ C_M (c1 ₓ c2) = (C_M c1) ∩ (C_M c2)
End

Definition S_M:
    (S_M (P α)             = α)
  ∧ (S_M (s1 ⊓ s2)         = (S_M s1) ∩ (S_M s2))
  ∧ (S_M (s1, s2)          = {b | ∀b'. b' ∈ S_M s1 ⇒ b' ∩ b ∈ S_M s2})
  ∧ (S_M (Parallell s1 s2) = {a ∩ b | a ∈ (S_M s1) ∧ b ∈ (S_M s2)})
End

Definition Implements:
    Implements c s ⇔ C_M c ∈ S_M s
End

Definition Refines:
    Refines s1 s2 ⇔ S_M s1 ⊆ S_M s2
End

Theorem IMPLEMENTS_AX_THM:
  ∀c s. c ◁ s ⇔ C_M c ∈ S_M s 
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem COMP_EX_THM:
  ∀s. C_M (Q s) = s
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem COMP_IMPL_EX_THM:
  ∀s. ∃s'. C_M s' = s
Proof
  ASSUME_TAC COMP_EX_THM >>
  metis_tac[]
QED

Theorem COMP_ASSOC_THM:
  ∀c1 c2 c3 s. c1 ₓ c2 ₓ c3 ◁ s ⇔ c1 ₓ (c2 ₓ c3) ◁ s
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[pred_setTheory.INTER_ASSOC]
QED

Theorem COMP_COMM_THM:
  ∀c1 c2 s. c1 ₓ c2 ◁ s ⇔ c2 ₓ c1 ◁ s
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[pred_setTheory.INTER_COMM]
QED

Theorem ELEM_IN_AND_THM:
  ∀e s1 s2. e ∈ S_M s1 ∧ e ∈ S_M s2 ⇔ e ∈ S_M (s1 ⊓ s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_THM:
  ∀c s1 s2. c ◁ s1 ∧ c ◁ s2 ⇔ c ◁ s1 ⊓ s2
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_ELIM_1_THM:
  ∀c s1 s2. c ◁ s1 ⊓ s2 ⇒ c ◁ s2
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_ELIM_2_THM:
  ∀c s1 s2. c ◁ s1 ⊓ s2 ⇒ c ◁ s1
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem REFINEMENT_THM:
  ∀c s1 s2. c ◁ s1 ∧ s1 ⊑ s2 ⇒ c ◁ s2
Proof
  EVAL_TAC >>
  metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.SUBSET_TRANS]
QED

Theorem CONTRACT_ELIM_THM:
  ∀c1 c2 s1 s2. c1 ◁ s1 ∧ c2 ◁ (s1, s2) ⇒ c1 ₓ c2 ◁ s2
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem CONTRACT_INTRO_THM:
  ∀q0 c s1 s2. (∀q0. (q0 ◁ s1) ⇒ q0 ₓ c ◁ s2) ⇒ c ◁ (s1,s2)
Proof
  EVAL_TAC >>
  rw[] >>
  metis_tac[COMP_IMPL_EX_THM]
QED

val Assertional_AX =
 new_axiom("Assertional_AX", “∀c1 c2 s. c1 ◁ s ∧ Assertional(s) ⇒ c1 ₓ c2 ◁ s”);

(*
https://github.com/HOL-Theorem-Prover/HOL/blob/develop/examples/logic/propositional_logic/IntuitionisticProofScript.sml
*)

(* todo: or intro, or elim
Inductive G:
    (∀f. G {f} f) (* Base case *)
  ∧ (∀f1 f2 Γ1 Γ2. G Γ1 f1 ∧ G Γ2 f2
         ⇒ G (Γ1 UNION Γ2) (f1 ∧ f2)) (* And Intro *)
  ∧ (∀f1 f2 Γ. G Γ (f1 ∧ f2)
         ⇒ G Γ f1) (* And elim left *)
  ∧ (∀f1 f2 Γ. G Γ (f1 ∧ f2)
         ⇒ G Γ f2) (* And elim right *)
  ∧ (∀f1 f2 Γ. G (f1 INSERT Γ) f2
         ⇒ G Γ (f1 ⇒ f2)) (* Imp intro *)
  ∧ (∀f1 f2 Γ1 Γ2. G Γ2 (f1 ⇒ f2) ∧ G Γ1 f1
         ⇒ G (Γ1 UNION Γ2) f2) (* Imp Elim *)
End

val [G_AX, G_AND_IN, G_AND_EL_R, G_AND_EL_L, G_IMP_IN, G_IMP_EL] = CONJUNCTS G_rules;

Theorem G_lw:
  ∀Γ f1. G Γ f1 ⇒ ∀f2. G (f2 INSERT Γ) f1
Proof
  rw[] >>
  ‘G {f2} f2’ by metis_tac[G_AX] >>
  ‘G ({f2} ∪ Γ) (f2 ∧ f1)’ by metis_tac[G_AND_IN] >>
  ‘G ({f2} ∪ Γ) f1’ by metis_tac[G_AND_EL_L] >>
  metis_tac[INSERT_SING_UNION]
QED
*)

val _ = export_theory();

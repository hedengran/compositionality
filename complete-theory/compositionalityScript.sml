
open HolKernel boolLib bossLib Parse pred_setTheory boolTheory bagTheory
val _ = new_theory "compositionality";

val _ = add_rule
  {term_name = "Contract", fixity = Closefix,
  pp_elements = [TOK "(", TM, TOK ",", TM, TOK ")"], paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2))};

val _ = add_rule
  {term_name = "Interpretation_S", fixity = Closefix,
  pp_elements = [TOK "⟨", TM, TOK "⟩MS"], paren_style = OnlyIfNecessary,
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
                  term_name = "Composition"}

Datatype:
  C = Q α | Composition C C
End

Datatype:
  S = P (α set) | And S S | Contract S S | Parallell S S | Assertional S
End

Definition C_M:
    C_M (Q α) = {α}
  ∧ C_M (c1 ₓ c2) = (C_M c1) ∩ (C_M c2)
End

(* TODO Contract, Parallell *)
Definition Interpretation:
    (S_M (P α) = {α})
  ∧ (S_M (And s1 s2) = (S_M s1) ∩ (S_M s2))
  ∧ (S_M (Contract s1 s2) = {b | ∀b'. b' ∈ S_M s1 ⇒ b' ∩ b ∈ S_M s2})
  ∧ (S_M (Parallell s1 s2) = {a ∩ b | a ∈ (S_M s1) ∧ b ∈ (S_M s2)})
  ∧ (S_M (Assertional s) = S_M s)
End

Definition Impl:
    (Impl (c:α C) (s:α S) = if C_M c ∈ S_M s then T else F)
End

Definition Refines:
  Refines (s1:α S) (s2:α S) = if S_M s1 ⊆ S_M s2 then T else F
End

Theorem IMPL_AX_THM:
  ∀c s. C_M c ∈ S_M s ⇔ Impl c s
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem ELEM_IN_AND_THM:
  ∀e s1 s2. e ∈ S_M s1 ∧ e ∈ S_M s2 ⇒ e ∈ S_M (And s1 s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_THM:
  ∀c s1 s2. Impl c s1 ∧ Impl c s2 ⇒ Impl c (And s1 s2)
Proof
  rw[] >>
  metis_tac[IMPL_AX_THM, ELEM_IN_AND_THM]
QED

Theorem AND_ELIM_1_THM:
  ∀c s1 s2. Impl c (And s1 s2) ⇒ Impl c s2
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem AND_ELIM_2_THM:
  ∀c s1 s2. Impl c (And s1 s2) ⇒ Impl c s1
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem CONTRACT_ELIM_THM:
  ∀c1 c2 s1 s2. Impl c1 s1 ∧ Impl c2 (s1, s2) ⇒ Impl (Composition c1 c2) s2
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem SPEC_CONTRACT_INTRO_THM:
  ∀c2 s1 s2. (∀q0. q0 ∈ S_M s1 ⇒ (q0 ∩ C_M c2) ∈ S_M s2) ⇒ Impl c2 (s1,s2)
Proof
  EVAL_TAC >>
  rw[]
QED

Theorem REFINEMENT_THM:
  ∀c s1 s2. Impl c s1 ∧ Refines s1 s2 ⇒ Impl c s2
Proof
  EVAL_TAC >>
  metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.SUBSET_TRANS]
QED

(*
Theorem CONTRACT_INTRO_THM:
  ∀c2 s1 s2. (∀c1. Impl c1 s1 ⇒ Impl (Composition c1 c2) s2) ⇒ Impl c2 (s1,s2)
Proof
  EVAL_TAC
  rw[]

QED
*)

(*
Context menu

Pallet
        
ax
and-introduction
and-elimination-1
and-elimination-2
contract-introduction
contract-elimination
assertional
refinement
*)


val _ = export_theory();

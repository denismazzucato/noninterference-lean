import .phrase
import .type_system
import .semantics
import .lemmata.structural_subtyping
import .lemmata.phrase_partial_order
import .lemmata.type_soundness

/- -----------------------------------------------------------------------------
 ------------------------------------ Demo ------------------------------------
--------------------------------------------------------------------------- - -/

/- -----------------------------------------------------------------------------
 --------------------------------- First case study, Data Types vs Phrase Types

 Which type is required by this rule? (type system, page 4, 7 and 8)

 λ ⊢ e : τ var,
 λ ⊢ e' : τ
 --------------
 λ ⊢ e := e' : τ cmd

 This rule doesn't tell us precisely which type is typing e'
 1) e' is typed by the phrase type τ (called 'phrase.base τ' in Lean),
    so, e' is of phrase
 2) e' is directly typed by the data type τ
    so, e' is of security_class

 The "e" letter tell us a place for expressions, so if we type the first
 hypothesis with a phrase type also the second must be a phrase type.
 So we type e' as a phrase.

 ------------------------------------------------------------------------------

 And what about this case?
 λ ⊢ l : τ var, if λ(l) = τ

 is τ intended as a data type or the data type wrapped by a phrase?
 In this case is directly a data type (security_class in Lean)

 This is specified in the paper (at the end of page 7), but this is not a
 general rule because it doesn't hold everywhere

 ------------------------------------------------------------------------------

 In conclusion, we can't code directly a paper into Lean, without thinking to
 the details too much.
 We need to be able to formalize every details in a rigorous way.
 A lot of works need to be done before start coding a paper into Lean.

----------------------------------------------------------------------------- -/

#print flow_analysis.security_class
#print flow_analysis.phrase

/- -----------------------------------------------------------------------------
 ---------------------------------------------- Second case study, short proofs

 Regarding Lemma 4.1, every line of paper proof corresponds at almost 7 lines
 in Lean. In Lemma 4.2, this value increases up to 25 lines.
----------------------------------------------------------------------------- -/

#check flow_analysis.structural_subtyping
#check flow_analysis.phrase_partial_order

/- -----------------------------------------------------------------------------
 ------ Third case study, rules and systems need to be splitted to work in Lean

 Deep embedding of expressions need to split every type system into two blocks,
 in the paper they just put expressions and programs all together in the same
 system, Lean doesn't allow this.

 Also to avoid non-determinism some rules need to be splitted in two new rules
----------------------------------------------------------------------------- -/

#check flow_analysis.type_system.program_typing

#check flow_analysis.base_expr
#check flow_analysis.program

/- -----------------------------------------------------------------------------
 ---------------------------- Fourth case study, Rigorous proof vs Formal proof

 In Lemma 6.4 they use induction on the structure of the program,
 this for the letvar case means: (λ, γ ⊢ let x := e in c : τ cmd)
   if I had "λ, γ ⊢ c : τ cmd" I would be able to conclude this case using
   the inductive hypothesis.
   (conclusion coincides because letvar cannot build new locations)
 now "λ, γ ⊢ let x := e in c : τ cmd" tell us two things:
 1) λ, γ ⊢ e : τ, and
 2) λ, γ[x : τ var] ⊢ c : τ cmd
 I can't use the first one to prove "λ, γ ⊢ c : τ cmd" for obviously reasons
 But I can't also use the second one!
 from "λ, γ[x : τ var] ⊢ c : τ cmd" I cannot prove "λ, γ ⊢ c : τ cmd",

 This is very easy to see, just replace c with this simple program "x := 0"
 from an empty context:
   "∅, ∅[x : τ var] ⊢ x := 0 : τ cmd" holds and "∅, ∅ ⊢ x := 0 : τ cmd" does not
   , because it has no information about the x type

 ------------------------------------------------------------------------------

 In conclusion, the lemma holds but the proof isn't totally correct

----------------------------------------------------------------------------- -/

#check flow_analysis.confinement
#check flow_analysis.confinement.exists_variant

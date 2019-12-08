/- Typing rules for secure information flow -/

import .semantics

namespace flow_analysis

namespace syntax_directed

open base_expr program

/- Typing system in a syntax directed fashion
 - in this module, the subtyping rules are carried in the typing rules
 -
 - I wrote lemmata in the classic type system defined in type_system.lean
 - but for the proof work I actually use this one, the benefit of the syntax
 - directed system is that the last used rule in the derivation is uniquely
 - determined, otherwise the subtype rule would always be an option
 -/

inductive expr_typing : base_expr × location × identifier → phrase → Prop
| int {Λ γ n τ} : expr_typing (val n, Λ, γ) (phrase.base τ)
| var {Λ γ x τ} (h : map.lookup x γ = phrase.var τ) :
  expr_typing (var x, Λ, γ) (phrase.var τ)
| varloc {Λ γ x τ} (h : map.lookup x Λ = τ) :
  expr_typing (var x, Λ, γ) (phrase.var τ)
| binop {Λ γ e e' bop τ} :
    expr_typing (e, Λ, γ) (phrase.base τ)
  → expr_typing (e', Λ, γ) (phrase.base τ)
  → expr_typing (e ⟪bop⟫ e', Λ, γ) (phrase.base τ)
| r_val {Λ γ e τ τ'} : --
    expr_typing (e, Λ, γ) (phrase.var τ)
  → τ ≤ τ'
  → expr_typing (e, Λ, γ) (phrase.base τ')

inductive program_typing : program × location × identifier → phrase → Prop
| assign_var {Λ γ e e' τ τ'} : --
    expr_typing (var e, Λ, γ) (phrase.var τ)
  → expr_typing (e', Λ, γ) (phrase.base τ)
  → τ' ≤ τ
  → program_typing (assignv e e', Λ, γ) (phrase.cmd τ')
| assign_loc {Λ γ e e' τ τ'} : --
    expr_typing (loc e, Λ, γ) (phrase.var τ)
  → expr_typing (e', Λ, γ) (phrase.base τ)
  → τ' ≤ τ
  → program_typing (assignl e e', Λ, γ) (phrase.cmd τ')
| compose {Λ γ c c' τ} :
    program_typing (c, Λ, γ) (phrase.cmd τ)
  → program_typing (c', Λ, γ) (phrase.cmd τ)
  → program_typing (c ;; c', Λ, γ) (phrase.cmd τ)
| branch {Λ γ e c c' τ τ'} : --
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ) (phrase.cmd τ)
  → program_typing (c', Λ, γ) (phrase.cmd τ)
  → τ' ≤ τ
  → program_typing (ite e c c', Λ, γ) (phrase.cmd τ')
| while {Λ γ e c τ τ'} : --
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ) (phrase.cmd τ)
  → τ' ≤ τ
  → program_typing (while e c, Λ, γ) (phrase.cmd τ')
| letvar {Λ γ x e c τ τ'} :
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ[ᵢx : phrase.var τ]) (phrase.cmd τ')
  → program_typing (lvar x e c, Λ, γ) (phrase.cmd τ')

notation γ ` ⊢ₛₑ ` e ` : ` ρ:90 := expr_typing (e, γ.1, γ.2) ρ
notation γ ` ⊢ₛ ` p ` : ` ρ:90 := program_typing (p, γ.1, γ.2) ρ

end syntax_directed

end flow_analysis

/- Typing rules for secure information flow -/

import .semantics

namespace flow_analysis

namespace type_system

open base_expr program

/- Typing system
 - this is the core module
 -
 - in this module is specified the typing rules for expressions and programs
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
| r_val {Λ γ e τ} :
    expr_typing (e, Λ, γ) (phrase.var τ)
  → expr_typing (e, Λ, γ) (phrase.base τ)
| subtype {Λ γ p ρ ρ'} :
    expr_typing (p, Λ, γ) ρ
  → ρ ⊆ₛ ρ'
  → expr_typing (p, Λ, γ) ρ'

inductive program_typing : program × location × identifier → phrase → Prop
| assign_var {Λ γ e e' τ} : --
    expr_typing (var e, Λ, γ) (phrase.var τ)
  → expr_typing (e', Λ, γ) (phrase.base τ)
  → program_typing (assignv e e', Λ, γ) (phrase.cmd τ)
| assign_loc {Λ γ e e' τ} : --
    expr_typing (loc e, Λ, γ) (phrase.var τ)
  → expr_typing (e', Λ, γ) (phrase.base τ)
  → program_typing (assignl e e', Λ, γ) (phrase.cmd τ)
| compose {Λ γ c c' τ} :
    program_typing (c, Λ, γ) (phrase.cmd τ)
  → program_typing (c', Λ, γ) (phrase.cmd τ)
  → program_typing (c ;; c', Λ, γ) (phrase.cmd τ)
| branch {Λ γ e c c' τ} :
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ) (phrase.cmd τ)
  → program_typing (c', Λ, γ) (phrase.cmd τ)
  → program_typing (ite e c c', Λ, γ) (phrase.cmd τ)
| while {Λ γ e c τ} :
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ) (phrase.cmd τ)
  → program_typing (while e c, Λ, γ) (phrase.cmd τ)
| letvar {Λ γ x e c τ τ'} :
    expr_typing (e, Λ, γ) (phrase.base τ)
  → program_typing (c, Λ, γ[ᵢx : phrase.var τ]) (phrase.cmd τ')
  → program_typing (lvar x e c, Λ, γ) (phrase.cmd τ')
| subtype {Λ γ p ρ ρ'} :
    program_typing (p, Λ, γ) ρ
  → ρ ⊆ₛ ρ'
  → program_typing (p, Λ, γ) ρ'

notation γ ` ⊢ₑ ` e ` : ` ρ:90 := expr_typing (e, γ.1, γ.2) ρ
notation γ ` ⊢ₜ ` p ` : ` ρ:90 := program_typing (p, γ.1, γ.2) ρ

end type_system

end flow_analysis

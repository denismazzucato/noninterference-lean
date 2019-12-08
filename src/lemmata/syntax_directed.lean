import ..syntax_directed
import ..type_system
import .structural_subtyping

namespace flow_analysis

lemma syntax_directed_subtyping.expr {Λ : location} {γ : identifier} {e : base_expr}
    {ρ ρ' : phrase} :
  ((Λ, γ) ⊢ₛₑ e : ρ ∧ ρ ⊆ₛ ρ') → ((Λ, γ) ⊢ₛₑ e : ρ')
:= begin
  intro h,
  cases h with h_ctx h_sub,
  induction h_ctx,
  case syntax_directed.expr_typing.int : n _ {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    cases h_lemma4,
    have h2 := h_lemma4.right.left,
    rw h2,
    apply syntax_directed.expr_typing.int,
    cc,
  },
  case syntax_directed.expr_typing.var : Λ γ v x ih {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with a h_lemma4,
    cases h_lemma4 with b h_lemma4,
    cases h_lemma4,
    cc,
    repeat { cases h_lemma4, },
    rw eq.symm h_lemma4_right,
    apply syntax_directed.expr_typing.var ih,
    cc,
  },
  case syntax_directed.expr_typing.varloc : Λ γ v x ih {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with a h_lemma4,
    cases h_lemma4 with b h_lemma4,
    cases h_lemma4,
    cc,
    repeat { cases h_lemma4, },
    rw eq.symm h_lemma4_right,
    apply syntax_directed.expr_typing.varloc ih,
    cc,
  },
  case syntax_directed.expr_typing.binop : Λ γ a b z τ iha ihb ihsuba ihsubb {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    cases h_lemma4,
    have h := h_lemma4.right.left,
    simp[h] at *,
    apply syntax_directed.expr_typing.binop (ihsuba h_sub) (ihsubb h_sub),
    cc,
  },
  case syntax_directed.expr_typing.r_val : Λ γ e τ τ' he hxy ih {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    cases h_lemma4,
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    have h := le_trans hxy h3,
    apply syntax_directed.expr_typing.r_val he h,
    cc,
  },
end

/- Lemma 6.1
 - If (Λ, γ) ⊢ₛ p : ρ and ⊢ ρ ⊆ₛ ρ', then (Λ, γ) ⊢ₛ p : ρ'
 -/
lemma syntax_directed_subtyping {Λ : location} {γ : identifier} {p : program}
    {ρ ρ' : phrase} :
  ((Λ, γ) ⊢ₛ p : ρ ∧ ρ ⊆ₛ ρ') → ((Λ, γ) ⊢ₛ p : ρ')
:= begin
  intro h,
  cases h with h_ctx h_sub,
  induction h_ctx,
  case syntax_directed.program_typing.assign_var : Λ γ v e τ τ' ihv ihe ihyx {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    have h := le_trans h3 ihyx,
    apply syntax_directed.program_typing.assign_var ihv ihe h,
  },
  case syntax_directed.program_typing.assign_loc : Λ γ v e τ τ' ihv ihe ihyx {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    have h := le_trans h3 ihyx,
    apply syntax_directed.program_typing.assign_loc ihv ihe h,
  },
  case syntax_directed.program_typing.compose : Λ γ c c' τ hc hc' ihc ihc' {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    have h := h_lemma4.right.left,
    simp[h] at *,
    apply syntax_directed.program_typing.compose (ihc h_sub) (ihc' h_sub),
  },
  case syntax_directed.program_typing.branch
    : Λ γ e c c' τ τ' he hc hc' ihc ihc' ih {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    have h := le_trans h3 ihc,
    apply syntax_directed.program_typing.branch he hc hc' h,
  },
  case syntax_directed.program_typing.while : Λ γ e c τ τ' he hc hττ' ihc {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    have h := le_trans h3 hττ',
    apply syntax_directed.program_typing.while he hc h,
  },
  case syntax_directed.program_typing.letvar : Λ γ x e c τ τ' he hc ih {
    have h_lemma4 := structural_subtyping h_sub,
    cases h_lemma4 with x h_lemma4,
    cases h_lemma4 with y h_lemma4,
    repeat { cases h_lemma4, cc, },
    cases h_lemma4 with h1 h_lemma4,
    cases h_lemma4 with h2 h3,
    simp at h1,
    simp[h1, h2] at *,
    apply syntax_directed.program_typing.letvar he (ih h_sub),
  },
end

lemma program_typing_eq.expr {Λ : location} {γ : identifier} {e : base_expr}
  {ρ : phrase} : ((Λ, γ) ⊢ₑ e : ρ) ↔ ((Λ, γ) ⊢ₛₑ e : ρ)
:= begin
  apply iff.intro,
  { intro h,
    induction h,
    { exact syntax_directed.expr_typing.int, },
    { rename h_h h,
      exact syntax_directed.expr_typing.var h, },
    { rename h_h h,
      exact syntax_directed.expr_typing.varloc h, },
    { rename h_ih_a ha, rename h_ih_a_1 hb,
      exact syntax_directed.expr_typing.binop ha hb, },
    case type_system.expr_typing.r_val : Λ γ e τ he ihe {
      exact syntax_directed.expr_typing.r_val ihe (le_refl τ), },
    case type_system.expr_typing.subtype : Λ γ p ρ ρ' hp hρρ' ih {
      exact syntax_directed_subtyping.expr (and.intro ih hρρ'),
    },
  },
  { intro h,
    induction h,
    { exact type_system.expr_typing.int, },
    { rename h_h h,
      exact type_system.expr_typing.var h, },
    { rename h_h h,
      exact type_system.expr_typing.varloc h, },
    { rename h_ih_a ha, rename h_ih_a_1 hb,
      exact type_system.expr_typing.binop ha hb, },
    case syntax_directed.expr_typing.r_val : Λ γ e τ τ' he hττ' ih {
      have h := phrase.ss.base hττ',
      have h_rval := type_system.expr_typing.r_val ih,
      exact type_system.expr_typing.subtype h_rval h, },
  },
end

/- Theorem 6.2
 - (Λ, γ) ⊢ₜ p : ρ ↔ (Λ, γ) ⊢ₛ p : ρ -/
theorem program_typing_eq {Λ : location} {γ : identifier}
  {p : program} {ρ : phrase} : ((Λ, γ) ⊢ₜ p : ρ) ↔ ((Λ, γ) ⊢ₛ p : ρ)
:= begin
  apply iff.intro,
  { intro h,
    induction h,
    case type_system.program_typing.assign_var : Λ γ e e' τ he he' {
      have ha := program_typing_eq.expr.1 he,
      have hb := program_typing_eq.expr.1 he',
      exact syntax_directed.program_typing.assign_var ha hb (le_refl τ),
    },
    case type_system.program_typing.assign_loc : Λ γ e e' τ he he' {
      have ha := program_typing_eq.expr.1 he,
      have hb := program_typing_eq.expr.1 he',
      exact syntax_directed.program_typing.assign_loc ha hb (le_refl τ),
    },
    case type_system.program_typing.compose : Λ γ c c' τ hc hc' ihc ihc' {
      exact syntax_directed.program_typing.compose ihc ihc',
    },
    case type_system.program_typing.branch : Λ γ e c c' τ he hc hc' ihc ihc' {
      have ihe := program_typing_eq.expr.1 he,
      exact syntax_directed.program_typing.branch ihe ihc ihc' (le_refl τ),
    },
    case type_system.program_typing.while : Λ γ e c τ he hc ihc {
      have ihe := program_typing_eq.expr.1 he,
      exact syntax_directed.program_typing.while ihe ihc (le_refl τ),
    },
    case type_system.program_typing.letvar : Λ γ x e c τ τ' he hc ihc {
      have ihe := program_typing_eq.expr.1 he,
      exact syntax_directed.program_typing.letvar ihe ihc,
    },
    case type_system.program_typing.subtype : Λ γ p ρ ρ' hp hρρ' ihp {
      exact syntax_directed_subtyping (and.intro ihp hρρ'),
    },
  },
  { intro h,
    induction h,
    case syntax_directed.program_typing.assign_var : Λ γ e e' τ τ' he he' hττ' {
      have ha := program_typing_eq.expr.2 he,
      have hb := program_typing_eq.expr.2 he',
      have h_cmd := (phrase.ss.cmd (phrase.ss.base hττ')),
      have h_assign := type_system.program_typing.assign_var ha hb,
      exact type_system.program_typing.subtype h_assign h_cmd,
    },
    case syntax_directed.program_typing.assign_loc : Λ γ e e' τ τ' he he' hττ' {
      have ha := program_typing_eq.expr.2 he,
      have hb := program_typing_eq.expr.2 he',
      have h_cmd := (phrase.ss.cmd (phrase.ss.base hττ')),
      have h_assign := type_system.program_typing.assign_loc ha hb,
      exact type_system.program_typing.subtype h_assign h_cmd,
    },
    case syntax_directed.program_typing.compose : Λ γ c c' τ hc hc' ihc ihc' {
      exact type_system.program_typing.compose ihc ihc',
    },
    case syntax_directed.program_typing.branch
        : Λ γ e c c' τ τ' he hc hc' hτ'τ ihc ihc' {
      have ihe := program_typing_eq.expr.2 he,
      have h_sub := phrase.ss.cmd (phrase.ss.base hτ'τ),
      have h_ctx := type_system.program_typing.branch ihe ihc ihc',
      exact type_system.program_typing.subtype h_ctx h_sub,
    },
    case syntax_directed.program_typing.while : Λ γ e c τ τ' he hc hττ' ihc {
      have ihe := program_typing_eq.expr.2 he,
      have h_sub := phrase.ss.cmd (phrase.ss.base hττ'),
      have h_ctx := type_system.program_typing.while ihe ihc,
      exact type_system.program_typing.subtype h_ctx h_sub,
    },
    case syntax_directed.program_typing.letvar
        : Λ γ x e c τ τ' he hc ihc {
      have ihe := program_typing_eq.expr.2 he,
      exact type_system.program_typing.letvar ihe ihc,
    },
  },
end
end flow_analysis
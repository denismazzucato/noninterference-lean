import ..type_system
import .syntax_directed
import .phrase_partial_order
import ..phrase
import ..expr

namespace flow_analysis

/- Lemma 6.3 (Simple Security)
 - If (Λ, γ) ⊢ e : base τ, then for every x in e, γ(x) ≤ τ
 -/
open program_typing_eq
lemma simple_security {Λ : location} {γ : identifier}
    {e : base_expr} {τ : security_class} :
  (Λ, γ) ⊢ₑ e : phrase.base τ → ∀x, x ∈ base_expr.fl e → map.lookup x Λ ≤ τ
:= begin
  intros h x h_dom,
  have h_sd := program_typing_eq.expr.1 h, clear h,
  rename h_sd h,
  simp at h,

  induction e,
  repeat { simp[base_expr.fl] at h_dom, },
  repeat { cc, },
  rw h_dom,
  cases h, rename h_τ a, rename h_a he, rename h_a_1 haτ,
  cases he,
  case base_expr.bin_op : e b e' ihe ihe' {
    cases h, rename h_a he, rename h_a_1 he',
    cases h_dom,
    exact ihe h_dom he,
    exact ihe' h_dom he',
    rename h_a h_var,
    cases h_var,
  },
end

lemma confinement.type_to_syntax {Λ : location} {c : program}
    {τ : security_class} :
  (∃x, (Λ, x) ⊢ₜ c : phrase.cmd τ) → (∃x, (Λ, x) ⊢ₛ c : phrase.cmd τ)
:= begin
  intro ht,
  cases ht with x hx,
  apply exists.intro x,
  have h := program_typing_eq.1 hx,
  assumption,
end

lemma confinement.exists_variant {Λ : location}
      {c : program} {τ : security_class} :
    (∃x, (Λ, x) ⊢ₜ c : phrase.cmd τ)
  → ∀x, program.assigned_to_in x c → map.lookup x Λ ≥ τ
:= begin
  simp only[prod.fst, prod.snd],
  intros ht x hx,
  have h := confinement.type_to_syntax ht, simp at h, clear ht,
  apply ge_iff_le.2,

  induction hx,
  case program.assigned_to_in.update : v e {
    cases h with γ h,
    cases h, rename h_a ih,
    cases ih,
  },
  case program.assigned_to_in.seq_left : v c c' hv ih {
    cases h with γ h,
    cases h,
    apply ih,
    apply exists.intro γ,
    assumption,
  },
  case program.assigned_to_in.seq_right : v c c' hv ih {
    cases h with γ h,
    cases h,
    apply ih,
    apply exists.intro γ,
    assumption,
  },
  case program.assigned_to_in.branch_true : v e c c' hv ih {
    cases h with γ h,
    cases h, rename h_τ τ', rename h_a_1 hc, rename h_a_3 hττ',
    apply ih,
    apply exists.intro γ,
    exact syntax_directed_subtyping (
      and.intro hc (
        phrase.ss.cmd (
          phrase.ss.base hττ'))),
  },
  case program.assigned_to_in.branch_false : v e c c' hv ih {
    cases h with γ h,
    cases h, rename h_τ τ', rename h_a_2 hc', rename h_a_3 hττ',
    apply ih,
    apply exists.intro γ,
    exact syntax_directed_subtyping (
      and.intro hc' (
        phrase.ss.cmd (
          phrase.ss.base hττ'))),
  },
  case program.assigned_to_in.loop : v e c hv ih {
    cases h with γ h,
    cases h, rename h_τ τ', rename h_a_1 hc, rename h_a_2 hττ',
    apply ih,
    apply exists.intro γ,
    exact syntax_directed_subtyping (
      and.intro hc (
        phrase.ss.cmd (
          phrase.ss.base hττ'))),
  },
  case program.assigned_to_in.bind_var : v x e c h_neq hv ih {
    cases h with γ h,
    cases h, rename h_τ τ', rename h_a_1 hc,
    apply ih,
    apply exists.intro (γ[ₗ x : phrase.var τ']), -- main point
    assumption,
  },
end

/- Lemma 6.4 (Confinement)
 - If (Λ, γ) ⊢ c : cmd τ, then for every x assigned to in c, γ(x) ≥ τ
 -/
lemma confinement {Λ : location} {γ : identifier}
      {l : location} {c : program} {τ : security_class} :
    (Λ, γ) ⊢ₜ c : phrase.cmd τ
  → ∀x, program.assigned_to_in x c → map.lookup x Λ ≥ τ
:= begin
  intros h x hx,
  apply confinement.exists_variant,
  apply exists.intro γ,
  repeat { assumption },
end

/- Lemma 6.5 (Substitution)
 - If (Λ, γ) ⊢ l : τ var and (Λ, γ[x  : τ var]) ⊢ c : τ' cmd,
 - then (Λ, γ) ⊢ [l/x]c : τ' cmd.
 -/
lemma substitution {Λ : location} {γ : identifier}
    {c : program} {l x : vname} {τ τ': security_class} :
  ((Λ, γ) ⊢ₑ base_expr.loc l : phrase.var τ)
∧ ((Λ, γ[ᵢx  : phrase.var τ]) ⊢ₜ c : phrase.cmd τ')
→ ((Λ, γ) ⊢ₜ program.substitution l x c : phrase.cmd τ')
:= begin
  sorry,
end

/- Lemma 6.6
 - If μ ⊢ c ⟹ μ', then dom(μ) = dom(μ')
 -/
lemma dom_equality {μ μ': state} {c : program} :
  (c, μ) ⟹ μ' → map.dom μ = map.dom μ'
:= begin
  sorry,
end

/- Lemma 6.7
 - If μ ⊢ c ⟹ μ', l ∈ dom(μ), and l is not assigned to in c, then μ(l) = μ'(l)
 -/
lemma eq_if_not_used {μ μ': state} {c : program} {l : vname} :
    (c, μ) ⟹ μ' ∧ l ∈ map.dom μ ∧ program.not_assigned_to_in l c
  → map.lookup l μ = map.lookup l μ'
:= begin
  sorry,
end

/- Theorem 6.8 (Type Soundness), Suppose
 - λ ⊢ c : ρ,
 - μ ⊢ c ⟹ μ',
 - ν ⊢ c ⟹ ν',
 - dom(μ) = dom(ν) = dom(λ), and
 - ν(l) = μ(l) for all l such that λ(l) ≤ τ
 - Then ν'(l) = μ'(l) for all l such that λ(l) ≤ τ
 -/

end flow_analysis
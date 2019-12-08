/- structural subtyping -/
import ..phrase

namespace flow_analysis

open phrase
lemma structural_subtyping.base {a b : security_class} (h : a ≤ b) :
  ∃τ τ', base a = base τ ∧ base b = base τ' ∧ τ ≤ τ'
       ∨ base a = var τ ∧ base a = base b
       ∨ base a = cmd τ ∧ base b = cmd τ' ∧ τ' ≤ τ
:= begin
  apply exists.intro a,
  apply exists.intro b,
  cc,
end

lemma structural_subtyping.reflex {ρ : phrase} :
  ∃τ τ', ρ = base τ ∧ ρ = base τ' ∧ τ ≤ τ'
       ∨ ρ = var τ ∧ ρ = ρ
       ∨ ρ = cmd τ ∧ ρ = cmd τ' ∧ τ' ≤ τ
:= begin
  cases ρ,
  repeat {apply exists.intro ρ},
  repeat {simp},
end

lemma structural_subtyping.trans.base {a : security_class} {b c : phrase}
    (ihbc : ∃τ τ', b = base τ ∧ c = base τ' ∧ τ ≤ τ'
                 ∨ b = var τ ∧ b = c
                 ∨ b = cmd τ ∧ c = cmd τ' ∧ τ' ≤ τ)
    (ihab : ∃τ τ', cmd a = base τ ∧ b = base τ' ∧ τ ≤ τ'
                 ∨ cmd a = var τ ∧ cmd a = b
                 ∨ cmd a = cmd τ ∧ b = cmd τ' ∧ τ' ≤ τ) :
  ∃τ τ', cmd a = base τ ∧ c = base τ' ∧ τ ≤ τ'
       ∨ cmd a = var τ ∧ cmd a = c
       ∨ cmd a = cmd τ ∧ c = cmd τ' ∧ τ' ≤ τ
:= begin
  cases ihab with x ihab,
  cases ihab with y ihab,
  repeat { cases ihab, },
  repeat { cc, },
  cases ihab_right with ihby ihyx,
  cases ihbc with y' ihbc,
  cases ihbc with z ihbc,
  repeat { cases ihbc with _ ihbc, },
  repeat { cc, },
  simp[ihby] at *,
  apply exists.intro x,
  apply exists.intro y',
  cc,
  apply exists.intro x,
  apply exists.intro security_class.low,
  repeat { apply or.inr, },
  apply and.intro ihab_left,
  apply and.intro ihbc_left_1,
  cases x,
  apply security_class.le.lower,
  apply security_class.le.refl,
end

lemma structural_subtyping.trans {a b c : phrase}
    (ihab : ∃τ τ', a = base τ ∧ b = base τ' ∧ τ ≤ τ'
                 ∨ a = var τ ∧ a = b
                 ∨ a = cmd τ ∧ b = cmd τ' ∧ τ' ≤ τ)
    (ihbc : ∃τ τ', b = base τ ∧ c = base τ' ∧ τ ≤ τ'
                 ∨ b = var τ ∧ b = c
                 ∨ b = cmd τ ∧ c = cmd τ' ∧ τ' ≤ τ):
  ∃ (τ τ' : security_class),
    a = base τ ∧ c = base τ' ∧ τ ≤ τ' ∨
      a = var τ ∧ a = c ∨ a = cmd τ ∧ c = cmd τ' ∧ τ' ≤ τ
:= begin
  cases a,
  case phrase.base : {
    cases ihab with x ihab,
    cases ihab with y ihab,
    repeat { cases ihab, },
    cases ihab_right,
    cases ihbc with y' ihbc,
    cases ihbc with z ihbc,
    repeat { cases ihbc, },
    cases ihbc_right,
    apply exists.intro x,
    apply exists.intro z,
    apply or.inl,
    apply and.intro ihab_left,
    apply and.intro ihbc_right_left,
    simp[ihab_right_left] at ihbc_left,
    simp[ihbc_left] at *,
    apply le_trans ihab_right_right ihbc_right_right,
    repeat { cc, },
  },
  case phrase.var : {
    repeat { cases ihab with _ ihab, cases ihbc with _ ihbc, },
    repeat { apply exists.intro a },
    repeat { cc, },
  },
  case phrase.cmd : {
    cases ihab with x ihab,
    cases ihab with y ihab,
    repeat { cases ihab, },
    repeat { cc, },
    cases ihab_right with ihby ihyx,
    cases ihbc with y' ihbc,
    cases ihbc with z ihbc,
    repeat { cases ihbc with _ ihbc, },
    repeat { cc, },
    simp[ihby] at *,
    apply exists.intro x,
    apply exists.intro y',
    cc,
    apply exists.intro x,
    apply exists.intro security_class.low,
    repeat { apply or.inr, },
    apply and.intro ihab_left,
    apply and.intro ihbc_left_1,
    cases x,
    apply security_class.le.lower,
    apply security_class.le.refl,
  },
end

lemma structural_subtyping.cmd {a b : security_class}
    (ih : ∃τ τ', base a = base τ ∧ base b = base τ' ∧ τ ≤ τ'
               ∨ base a = var τ ∧ base a = base b
               ∨ base a = cmd τ ∧ base b = cmd τ' ∧ τ' ≤ τ):
  ∃ (τ τ' : security_class),
    cmd b = base τ ∧ cmd a = base τ' ∧ τ ≤ τ' ∨
      cmd b = var τ ∧ cmd b = cmd a ∨ cmd b = cmd τ ∧ cmd a = cmd τ' ∧ τ' ≤ τ
:= begin
  cases ih with y ih,
  cases ih with x ih,
  apply exists.intro x,
  apply exists.intro y,
  cc,
end

/- Lemma 4.1 (Structural Subtyping)
 - If ⊢ ρ ⊆ ρ', then either
 - (a) ρ is of the form base τ, ρ' is of the form base τ' and τ ≤ τ'
 - (b) ρ is of the form var τ and ρ' = ρ, or
 - (c) ρ is of the form cmd τ, ρ' is of the form cmd τ' and τ' ≤ τ
-/
lemma structural_subtyping {ρ ρ' : phrase} (h : ρ ⊆ₛ ρ') :
  ∃τ τ', (ρ = base τ ∧ ρ' = base τ' ∧ τ ≤ τ')
       ∨ (ρ = var τ ∧ ρ = ρ')
       ∨ (ρ = cmd τ ∧ ρ' = cmd τ' ∧ τ' ≤ τ)
:= begin
  induction h,
  case phrase.ss.base : a b h {
    apply structural_subtyping.base h,
  },
  case phrase.ss.reflex : ρ {
    apply structural_subtyping.reflex,
  },
  case phrase.ss.trans : a b c _ _ ihab ihbc {
    apply structural_subtyping.trans ihab ihbc,
  },
  case phrase.ss.cmd : a b hab ih {
    apply structural_subtyping.cmd ih,
  },
end

end flow_analysis
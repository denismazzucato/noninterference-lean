import ..phrase
import .structural_subtyping
import ..security_class

namespace flow_analysis

open phrase

/- Lemma 4.2 ⊆ is a partial order -/
instance phrase_partial_order : partial_order phrase :=
{ le := phrase.ss,
  le_refl := assume a, ss.reflex,
  le_trans := assume a b c hab hbc, ss.trans hab hbc,
  le_antisymm := begin
    intros a b hab hba,
    have h := structural_subtyping hab,
    cases h with x h,
    cases h with y hxy,
    have h := structural_subtyping hba,
    cases h with j h,
    cases h with k hjk,
    cases hxy,
    cases hjk,
    { cases hxy,
      cases hjk,
      cases hxy_right,
      cases hjk_right,
      simp *,
      rw hjk_left at *,
      simp at hxy_right_left,
      rw eq.symm hxy_right_left at *,
      rw hxy_left at *,
      simp at hjk_right_left,
      rw hjk_right_left at *,
      exact (le_antisymm hxy_right_right hjk_right_right), },
    { cases hxy,
      cases hjk,
      repeat { cc, }, },
    { repeat { cases hjk, cases hxy, cc, },
      cases hxy,
      cases hxy_right,
      cases hjk_right,
      have hjy := eq.trans (eq.symm hjk_left) hxy_right_left,
      have hxk := eq.trans (eq.symm hxy_left) hjk_right_left,
      simp at *,
      simp [hjy, hxk] at *,
      have h := le_antisymm hxy_right_right hjk_right_right,
      cc, },
  end
}

end flow_analysis

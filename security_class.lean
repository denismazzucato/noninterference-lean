/- Typing rules for secure information flow -/

import .base

namespace flow_analysis

/- for the security class I decide to use only High or Low level, as defined
 - in the paper -/
inductive security_class : Type
| high : security_class
| low : security_class
open security_class

namespace security_class

/- lower-equal operator (and relative instantiation)
 - for security_class partial order -/
inductive le : security_class → security_class → Prop
| refl {a} : le a a
| lower    : le low high

instance : partial_order security_class :=
{ le := security_class.le,
  le_refl := assume a, le.refl,
  le_trans :=
    begin
      intros _ _ _ hab hbc,
      cases hab,
      assumption,
      cases hbc,
      assumption,
    end,
  le_antisymm :=
    begin
      intros a b hab hba,
      cases a,
      case high : {
        cases hab,
        refl,
      },
      case low : {
        cases hba,
        refl,
      },
    end,
}

instance : inhabited security_class := ⟨low⟩

end security_class

end flow_analysis



/- phrase -/

import .security_class

namespace flow_analysis

inductive phrase : Type
| base : security_class → phrase
| var  : security_class → phrase
| cmd  : security_class → phrase
open phrase

namespace phrase

/- subset inductive binary proposition for phrases -/
inductive ss : phrase → phrase → Prop
| base {τ τ' : security_class} :
    τ ≤ τ'
  → ss (base τ) (base τ')
| reflex {ρ} : ss ρ ρ
| trans {ρ ρ' ρ''} :
    ss ρ ρ'
  → ss ρ' ρ''
  → ss ρ ρ''
| cmd {τ τ'} :
    ss (base τ) (base τ')
  → ss (cmd τ') (cmd τ)

infix ` ⊆ₛ `:90 := phrase.ss

/- I need for key without values in context -/
instance : inhabited phrase :=
  ⟨base (inhabited.default security_class)⟩

end phrase

end flow_analysis
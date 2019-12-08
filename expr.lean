import .base
import .context
import data.finset

namespace flow_analysis

-- binary operator
inductive bop : Type
| less : bop
| eq   : bop
| sub  : bop
| add  : bop

/- base expression
 -
 - note that location and variables are different, location are more near to
 - memory location, they are mostly used to simulate input and output.
 - the key difference is that a closed program may have some free location
 - inside it while all the variables must be binded by a let var definition
 -/
inductive base_expr : Type
| val : valt → base_expr
| var : vname → base_expr -- for variables
| loc : vname → base_expr -- for locations
| bin_op : base_expr → bop → base_expr → base_expr
notation e ` ⟪ ` b ` ⟫ ` e' := base_expr.bin_op e b e'

namespace base_expr

open bop valt
-- cases evaluation for binary arithmetic expressions
def eval_binop : bop → valt → valt → valt
| eq   (natural e₁) (natural e₂) := boolean $ e₁ = e₂
| eq   (boolean e₁) (boolean e₂) := boolean $ e₁ = e₂
| less (natural e₁) (natural e₂) := boolean $ e₁ < e₂
| sub  (natural e₁) (natural e₂) := natural $ e₁ - e₂
| add  (natural e₁) (natural e₂) := natural $ e₁ + e₂
| _    _            _            := false
/- in the last case I don't check that expression should be well typed
 - because my goal is to obtain well formed program only when there is no
 - variables interference -/

/- free variables -/
def fv : base_expr → finset vname
| (val _) := ∅
| (var v) := {v}
| (loc _) := ∅
| (bin_op e₁ bop e₂) := fv e₁ ∪ fv e₂

/- hold when a given variable is free inside the expression -/
inductive is_in_fv : vname × base_expr → Prop
| var {v}                    : is_in_fv (v, var v)
| bin_op_left  {e₁ e₂ bop v} : is_in_fv (v, e₁) → is_in_fv (v, e₁ ⟪bop⟫ e₂)
| bin_op_right {e₁ e₂ bop v} : is_in_fv (v, e₂) → is_in_fv (v, e₁ ⟪bop⟫ e₂)

/- hold when a given variable isn't inside the expression (or is binded) -/
inductive isnt_in_fv : vname × base_expr → Prop
| val {x n} : isnt_in_fv (x, val n)
| var {v x}                    :
  x ≠ v → isnt_in_fv (x, var v)
| loc {l x} : isnt_in_fv (x, loc l)
| bin_op  {e₁ e₂ bop x} :
  isnt_in_fv (x, e₁) → isnt_in_fv (x, e₂) → isnt_in_fv (x, e₁ ⟪bop⟫ e₂)

/- free locations -/
def fl : base_expr → finset vname
| (val _) := ∅
| (var _) := ∅
| (loc l) := {l}
| (bin_op e₁ bop e₂) := fl e₁ ∪ fl e₂

/- hold when a given location is free inside the expression -/
inductive is_in_fl : vname × base_expr → Prop
| loc {v}                    : is_in_fl (v, loc v)
| bin_op_left  {e₁ e₂ bop v} : is_in_fl (v, e₁) → is_in_fl (v, e₁ ⟪bop⟫ e₂)
| bin_op_right {e₁ e₂ bop v} : is_in_fl (v, e₂) → is_in_fl (v, e₁ ⟪bop⟫ e₂)

/- expression evaluation rule, big-step semantic -/
inductive expr_sem : base_expr × state → valt → Prop
| base {v s} :
  expr_sem (val v, s) v
| contents {l s} (h : l ∈ map.dom s) :
  expr_sem (loc l, s) (map.lookup l s)
| binop {e e' n n' bop s} :
    expr_sem (e, s) n
  → expr_sem (e', s) n'
  → expr_sem (e ⟪bop⟫ e', s) (eval_binop bop n n')
infixr `⇒ₑ`:110 := expr_sem

/- [l/x]e operator (paper page 10, over expressions) -/
def substitution (l x : vname) : base_expr → base_expr
| (val n) := val n
| (var v) := if v = x then loc v else var v
| (loc v) := loc v
| (bin_op e₁ bop e₂) := bin_op (substitution e₁) bop (substitution e₂)

end base_expr

end flow_analysis
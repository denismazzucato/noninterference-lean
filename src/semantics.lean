/- Language Semantics -/

import .lovelib
import .expr
import .map
import data.finset

namespace flow_analysis

/- Expressions and Commands -/
inductive program : Type
| assignv : vname → base_expr → program -- for variables
| assignl : vname → base_expr → program -- for locations
| seq     : program → program → program
| ite     : base_expr → program → program → program
| while   : base_expr → program → program
| lvar    : vname → base_expr → program → program
-- lvar can only build new vars
infixr ` ;; `:90 := program.seq

namespace program
open program
/- [l/x]c operator (paper page 10) -/
def substitution (l x : vname) : program → program
| (assignv v e) := if v = x
  then assignv l (base_expr.substitution l x e)
  else assignv v (base_expr.substitution l x e)
| (assignl v e) := assignl v (base_expr.substitution l x e)
| (seq c c') := seq (substitution c) (substitution c')
| (ite e c c') := ite
  (base_expr.substitution l x e)
  (substitution c)
  (substitution c')
| (while e c) := while (base_expr.substitution l x e) (substitution c)
| (lvar v e c) := if v = x
  then lvar v (base_expr.substitution l x e) c -- nearest binder win
  else lvar v (base_expr.substitution l x e) (substitution c)

/- free variables -/
def fv : program → finset vname
| (assignv v e) := {v} ∪ base_expr.fv e
| (assignl v e) := base_expr.fv e
| (seq c c') := fv c ∪ fv c'
| (ite e c c') := base_expr.fv e ∪ fv c ∪ fv c'
| (while e c) := base_expr.fv e ∪ fv c
| (lvar v e c) := base_expr.fv e ∪ (fv c \ {v})

/- hold when a given variable isn't inside the program (or is binded) -/
inductive isnt_in_fv : vname × program → Prop
| assignv {x v e} :
    x ≠ v
  → base_expr.isnt_in_fv (x, e)
  → isnt_in_fv (x, assignv v e)
| assignl {x v e} :
    base_expr.isnt_in_fv (x, e)
  → isnt_in_fv (x, assignl v e)
| seq {x c c'} :
    isnt_in_fv (x, c)
  → isnt_in_fv (x, c')
  → isnt_in_fv (x, c ;; c')
| ite {x e c c'} :
    base_expr.isnt_in_fv (x, e)
  → isnt_in_fv (x, c)
  → isnt_in_fv (x, c')
  → isnt_in_fv (x, ite e c c')
| while {x e c} :
    base_expr.isnt_in_fv (x, e)
  → isnt_in_fv (x, c)
  → isnt_in_fv (x, while e c)
| lvar_neq {x v e c} :
    base_expr.isnt_in_fv (x, e)
  → x ≠ v
  → isnt_in_fv (x, c)
  → isnt_in_fv (x, lvar v e c)
| lvar_eq {x v e c} :
    base_expr.isnt_in_fv (x, e)
  → x = v
  → isnt_in_fv (x, lvar v e c)

/- hold when a given variable is free inside the program -/
inductive is_in_fv : vname × program → Prop
| assignv_left {x v e} :
    x = v
  → is_in_fv (x, assignv v e)
| assignv_right {x v e} :
    base_expr.is_in_fv (x, e)
  → is_in_fv (x, assignv v e)
| seq_left {x c c'} :
    is_in_fv (x, c)
  → is_in_fv (x, c ;; c')
| seq_right {x c c'} :
    is_in_fv (x, c')
  → is_in_fv (x, c ;; c')
| ite_left {x e c c'} :
    is_in_fv (x, c)
  → is_in_fv (x, ite e c c')
| ite_right {x e c c'} :
    is_in_fv (x, c')
  → is_in_fv (x, ite e c c')
| ite_cond {x e c c'} :
    base_expr.is_in_fv (x, e)
  → is_in_fv (x, ite e c c')
| while {x e c} :
    is_in_fv (x, c)
  → is_in_fv (x, while e c)
| while_cond {x e c} :
    base_expr.is_in_fv (x, e)
  → is_in_fv (x, while e c)
| lvar_cond {x v e c} :
    base_expr.is_in_fv (x, e)
  → is_in_fv (x, lvar v e c)
| lvar {x v e c} :
    x ≠ v
  → is_in_fv (x, c)
  → is_in_fv (x, lvar v e c)

/- free location -/
def fl : program → finset vname
| (assignv v e) := base_expr.fl e
| (assignl v e) := {v} ∪ base_expr.fl e
| (seq c c') := fl c ∪ fl c'
| (ite e c c') := base_expr.fl e ∪ fl c ∪ fl c'
| (while e c) := base_expr.fl e ∪ fl c
| (lvar v e c) := base_expr.fl e ∪ fl c

/- big step semantic evaluation rule -/
inductive sem : program × state → state → Prop
| update {l e n μ} (h : l ∈ map.dom μ) : -- no rule for variables
    (e, μ) ⇒ₑ n
  → sem (assignl l e, μ) (μ[ₛl := n])
| seq {c c' μ μ' μ''} :
    sem (c, μ) μ'
  → sem (c', μ') μ''
  → sem (c ;; c', μ) μ''
| branch_true {e c c' μ μ'} :
    (e, μ) ⇒ₑ true
  → sem (c, μ) μ'
  → sem (ite e c c', μ) μ'
| branch_false {e c c' μ μ'} :
    (e, μ) ⇒ₑ false
  → sem (c', μ) μ'
  → sem (ite e c c', μ) μ'
| loop_false {e c μ} :
    (e, μ) ⇒ₑ false
  → sem (while e c, μ) μ
| loop_true {e c μ μ' μ''} :
    (e, μ) ⇒ₑ true
  → sem (c, μ) μ'
  → sem (while e c, μ') μ''
  → sem (while e c, μ) μ''
| bind_var {x e c n l μ μ'}  :
    (e, μ) ⇒ₑ n
  → l ∉ₛ μ -- this create a new fresh variable
  → sem (substitution l x c, μ[ₛl := n]) μ'
  → sem (lvar x e c, μ) (l −ₛ μ')

infixr ` ⟹ ` : 110 := sem
infixr ` ⟹* ` : 100 := LoVe.refl_trans sem

/- hold when a given location is assigned to inside the program -/
inductive assigned_to_in : vname → program → Prop
| update {v e} : -- no rule for variables
  assigned_to_in v (assignl v e)
| seq_left {v c c'} :
    assigned_to_in v c
  → assigned_to_in v (c ;; c')
| seq_right {v c c'} :
    assigned_to_in v c'
  → assigned_to_in v (c ;; c')
| branch_true {v e c c'} :
    assigned_to_in v c
  → assigned_to_in v (ite e c c')
| branch_false {v e c c'} :
    assigned_to_in v c'
  → assigned_to_in v (ite e c c')
| loop {v e c} :
    assigned_to_in v c
  → assigned_to_in v (while e c)
| bind_var {v x e c}  :
    v ≠ x -- otherwise would be binded incorrectly
  → assigned_to_in v c
  → assigned_to_in v (lvar x e c)

def not_assigned_to_in (v : vname) (p : program) : Prop :=
¬program.assigned_to_in v p

end program

end flow_analysis

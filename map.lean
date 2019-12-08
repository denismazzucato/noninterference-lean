import .base
import data.list.alist

/- Map -/
abbreviation map (β: Type) := alist (λ_ : string, β)

namespace map

def dom {β : Type} : map β → list string := alist.keys

def add {β : Type} : string → β → map β → map β :=
alist.insert

/- this is the explanation why I need that phrase is a instance of inhabited,
 - because I prefer a simple value instead of an optional value -/
def lookup {β : Type} [inhabited β] (k : string) (s : map β)
  : β :=
match alist.lookup k s with
| (some v) := v
| none     := inhabited.default β
end

def erase {β : Type} : string → map β → map β := alist.erase

/- these functions build and return a new fresh variable,
 - this feature is required at bind var rule inside the evaluation function -/
def basic_filter {α : Type} (p : α → bool) : list α → list α
| [] := []
| (x :: xs) := if p x then [x] ++ basic_filter xs else basic_filter xs

def is_computation_var : string → bool
| ⟨'_'::xs⟩ := tt
| _         := ff

def length_computation_vars (keys : list string) : ℕ :=
list.length $ basic_filter is_computation_var keys

def fresh_key {β : Type} (s : map β) : string :=
"_x" ++ (to_string $ length_computation_vars (alist.keys s))

/- this hold when the given variable name is a fresh name for the map -/
inductive fresh_var {β : Type} : string → map β → Prop
| fresh {l s} : fresh_key s = l → fresh_var l s

/- map string representation -/
def to_string_concat (β : Type) [has_to_string β]
  (acc : string) (k : string) (v : β) : string :=
acc ++ "(" ++ (to_string k) ++ ": " ++ (to_string v) ++ ")"

def repr {β : Type} [has_to_string β] (s: map β) : string :=
alist.foldl (to_string_concat β) "" s

instance {β : Type} [has_to_string β] : has_repr (map β) := ⟨repr⟩
instance {β : Type} [has_to_string β] : has_to_string (map β) := ⟨repr⟩

end map
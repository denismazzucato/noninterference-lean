namespace flow_analysis

/- Variables and Values
 -
 - this module cover the basic type of value
 - literal in the program syntax range over valt
 -/
abbreviation vname := string

inductive valt : Type
| boolean : bool → valt
| natural : ℕ → valt

/- short-hand for boolean values -/
def true : valt := valt.boolean tt
def false : valt := valt.boolean ff

namespace valt

/- valt string rrepresentation -/
def valt.repr : valt → string
| (boolean b) := "(b " ++ (to_string b) ++ ")"
| (natural n) := "(n " ++ (to_string n) ++ ")"

instance : has_repr valt := ⟨valt.repr⟩
instance : has_to_string valt := ⟨valt.repr⟩
instance : inhabited valt := ⟨false⟩

end valt

end flow_analysis
import .map
import .phrase

namespace flow_analysis

/- State
 - this module is used in the big-step evaluation rule
 -/
abbreviation state := map valt

notation s `[ₛ` name ` := ` val `]` := map.add name val s
infix ` ∉ₛ `:90 := map.fresh_var
infix ` −ₛ `:90 := map.erase

/- Identifier
 - this module is used to store phrases type
 -/
abbreviation identifier := map phrase

notation s `[ᵢ` name ` : ` val `]` := map.add name val s
infix ` ∉ᵢ `:90 := map.fresh_var
infix ` −ᵢ `:90 := map.erase

/- Location
 - this module is used to store location type,
 - the key difference between location map and identifier map is that for
 - location I don't need to specify the phrase (base, var or cmd) before its
 - security class as specified in the paper
 -/
abbreviation location := map security_class

notation s `[ₗ` name ` : ` val `]` := map.add name val s
infix ` ∉ₗ `:90 := map.fresh_var
infix ` −ₗ `:90 := map.erase

end flow_analysis

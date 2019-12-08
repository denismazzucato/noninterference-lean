# A SoundType System for Secure Flow Analysis

For this project, I try to code inside Lean the paper by Volpano, Smith and
Irvine [A SoundType System for Secure Flow Analysis](http://users.cis.fiu.edu/~smithg/papers/jcs96.pdf).
This work doesn't totally complete the paper, lemmata 6.5, 6.6, 6.7 and theorem
6.8 are left out. I'm sorry for this but the project already count more than
1000 loc so I decided to stop here.

## Modules overview
- **base**, simple module that stores the basic literals value
- **map**, definition of map based on alist, this object would be
  instantiate to be one of the context in both the typing rules and evaluation
  function
- **context**, this module build the instance of the state, identifier and
  location map
- **security_class**, I defined the security class inductive type and the
  relative ≤ operator, the only values allowed for security classes are High and
  Low
- **phrase**, this is the wrapper of the security_class, with this module I can
  type every expression or program inside the framework
- **semantics**, this module stores the program syntax definition and (big-step)
  evaluation rule
- **type_system**, regards the paper, this is the first typing systems showed in
  the paper, these rules are combined with the subtype and the fact that phrase
  is partially ordered
- **syntax_directed**, this typing systems differs from the previous one by the
  subtyping rule, which is included inside (almost) each rule
- **lemmata/phrase_partial_order**, proof that phrase is partially ordered, by
  an instance of partial_order over phrase
- **lemmata/structural_subtyping**, properties about the ≤ operation over
  phrases (lemma 4.1)
- **lemmata/syntax_directed**, property about subtype (lemma 6.1) and the proof
  that the two type systems defined are equivalent (lemma 6.2)
- **lemmata/type_soundness**, simple security (lemma 6.3) and confinement
  (lemma 6.4) properties
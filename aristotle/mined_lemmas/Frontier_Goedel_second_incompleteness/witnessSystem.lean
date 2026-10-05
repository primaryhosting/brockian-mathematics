/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The syntactic setting

We work with the standard abstract (Hilbert–Bernays–Löb) formulation of Gödel's second
incompleteness theorem.

`Fml` is a language of sentences built from atoms, falsum and implication, together with a
unary operator `box`.  For a recursively axiomatized theory `T` extending `PA`, one reads
`Fml` as (a fragment of) the sentences of arithmetic and `box p` as the arithmetized
provability sentence `Prov_T(⌜p⌝)`; the fact that `T` is recursively axiomatized and extends
`PA` is exactly what supplies the three Löb derivability conditions `D1`, `D2`, `D3` recorded
in `ProvabilitySystem` below, and the diagonal lemma supplies the Gödel fixed point.
-/

/-- Sentences: propositional atoms, falsum, implication, and a provability operator `box`. -/
inductive Fml where
  | atom : Nat → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

namespace Fml

/-- Negation, `¬ p := p → ⊥`. -/

def witnessSystem : ProvabilitySystem where
  Thm p := eval (fun _ => true) p = true
  taut p hp := hp _
  mp {a b} hab ha := by
    simp only [eval, ha] at hab
    simpa using hab
  D1 {a} _ := rfl
  D2 a b := by simp [eval]
  D3 a := by simp [eval]


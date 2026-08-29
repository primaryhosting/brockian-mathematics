/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

def colorings (X : Finset α) (m : ℕ) : Finset (∀ a ∈ X, Fin m) :=
  X.pi (fun _ => (Finset.univ : Finset (Fin m)))

/-- **The main technical estimate** of Alweiss–Lovett–Wu–Zhang, Rao and
Bell–Chueluecha–Warnke (Theorem 3 of Bell–Chueluecha–Warnke, with `δ = 1/m` and `ε = 1/2`):
if a family `S` of `k`-element subsets of `X` is `r`-spread with at least `r ^ k` members, where
`r = B * m * log (k+1)`, then for each colour `i`, more than half of all `m`-colourings of `X`
have their `i`-th colour class containing a member of `S`.

This is the one deep ingredient of the improved sunflower bound that is assumed here; everything
else in this file is proved. -/

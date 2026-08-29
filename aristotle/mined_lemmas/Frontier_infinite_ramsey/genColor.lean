import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

open Classical in
/-- The `U`-generic colour at `n`: the colour `b` such that `{m | c n m = b} ∈ U`. -/

noncomputable def genColor (U : Ultrafilter ℕ) (c : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  if {m | c n m = true} ∈ U then true else false


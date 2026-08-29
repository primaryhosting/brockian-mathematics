/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/

lemma ip_add {n : ℕ} (y x s : Vec n) : ip y (x + s) = ip y x + ip y s := by
  simp [ip, mul_add, Finset.sum_add_distrib]


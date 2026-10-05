/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/

lemma G8_no_indep4 : ∀ t : Finset (Fin 8), ¬ G8.IsNIndepSet 4 t := by decide

/-- Lower bound: `R(3,4) > 8`, hence any `n` with the Ramsey property satisfies `9 ≤ n`. -/

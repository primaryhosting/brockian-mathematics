/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
recorded with integer entries. -/

theorem ks_double_count (g : Fin 18 → ℕ) :
    ∑ j : Fin 9, ∑ k : Fin 4, g (ksBasis j k) = 2 * ∑ i : Fin 18, g i := by
  simp [ksBasis, Fin.sum_univ_succ]
  ring

/-- **Kochen–Specker theorem, 18-vector version.**
There is no `{0,1}`-coloring of the vectors of `ℝ⁴` assigning the value `1` to exactly one
vector of each of the nine orthogonal bases of the Cabello–Estebaranz–García-Alcaine set.
(The hypothesis that `f` takes only the values `0` and `1` is part of the requested
statement; it is in fact implied by the second condition.) -/

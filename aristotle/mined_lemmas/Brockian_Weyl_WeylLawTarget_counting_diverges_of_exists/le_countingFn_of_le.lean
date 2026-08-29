import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectral sequence `mu : ℕ → ℝ`:
`countingFn mu lam` is the number of indices `n` with `mu n ≤ lam`. -/

theorem le_countingFn_of_le
    (mu : ℕ → ℝ) (hfin : ∀ lam : ℝ, {n : ℕ | mu n ≤ lam}.Finite)
    (M : ℕ) {lam : ℝ} (hlam : ∀ i ∈ Finset.range M, mu i ≤ lam) :
    M ≤ countingFn mu lam := by
  have hsub : (↑(Finset.range M) : Set ℕ) ⊆ {n : ℕ | mu n ≤ lam} := by
    intro i hi
    exact hlam i (by simpa using hi)
  have h := Set.ncard_le_ncard hsub (hfin lam)
  simpa [countingFn, Set.ncard_coe_finset] using h

/-- Discreteness of the spectrum follows from the existence, for each threshold
`lam`, of a cutoff index beyond which all eigenvalues exceed `lam`. -/

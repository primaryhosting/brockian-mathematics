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

theorem sublevel_finite_of_exists_cutoff
    (mu : ℕ → ℝ) (hcut : ∀ lam : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lam < mu n)
    (lam : ℝ) : {n : ℕ | mu n ≤ lam}.Finite := by
  obtain ⟨N, hN⟩ := hcut lam
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  by_contra hlt
  exact absurd hn (not_le.2 (hN n (le_of_not_gt hlt)))

/-- **Divergence of the eigenvalue counting function.**
If for every threshold `lam` there exists a cutoff index `N` beyond which every
eigenvalue of the spectral sequence `mu : ℕ → ℝ` exceeds `lam` (so that only
finitely many eigenvalues lie below any given threshold), then the counting
function `lam ↦ #{n | mu n ≤ lam}` diverges to infinity as `lam → ∞`. -/

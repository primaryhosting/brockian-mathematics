import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem area_law_1d_geometric (d : ℕ) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, ∀ (n m : ℕ) (psi : Matrix (Fin m → Fin d) (Fin (n - m) → Fin d) ℂ),
      (psi * psiᴴ).trace = 1 →
      (∀ k : ℕ, ∃ s : Finset (Fin m → Fin d), s.card ≤ k ∧
          ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C * q ^ k) →
      entanglementEntropy psi ≤ K := by
  refine ⟨(C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)), ?_⟩
  intro n m psi hnorm hdecay
  exact entropy_le_of_schmidt_decay psi hnorm hq0 hq1 hdecay

end Phys

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


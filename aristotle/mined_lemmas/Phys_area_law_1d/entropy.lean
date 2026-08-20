/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to precede any module docstring, so the header above is a plain
comment and is repeated verbatim as the module docstring below.)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real Finset

/-- A **Schmidt spectrum** across a cut of a one–dimensional chain: the (squared) Schmidt
coefficients `p i` of a pure state with respect to a bipartition `A ∣ B`.  Equivalently, the
eigenvalue distribution of the reduced density matrix `ρ_A`.  Only finitely many coefficients
are non-zero; `support` is a finite set carrying them, and its cardinality bounds the
Schmidt rank (= the bond dimension needed to cut the state at this position). -/
structure SchmidtSpectrum (ι : Type*) where
  /-- The squared Schmidt coefficients, i.e. the eigenvalues of the reduced density matrix. -/
  p : ι → ℝ
  /-- A finite set containing all indices with non-zero weight. -/
  support : Finset ι
  /-- Eigenvalues of a density matrix are non-negative. -/
  nonneg : ∀ i, 0 ≤ p i
  /-- Outside the support the weights vanish. -/
  vanish : ∀ i ∉ support, p i = 0
  /-- The reduced density matrix has unit trace. -/
  total : ∑ i ∈ support, p i = 1

namespace SchmidtSpectrum

variable {ι : Type*} (σ : SchmidtSpectrum ι)

/-- The **entanglement entropy** (von Neumann entropy of the reduced density matrix)
`S(ρ_A) = -∑ᵢ pᵢ log pᵢ`. -/

noncomputable def entropy : ℝ := ∑ i ∈ σ.support, Real.negMulLog (σ.p i)

/-- The Schmidt rank across the cut, bounded by the cardinality of the support. -/

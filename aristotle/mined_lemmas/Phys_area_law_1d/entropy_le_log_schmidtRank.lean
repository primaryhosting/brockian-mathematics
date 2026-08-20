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

theorem entropy_le_log_schmidtRank : σ.entropy ≤ Real.log σ.schmidtRank := by
  set N : ℝ := (σ.schmidtRank : ℝ) with hNdef
  have hN : 0 < N := by
    rw [hNdef]
    exact_mod_cast σ.schmidtRank_pos
  have key : σ.entropy ≤ ∑ i ∈ σ.support, (σ.p i * Real.log N + 1 / N - σ.p i) :=
    Finset.sum_le_sum fun i _ => negMulLog_le_aux (σ.nonneg i) hN
  have hsum : ∑ i ∈ σ.support, (σ.p i * Real.log N + 1 / N - σ.p i)
      = (∑ i ∈ σ.support, σ.p i) * Real.log N
        + σ.support.card * (1 / N) - ∑ i ∈ σ.support, σ.p i := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_const, nsmul_eq_mul]
  rw [hsum, σ.total] at key
  have hcard : (σ.support.card : ℝ) = N := by rw [hNdef]; rfl
  rw [hcard] at key
  have : N * (1 / N) = 1 := by field_simp
  linarith [key, this.le, this.ge]

end SchmidtSpectrum

/-- **Area law in one dimension.**

A family of cuts of a one-dimensional chain (indexed by `n`, which one should think of as the
size of the region `A`, or the position of the cut in a chain of growing length) whose Schmidt
rank is uniformly bounded by a bond dimension `D` has entanglement entropy bounded by the
constant `log D`, *independently of the size of the region*.  This is the area law: in one
dimension the boundary of a region consists of a bounded number of points, so the entropy
does not grow with the volume of the region.

The hypothesis `hD` is exactly the content of Hastings' theorem for gapped local Hamiltonians:
the ground state of a gapped 1D chain is (approximated by) a matrix product state of bond
dimension `D` bounded in terms of the spectral gap, hence every cut has Schmidt rank `≤ D`.
The conclusion below is the entropy bound that follows from this hypothesis. -/

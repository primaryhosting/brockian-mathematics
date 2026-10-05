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
noncomputable def countingFn (mu : ℕ → ℝ) (lam : ℝ) : ℕ :=
  {n : ℕ | mu n ≤ lam}.ncard

/-- Under discreteness of the spectrum (all sublevel sets finite), the counting
function is at least `M` as soon as `lam` dominates the first `M` values. -/
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
theorem counting_diverges_of_exists
    (mu : ℕ → ℝ) (hcut : ∀ lam : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lam < mu n) :
    Filter.Tendsto (countingFn mu) Filter.atTop Filter.atTop := by
  have hfin : ∀ lam : ℝ, {n : ℕ | mu n ≤ lam}.Finite :=
    sublevel_finite_of_exists_cutoff mu hcut
  refine Filter.tendsto_atTop.2 fun M => ?_
  obtain ⟨L, hLmem⟩ := Finset.exists_le ((Finset.range M).image mu)
  filter_upwards [Filter.eventually_ge_atTop L] with lam hlam
  refine le_countingFn_of_le mu hfin M ?_
  intro i hi
  exact le_trans (hLmem (mu i) (Finset.mem_image_of_mem mu hi)) hlam

/-- The hypothesis of `counting_diverges_of_exists` is non-vacuous: the model
spectrum `mu n = n` satisfies it. -/
example : ∀ lam : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lam < (n : ℝ) := by
  intro lam
  obtain ⟨N, hN⟩ := exists_nat_gt lam
  exact ⟨N, fun n hn => lt_of_lt_of_le hN (by exact_mod_cast hn)⟩

#print axioms Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists

end Brockian.Weyl.WeylLawTarget


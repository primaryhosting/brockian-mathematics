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
def schmidtRank : ℕ := σ.support.card

/-- The support of a normalised spectrum is non-empty. -/
lemma support_nonempty : σ.support.Nonempty := by
  rcases Finset.eq_empty_or_nonempty σ.support with h | h
  · exfalso
    have := σ.total
    rw [h] at this
    simp at this
  · exact h

lemma schmidtRank_pos : 0 < σ.schmidtRank :=
  Finset.card_pos.mpr σ.support_nonempty

/-- Entanglement entropy is non-negative. -/
lemma entropy_nonneg (h : ∀ i, σ.p i ≤ 1) : 0 ≤ σ.entropy :=
  Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (σ.nonneg i) (h i)

/-- Pointwise form of the Gibbs inequality, obtained from `log x ≤ x - 1`:
for `0 ≤ p` and `0 < N`, `-p log p ≤ p log N + 1/N - p`. -/
lemma negMulLog_le_aux {p : ℝ} (hp : 0 ≤ p) {N : ℝ} (hN : 0 < N) :
    Real.negMulLog p ≤ p * Real.log N + 1 / N - p := by
  rcases eq_or_lt_of_le hp with h | hp'
  · simp only [← h, Real.negMulLog_zero, zero_mul, zero_add, sub_zero]
    positivity
  · have hx : 0 < 1 / (p * N) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    have hmul : p * Real.log (1 / (p * N)) ≤ p * (1 / (p * N) - 1) :=
      mul_le_mul_of_nonneg_left hlog hp
    have hrw : Real.log (1 / (p * N)) = -(Real.log p + Real.log N) := by
      rw [Real.log_div one_ne_zero (by positivity), Real.log_mul (ne_of_gt hp') (ne_of_gt hN)]
      simp
    have hval : p * (1 / (p * N) - 1) = 1 / N - p := by
      field_simp
    rw [hrw, hval] at hmul
    have : Real.negMulLog p = -(p * Real.log p) := by
      rw [Real.negMulLog_def]; ring
    nlinarith [hmul]

/-- **Maximum-entropy bound.**  The entanglement entropy is at most the logarithm of the
Schmidt rank across the cut. -/
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
theorem area_law_1d {ι : Type*} (D : ℕ) (σ : ℕ → SchmidtSpectrum ι)
    (hD : ∀ n, (σ n).schmidtRank ≤ D) :
    ∀ n, (σ n).entropy ≤ Real.log D := by
  intro n
  refine (σ n).entropy_le_log_schmidtRank.trans ?_
  have hpos : 0 < ((σ n).schmidtRank : ℝ) := by
    exact_mod_cast (σ n).schmidtRank_pos
  exact Real.log_le_log hpos (by exact_mod_cast hD n)

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


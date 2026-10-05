/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A pure state of a bipartite quantum system `A ⊗ B` is described, in a product basis, by its
amplitude matrix `M : Matrix A B ℂ`, normalised so that `∑ a b, ‖M a b‖ ^ 2 = 1`.  The reduced
density matrix of the left half is `ρ_A = M * Mᴴ`, and the *entanglement entropy* across the cut
is the von Neumann entropy `-Tr ρ_A log ρ_A = ∑ᵢ negMulLog λᵢ` of its eigenvalues.

The entanglement *area law* in one dimension says that for a gapped local Hamiltonian the ground
state's entanglement entropy across a cut of the chain is bounded by a constant that does not grow
with the length of the chain (the "area" of a cut of a 1D chain being a single point).  The
mechanism, which is the content of Hastings' theorem, is that the gap forces the Schmidt rank
(equivalently, the matrix–product bond dimension) across the cut to be bounded by a constant `D`
independent of the system size.

Here we formalise the area law given that input: from a uniform bound `D` on the Schmidt rank
across the cut we derive the uniform entropy bound `log D`, valid for every chain length.  The
final theorem `Phys.area_law_1d` is stated for a family of chain states indexed by the number of
sites, and its conclusion is a bound that is *independent of the number of sites*.

Note on the file header: it is written as a plain block comment `/- ... -/` rather than a module
docstring `/-! ... -/`, because Lean requires all `import` commands to come before any module
docstring, so a `/-! ... -/` header on line 1 would make the file fail to compile.
-/

open scoped BigOperators ComplexOrder
open Finset Matrix

namespace Phys

/-- The entanglement entropy across a cut, computed from the amplitude matrix `M` of the state:
the von Neumann entropy `∑ᵢ -λᵢ log λᵢ` of the reduced density matrix `ρ = M * Mᴴ`. -/

theorem entropy_le_log_card_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (D : ℕ)
    (hcard : {i | p i ≠ 0}.ncard ≤ D) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log D := by
  classical
  set s : Finset ι := univ.filter (fun i => p i ≠ 0) with hs
  have hsc : s.card ≤ D := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] at hcard
    exact hcard
  have hsum_s : ∑ i ∈ s, p i = 1 := by rw [hs, Finset.sum_filter_ne_zero, hsum]
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      subst h
      have hempty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hsc)
      rw [hempty] at hsum_s
      simp at hsum_s
    · exact_mod_cast h
  have hsum_eq : ∑ i, Real.negMulLog (p i) = ∑ i ∈ s, Real.negMulLog (p i) := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  rw [hsum_eq]
  have key : ∀ i ∈ s, Real.negMulLog (p i) ≤ (1 / (D : ℝ) - p i) + p i * Real.log D := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (by
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact fun h => hi h.symm)
    have hx : 0 < 1 / ((D : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity) (ne_of_gt hpi)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
    rw [Real.negMulLog_def]
    field_simp at hmul ⊢
    nlinarith [hmul, hpi, hDpos]
  calc ∑ i ∈ s, Real.negMulLog (p i)
      ≤ ∑ i ∈ s, ((1 / (D : ℝ) - p i) + p i * Real.log D) := Finset.sum_le_sum key
    _ = s.card / (D : ℝ) - 1 + Real.log D := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_s]
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ Real.log D := by
        have hle : (s.card : ℝ) / D ≤ 1 := by
          rw [div_le_one hDpos]; exact_mod_cast hsc
        linarith

/-- The eigenvalues of the reduced density matrix are non-negative. -/

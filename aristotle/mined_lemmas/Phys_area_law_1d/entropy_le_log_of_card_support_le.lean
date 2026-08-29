/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is reproduced verbatim as a module docstring below; Lean 4 requires
-- `import` commands to precede any module docstring.)

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

Hastings' area law states that the ground state of a gapped local Hamiltonian on a
one-dimensional chain has entanglement entropy across any cut bounded by a constant,
independent of the length of the chain and of the position of the cut.  The mechanism
behind the theorem is that such a ground state is (approximated by) a *finitely
correlated state* / *matrix product state* of bounded bond dimension `D`; a state with
a bond dimension `D` across a cut has Schmidt rank at most `D`, hence entanglement
entropy at most `log D`.

Here we formalize this final, mathematical content of the area law: for a matrix
product state on a chain of `k + m` sites built from `D × D` transfer matrices, the
von Neumann entropy of the reduced density matrix of the first `k` sites is at most
`log D`, *uniformly in `k` and `m`*.  This is the quantitative area-law bound: a
constant, independent of the subsystem size and of the total system size (in one
dimension the boundary of an interval consists of a bounded number of points, so a
constant bound *is* an area law).  The physical input of Hastings' theorem — that a
gapped local Hamiltonian has a ground state of this form — is an approximation
statement about Hamiltonians and is not part of the formalization below.

The two mathematical ingredients that are proved from scratch are:

* `Phys.entropy_le_log_of_card_support_le` — the maximum-entropy bound: a probability
  vector supported on at most `D` outcomes has Shannon entropy at most `log D`;
* `Phys.cutMatrix_eq_mul` — the matrix product structure factors the coefficient
  matrix of the state across the cut through a `D`-dimensional space, so the reduced
  density matrix has rank at most `D`.
-/

namespace Phys

open Matrix Finset

/-! ## Shannon entropy and the maximum entropy bound -/

/-- Shannon (von Neumann) entropy of a finite family of numbers,
`H(p) = -∑ pᵢ log pᵢ`. -/

theorem entropy_le_log_of_card_support_le {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (D : ℕ)
    (hcard : #{i | p i ≠ 0} ≤ D) :
    entropy p ≤ Real.log D := by
  classical
  rw [entropy]
  set s : Finset ι := {i | p i ≠ 0} with hs
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso
      have hz : ∀ i ∈ (Finset.univ : Finset ι), p i = 0 := by
        intro i _
        by_contra hi
        exact absurd (by simp [hs, hi] : i ∈ s) (by simp [h])
      rw [Finset.sum_congr rfl hz] at hsum
      simp at hsum
    · exact h
  have hD : 1 ≤ D := le_trans (Finset.card_pos.mpr hsne) hcard
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum_s : ∑ i ∈ s, p i = 1 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.subset_univ s) ?_
    intro i _ hi
    simpa [hs] using hi
  have hent : -∑ i, p i * Real.log (p i) = -∑ i ∈ s, p i * Real.log (p i) := by
    congr 1
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    have : p i = 0 := by simpa [hs] using hi
    simp [this]
  rw [hent]
  have key : ∀ i ∈ s, -(p i * Real.log (p i)) - p i * Real.log D ≤ 1 / (D : ℝ) - p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (by simpa [hs] using hi))
    have h1 : Real.log (1 / (p i * D)) ≤ 1 / (p i * D) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (1 / (p i * D)) = -Real.log (p i) - Real.log D := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hpi) (ne_of_gt hDpos)]
      ring
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hpi)
    rw [h2] at h3
    calc -(p i * Real.log (p i)) - p i * Real.log D
        = p i * (-Real.log (p i) - Real.log D) := by ring
      _ ≤ p i * (1 / (p i * D) - 1) := h3
      _ = 1 / (D : ℝ) - p i := by field_simp
  have hsum2 : ∑ i ∈ s, (-(p i * Real.log (p i)) - p i * Real.log D)
      ≤ ∑ i ∈ s, (1 / (D : ℝ) - p i) := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_s] at hsum2
  simp only [Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul] at hsum2
  have hcards : (s.card : ℝ) ≤ D := by exact_mod_cast hcard
  have hfin : (s.card : ℝ) * (1 / (D : ℝ)) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hDpos).mpr hcards
  linarith [hsum2]

/-! ## Matrix product states on a one-dimensional chain -/

variable {S : Type*} {D : ℕ}

/-- `prodMat A s len start` is the ordered product `A_start(s_start) ⋯ A_{start+len-1}(s_{start+len-1})`
of the MPS transfer matrices along `len` consecutive sites of the chain, in the
configuration `s`. -/

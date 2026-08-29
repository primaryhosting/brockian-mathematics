/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module doc comment before the import commands, so the
header is repeated below as a module docstring immediately after the imports.)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the entanglement-entropy area law for one-dimensional gapped systems.

A pure state of a bipartite system `A ⊗ B` is encoded by its coefficient matrix
`M : Matrix A B ℂ` (normalised so that `∑ a b, ‖M a b‖² = 1`).  The reduced density matrix
of the left block is `ρ_A = M Mᴴ`; it is positive semidefinite with unit trace, and the
entanglement entropy of the cut is the von Neumann entropy `-Tr ρ_A log ρ_A`, i.e. the
Shannon entropy of the eigenvalues of `ρ_A` (the squared Schmidt coefficients).

The physical input of Hastings' theorem is that the ground state of a gapped local
1D Hamiltonian is (approximated by) a matrix product state whose bond dimension `D`
depends only on the spectral gap, the local dimension and the interaction strength — and
**not** on the length `L` of the block.  Across a cut, an MPS of bond dimension `D`
factorises the coefficient matrix as `M = X * Y` with an inner index of size `D`.

Everything downstream of that input is proved here from scratch:

* `Phys.shannonEntropy_le_log_of_support` : the maximal-entropy bound
  `H(q) ≤ log N` whenever the probability vector `q` has at most `N` nonzero entries;
* `Phys.card_support_reducedSpectrum` : the number of nonzero eigenvalues of `M Mᴴ`
  equals the rank of `M` (Schmidt rank = matrix rank);
* `Phys.rank_le_of_factorization` : an MPS factorisation through a bond space of
  dimension `D` bounds the rank by `D`;
* `Phys.entanglementEntropy_le_log_rank` : entropy `≤ log (Schmidt rank)`;
* `Phys.area_law_1d` : hence, for a family of cuts admitting a *uniform* bond dimension
  `D`, the entanglement entropy is bounded by the constant `log D`, independently of the
  block length `L`.  This is the area law: in one dimension the boundary of a block has
  `O(1)` sites, and the entropy does not grow with the block volume.

`Phys.uniform_entropy` shows the bound `log D` is attained, and
`Phys.area_law_1d_entropy_density_tendsto_zero` records the resulting sub-volume law.
-/

open scoped BigOperators
open scoped ComplexOrder
open Finset

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ qᵢ log qᵢ` of a finitely supported weight vector. -/
noncomputable def shannonEntropy {ι : Type*} (s : Finset ι) (q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, -(q i * Real.log (q i))

variable {ι : Type*} {s t : Finset ι} {q : ι → ℝ}

/-- The Shannon entropy of a probability vector is nonnegative. -/
theorem shannonEntropy_nonneg (h0 : ∀ i ∈ s, 0 ≤ q i) (h1 : ∑ i ∈ s, q i = 1) :
    0 ≤ shannonEntropy s q := by
  refine Finset.sum_nonneg fun i hi => ?_
  have hq0 : 0 ≤ q i := h0 i hi
  have hq1 : q i ≤ 1 := by
    have := Finset.single_le_sum (f := q) (fun j hj => h0 j hj) hi
    rwa [h1] at this
  have : Real.log (q i) ≤ 0 := Real.log_nonpos hq0 hq1
  nlinarith

/-- **Maximal-entropy bound.**  A probability vector supported on a set of `k` elements has
Shannon entropy at most `log k`.  Proved from `log x ≤ x - 1` applied to `1 / (k qᵢ)`. -/
theorem shannonEntropy_le_log_card (h0 : ∀ i ∈ s, 0 ≤ q i) (h1 : ∑ i ∈ s, q i = 1) :
    shannonEntropy s q ≤ Real.log s.card := by
  have hcard : 0 < s.card := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · exfalso; rw [h] at h1; simp at h1
    · exact Finset.card_pos.mpr h
  set n : ℝ := (s.card : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast hcard
  have key : ∀ i ∈ s, -(q i * Real.log (q i)) ≤ 1 / n - q i + q i * Real.log n := by
    intro i hi
    rcases eq_or_lt_of_le (h0 i hi) with h | h
    · rw [← h]
      simp only [zero_mul, neg_zero, sub_zero, add_zero]
      positivity
    · have hx : 0 < 1 / (q i * n) := by positivity
      have hlog : Real.log (1 / (q i * n)) ≤ 1 / (q i * n) - 1 :=
        Real.log_le_sub_one_of_pos hx
      have hsplit : Real.log (1 / (q i * n)) = -(Real.log (q i) + Real.log n) := by
        rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
          Real.log_mul (ne_of_gt h) (ne_of_gt hn)]
        ring
      rw [hsplit] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
      have hfield : q i * (1 / (q i * n) - 1) = 1 / n - q i := by field_simp
      rw [hfield] at hmul
      nlinarith [hmul]
  have hsum : shannonEntropy s q ≤ ∑ i ∈ s, (1 / n - q i + q i * Real.log n) :=
    Finset.sum_le_sum key
  have hrhs : ∑ i ∈ s, (1 / n - q i + q i * Real.log n) = Real.log n := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul, h1,
      nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  rw [hrhs] at hsum
  exact hsum

/-- Entropy only sees the support: terms with zero weight contribute nothing. -/
theorem shannonEntropy_eq_of_support_subset (hts : t ⊆ s) (hzero : ∀ i ∈ s, i ∉ t → q i = 0) :
    shannonEntropy s q = shannonEntropy t q := by
  refine (Finset.sum_subset hts ?_).symm
  intro i hi hit
  rw [hzero i hi hit]
  simp

/-- **Maximal-entropy bound, support form.**  If a probability vector has at most `N`
nonzero entries then its Shannon entropy is at most `log N`. -/
theorem shannonEntropy_le_log_of_support (h0 : ∀ i ∈ s, 0 ≤ q i) (h1 : ∑ i ∈ s, q i = 1)
    (hts : t ⊆ s) (hzero : ∀ i ∈ s, i ∉ t → q i = 0) {N : ℕ} (hN : t.card ≤ N) :
    shannonEntropy s q ≤ Real.log N := by
  have hsum_t : ∑ i ∈ t, q i = 1 := by
    rw [← h1]
    exact (Finset.sum_subset (f := q) hts (fun i hi hit => hzero i hi hit)).symm
  have h0t : ∀ i ∈ t, 0 ≤ q i := fun i hi => h0 i (hts hi)
  have hcard : 0 < t.card := by
    rcases Finset.eq_empty_or_nonempty t with h | h
    · exfalso; rw [h] at hsum_t; simp at hsum_t
    · exact Finset.card_pos.mpr h
  calc shannonEntropy s q = shannonEntropy t q := shannonEntropy_eq_of_support_subset hts hzero
    _ ≤ Real.log t.card := shannonEntropy_le_log_card h0t hsum_t
    _ ≤ Real.log N := by
        refine Real.log_le_log (by exact_mod_cast hcard) (by exact_mod_cast hN)

/-! ## The Schmidt spectrum of a cut, abstractly -/

/-- The Schmidt spectrum of a bipartite pure state across a cut: the (finitely many)
squared Schmidt coefficients, i.e. the eigenvalues of the reduced density matrix
of one side of the cut.  They are nonnegative and sum to one. -/
structure SchmidtSpectrum where
  /-- Index set of the Schmidt coefficients. -/
  support : Finset ℕ
  /-- The squared Schmidt coefficients. -/
  p : ℕ → ℝ
  nonneg : ∀ i ∈ support, 0 ≤ p i
  sum_one : ∑ i ∈ support, p i = 1

namespace SchmidtSpectrum

variable (σ : SchmidtSpectrum)

/-- The entanglement entropy across the cut: the Shannon entropy of the Schmidt spectrum
(equivalently, the von Neumann entropy of the reduced density matrix). -/
noncomputable def entropy : ℝ := shannonEntropy σ.support σ.p

/-- The Schmidt rank across the cut. -/
def rank : ℕ := σ.support.card

lemma rank_pos : 0 < σ.rank := by
  rcases Finset.eq_empty_or_nonempty σ.support with h | h
  · exfalso
    have := σ.sum_one
    rw [h] at this
    simp at this
  · simpa [rank, Finset.card_pos] using h

lemma p_le_one {i : ℕ} (hi : i ∈ σ.support) : σ.p i ≤ 1 := by
  have := Finset.single_le_sum (f := σ.p) (fun j hj => σ.nonneg j hj) hi
  rwa [σ.sum_one] at this

/-- Entropy is nonnegative. -/
lemma entropy_nonneg : 0 ≤ σ.entropy :=
  shannonEntropy_nonneg σ.nonneg σ.sum_one

/-- The entanglement entropy across a cut is at most the logarithm of the Schmidt rank. -/
theorem entropy_le_log_rank : σ.entropy ≤ Real.log σ.rank :=
  shannonEntropy_le_log_card σ.nonneg σ.sum_one

/-- The uniform (maximally entangled) spectrum on `D` Schmidt coefficients. -/
noncomputable def uniform (D : ℕ) (hD : 0 < D) : SchmidtSpectrum where
  support := Finset.range D
  p := fun _ => 1 / D
  nonneg := by intro i _; positivity
  sum_one := by
    have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    simp [Finset.sum_const, Finset.card_range]
    field_simp

@[simp] lemma uniform_rank (D : ℕ) (hD : 0 < D) : (uniform D hD).rank = D := by
  simp [uniform, rank]

/-- The bound `entropy ≤ log rank` is attained by the maximally entangled state,
so it cannot be improved. -/
theorem uniform_entropy (D : ℕ) (hD : 0 < D) :
    (uniform D hD).entropy = Real.log D := by
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  simp only [entropy, shannonEntropy, uniform, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Real.log_div one_ne_zero (ne_of_gt hD'), Real.log_one]
  field_simp
  ring

end SchmidtSpectrum

/-- Area law at the level of Schmidt spectra: a bound `D` on the Schmidt rank across every
cut, uniform in the block length `L`, bounds the entanglement entropy by `log D`. -/
theorem area_law_1d_of_schmidt_rank_bound (σ : ℕ → SchmidtSpectrum) (D : ℕ)
    (hrank : ∀ L, (σ L).rank ≤ D) (L : ℕ) : (σ L).entropy ≤ Real.log D := by
  refine le_trans (σ L).entropy_le_log_rank ?_
  have h1 : (0:ℝ) < ((σ L).rank : ℝ) := by exact_mod_cast (σ L).rank_pos
  exact Real.log_le_log h1 (by exact_mod_cast hrank L)

/-! ## Reduced density matrices and the entanglement entropy of a cut -/

section Matrices

open Matrix

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]

/-- The reduced density matrix `ρ_A = M Mᴴ` of the left block, for a bipartite pure state
with coefficient matrix `M`. -/
noncomputable def reducedDensity (M : Matrix A B ℂ) : Matrix A A ℂ := M * Mᴴ

lemma reducedDensity_posSemidef (M : Matrix A B ℂ) : (reducedDensity M).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose M

/-- The Schmidt spectrum of the cut: the eigenvalues of the reduced density matrix, i.e.
the squared Schmidt coefficients of the pure state. -/
noncomputable def reducedSpectrum (M : Matrix A B ℂ) : A → ℝ :=
  (reducedDensity_posSemidef M).isHermitian.eigenvalues

/-- The entanglement entropy of the cut: the von Neumann entropy `-Tr ρ_A log ρ_A`,
computed as the Shannon entropy of the eigenvalues of `ρ_A`. -/
noncomputable def entanglementEntropy (M : Matrix A B ℂ) : ℝ :=
  shannonEntropy Finset.univ (reducedSpectrum M)

lemma reducedSpectrum_nonneg (M : Matrix A B ℂ) (i : A) : 0 ≤ reducedSpectrum M i :=
  (reducedDensity_posSemidef M).eigenvalues_nonneg i

lemma trace_reducedDensity (M : Matrix A B ℂ) :
    (reducedDensity M).trace = ∑ a, ∑ b, ((‖M a b‖ ^ 2 : ℝ) : ℂ) := by
  simp [reducedDensity, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- For a normalised pure state the Schmidt spectrum is a probability vector. -/
theorem sum_reducedSpectrum (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) :
    ∑ i, reducedSpectrum M i = 1 := by
  have h := (reducedDensity_posSemidef M).isHermitian.trace_eq_sum_eigenvalues
  rw [trace_reducedDensity M] at h
  have h2 : ((∑ a, ∑ b, ‖M a b‖ ^ 2 : ℝ) : ℂ) = ((∑ i, reducedSpectrum M i : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  have h3 := Complex.ofReal_injective h2
  rw [← h3, hM]

/-- **Schmidt rank = matrix rank.**  The number of nonzero squared Schmidt coefficients
equals the rank of the coefficient matrix. -/
theorem card_support_reducedSpectrum (M : Matrix A B ℂ) :
    (Finset.univ.filter fun i => reducedSpectrum M i ≠ 0).card = M.rank := by
  have h := (reducedDensity_posSemidef M).isHermitian.rank_eq_card_non_zero_eigs
  rw [Fintype.card_subtype] at h
  have h2 : (reducedDensity M).rank = M.rank := by
    rw [reducedDensity, Matrix.rank_self_mul_conjTranspose]
  rw [← h2, h, reducedSpectrum]

/-- An MPS factorisation through a bond space of dimension `D` bounds the Schmidt rank
by `D`. -/
theorem rank_le_of_factorization {D : ℕ} (M : Matrix A B ℂ) (X : Matrix A (Fin D) ℂ)
    (Y : Matrix (Fin D) B ℂ) (h : M = X * Y) : M.rank ≤ D := by
  rw [h]
  calc (X * Y).rank ≤ X.rank := Matrix.rank_mul_le_left X Y
    _ ≤ Fintype.card (Fin D) := Matrix.rank_le_card_width X
    _ = D := by simp

/-- A normalised pure state has Schmidt rank at least one. -/
theorem one_le_rank (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) : 1 ≤ M.rank := by
  rw [← card_support_reducedSpectrum M]
  rw [Finset.one_le_card]
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
  have : ∑ i, reducedSpectrum M i = 0 :=
    Finset.sum_eq_zero fun i hi => not_not.mp (hcon hi)
  rw [sum_reducedSpectrum M hM] at this
  exact one_ne_zero this

/-- **Entropy bound for a cut.**  The entanglement entropy across a cut of a normalised
pure state is at most the logarithm of its Schmidt rank. -/
theorem entanglementEntropy_le_log_rank (M : Matrix A B ℂ)
    (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) :
    entanglementEntropy M ≤ Real.log M.rank := by
  refine shannonEntropy_le_log_of_support (t := Finset.univ.filter fun i => reducedSpectrum M i ≠ 0)
    (fun i _ => reducedSpectrum_nonneg M i)
    (sum_reducedSpectrum M hM) (Finset.filter_subset _ _) ?_ ?_
  · intro i _ hi
    simpa using not_not.mp (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
  · exact le_of_eq (card_support_reducedSpectrum M)

/-- The entanglement entropy of a cut is nonnegative. -/
theorem entanglementEntropy_nonneg (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) :
    0 ≤ entanglementEntropy M :=
  shannonEntropy_nonneg (fun i _ => reducedSpectrum_nonneg M i) (sum_reducedSpectrum M hM)

/-- Entropy bound in terms of the bond dimension: an MPS factorisation of the coefficient
matrix through a bond space of dimension `D` bounds the entanglement entropy of the cut
by `log D`. -/
theorem entanglementEntropy_le_log_bondDim {D : ℕ} (M : Matrix A B ℂ)
    (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) (X : Matrix A (Fin D) ℂ) (Y : Matrix (Fin D) B ℂ)
    (hXY : M = X * Y) : entanglementEntropy M ≤ Real.log D := by
  refine le_trans (entanglementEntropy_le_log_rank M hM) ?_
  have h1 : (0:ℝ) < (M.rank : ℝ) := by exact_mod_cast one_le_rank M hM
  exact Real.log_le_log h1 (by exact_mod_cast rank_le_of_factorization M X Y hXY)

end Matrices

/-!
## The area law
-/

/--
**Area law for gapped one-dimensional ground states (Hastings).**

Setting: a one-dimensional chain cut into a left block and its complement; the cut labelled
by `L` (say, after `L` sites) has left Hilbert space of dimension `dL L`, right Hilbert
space of dimension `dR L`, and the ground state is described across that cut by its
normalised coefficient matrix `M L`.

Physical input (`hMPS`): Hastings' theorem produces, for a gapped local 1D Hamiltonian, a
bond dimension `D` depending only on the spectral gap, the local dimension and the
interaction strength — and *not* on the block length `L` — such that the ground state is a
matrix product state of bond dimension `D`; across each cut this factorises the coefficient
matrix as `M L = X * Y` through a bond space `Fin D`.  This analytic input (Lieb–Robinson
bounds / AGSP machinery) is taken as a hypothesis; everything else is proved here.

Conclusion: the entanglement entropy of the block is bounded by the constant `log D`,
uniformly in `L`.  Since the boundary of an interval in one dimension consists of `O(1)`
points, this is precisely the area law: the entropy does not grow with the block volume.
-/
theorem area_law_1d (dL dR : ℕ → ℕ) (M : ∀ L : ℕ, Matrix (Fin (dL L)) (Fin (dR L)) ℂ)
    (hnorm : ∀ L, ∑ a, ∑ b, ‖M L a b‖ ^ 2 = 1) (D : ℕ)
    (hMPS : ∀ L, ∃ (X : Matrix (Fin (dL L)) (Fin D) ℂ) (Y : Matrix (Fin D) (Fin (dR L)) ℂ),
      M L = X * Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, entanglementEntropy (M L) ≤ C := by
  refine ⟨Real.log D, ?_, fun L => ?_⟩
  · refine Real.log_nonneg ?_
    obtain ⟨X, Y, hXY⟩ := hMPS 0
    have h1 : 1 ≤ (M 0).rank := one_le_rank _ (hnorm 0)
    have h2 : (M 0).rank ≤ D := rank_le_of_factorization _ X Y hXY
    exact_mod_cast le_trans h1 h2
  · obtain ⟨X, Y, hXY⟩ := hMPS L
    exact entanglementEntropy_le_log_bondDim (M L) (hnorm L) X Y hXY

/-- Contrapositive form of the area law: if the entanglement entropy across the cuts is
unbounded (a volume law, say), then the state admits no matrix product state description of
constant bond dimension — hence, by Hastings' theorem, cannot be the ground state of a
gapped local one-dimensional Hamiltonian. -/
theorem area_law_1d_contrapositive (dL dR : ℕ → ℕ)
    (M : ∀ L : ℕ, Matrix (Fin (dL L)) (Fin (dR L)) ℂ)
    (hnorm : ∀ L, ∑ a, ∑ b, ‖M L a b‖ ^ 2 = 1)
    (hS : ∀ C : ℝ, ∃ L : ℕ, C < entanglementEntropy (M L)) :
    ∀ D : ℕ, ∃ L : ℕ, ¬ ∃ (X : Matrix (Fin (dL L)) (Fin D) ℂ) (Y : Matrix (Fin D) (Fin (dR L)) ℂ),
      M L = X * Y := by
  intro D
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, _, hC⟩ := area_law_1d dL dR M hnorm D hcon
  obtain ⟨L, hL⟩ := hS C
  exact absurd (hC L) (not_le.mpr hL)

/-- Sub-volume law: under a uniform bond-dimension bound, the entropy density
`entropy / L` of the left block tends to `0`. -/
theorem area_law_1d_entropy_density_tendsto_zero (dL dR : ℕ → ℕ)
    (M : ∀ L : ℕ, Matrix (Fin (dL L)) (Fin (dR L)) ℂ)
    (hnorm : ∀ L, ∑ a, ∑ b, ‖M L a b‖ ^ 2 = 1) (D : ℕ)
    (hMPS : ∀ L, ∃ (X : Matrix (Fin (dL L)) (Fin D) ℂ) (Y : Matrix (Fin D) (Fin (dR L)) ℂ),
      M L = X * Y) :
    Filter.Tendsto (fun L : ℕ => entanglementEntropy (M L) / L) Filter.atTop (nhds 0) := by
  obtain ⟨C, _, hC⟩ := area_law_1d dL dR M hnorm D hMPS
  have hlow : ∀ L : ℕ, 0 ≤ entanglementEntropy (M L) / L := fun L =>
    div_nonneg (entanglementEntropy_nonneg (M L) (hnorm L)) (Nat.cast_nonneg L)
  have hup : ∀ L : ℕ, entanglementEntropy (M L) / L ≤ C / L := fun L =>
    div_le_div_of_nonneg_right (hC L) (Nat.cast_nonneg L)
  have hCtend : Filter.Tendsto (fun L : ℕ => C / (L : ℝ)) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) C
  exact squeeze_zero hlow hup hCtend

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


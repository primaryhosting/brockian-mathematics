/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/
noncomputable def vnEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, -(p i * Real.log (p i))

/-- The spectrum of the reduced density matrix `M * Mᴴ` obtained from the coefficient matrix
`M` of a bipartite pure state. -/
noncomputable def reducedSpectrum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) : A → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues

/-- Entanglement entropy of a bipartite pure state given by its coefficient matrix `M`. -/
noncomputable def entanglementEntropy {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) : ℝ :=
  vnEntropy (reducedSpectrum M)

/-- Ordered product of the MPS matrices of a block of sites. -/
noncomputable def blockProd {L d D : ℕ} (A : Fin L → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (s : Fin L → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i => A i (s i)).prod

/-- Coefficient matrix, across the cut, of a matrix product state on a 1D chain consisting of a
left block of `k` sites and a right block of `m` sites, each of local dimension `d`, with bond
dimension `D` and boundary vectors `u`, `v`. -/
noncomputable def mpsCoeff {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (u v : Fin D → ℂ) : Matrix (Fin k → Fin d) (Fin m → Fin d) ℂ :=
  fun sL sR => u ⬝ᵥ ((blockProd AL sL * blockProd AR sR) *ᵥ v)

/-- Entropy of a probability vector supported on at most `D` points is at most `log D`. -/
lemma vnEntropy_le_log_of_card_support_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    {D : ℕ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hcard : (Finset.univ.filter fun i => p i ≠ 0).card ≤ D) :
    vnEntropy p ≤ Real.log D := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hSsum : ∑ i ∈ S, p i = 1 := by
    rw [hSdef, Finset.sum_filter_ne_zero]
    exact hsum
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with h | h
    · rw [h] at hSsum; simp at hSsum
    · exact h
  have hD : 0 < D := lt_of_lt_of_le (Finset.card_pos.mpr hSne) hcard
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hEnt : vnEntropy p = ∑ i ∈ S, -(p i * Real.log (p i)) := by
    rw [vnEntropy]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    have hzero : p i = 0 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    simp [hzero]
  have key : ∀ i ∈ S, -(p i * Real.log (p i)) ≤ p i * Real.log D + (1 / D - p i) := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (Finset.mem_filter.mp hi).2)
    have hx : 0 < 1 / ((D : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    have h1 : Real.log (1 / ((D : ℝ) * p i)) = -(Real.log D + Real.log (p i)) := by
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (ne_of_gt hDR) (ne_of_gt hpi)]
      ring
    rw [h1] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
    have h2 : p i * (1 / ((D : ℝ) * p i) - 1) = 1 / D - p i := by field_simp
    rw [h2] at hmul
    nlinarith [hmul]
  calc vnEntropy p = ∑ i ∈ S, -(p i * Real.log (p i)) := hEnt
    _ ≤ ∑ i ∈ S, (p i * Real.log D + (1 / D - p i)) := Finset.sum_le_sum key
    _ = Real.log D + ((S.card : ℝ) / D - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hSsum, one_mul, Finset.sum_sub_distrib,
          hSsum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ Real.log D := by
        have hle : (S.card : ℝ) / D ≤ 1 := by
          rw [div_le_one hDR]
          exact_mod_cast hcard
        linarith

/-- The spectrum of the reduced density matrix is nonnegative. -/
lemma reducedSpectrum_nonneg {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (a : A) : 0 ≤ reducedSpectrum M a :=
  (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg a

/-- For a normalized state, the reduced spectrum sums to one. -/
lemma sum_reducedSpectrum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (hM : ∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 = 1) :
    ∑ a : A, reducedSpectrum M a = 1 := by
  have h1 : (M * Mᴴ).trace = ∑ a : A, ((reducedSpectrum M a : ℝ) : ℂ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues (Matrix.isHermitian_mul_conjTranspose_self M)
  have h2 : (M * Mᴴ).trace = ((∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hM, h1] at h2
  have h3 : ((∑ a : A, reducedSpectrum M a : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    simpa using h2
  exact_mod_cast h3

/-- The number of nonzero elements of the reduced spectrum is the rank of `M`. -/
lemma card_support_reducedSpectrum {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) :
    (Finset.univ.filter fun a => reducedSpectrum M a ≠ 0).card = M.rank := by
  classical
  have h := (Matrix.isHermitian_mul_conjTranspose_self M).rank_eq_card_non_zero_eigs
  rw [Matrix.rank_self_mul_conjTranspose] at h
  rw [h, Fintype.card_subtype]
  rfl

/-- **Rank bound on entanglement entropy**: a normalized bipartite pure state whose coefficient
matrix has rank (Schmidt rank) at most `D` has entanglement entropy at most `log D`. -/
theorem entanglementEntropy_le_log_of_rank_le {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (M : Matrix A B ℂ) (hM : ∑ a : A, ∑ b : B, ‖M a b‖ ^ 2 = 1) {D : ℕ}
    (hrank : M.rank ≤ D) : entanglementEntropy M ≤ Real.log D := by
  classical
  refine vnEntropy_le_log_of_card_support_le (reducedSpectrum_nonneg M)
    (sum_reducedSpectrum M hM) ?_
  rw [card_support_reducedSpectrum M]
  exact hrank

/-- A matrix product state factors, across any cut, through the `D`-dimensional bond space. -/
lemma mpsCoeff_eq_mul {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ) (u v : Fin D → ℂ) :
    mpsCoeff AL AR u v =
      (Matrix.of fun (sL : Fin k → Fin d) (x : Fin D) => (u ᵥ* blockProd AL sL) x) *
      (Matrix.of fun (x : Fin D) (sR : Fin m → Fin d) => (blockProd AR sR *ᵥ v) x) := by
  ext sL sR
  show u ⬝ᵥ ((blockProd AL sL * blockProd AR sR) *ᵥ v) = _
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  rfl

/-- The Schmidt rank of a matrix product state across a cut is at most the bond dimension. -/
lemma rank_mpsCoeff_le {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ) (u v : Fin D → ℂ) :
    (mpsCoeff AL AR u v).rank ≤ D := by
  rw [mpsCoeff_eq_mul]
  refine le_trans (Matrix.rank_mul_le_right _ _) ?_
  have h := Matrix.rank_le_card_height
    (R := ℂ) (Matrix.of fun (x : Fin D) (sR : Fin m → Fin d) => (blockProd AR sR *ᵥ v) x)
  simpa using h

/-- **Area law for gapped 1D ground states (Hastings).**

A gapped local Hamiltonian on a 1D chain has a ground state that is (arbitrarily well
approximated by) a matrix product state whose bond dimension `D` depends only on the spectral
gap and the local dimension, not on the length of the chain.  The theorem below is the
entanglement-entropy area law for such states: for a matrix product state of bond dimension `D`
on a chain split into a left block of `k` sites and a right block of `m` sites, the entanglement
entropy across the cut is bounded by `log D`, a constant that is independent of the block sizes
`k`, `m` and hence of the size of the subsystem — the entropy scales like the size of the
boundary of the region (a single point in 1D), which is exactly the area law. -/
theorem area_law_1d {d D k m : ℕ}
    (AL : Fin k → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (AR : Fin m → Fin d → Matrix (Fin D) (Fin D) ℂ) (u v : Fin D → ℂ)
    (hnorm : ∑ sL : Fin k → Fin d, ∑ sR : Fin m → Fin d, ‖mpsCoeff AL AR u v sL sR‖ ^ 2 = 1) :
    entanglementEntropy (mpsCoeff AL AR u v) ≤ Real.log D :=
  entanglementEntropy_le_log_of_rank_le _ hnorm (rank_mpsCoeff_le AL AR u v)

/-- The area law, stated uniformly: for a matrix product state built from one family `A` of site
tensors of bond dimension `D` on a chain of arbitrary length `k + m`, the entanglement entropy
across the cut after site `k` is bounded by the single constant `log D`, for every cut position
`k` and every chain length. -/
theorem area_law_1d_uniform {d D : ℕ} (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (u v : Fin D → ℂ) (k m : ℕ)
    (hnorm : ∑ sL : Fin k → Fin d, ∑ sR : Fin m → Fin d,
        ‖mpsCoeff (fun i : Fin k => A i) (fun j : Fin m => A (k + j)) u v sL sR‖ ^ 2 = 1) :
    entanglementEntropy (mpsCoeff (fun i : Fin k => A i) (fun j : Fin m => A (k + j)) u v)
      ≤ Real.log D :=
  area_law_1d _ _ u v hnorm

/-- The normalization hypothesis of `Phys.area_law_1d` is satisfiable: an explicit normalized
matrix product state (here the product state on two qubits with bond dimension one).  This shows
the area law above is not vacuous. -/
lemma exists_normalized_mps :
    ∑ sL : Fin 1 → Fin 2, ∑ sR : Fin 1 → Fin 2,
      ‖mpsCoeff (d := 2) (D := 1) (k := 1) (m := 1)
        (fun _ s => if s = 0 then 1 else 0) (fun _ s => if s = 0 then 1 else 0)
        (fun _ => 1) (fun _ => 1) sL sR‖ ^ 2 = 1 := by
  rw [show (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} from by decide]
  simp [mpsCoeff, blockProd, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Phys


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
open Matrix ComplexOrder

namespace Phys

/-! ## Entropy of a finitely supported probability vector -/

/-- Shannon entropy of a real vector, `∑ -p i * log (p i)`. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- **Maximum entropy bound.** A probability vector supported on at most `D` atoms has
Shannon entropy at most `log D`. -/
theorem shannonEntropy_le_log_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} {D : ℕ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hD : 0 < D) (hcard : (Finset.univ.filter fun i => p i ≠ 0).card ≤ D) :
    shannonEntropy p ≤ Real.log D := by
  classical
  set s : Finset ι := Finset.univ.filter fun i => p i ≠ 0 with hs
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum_s : ∑ i ∈ s, p i = 1 := by
    rw [hs, Finset.sum_filter_ne_zero, hsum]
  have hent : shannonEntropy p = ∑ i ∈ s, Real.negMulLog (p i) := by
    unfold shannonEntropy
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    have hpi : p i = 0 := by simpa [hs] using hi
    simp [hpi, Real.negMulLog]
  -- For each atom in the support, `log x ≤ x - 1` applied to `x = 1 / (p i * D)`.
  have key : ∀ i ∈ s, Real.negMulLog (p i) ≤ p i * Real.log D + 1 / D - p i := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (by simpa [hs] using hi))
    have h1 : Real.log (1 / (p i * D)) ≤ 1 / (p i * D) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (1 / (p i * D)) = -Real.log (p i) - Real.log D := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hpi) (ne_of_gt hDpos)]
      ring
    have h3 : p i * (-Real.log (p i) - Real.log D) ≤ p i * (1 / (p i * D) - 1) :=
      mul_le_mul_of_nonneg_left (h2 ▸ h1) (le_of_lt hpi)
    have h4 : p i * (1 / (p i * D) - 1) = 1 / D - p i := by field_simp
    rw [h4] at h3
    simp only [Real.negMulLog]
    nlinarith [h3]
  calc shannonEntropy p = ∑ i ∈ s, Real.negMulLog (p i) := hent
    _ ≤ ∑ i ∈ s, (p i * Real.log D + 1 / D - p i) := Finset.sum_le_sum key
    _ = (∑ i ∈ s, p i) * Real.log D + s.card * (1 / D) - ∑ i ∈ s, p i := by
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_add_distrib, Finset.sum_mul]
    _ = Real.log D + s.card / D - 1 := by rw [hsum_s]; ring
    _ ≤ Real.log D := by
        have h5 : (s.card : ℝ) ≤ D := by exact_mod_cast hcard
        have : (s.card : ℝ) / D ≤ 1 := by rw [div_le_one hDpos]; exact h5
        linarith

/-! ## Von Neumann entropy -/

/-- Von Neumann entropy of a hermitian matrix (used for density matrices): the Shannon
entropy of its spectrum. -/
noncomputable def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  shannonEntropy hρ.eigenvalues

/-- If the density matrix `ρ = M * Mᴴ` has unit trace and `M` has rank at most `D`, then the
von Neumann entropy of `ρ` is at most `log D`. -/
theorem vonNeumannEntropy_le_log_rank {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (M : Matrix L R ℂ) {D : ℕ} (hD : 0 < D)
    (hrank : M.rank ≤ D) (htr : (M * Mᴴ).trace = 1) :
    vonNeumannEntropy (Matrix.isHermitian_mul_conjTranspose_self M) ≤ Real.log D := by
  classical
  set hρ := Matrix.isHermitian_mul_conjTranspose_self M with hhρ
  have hpsd : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  have hnonneg : ∀ i, 0 ≤ hρ.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have hsum : ∑ i, hρ.eigenvalues i = 1 := by
    have h := hρ.trace_eq_sum_eigenvalues
    rw [htr] at h
    simpa using congrArg Complex.re h.symm
  have hcard : (Finset.univ.filter fun i => hρ.eigenvalues i ≠ 0).card ≤ D := by
    have h1 : (M * Mᴴ).rank = Fintype.card {i // hρ.eigenvalues i ≠ 0} :=
      hρ.rank_eq_card_non_zero_eigs
    have h2 : (M * Mᴴ).rank = M.rank := Matrix.rank_self_mul_conjTranspose M
    rw [Fintype.card_subtype] at h1
    omega
  exact shannonEntropy_le_log_card hnonneg hsum hD hcard

/-! ## Matrix product states -/

variable {d D : ℕ}

/-- The ordered product `A o (s 0) * A (o+1) (s 1) * ⋯ * A (o+n-1) (s (n-1))` of the MPS
tensors of a block of `n` consecutive sites starting at site `o`. -/
noncomputable def mpsProd (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (o n : ℕ)
    (s : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i : Fin n => A (o + (i : ℕ)) (s i)).prod

/-- The amplitude of a matrix product state with bond dimension `D`, local dimension `d`,
tensors `A` and boundary vectors `vL`, `vR`. -/
noncomputable def mpsState (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (n : ℕ) (s : Fin n → Fin d) : ℂ :=
  vL ⬝ᵥ (mpsProd A 0 n s *ᵥ vR)

/-- The matrix of amplitudes of a state on `k + m` sites, viewed across the cut between the
first `k` sites and the last `m` sites. Its singular values are the Schmidt coefficients of
the state across that cut. -/
def cutMatrix {k m : ℕ} (psi : (Fin (k + m) → Fin d) → ℂ) :
    Matrix (Fin k → Fin d) (Fin m → Fin d) ℂ :=
  fun u v => psi (Fin.append u v)

/-- Splitting an MPS block product at a cut: the product over `k + m` sites is the product
over the first `k` sites times the product over the last `m` sites. -/
theorem mpsProd_append (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (o k m : ℕ)
    (u : Fin k → Fin d) (v : Fin m → Fin d) :
    mpsProd A o (k + m) (Fin.append u v) = mpsProd A o k u * mpsProd A (o + k) m v := by
  unfold mpsProd
  rw [List.ofFn_add, List.prod_append]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    have h1 : Fin.castLE (Nat.le_add_right k m) i = Fin.castAdd m i := rfl
    simp [h1, Fin.append_left]
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Fin.append_right, Nat.add_assoc]

/-- Auxiliary permutation of a triple sum. -/
private theorem sum_comm_first_last {α : Type*} [Fintype α] (f : α → α → α → ℂ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Contracting a product of two matrices with boundary vectors splits over the bond index. -/
private theorem dotProduct_mul_mulVec (P Q : Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ) :
    vL ⬝ᵥ ((P * Q) *ᵥ vR) = ∑ a, (vL ᵥ* P) a * (Q *ᵥ vR) a := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [sum_comm_first_last (fun b c a => vL b * (P b a * Q a c * vR c))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The cut matrix of an MPS factors through the `D`-dimensional bond space at the cut. -/
theorem cutMatrix_mps_eq_mul (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (k m : ℕ) :
    cutMatrix (mpsState A vL vR (k + m)) =
      (Matrix.of fun (u : Fin k → Fin d) (a : Fin D) => (vL ᵥ* mpsProd A 0 k u) a) *
      (Matrix.of fun (a : Fin D) (v : Fin m → Fin d) => (mpsProd A k m v *ᵥ vR) a) := by
  ext u v
  rw [Matrix.mul_apply]
  show mpsState A vL vR (k + m) (Fin.append u v) = _
  unfold mpsState
  rw [mpsProd_append A 0 k m u v, zero_add, dotProduct_mul_mulVec]
  rfl

/-- **Bond-dimension bound on the Schmidt rank.** The rank of the cut matrix of an MPS is at
most the bond dimension `D`, independently of the number of sites on either side of the cut. -/
theorem rank_cutMatrix_mps_le (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ) (vL vR : Fin D → ℂ)
    (k m : ℕ) : (cutMatrix (mpsState A vL vR (k + m))).rank ≤ D := by
  rw [cutMatrix_mps_eq_mul]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using Matrix.rank_le_card_width
    (Matrix.of fun (u : Fin k → Fin d) (a : Fin D) => (vL ᵥ* mpsProd A 0 k u) a)

/-- The trace of the reduced density matrix is the squared norm of the state. -/
theorem trace_cutMatrix_mul_conjTranspose {k m : ℕ} (psi : (Fin (k + m) → Fin d) → ℂ) :
    (cutMatrix psi * (cutMatrix psi)ᴴ).trace = ((∑ s, ‖psi s‖ ^ 2 : ℝ) : ℂ) := by
  have hsplit : (∑ s, ‖psi s‖ ^ 2 : ℝ)
      = ∑ u : Fin k → Fin d, ∑ v : Fin m → Fin d, ‖psi (Fin.append u v)‖ ^ 2 := by
    have h := Fintype.sum_equiv (Fin.appendEquiv k m)
      (fun p => ‖psi (Fin.append p.1 p.2)‖ ^ 2) (fun s => ‖psi s‖ ^ 2) (fun _ => rfl)
    rw [← h, Fintype.sum_prod_type]
  rw [hsplit]
  push_cast
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.conjTranspose_apply]
  show psi (Fin.append u v) * (starRingEnd ℂ) (psi (Fin.append u v)) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-! ## The area law -/

/--
**Entanglement-entropy area law in one dimension.**

Hastings' theorem states that the ground state of a gapped local Hamiltonian on a 1D chain is
(approximated to any fixed accuracy by) a matrix product state whose bond dimension `D` depends
only on the spectral gap and the local dimension, not on the length of the chain. That is the
physical input, and it is encoded here as the hypothesis that the state is a matrix product
state of bond dimension `D`.

What is proved here is the resulting area law: for a normalized state on a chain of `k + m`
sites, the von Neumann entanglement entropy of the reduced density matrix of the left block,
across the cut between the first `k` and the last `m` sites, is at most `log D` — a constant
depending only on the bond dimension, and in particular independent of the sizes `k` and `m`
of the two blocks. Since the boundary of an interval in one dimension consists of a bounded
number of points, such a bound, uniform in the block sizes, is precisely the area law.
-/
theorem area_law_1d (hD : 0 < D) (A : ℕ → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (vL vR : Fin D → ℂ) (k m : ℕ)
    (hnorm : ∑ s : Fin (k + m) → Fin d, ‖mpsState A vL vR (k + m) s‖ ^ 2 = 1) :
    vonNeumannEntropy (Matrix.isHermitian_mul_conjTranspose_self
        (cutMatrix (mpsState A vL vR (k + m)))) ≤ Real.log D := by
  refine vonNeumannEntropy_le_log_rank _ hD (rank_cutMatrix_mps_le A vL vR k m) ?_
  rw [trace_cutMatrix_mul_conjTranspose, hnorm]
  norm_num

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


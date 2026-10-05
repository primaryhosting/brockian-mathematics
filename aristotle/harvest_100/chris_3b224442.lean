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

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ pᵢ log pᵢ` of a finite family of reals. -/
noncomputable def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- **Maximum-entropy bound.** A probability vector supported on at most `D` points has
Shannon entropy at most `log D`. -/
theorem shannonEntropy_le_log_of_card_support_le
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (D : ℕ) (hD : (Finset.univ.filter fun i => p i ≠ 0).card ≤ D) :
    shannonEntropy p ≤ Real.log D := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => p i ≠ 0) with hS
  -- the support is nonempty, since the total mass is `1`
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∀ i, p i = 0 := by
      intro i
      by_contra hi
      have : i ∈ S := by simp [hS, hi]
      simp [h] at this
    rw [Finset.sum_congr rfl (fun i _ => this i)] at hsum
    simp at hsum
  set n : ℕ := S.card with hn
  have hn0 : 0 < n := Finset.card_pos.mpr hSne
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- restrict the entropy sum to the support
  have hrestrict : shannonEntropy p = ∑ i ∈ S, Real.negMulLog (p i) := by
    rw [shannonEntropy, ← Finset.sum_subset (Finset.subset_univ S)]
    intro i _ hi
    have : p i = 0 := by
      by_contra h
      exact hi (by simp [hS, h])
    simp [this, Real.negMulLog]
  -- pointwise bound coming from `log y ≤ y - 1`
  have hpt : ∀ i ∈ S, Real.negMulLog (p i) ≤ p i * Real.log n + (1 / n - p i) := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (by simpa [hS] using hi))
    have hy : 0 < 1 / ((n : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hy
    have hlogeq : Real.log (1 / ((n : ℝ) * p i)) = -Real.log n - Real.log (p i) := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hnR) (ne_of_gt hpi)]
      ring
    have key : -Real.log n - Real.log (p i) ≤ 1 / ((n : ℝ) * p i) - 1 := by
      rw [← hlogeq]; exact hlog
    have hmul := mul_le_mul_of_nonneg_left key (le_of_lt hpi)
    have hsimp : p i * (1 / ((n : ℝ) * p i) - 1) = 1 / n - p i := by
      field_simp
    rw [hsimp] at hmul
    calc Real.negMulLog (p i) = p i * (-Real.log n - Real.log (p i)) + p i * Real.log n := by
          simp [Real.negMulLog]; ring
      _ ≤ (1 / n - p i) + p i * Real.log n := by linarith
      _ = p i * Real.log n + (1 / n - p i) := by ring
  have hsumS : ∑ i ∈ S, p i = 1 := by
    rw [← hsum]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    by_contra h
    exact hi (by simp [hS, h])
  have hbound : ∑ i ∈ S, Real.negMulLog (p i)
      ≤ ∑ i ∈ S, (p i * Real.log n + (1 / n - p i)) := Finset.sum_le_sum hpt
  have hrhs : ∑ i ∈ S, (p i * Real.log n + (1 / n - p i)) = Real.log n := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumS, one_mul, Finset.sum_sub_distrib,
      hsumS, Finset.sum_const, ← hn, nsmul_eq_mul]
    field_simp
  have hlogle : Real.log n ≤ Real.log D := by
    have hnD : (n : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    exact Real.log_le_log hnR hnD
  rw [hrestrict]
  linarith [hbound, hrhs.le, hrhs.ge]

/-! ## Von Neumann entropy of a density matrix -/

/-- The von Neumann entropy `-Tr(ρ log ρ)` of a Hermitian matrix, computed from its spectrum
(and set to `0` for non-Hermitian matrices). -/
noncomputable def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) : ℝ :=
  if h : rho.IsHermitian then shannonEntropy h.eigenvalues else 0

/-- **Entropy bound from the Schmidt rank.** If a density matrix `ρ` (positive semidefinite,
unit trace) has rank at most `D`, then its von Neumann entropy is at most `log D`. -/
theorem vonNeumannEntropy_le_log_rank {n : Type*} [Fintype n] [DecidableEq n]
    {rho : Matrix n n ℂ} (hpsd : rho.PosSemidef) (htr : rho.trace = 1)
    (D : ℕ) (hrank : rho.rank ≤ D) :
    vonNeumannEntropy rho ≤ Real.log D := by
  classical
  have hherm : rho.IsHermitian := hpsd.isHermitian
  have hev_nonneg : ∀ i, 0 ≤ hherm.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have hev_sum : ∑ i, hherm.eigenvalues i = 1 := by
    have := hherm.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, hherm.eigenvalues i : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.ofReal_sum]; exact this.symm
    exact_mod_cast h2
  have hcard : (Finset.univ.filter fun i => hherm.eigenvalues i ≠ 0).card ≤ D := by
    have h : rho.rank = Fintype.card {i // hherm.eigenvalues i ≠ 0} :=
      hherm.rank_eq_card_non_zero_eigs
    rw [Fintype.card_subtype] at h
    rw [h] at hrank
    exact hrank
  rw [vonNeumannEntropy, dif_pos hherm]
  exact shannonEntropy_le_log_of_card_support_le _ hev_nonneg hev_sum D hcard

/-! ## The 1D chain: cuts, Schmidt matricization and reduced density matrices -/

/-- Splitting of the configuration space of a chain of `N` sites with local dimension `d`
into the configurations of the left block `{0, …, x-1}` and of the right block. -/
noncomputable def cutEquiv (d N x : ℕ) :
    ((Fin N) → Fin d) ≃
      (({i : Fin N // (i : ℕ) < x} → Fin d) × ({i : Fin N // ¬ (i : ℕ) < x} → Fin d)) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin N => (i : ℕ) < x) (fun _ => Fin d)

/-- The matricization (Schmidt matrix) of a state `psi` of the chain across the cut at `x`:
rows are labelled by configurations of the left block, columns by those of the right block. -/
noncomputable def cutMatrix (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    Matrix ({i : Fin N // (i : ℕ) < x} → Fin d) ({i : Fin N // ¬ (i : ℕ) < x} → Fin d) ℂ :=
  fun a b => psi ((cutEquiv d N x).symm (a, b))

/-- The reduced density matrix of the left block `{0, …, x-1}` for the state `psi`. -/
noncomputable def reducedDensity (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    Matrix ({i : Fin N // (i : ℕ) < x} → Fin d) ({i : Fin N // (i : ℕ) < x} → Fin d) ℂ :=
  cutMatrix d N x psi * (cutMatrix d N x psi)ᴴ

theorem reducedDensity_posSemidef (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    (reducedDensity d N x psi).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem trace_reducedDensity (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    (reducedDensity d N x psi).trace = ((∑ c, ‖psi c‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have h1 : (reducedDensity d N x psi).trace
      = ∑ a, ∑ b, ((‖cutMatrix d N x psi a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [reducedDensity, Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    norm_cast
  rw [h1]
  rw [Complex.ofReal_sum]
  rw [← Equiv.sum_comp (cutEquiv d N x) (fun q => ((‖psi ((cutEquiv d N x).symm q)‖ ^ 2 : ℝ) : ℂ))]
  · rw [Fintype.sum_prod_type]
    rfl

theorem rank_reducedDensity (d N x : ℕ) (psi : (Fin N → Fin d) → ℂ) :
    (reducedDensity d N x psi).rank = (cutMatrix d N x psi).rank :=
  Matrix.rank_self_mul_conjTranspose _

/-! ## The area law -/

/-- **Entanglement-entropy area law in one dimension (Hastings).**

Setting: a chain of `N` sites with local Hilbert-space dimension `d`, in a normalized pure state
`psi`. For a cut at position `x` the state is matricized into `cutMatrix`, whose rank is the
Schmidt rank across the cut; the reduced density matrix of the left block is
`reducedDensity = M Mᴴ`, and the entanglement entropy of the cut is its von Neumann entropy.

Hypothesis `hSchmidt` is the content of Hastings' matrix-product-state construction for gapped
local Hamiltonians: the ground state has Schmidt rank bounded by a *bond dimension* `D` that
depends only on the local dimension and the spectral gap (through the correlation length), and not
on the system size `N` nor on the location `x` of the cut.

Conclusion: the entanglement entropy across *every* cut is bounded by `log D`, a constant
independent of the size of the subsystem — i.e. the entropy obeys an area law (in one dimension the
"boundary" of a block is a single point, so the area law means a size-independent constant). -/
theorem area_law_1d (d N D : ℕ) (psi : (Fin N → Fin d) → ℂ)
    (hnorm : ∑ c, ‖psi c‖ ^ 2 = 1)
    (hSchmidt : ∀ x : ℕ, (cutMatrix d N x psi).rank ≤ D) :
    ∀ x : ℕ, vonNeumannEntropy (reducedDensity d N x psi) ≤ Real.log D := by
  intro x
  refine vonNeumannEntropy_le_log_rank (reducedDensity_posSemidef d N x psi) ?_ D ?_
  · rw [trace_reducedDensity, hnorm]; norm_num
  · rw [rank_reducedDensity]; exact hSchmidt x

end Phys


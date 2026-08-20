/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
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

namespace QI

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

lemma hasScalarRecovery_of_knillLaflammeCond (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E : ι → Matrix n n ℂ) (h : KnillLaflammeCond P E) : HasScalarRecovery P E := by
  classical
  obtain ⟨c, hc⟩ := h
  by_cases hP0 : P = 0
  · exact ⟨1, fun _ => 1, by simp, fun a k => ⟨0, by simp [hP0]⟩⟩
  -- a nonzero vector of the code
  obtain ⟨j, hj⟩ : ∃ j : n, P *ᵥ (Pi.single j (1 : ℂ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hP0 ?_
    ext i j
    have := congrFun (hcon j) i
    simpa [Matrix.mulVec_single_one] using this
  set v : n → ℂ := P *ᵥ (Pi.single j (1 : ℂ)) with hvdef
  have hPv : P *ᵥ v = v := by rw [hvdef, Matrix.mulVec_mulVec, hP.idem]
  have hstarv : star v ᵥ* P = star v := by
    have h7 : star (P *ᵥ v) = star v ᵥ* Pᴴ := star_mulVec P v
    rw [hPv, hP.herm] at h7
    exact h7.symm
  have hvv : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hj
  -- scalars are determined by their action on `P`
  have hscal : ∀ s s' : ℂ, s • P = s' • P → s = s' := by
    intro s s' hss
    have : (s - s') • P = 0 := by rw [sub_smul, hss, sub_self]
    rcases smul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hP0
  -- `c` is Hermitian
  have hcH : c.IsHermitian := by
    have hsymm : ∀ a b, (starRingEnd ℂ) (c a b) = c b a := by
      intro a b
      refine hscal _ _ ?_
      have h1 : (P * (E a)ᴴ * E b * P)ᴴ = (c a b • P)ᴴ := by rw [hc a b]
      rw [conjTranspose_smul, hP.herm] at h1
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP.herm, RCLike.star_def] at h1
      rw [← h1, ← hc b a]
      noncomm_ring
    ext a b
    rw [conjTranspose_apply, RCLike.star_def, hsymm b a]
  -- `c` is positive semidefinite
  have hcPSD : c.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hcH fun x => ?_
    set Fx : Matrix n n ℂ := ∑ b, x b • E b with hFx
    have hquad : P * Fxᴴ * Fx * P = (star x ⬝ᵥ (c *ᵥ x)) • P := by
      have expand : P * Fxᴴ * Fx * P
          = ∑ a, ∑ b, ((starRingEnd ℂ) (x a) * x b) • (P * (E a)ᴴ * E b * P) := by
        simp only [hFx, conjTranspose_sum, conjTranspose_smul, RCLike.star_def, Finset.sum_mul,
          Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
      rw [expand]
      have step : ∀ a b, ((starRingEnd ℂ) (x a) * x b) • (P * (E a)ᴴ * E b * P)
          = ((starRingEnd ℂ) (x a) * (c a b * x b)) • P := by
        intro a b
        rw [hc a b, smul_smul]
        ring_nf
      simp only [step, ← Finset.sum_smul]
      congr 1
      simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
    have hLHS : star v ⬝ᵥ ((P * Fxᴴ * Fx * P) *ᵥ v) = star (Fx *ᵥ v) ⬝ᵥ (Fx *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv,
        dotProduct_mulVec, hstarv, dotProduct_mulVec, ← star_mulVec]
    have hRHS : star v ⬝ᵥ (((star x ⬝ᵥ (c *ᵥ x)) • P) *ᵥ v)
        = (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) := by
      rw [smul_mulVec, hPv, dotProduct_smul, smul_eq_mul]
    have hkey : (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) = star (Fx *ᵥ v) ⬝ᵥ (Fx *ᵥ v) := by
      rw [← hRHS, ← hLHS, hquad]
    have hnn : (0 : ℂ) ≤ (star x ⬝ᵥ (c *ᵥ x)) * (star v ⬝ᵥ v) := by
      rw [hkey]; exact dotProduct_star_self_nonneg _
    rw [Complex.le_def] at hnn ⊢
    rw [Complex.lt_def] at hvv
    simp only [Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im] at *
    obtain ⟨h1, h2⟩ := hnn
    obtain ⟨h3, h4⟩ := hvv
    rw [← h4] at h1 h2
    constructor
    · nlinarith
    · nlinarith
  -- diagonalize `c`
  set u : Matrix ι ι ℂ := (hcH.eigenvectorUnitary : Matrix ι ι ℂ) with hudef
  set dd : ι → ℝ := hcH.eigenvalues with hdddef
  have hdnn : ∀ k, 0 ≤ dd k := fun k => hcPSD.eigenvalues_nonneg k
  have hdiag : star u * c * u = diagonal (RCLike.ofReal ∘ dd) := by
    have h8 := hcH.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at h8
  have huu : u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp hcH.eigenvectorUnitary.2
  set F : ι → Matrix n n ℂ := fun k => ∑ a, (u a k) • E a with hFdef
  have horth : ∀ k l, P * (F k)ᴴ * F l * P
      = (if k = l then ((dd k : ℝ) : ℂ) else 0) • P := by
    intro k l
    have expand : P * (F k)ᴴ * F l * P
        = ∑ a, ∑ b, ((starRingEnd ℂ) (u a k) * u b l) • (P * (E a)ᴴ * E b * P) := by
      simp only [hFdef, conjTranspose_sum, conjTranspose_smul, RCLike.star_def, Finset.sum_mul,
        Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [expand]
    have step : ∀ a b, ((starRingEnd ℂ) (u a k) * u b l) • (P * (E a)ᴴ * E b * P)
        = ((starRingEnd ℂ) (u a k) * (c a b * u b l)) • P := by
      intro a b
      rw [hc a b, smul_smul]
      ring_nf
    simp only [step, ← Finset.sum_smul]
    congr 1
    have hentry : ∑ a, ∑ b, ((starRingEnd ℂ) (u a k) * (c a b * u b l))
        = (star u * c * u) k l := by
      simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    rw [hentry, hdiag, diagonal_apply]
    by_cases hkl : k = l
    · rw [if_pos hkl, if_pos hkl]; rfl
    · rw [if_neg hkl, if_neg hkl]
  have hE : ∀ a, ∃ t : ι → ℂ, E a * P = ∑ k, t k • (F k * P) := by
    intro a
    refine ⟨fun k => (starRingEnd ℂ) (u a k), ?_⟩
    have hEa : E a = ∑ k, ((starRingEnd ℂ) (u a k)) • F k := by
      simp only [hFdef, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ b, ∑ k, ((starRingEnd ℂ) (u a k) * u b k) • E b
          = (if b = a then (1 : ℂ) else 0) • E b := by
        intro b
        rw [← Finset.sum_smul]
        congr 1
        have : ∑ k, (starRingEnd ℂ) (u a k) * u b k = (u * star u) b a := by
          simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [this, huu, Matrix.one_apply]
      rw [Finset.sum_congr rfl fun b _ => this b]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_smul]
      · intro b _ hba
        rw [if_neg hba, zero_smul]
      · intro hcon
        exact absurd (Finset.mem_univ a) hcon
    conv_lhs => rw [hEa]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul]
  exact hasScalarRecovery_of_orthogonal_family P hP E F dd hdnn horth hE

/-- **Knill–Laflamme theorem**: a code (given by the orthogonal projection `P` onto the code
subspace) corrects the error set `E` if and only if it satisfies the Knill–Laflamme
conditions. -/

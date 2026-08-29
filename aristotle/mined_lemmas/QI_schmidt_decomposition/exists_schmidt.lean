import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/

theorem exists_schmidt (psi : Fin m → Fin n → ℂ) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp psi s e f := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of psi with hMdef
  have hps : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  set hH : (M * Mᴴ).IsHermitian := hps.1 with hHdef
  set mu : Fin m → ℝ := hH.eigenvalues with hmudef
  set u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)) := hH.eigenvectorBasis with hudef
  have hmu0 : ∀ i, 0 ≤ mu i := hps.eigenvalues_nonneg
  have heig : ∀ i, (M * Mᴴ) *ᵥ (u i).ofLp = mu i • (u i).ofLp := hH.mulVec_eigenvectorBasis
  -- the (unnormalised) vectors in the second factor
  set F : Fin m → Fin n → ℂ := fun k j => ∑ i, M i j * (starRingEnd ℂ) (u k i) with hFdef
  have hHe : ∀ a b, (starRingEnd ℂ) ((M * Mᴴ) a b) = (M * Mᴴ) b a := by
    intro a b
    conv_rhs => rw [← hH]
    rfl
  have hstep : ∀ l i, ∑ i', (M * Mᴴ) i' i * (starRingEnd ℂ) (u l i')
      = (mu l : ℂ) * (starRingEnd ℂ) (u l i) := by
    intro l i
    have key : ∑ i', (M * Mᴴ) i i' * (u l i') = (mu l : ℂ) * u l i := by
      have h := congrFun (heig l) i
      simpa [Matrix.mulVec, dotProduct] using h
    have h2 := congrArg (starRingEnd ℂ) key
    rw [map_sum, map_mul, Complex.conj_ofReal] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i' _ => by rw [map_mul, hHe i i']
  have hMM : ∀ i i', ∑ j, (starRingEnd ℂ) (M i j) * M i' j = (M * Mᴴ) i' i := by
    intro i i'
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by
      simp [Matrix.conjTranspose_apply, mul_comm]
  have huu : ∀ k l, ∑ i, u k i * (starRingEnd ℂ) (u l i) = if k = l then 1 else 0 := by
    intro k l
    have h := orthonormal_iff_ite.mp u.orthonormal l k
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [h]
    simp [eq_comm]
  have hFF : ∀ k l, ∑ j, (starRingEnd ℂ) (F k j) * F l j
      = (mu l : ℂ) * (if k = l then 1 else 0) := by
    intro k l
    calc ∑ j, (starRingEnd ℂ) (F k j) * F l j
        = ∑ j, ∑ i, ∑ i', (u k i * (starRingEnd ℂ) (u l i')) *
            ((starRingEnd ℂ) (M i j) * M i' j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hFdef]
          simp only
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
          simp only [map_mul, Complex.conj_conj]
          ring
      _ = ∑ i, ∑ i', (u k i * (starRingEnd ℂ) (u l i')) *
            ∑ j, ((starRingEnd ℂ) (M i j) * M i' j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i' _ => by rw [Finset.mul_sum]
      _ = ∑ i, u k i * ∑ i', (M * Mᴴ) i' i * (starRingEnd ℂ) (u l i') := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by rw [hMM i i']; ring
      _ = (mu l : ℂ) * ∑ i, u k i * (starRingEnd ℂ) (u l i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hstep l i]; ring
      _ = (mu l : ℂ) * (if k = l then 1 else 0) := by rw [huu k l]
  have hFzero : ∀ k, mu k = 0 → ∀ j, F k j = 0 := by
    intro k hk j
    have h := hFF k k
    rw [if_pos rfl, mul_one, hk, Complex.ofReal_zero] at h
    have h2 : ∑ j, ((Complex.normSq (F k j) : ℝ) : ℂ) = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => Complex.normSq_eq_conj_mul_self
    have h4 : ∑ j, Complex.normSq (F k j) = 0 := by exact_mod_cast h2
    have h5 : Complex.normSq (F k j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp h4 j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp h5
  -- the Schmidt decomposition indexed by the strictly positive eigenvalues
  have key : IsSchmidtDecomp psi (fun k : {k : Fin m // 0 < mu k} => Real.sqrt (mu k.1))
      (fun k => u k.1)
      (fun k => (WithLp.toLp 2 (fun j => ((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j) :
        EuclideanSpace ℂ (Fin n))) := by
    have hsq : ∀ k : {k : Fin m // 0 < mu k}, 0 < Real.sqrt (mu k.1) :=
      fun k => Real.sqrt_pos.mpr k.2
    refine ⟨hsq, u.orthonormal.comp _ Subtype.val_injective, ?_, ?_⟩
    · refine orthonormal_iff_ite.mpr fun k l => ?_
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply]
      have : ∀ j, (((Real.sqrt (mu l.1) : ℂ))⁻¹ * F l.1 j) *
          (starRingEnd ℂ) (((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j)
          = ((Real.sqrt (mu k.1) : ℂ))⁻¹ * ((Real.sqrt (mu l.1) : ℂ))⁻¹ *
            ((starRingEnd ℂ) (F k.1 j) * F l.1 j) := by
        intro j
        simp only [map_mul, map_inv₀, Complex.conj_ofReal]
        ring
      rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, hFF k.1 l.1]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, mul_one]
        have h1 : ((Real.sqrt (mu k.1) : ℂ)) ≠ 0 := by
          exact_mod_cast ne_of_gt (hsq k)
        field_simp
        rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt k.2)]
      · rw [if_neg hkl, if_neg (fun h : k.1 = l.1 => hkl (Subtype.ext h))]
        ring
    · intro i j
      have h1 : ∑ k : {k : Fin m // 0 < mu k},
          ((Real.sqrt (mu k.1) : ℝ) : ℂ) * u k.1 i *
            (((Real.sqrt (mu k.1) : ℂ))⁻¹ * F k.1 j)
          = ∑ k : {k : Fin m // 0 < mu k}, u k.1 i * F k.1 j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 : ((Real.sqrt (mu k.1) : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt (hsq k)
        field_simp
      have h2 : ∑ k : {k : Fin m // 0 < mu k}, u k.1 i * F k.1 j
          = ∑ k : Fin m, u k i * F k j := by
        rw [← Finset.sum_subtype (univ.filter (fun k => 0 < mu k))
          (fun x => by simp) (fun k => u k i * F k j)]
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro k _ hk
        have : mu k = 0 := le_antisymm (by simpa using (not_lt.mp (by simpa using hk))) (hmu0 k)
        rw [hFzero k this j, mul_zero]
      have h3 : ∑ k : Fin m, u k i * F k j = psi i j := by
        have : ∀ k, u k i * F k j = ∑ i', M i' j * ((starRingEnd ℂ) (u k i') * u k i) := by
          intro k
          rw [hFdef]
          simp only
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
        rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_comm]
        have hcomp : ∀ i' : Fin m, ∑ k, (starRingEnd ℂ) (u k i') * u k i
            = if i = i' then 1 else 0 := by
          intro i'
          have h := u.sum_repr' (EuclideanSpace.single i' (1 : ℂ))
          have h2 := congrArg (fun w : EuclideanSpace ℂ (Fin m) => w i) h
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, EuclideanSpace.single_apply] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          simp [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single_apply]
        rw [Finset.sum_congr rfl fun i' _ => by rw [← Finset.mul_sum, hcomp i']]
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl, mul_one]; rfl
        · intro i' _ hi'; rw [if_neg (Ne.symm hi'), mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [h1, h2, h3]
  exact ⟨_, _, _, _, key.reindex (Fintype.equivFin _).symm⟩

/-- **Uniqueness** of the Schmidt coefficients. -/

/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem exists_isSchmidt {m n : ℕ} (ψ : Fin m → Fin n → ℂ) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ),
      IsSchmidt ψ σ u v := by
  classical
  have hpsd : (rho ψ).PosSemidef := by
    have hmul : rho ψ = (Matrix.of ψ) * (Matrix.of ψ)ᴴ := by
      ext i i'
      simp [rho, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hmul]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  set hA : (rho ψ).IsHermitian := hpsd.isHermitian with hAdef
  set μ : Fin m → ℝ := hA.eigenvalues with hμdef
  set b : Fin m → (Fin m → ℂ) := fun i x => (hA.eigenvectorBasis i) x with hbdef
  have hμnn : ∀ i, 0 ≤ μ i := fun i => hpsd.eigenvalues_nonneg i
  have hbon : ∀ i j, cdot (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    have hor := hA.eigenvectorBasis.orthonormal
    rw [orthonormal_iff_ite] at hor
    have h2 := hor i j
    rw [PiLp.inner_apply] at h2
    simpa [cdot, hbdef, RCLike.inner_apply, mul_comm] using h2
  have hbcomp : ∀ x y, ∑ i, b i x * (starRingEnd ℂ) (b i y) = if x = y then 1 else 0 := by
    intro x y
    have hU : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
      Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    have h2 := congrFun (congrFun hU x) y
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hbdef,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h2
  have hbeig : ∀ i x, (rho ψ *ᵥ b i) x = (μ i : ℂ) * b i x := by
    intro i x
    have h2 := congrFun (hA.mulVec_eigenvectorBasis i) x
    simpa [hbdef, hμdef, Pi.smul_apply, Complex.real_smul] using h2
  set P : Fin m → (Fin n → ℂ) := fun i j => ∑ i', (starRingEnd ℂ) (b i i') * ψ i' j with hPdef
  have hPcdot : ∀ a c, cdot (P a) (P c) = (μ a : ℂ) * (if c = a then 1 else 0) := by
    intro a c
    have hpr := cdot_proj ψ (b a) (b c)
    have hfun : (rho ψ *ᵥ b a) = fun x => (μ a : ℂ) * b a x := funext (hbeig a)
    rw [show cdot (P a) (P c) = cdot (fun j => ∑ i, (starRingEnd ℂ) (b a i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (b c i) * ψ i j) from rfl, hpr, hfun, cdot_smul, hbon c a]
  have hPzero : ∀ i, μ i = 0 → ∀ j, P i j = 0 := by
    intro i hi j
    refine eq_zero_of_cdot_self ?_ j
    rw [hPcdot i i, hi]
    simp
  set e : Fin (Fintype.card {i : Fin m // μ i ≠ 0}) ≃ {i : Fin m // μ i ≠ 0} :=
    (Fintype.equivFin {i : Fin m // μ i ≠ 0}).symm with he
  set idx : Fin (Fintype.card {i : Fin m // μ i ≠ 0}) → Fin m := fun k => (e k).1 with hidx
  have hidx_inj : Function.Injective idx := fun k l hkl => e.injective (Subtype.ext hkl)
  have hidx_pos : ∀ k, 0 < μ (idx k) := fun k => lt_of_le_of_ne (hμnn _) (Ne.symm (e k).2)
  have hsq : ∀ k, (Real.sqrt (μ (idx k))) ^ 2 = μ (idx k) := fun k => Real.sq_sqrt (hμnn _)
  have hspos : ∀ k, 0 < Real.sqrt (μ (idx k)) := fun k => Real.sqrt_pos.2 (hidx_pos k)
  have hcne : ∀ k, ((Real.sqrt (μ (idx k)) : ℂ)) ≠ 0 := by
    intro k
    exact_mod_cast ne_of_gt (hspos k)
  have hmu : ∀ k, ((μ (idx k) : ℂ)) = (Real.sqrt (μ (idx k)) : ℂ) ^ 2 := by
    intro k
    rw [show ((Real.sqrt (μ (idx k)) : ℂ)) ^ 2 = ((Real.sqrt (μ (idx k)) ^ 2 : ℝ) : ℂ) by
      push_cast; ring, hsq k]
  refine ⟨Fintype.card {i : Fin m // μ i ≠ 0}, fun k => Real.sqrt (μ (idx k)),
    fun k => b (idx k), fun k j => ((Real.sqrt (μ (idx k)) : ℂ))⁻¹ * P (idx k) j,
    hspos, ?_, ?_, ?_⟩
  · intro k l
    rw [hbon]
    by_cases hkl : k = l
    · simp [hkl]
    · have hne : idx k ≠ idx l := fun hc => hkl (hidx_inj hc)
      simp [hkl, hne]
  · intro k l
    rw [cdot_smul_left, cdot_smul, hPcdot (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, map_inv₀, Complex.conj_ofReal, hmu k]
      have hc := hcne k
      field_simp
      simp
    · have hne : idx l ≠ idx k := fun hc => hkl (hidx_inj hc).symm
      simp [hkl, hne]
  · intro i j
    have hterm : ∀ k, ((Real.sqrt (μ (idx k)) : ℂ)) * b (idx k) i *
        (((Real.sqrt (μ (idx k)) : ℂ))⁻¹ * P (idx k) j) = b (idx k) i * P (idx k) j := by
      intro k
      have hc := hcne k
      field_simp
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    have hsum1 : ∑ k, b (idx k) i * P (idx k) j
        = ∑ x : {i : Fin m // μ i ≠ 0}, b x.1 i * P x.1 j :=
      Equiv.sum_comp e (fun x : {i : Fin m // μ i ≠ 0} => b x.1 i * P x.1 j)
    have hsum2 : ∑ x : {i : Fin m // μ i ≠ 0}, b x.1 i * P x.1 j
        = ∑ i' ∈ Finset.univ.filter (fun i' => μ i' ≠ 0), b i' i * P i' j :=
      (Finset.sum_subtype (Finset.univ.filter (fun i' => μ i' ≠ 0))
        (p := fun i' => μ i' ≠ 0) (fun x => by simp) (fun i' => b i' i * P i' j)).symm
    have hsum3 : ∑ i' ∈ Finset.univ.filter (fun i' => μ i' ≠ 0), b i' i * P i' j
        = ∑ i', b i' i * P i' j := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _ hx
      have hx0 : μ x = 0 := by simpa using hx
      simp [hPzero x hx0]
    have hfin : ∑ i', b i' i * P i' j = ψ i j := by
      have e1 : ∀ i', b i' i * P i' j
          = ∑ i'', (b i' i * (starRingEnd ℂ) (b i' i'')) * ψ i'' j := by
        intro i'
        rw [hPdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i'' _ => by ring
      rw [Finset.sum_congr rfl fun i' _ => e1 i', Finset.sum_comm]
      have e2 : ∀ i'', ∑ i', (b i' i * (starRingEnd ℂ) (b i' i'')) * ψ i'' j
          = (if i = i'' then 1 else 0) * ψ i'' j := by
        intro i''
        rw [← Finset.sum_mul, hbcomp i i'']
      rw [Finset.sum_congr rfl fun i'' _ => e2 i'']
      simp
    rw [hsum1, hsum2, hsum3, hfin]

/-- **Schmidt decomposition.** Every bipartite pure state `ψ` (a unit vector of
`ℂ^m ⊗ ℂ^n`, written in coordinates) admits a Schmidt decomposition
`ψ i j = ∑ k, σ k * u k i * v k j` with strictly positive Schmidt coefficients `σ k`
summing (in squares) to `1` and with orthonormal families `u` and `v`; moreover the
multiset of Schmidt coefficients is uniquely determined by `ψ`. -/

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

namespace QI

open Finset Matrix ComplexConjugate

variable {m n : ℕ}

/-- The coefficient matrix of a bipartite vector `ψ ∈ ℂ^m ⊗ ℂ^n`, where the tensor product is
modelled as `EuclideanSpace ℂ (Fin m × Fin n)`. -/

lemma exists_isSchmidtDecomp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
      (f : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp ψ r σ e f := by
  classical
  have hH : (rho ψ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
  set u : Fin m → EuclideanSpace ℂ (Fin m) := fun a => hH.eigenvectorBasis a with hu
  set μ : Fin m → ℝ := hH.eigenvalues with hmu
  have hun : Orthonormal ℂ u := hH.eigenvectorBasis.orthonormal
  have hip : ∀ b a : Fin m, (inner ℂ (u b) (u a) : ℂ) = if b = a then 1 else 0 :=
    orthonormal_iff_ite.mp hun
  have hcomplete : ∀ i i' : Fin m, ∑ a, u a i * conj (u a i') = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 := Unitary.coe_mul_star_self _
    have h2 := congrFun (congrFun h1 i) i'
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, hu] using h2
  have heig : ∀ (a i : Fin m), ∑ i', rho ψ i i' * u a i' = (μ a : ℂ) * u a i := by
    intro a i
    have h1 := congrFun (hH.mulVec_eigenvectorBasis a) i
    simpa [Matrix.mulVec, dotProduct, hu, hmu] using h1
  set w : Fin m → EuclideanSpace ℂ (Fin n) :=
    fun a => WithLp.toLp 2 (fun j => ∑ i', conj (u a i') * ψ (i', j)) with hw
  have hwapp : ∀ (a : Fin m) (j : Fin n), w a j = ∑ i', conj (u a i') * ψ (i', j) := by
    intro a j; simp [hw]
  have hexpand : ∀ a b : Fin m, (inner ℂ (w a) (w b) : ℂ)
      = ∑ i'', conj (u b i'') * (∑ i', rho ψ i'' i' * u a i') := by
    intro a b
    rw [inner_eq_sum]
    have step1 : ∀ j, conj (w a j) * w b j
        = ∑ i', ∑ i'', (u a i' * conj (ψ (i', j))) * (conj (u b i'') * ψ (i'', j)) := by
      intro j
      rw [hwapp, hwapp, map_sum]
      simp only [map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
    simp only [step1]
    rw [sum_comm3 (fun j i' i'' => (u a i' * conj (ψ (i', j))) * (conj (u b i'') * ψ (i'', j)))]
    refine Finset.sum_congr rfl fun i'' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [rho_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hinner : ∀ a b : Fin m, (inner ℂ (w a) (w b) : ℂ) = if b = a then (μ a : ℂ) else 0 := by
    intro a b
    rw [hexpand a b]
    simp only [heig]
    have hfac : ∑ i'', conj (u b i'') * ((μ a : ℂ) * u a i'')
        = (μ a : ℂ) * ∑ i'', conj (u b i'') * u a i'' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i'' _ => by ring
    rw [hfac, ← inner_eq_sum, hip b a]
    by_cases hba : b = a <;> simp [hba]
  have hmnorm : ∀ a, μ a = ‖w a‖ ^ 2 := by
    intro a
    have h1 : (inner ℂ (w a) (w a) : ℂ) = ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [hinner a a, if_pos rfl] at h1
    exact_mod_cast h1
  have hwzero : ∀ a, μ a = 0 → w a = 0 := by
    intro a ha
    have hn : ‖w a‖ = 0 := by
      have := hmnorm a
      nlinarith [norm_nonneg (w a)]
    exact norm_eq_zero.mp hn
  have hnonneg : ∀ a, 0 ≤ μ a := fun a => by rw [hmnorm a]; positivity
  have hrecon : ∀ (i : Fin m) (j : Fin n), ψ (i, j) = ∑ a, u a i * w a j := by
    intro i j
    have hterm : ∀ a, u a i * w a j = ∑ i', (u a i * conj (u a i')) * ψ (i', j) := by
      intro a
      rw [hwapp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    simp only [hterm]
    rw [Finset.sum_comm]
    have hterm2 : ∀ i' : Fin m, ∑ a, (u a i * conj (u a i')) * ψ (i', j)
        = (if i = i' then 1 else 0) * ψ (i', j) := by
      intro i'
      rw [← Finset.sum_mul, hcomplete i i']
    simp only [hterm2]
    simp
  -- the indices carrying a positive eigenvalue
  set S : Finset (Fin m) := Finset.univ.filter (fun a => 0 < μ a) with hS
  set ι : Fin S.card → Fin m := fun k => ((S.equivFin.symm k : {x // x ∈ S}) : Fin m) with hι
  have hιmem : ∀ k, ι k ∈ S := fun k => (S.equivFin.symm k).2
  have hιpos : ∀ k, 0 < μ (ι k) := by
    intro k
    have hk := hιmem k
    rw [hS, Finset.mem_filter] at hk
    exact hk.2
  have hιinj : Function.Injective ι := Subtype.val_injective.comp S.equivFin.symm.injective
  have hreindex : ∀ g : Fin m → ℂ, ∑ k, g (ι k) = ∑ a ∈ S, g a := by
    intro g
    rw [← Finset.sum_coe_sort S g]
    exact Equiv.sum_comp S.equivFin.symm (fun x : {x // x ∈ S} => g x)
  have hcne : ∀ k, ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) ≠ 0 := by
    intro k
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (hιpos k))
  refine ⟨S.card, fun k => Real.sqrt (μ (ι k)), fun k => u (ι k),
    fun k => (((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k),
    fun k => Real.sqrt_pos.mpr (hιpos k), hun.comp ι hιinj, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro k l
    rw [inner_smul_left, inner_smul_right, hinner (ι k) (ι l)]
    by_cases hkl : k = l
    · subst hkl
      have hsq : Real.sqrt (μ (ι k)) * Real.sqrt (μ (ι k)) = μ (ι k) :=
        Real.mul_self_sqrt (le_of_lt (hιpos k))
      have hcast : ((μ (ι k) : ℝ) : ℂ)
          = ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) * ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsq]
      rw [if_pos rfl, if_pos rfl, hcast, map_inv₀, Complex.conj_ofReal]
      field_simp
      exact div_self (hcne k)
    · rw [if_neg hkl, if_neg (fun hc => hkl (hιinj hc).symm)]
      ring
  · intro i j
    have hcancel : ∀ k, ((Real.sqrt (μ (ι k)) : ℝ) : ℂ) * u (ι k) i
        * ((((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k)) j = u (ι k) i * w (ι k) j := by
      intro k
      have hsmul : ((((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ • w (ι k)) j
          = (((Real.sqrt (μ (ι k)) : ℝ) : ℂ))⁻¹ * w (ι k) j := by simp
      rw [hsmul]
      have := hcne k
      field_simp
    simp only [hcancel]
    rw [hreindex (fun a => u a i * w a j), hrecon i j]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro a _ haS
    have hza : μ a = 0 := by
      rw [hS, Finset.mem_filter] at haS
      simp only [Finset.mem_univ, true_and, not_lt] at haS
      have := hnonneg a
      linarith
    rw [hwzero a hza]
    simp

/-- The Schmidt coefficients can always be sorted in decreasing order. -/

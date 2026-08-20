import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

theorem schmidt_exists {m n : ℕ} (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi s u v := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun j k => psi (j, k) with hMdef
  have hA : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  set b := hA.eigenvectorBasis with hbdef
  set mu := hA.eigenvalues with hmudef
  set w : Fin m → Fin n → ℂ := fun i k => ∑ j, (starRingEnd ℂ) (b i j) * M j k with hwdef
  -- the eigenvalue equation, in coordinates
  have heig : ∀ i a, ∑ j, (M * Mᴴ) a j * b i j = (mu i : ℂ) * b i a := by
    intro i a
    have h := congrFun (hA.mulVec_eigenvectorBasis i) a
    simpa [Matrix.mulVec, dotProduct, Complex.real_smul] using h
  -- the vectors `w i` are orthogonal, with squared norms the eigenvalues
  have gram : ∀ i l, ∑ k, (starRingEnd ℂ) (w i k) * w l k
      = (mu i : ℂ) * (if l = i then 1 else 0) := by
    intro i l
    have e0 : ∑ k, (starRingEnd ℂ) (w i k) * w l k
        = ∑ a, (starRingEnd ℂ) (b l a) * ∑ j, (M * Mᴴ) a j * b i j := by
      have e1 : ∀ k, (starRingEnd ℂ) (w i k) * w l k
          = ∑ j, ∑ a, (b i j * (starRingEnd ℂ) (M j k)) * ((starRingEnd ℂ) (b l a) * M a k) := by
        intro k
        rw [hwdef]
        simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_mul_sum]
      simp only [e1]
      rw [Finset.sum_comm]
      have e2 : ∀ j : Fin m, ∑ k, ∑ a, (b i j * (starRingEnd ℂ) (M j k)) *
            ((starRingEnd ℂ) (b l a) * M a k)
          = ∑ a, ∑ k, (b i j * (starRingEnd ℂ) (M j k)) * ((starRingEnd ℂ) (b l a) * M a k) :=
        fun j => Finset.sum_comm
      simp only [e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Matrix.conjTranspose_apply]; ring
    rw [e0]
    simp only [heig]
    have e3 : ∑ a, (starRingEnd ℂ) (b l a) * ((mu i : ℂ) * b i a)
        = (mu i : ℂ) * (inner ℂ (b l) (b i)) := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by simp [RCLike.inner_apply]; ring
    rw [e3, (orthonormal_iff_ite.mp b.orthonormal) l i]
  have hsq : ∀ i, mu i = ∑ k, ‖w i k‖ ^ 2 := by
    intro i
    have h := gram i i
    rw [if_pos rfl, mul_one] at h
    have h2 : (∑ k, (starRingEnd ℂ) (w i k) * w i k) = ((∑ k, ‖w i k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm, Complex.mul_conj']
    rw [h2] at h
    exact_mod_cast h.symm
  have hmupos : ∀ i, 0 ≤ mu i := fun i => by rw [hsq i]; positivity
  have hw0 : ∀ i, mu i = 0 → ∀ k, w i k = 0 := by
    intro i hi k
    have h := hsq i
    rw [hi] at h
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h.symm k
      (Finset.mem_univ k)
    simpa using h3
  have hrecon : ∀ j k, M j k = ∑ i, b i j * w i k := by
    intro j k
    have h := b.sum_repr' (WithLp.toLp 2 (fun j => M j k) : EuclideanSpace ℂ (Fin m))
    have h2 := congrArg (fun (x : EuclideanSpace ℂ (Fin m)) => x j) h
    simp only [PiLp.inner_apply, RCLike.inner_apply] at h2
    simp at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  -- the indices with nonzero eigenvalue
  set S : Finset (Fin m) := Finset.univ.filter (fun i => mu i ≠ 0) with hSdef
  have hmemS : ∀ x, x ∈ S ↔ mu x ≠ 0 := by
    intro x; rw [hSdef, Finset.mem_filter]; simp
  set g : Fin S.card → Fin m := fun i => ((S.equivFin.symm i : {x // x ∈ S}) : Fin m) with hgdef
  have hgne : ∀ i, mu (g i) ≠ 0 := fun i => (hmemS _).mp (S.equivFin.symm i).2
  have hginj : Function.Injective g := by
    intro i j hij
    have h : (S.equivFin.symm i) = (S.equivFin.symm j) := Subtype.ext hij
    simpa using h
  have hgpos : ∀ i, 0 < Real.sqrt (mu (g i)) :=
    fun i => Real.sqrt_pos.mpr (lt_of_le_of_ne (hmupos _) (Ne.symm (hgne i)))
  have hsqrt_ne : ∀ i, ((Real.sqrt (mu (g i)) : ℂ)) ≠ 0 := by
    intro i
    exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt (hgpos i))
  have hsqrt_sq : ∀ i, ((Real.sqrt (mu (g i)) : ℂ)) ^ 2 = (mu (g i) : ℂ) := by
    intro i
    have : Real.sqrt (mu (g i)) ^ 2 = mu (g i) := Real.sq_sqrt (hmupos _)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  refine ⟨S.card, fun i => Real.sqrt (mu (g i)), fun i => b (g i),
    fun i => (WithLp.toLp 2 (fun k => ((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) :
      EuclideanSpace ℂ (Fin n)), hgpos, b.orthonormal.comp g hginj, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i l
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    have hcalc : ∑ k, (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) *
        (((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k)
        = ((Real.sqrt (mu (g i)) : ℂ))⁻¹ * ((Real.sqrt (mu (g l)) : ℂ))⁻¹ *
            ((mu (g i) : ℂ) * (if g l = g i then 1 else 0)) := by
      rw [← gram (g i) (g l), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    have hswap : ∑ k, ((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k *
        (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k)
        = ∑ k, (starRingEnd ℂ) (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) *
            (((Real.sqrt (mu (g l)) : ℂ))⁻¹ * w (g l) k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hswap, hcalc]
    by_cases hil : i = l
    · subst hil
      rw [if_pos rfl, if_pos rfl, mul_one]
      field_simp
      rw [hsqrt_sq i, div_self (Complex.ofReal_ne_zero.mpr (hgne i))]
    · rw [if_neg hil, if_neg (fun hc => hil (hginj hc).symm)]
      ring
  · intro j k
    have hzero : ∀ x ∈ (Finset.univ : Finset (Fin m)), x ∉ S → b x j * w x k = 0 := by
      intro x _ hx
      have hx0 : mu x = 0 := by
        by_contra hne
        exact hx ((hmemS x).mpr hne)
      rw [hw0 x hx0 k, mul_zero]
    have step : ∑ i, b i j * w i k = ∑ i : Fin S.card, (Real.sqrt (mu (g i)) : ℂ) * b (g i) j *
        (((Real.sqrt (mu (g i)) : ℂ))⁻¹ * w (g i) k) := by
      rw [← Finset.sum_subset (Finset.subset_univ S) hzero,
        ← Finset.sum_coe_sort S (fun i => b i j * w i k),
        ← Equiv.sum_comp (S.equivFin.symm)
          (fun (x : {x // x ∈ S}) => b (x : Fin m) j * w (x : Fin m) k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hgi : ((S.equivFin.symm i : {x // x ∈ S}) : Fin m) = g i := rfl
      rw [hgi]
      calc b (g i) j * w (g i) k
          = (((Real.sqrt (mu (g i)) : ℂ)) * ((Real.sqrt (mu (g i)) : ℂ))⁻¹) *
              (b (g i) j * w (g i) k) := by
            rw [mul_inv_cancel₀ (hsqrt_ne i), one_mul]
        _ = _ := by ring
    have hpsi : psi (j, k) = M j k := rfl
    rw [hpsi, hrecon j k, step]


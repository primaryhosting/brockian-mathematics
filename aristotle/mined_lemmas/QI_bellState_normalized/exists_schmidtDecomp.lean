import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma exists_schmidtDecomp (psi : Fin m × Fin n → ℂ) : Nonempty (SchmidtDecomp psi) := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun k => eigMu psi k ≠ 0) with hSdef
  set kk : Fin S.card → Fin m := fun t => ((S.equivFin.symm t : S) : Fin m) with hkkdef
  have hkk_mem : ∀ t, kk t ∈ S := fun t => (S.equivFin.symm t).2
  have hkk_inj : Function.Injective kk := by
    intro a b hab
    have h1 : (S.equivFin.symm a) = (S.equivFin.symm b) := Subtype.ext hab
    simpa using congrArg S.equivFin h1
  have hmu_ne : ∀ t, eigMu psi (kk t) ≠ 0 := by
    intro t
    have := hkk_mem t
    rw [hSdef, Finset.mem_filter] at this
    exact this.2
  have hmu_pos : ∀ t, 0 < eigMu psi (kk t) := fun t =>
    lt_of_le_of_ne (eigMu_nonneg psi (kk t)) (Ne.symm (hmu_ne t))
  have hsqrt_pos : ∀ t, 0 < Real.sqrt (eigMu psi (kk t)) := fun t => Real.sqrt_pos.2 (hmu_pos t)
  have hsqrt_sq : ∀ t, Real.sqrt (eigMu psi (kk t)) ^ 2 = eigMu psi (kk t) := fun t =>
    Real.sq_sqrt (eigMu_nonneg psi (kk t))
  refine ⟨{ rank := S.card
            lam := fun t => Real.sqrt (eigMu psi (kk t))
            e := fun t => eigVec psi (kk t)
            f := fun t j => ((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j
            lam_pos := hsqrt_pos
            e_orthonormal := ?_
            f_orthonormal := ?_
            eq_sum := ?_ }⟩
  · intro t s
    rw [eigVec_orthonormal]
    by_cases h : t = s
    · simp [h]
    · rw [if_neg (fun hc => h (hkk_inj hc)), if_neg h]
  · intro t s
    have hct : ((Real.sqrt (eigMu psi (kk t)) : ℂ)) ≠ 0 := by
      simpa using (hsqrt_pos t).ne'
    have hcs : ((Real.sqrt (eigMu psi (kk s)) : ℂ)) ≠ 0 := by
      simpa using (hsqrt_pos s).ne'
    have hstep : ∑ j, (starRingEnd ℂ) (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j) *
        (((Real.sqrt (eigMu psi (kk s)) : ℂ))⁻¹ * wvec psi (kk s) j)
        = (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * ((Real.sqrt (eigMu psi (kk s)) : ℂ))⁻¹) *
          ∑ j, (starRingEnd ℂ) (wvec psi (kk t) j) * wvec psi (kk s) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hstep, wvec_inner]
    by_cases h : t = s
    · subst h
      rw [if_pos rfl]
      field_simp
      rw [← Complex.ofReal_pow, hsqrt_sq t]
      simp
    · rw [if_neg (fun hc => h (hkk_inj hc)), if_neg h, mul_zero]
  · intro i j
    have hterm : ∀ t : Fin S.card,
        ((Real.sqrt (eigMu psi (kk t)) : ℝ) : ℂ) * eigVec psi (kk t) i *
          (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j)
          = eigVec psi (kk t) i * wvec psi (kk t) j := by
      intro t
      have hct : ((Real.sqrt (eigMu psi (kk t)) : ℂ)) ≠ 0 := by
        simpa using (hsqrt_pos t).ne'
      field_simp
    rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hterm t]
    have hre : ∑ t : Fin S.card, eigVec psi (kk t) i * wvec psi (kk t) j
        = ∑ k ∈ S, eigVec psi k i * wvec psi k j := by
      rw [Equiv.sum_comp S.equivFin.symm (fun x : S => eigVec psi (x : Fin m) i *
        wvec psi (x : Fin m) j)]
      exact Finset.sum_coe_sort S (fun k => eigVec psi k i * wvec psi k j)
    rw [hre]
    have hall : ∑ k ∈ S, eigVec psi k i * wvec psi k j
        = ∑ k : Fin m, eigVec psi k i * wvec psi k j := by
      refine Finset.sum_subset (Finset.subset_univ S) fun k _ hk => ?_
      have hk0 : eigMu psi k = 0 := by
        rw [hSdef, Finset.mem_filter] at hk
        simpa using not_and.1 hk (Finset.mem_univ k)
      rw [wvec_eq_zero psi k hk0]
      simp
    rw [hall]
    exact psi_eq_sum psi i j

/-! ### Main theorem -/

/-- **Schmidt decomposition**: every bipartite pure state `psi` on `ℂ^m ⊗ ℂ^n` admits a
decomposition `psi (i, j) = ∑ k, lam k * e k i * f k j` with positive Schmidt coefficients
`lam k` (whose squares sum to `1`) and orthonormal families `e`, `f`; moreover the multiset
of Schmidt coefficients is the same for any two such decompositions. -/

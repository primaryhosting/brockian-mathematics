import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Statement: A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Phys

/-- A vector and its image under an antiunitary time-reversal operator squaring to `-1`
are linearly independent (the algebraic heart of Kramers' theorem). -/

theorem kramers_pair_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ⋆[ℂ] V) (hT : ∀ v, T (T v) = -v) (v : V) (hv : v ≠ 0) :
    LinearIndependent ℂ ![v, T v] := by
  have hsmul : ∀ (a b : ℂ), a • v = b • v → a = b := by
    intro a b hab
    by_contra hne
    have h0 : (a - b) • v = 0 := by
      rw [sub_smul, hab, sub_self]
    have : v = 0 := by
      have := congrArg (fun w => (a - b)⁻¹ • w) h0
      simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using this
    exact hv this
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hv
  · -- `T v = c • v` with `c = -s/t`, then `T (T v) = |c|^2 • v = -v` forces `|c|^2 = -1`
    have hTv : T v = (-(s / t)) • v := by
      have : t • T v = (-s) • v := by
        rw [neg_smul, eq_comm, neg_eq_iff_add_eq_zero]
        exact hst
      have := congrArg (fun w => t⁻¹ • w) this
      simpa [smul_smul, inv_mul_cancel₀ ht, div_eq_inv_mul, mul_comm] using this
    have h2 : T (T v) = (starRingEnd ℂ (-(s / t)) * (-(s / t))) • v := by
      rw [hTv, map_smulₛₗ, hTv, smul_smul]
    rw [hT v] at h2
    have h3 : (-1 : ℂ) = starRingEnd ℂ (-(s / t)) * (-(s / t)) := by
      apply hsmul
      rw [← h2]
      simp
    set c : ℂ := -(s / t) with hc
    have h4 : (Complex.normSq c : ℂ) = -1 := by
      rw [h3, Complex.normSq_eq_conj_mul_self]
    have h5 : Complex.normSq c = -1 := by exact_mod_cast h4
    have := Complex.normSq_nonneg c
    linarith [h5 ▸ this]

/-- **Kramers degeneracy.**  Let `V` be a complex vector space carrying an antilinear
time-reversal operator `T` with `T² = -1` (a half-integer-spin system), and let `H` be a
Hamiltonian commuting with `T`.  Then for every eigenvector `v` of `H` with real eigenvalue `e`,
the vector `T v` is an eigenvector with the *same* eigenvalue, linearly independent from `v`;
consequently every energy level has degeneracy at least two. -/

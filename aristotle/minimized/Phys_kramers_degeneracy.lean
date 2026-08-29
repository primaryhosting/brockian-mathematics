import Mathlib
/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command in a file
-- (a module doc comment before `import Mathlib` is a hard parse error), so the
-- requested header comment is placed immediately after the single import.

namespace Phys

/-- **Kramers degeneracy.**

Let `V` be a complex vector space (the state space of a quantum system), let
`T : V →ₛₗ[starRingEnd ℂ] V` be the (conjugate-linear) time-reversal operator of a
half-integer-spin system, so that `T ∘ T = -1`, and let `H` be a linear operator
(the Hamiltonian) commuting with `T` (time-reversal invariance).

Then every eigenvector `v ≠ 0` of `H` with real eigenvalue `lam` gives rise to a second
eigenvector `T v` for the same eigenvalue, and `v`, `T v` are linearly independent:
the level `lam` is (at least) doubly degenerate. -/

theorem kramers_degeneracy
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₛₗ[starRingEnd ℂ] V) (hT2 : ∀ v, T (T v) = -v)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ v, H (T v) = T (H v))
    (lam : ℝ) (v : V) (hv : v ≠ 0) (hHv : H v = (lam : ℂ) • v) :
    H (T v) = (lam : ℂ) • T v ∧ LinearIndependent ℂ ![v, T v] := by
  constructor
  · rw [hcomm, hHv, map_smulₛₗ]
    simp
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    -- Apply `T` to the relation `s • v + t • T v = 0`.
    have hT : (starRingEnd ℂ) s • T v - (starRingEnd ℂ) t • v = 0 := by
      have h := congrArg T hst
      rw [map_add, map_smulₛₗ, map_smulₛₗ, hT2, map_zero] at h
      rw [← h]; module
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨by simpa [hv] using smul_eq_zero.1 hst, rfl⟩
    · exfalso
      -- From the original relation, `T v = -(s / t) • v`.
      have h1 : t • T v = (-s) • v := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have hTv : T v = (-(s / t)) • v :=
        calc T v = (t⁻¹ * t) • T v := by rw [inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (t • T v) := by rw [mul_smul]
          _ = t⁻¹ • ((-s) • v) := by rw [h1]
          _ = (-(s / t)) • v := by rw [smul_smul]; congr 1; field_simp
      rw [hTv, smul_smul, ← sub_smul] at hT
      have hcoef : (starRingEnd ℂ) s * -(s / t) - (starRingEnd ℂ) t = 0 := by
        rcases smul_eq_zero.1 hT with h | h
        · exact h
        · exact absurd h hv
      have hst2 : (starRingEnd ℂ) s * s + (starRingEnd ℂ) t * t = 0 := by
        field_simp at hcoef
        linear_combination -hcoef
      have habs : s.re * s.re + s.im * s.im + (t.re * t.re + t.im * t.im) = 0 := by
        simpa using congrArg Complex.re hst2
      have htre : t.re = 0 := by
        nlinarith [mul_self_nonneg s.re, mul_self_nonneg s.im, mul_self_nonneg t.re,
          mul_self_nonneg t.im]
      have htim : t.im = 0 := by
        nlinarith [mul_self_nonneg s.re, mul_self_nonneg s.im, mul_self_nonneg t.re,
          mul_self_nonneg t.im]
      exact ht (Complex.ext (by simpa using htre) (by simpa using htim))

/-- **Kramers degeneracy, dimension form.** Under time-reversal invariance with `T ∘ T = -1`
(half-integer spin), every occupied energy level `lam` of the Hamiltonian `H` has an
eigenspace of dimension at least two. -/

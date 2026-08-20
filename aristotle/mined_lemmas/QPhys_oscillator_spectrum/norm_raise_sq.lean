import RequestProject.Main

/-!
# A concrete model: the Fock space of finitely supported sequences

This file constructs an explicit `QPhys.LadderSystem`, showing that the hypotheses of
`QPhys.oscillator_spectrum` are consistent (non-vacuous).

The state space is `ℕ →₀ ℂ`, the space of finitely supported complex sequences,
with the usual `ℓ²` inner product `⟪f, g⟫ = ∑ conj (f i) * g i`.  The basis vector
`|n⟩ = single n 1` plays the role of the `n`-th excited state, and the ladder operators
act by `a |n⟩ = √n |n-1⟩`, `a† |n⟩ = √(n+1) |n+1⟩`.
-/

open scoped InnerProductSpace

namespace QPhys

namespace Fock

/-- The `ℓ²` inner product on finitely supported complex sequences. -/

lemma norm_raise_sq (x : H) :
    (‖L.raise x‖ ^ 2 : ℝ) = (⟪x, numberOp L x⟫_ℂ).re + ‖x‖ ^ 2 := by
  have h1 : ⟪L.raise x, L.raise x⟫_ℂ = ⟪L.lower (L.raise x), x⟫_ℂ := by
    rw [L.adjoint]
  have h2 : L.lower (L.raise x) = numberOp L x + x := by
    have h := sub_eq_iff_eq_add.mp (L.comm x)
    rw [numberOp_apply, h]; abel
  rw [h2] at h1
  have h3 : ⟪numberOp L x + x, x⟫_ℂ = ⟪numberOp L x, x⟫_ℂ + ⟪x, x⟫_ℂ := inner_add_left _ _ _
  have h4 : ⟪numberOp L x, x⟫_ℂ = (starRingEnd ℂ) ⟪x, numberOp L x⟫_ℂ := by
    rw [inner_conj_symm]
  rw [h3, h4] at h1
  have h5 := congrArg Complex.re h1
  have h6 : (⟪numberOp L x, x⟫_ℂ).re = (⟪x, numberOp L x⟫_ℂ).re := by
    rw [h4]
    exact Complex.conj_re _
  rw [← h6]
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.add_re, Complex.conj_re,
    inner_self_eq_norm_sq] using h5

end Basic

section Eigen

variable (L : LadderSystem H)

/-- An eigenvalue of the number operator is the nonnegative real number `‖a x‖² / ‖x‖²`. -/

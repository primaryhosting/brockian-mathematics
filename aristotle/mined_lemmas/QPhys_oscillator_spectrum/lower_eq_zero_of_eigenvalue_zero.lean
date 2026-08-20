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

lemma lower_eq_zero_of_eigenvalue_zero {x : H} (hE : numberOp L x = (0 : ℂ) • x) :
    L.lower x = 0 := by
  have h := inner_numberOp_self L x
  rw [hE] at h
  simp only [zero_smul, inner_zero_right] at h
  have : (‖L.lower x‖ : ℝ) ^ 2 = 0 := by exact_mod_cast h.symm
  have : (‖L.lower x‖ : ℝ) = 0 := by nlinarith [norm_nonneg (L.lower x)]
  exact norm_eq_zero.mp this

/-- Descent step: if `x` is a nonzero eigenvector of `N` with eigenvalue `r` and
`a x ≠ 0`, then `a x` is an eigenvector with eigenvalue `r - 1`. -/

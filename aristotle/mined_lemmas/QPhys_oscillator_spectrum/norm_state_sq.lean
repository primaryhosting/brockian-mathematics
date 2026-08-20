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

lemma norm_state_sq (n : ℕ) : (‖state L n‖ ^ 2 : ℝ) = (n ! : ℝ) * ‖L.vacuum‖ ^ 2 := by
  induction n with
  | zero => simp [state_zero]
  | succ n ih =>
      have h := norm_raise_sq L (state L n)
      rw [numberOp_state, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
      have h' : (‖L.raise (state L n)‖ ^ 2 : ℝ) = (n : ℝ) * ‖state L n‖ ^ 2 + ‖state L n‖ ^ 2 := by
        simpa [Complex.mul_re, ← Complex.ofReal_pow] using h
      rw [state_succ, h', ih, Nat.factorial_succ]
      push_cast
      ring


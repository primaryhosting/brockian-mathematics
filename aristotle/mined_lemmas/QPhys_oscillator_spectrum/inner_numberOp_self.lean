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

lemma inner_numberOp_self (x : H) : ⟪x, numberOp L x⟫_ℂ = ((‖L.lower x‖ ^ 2 : ℝ) : ℂ) := by
  rw [numberOp_apply, ← L.adjoint, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `‖a† x‖² = re ⟪x, N x⟫ + ‖x‖²`. -/

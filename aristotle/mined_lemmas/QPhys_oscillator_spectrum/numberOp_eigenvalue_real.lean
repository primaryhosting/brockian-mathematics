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

lemma numberOp_eigenvalue_real {E : ℂ} {x : H} (hx : x ≠ 0) (hE : numberOp L x = E • x) :
    E = ((‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_numberOp_self L x
  rw [hE, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx2 : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hxn)
  push_cast at h ⊢
  rw [eq_div_iff hx2]
  exact_mod_cast h

/-- If a number-operator eigenvector has eigenvalue `0`, it is annihilated by `a`. -/

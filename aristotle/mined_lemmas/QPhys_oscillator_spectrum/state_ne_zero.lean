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

lemma state_ne_zero (n : ℕ) : state L n ≠ 0 := by
  intro h
  have h1 := norm_state_sq L n
  rw [h] at h1
  simp only [norm_zero] at h1
  have hv : (0 : ℝ) < ‖L.vacuum‖ := norm_pos_iff.mpr L.vacuum_ne_zero
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpos : (0 : ℝ) < (n ! : ℝ) * ‖L.vacuum‖ ^ 2 := mul_pos hfac (pow_pos hv 2)
  rw [← h1] at hpos
  norm_num at hpos

end Eigen

/-- **Spectrum of the quantum harmonic oscillator.**

For a ladder system `L` on a complex inner product space (an annihilation operator `a`,
a creation operator `a†` formally adjoint to it with `[a, a†] = 1`, and a nonzero vacuum
vector annihilated by `a`), the set of eigenvalues of the Hamiltonian
`Ĥ = ℏω (a† a + 1/2)` is exactly `{ℏω (n + 1/2) : n ∈ ℕ}`. -/

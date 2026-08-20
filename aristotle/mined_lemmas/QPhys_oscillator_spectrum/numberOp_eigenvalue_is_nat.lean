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

lemma numberOp_eigenvalue_is_nat {E : ℂ} {x : H} (hx : x ≠ 0) (hE : numberOp L x = E • x) :
    ∃ n : ℕ, E = (n : ℂ) := by
  set r : ℝ := ‖L.lower x‖ ^ 2 / ‖x‖ ^ 2 with hrdef
  have hE' : E = ((r : ℝ) : ℂ) := numberOp_eigenvalue_real L hx hE
  have hEr : numberOp L x = ((r : ℝ) : ℂ) • x := by rw [hE, hE']
  obtain ⟨m, hm⟩ :=
    numberOp_eigenvalue_nat_of_le L ⌈r⌉₊ r x hx hEr (Nat.le_ceil r)
  exact ⟨m, by rw [hE', hm]; norm_cast⟩

/-- The `n`-th excited state `(a†)ⁿ |0⟩`. -/

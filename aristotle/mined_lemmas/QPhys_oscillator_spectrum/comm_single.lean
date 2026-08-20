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

lemma comm_single (m : ℕ) (c : ℂ) :
    lower (raise (Finsupp.single m c)) - raise (lower (Finsupp.single m c)) =
      Finsupp.single m c := by
  rw [raise_single, lower_single, lower_single, raise_single]
  rcases m with _ | k
  · rw [show c * wt (0 + 1) * wt (0 + 1) = c by rw [mul_assoc, wt_mul_self]; norm_num,
      show c * wt 0 * wt (0 - 1 + 1) = 0 by rw [wt_zero]; ring, Finsupp.single_zero, sub_zero]
  · rw [show k + 1 + 1 - 1 = k + 1 from rfl, show k + 1 - 1 + 1 = k + 1 from rfl,
      mul_assoc, wt_mul_self, mul_assoc, wt_mul_self, ← Finsupp.single_sub]
    congr 1
    push_cast
    ring


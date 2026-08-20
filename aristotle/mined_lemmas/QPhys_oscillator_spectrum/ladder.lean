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

noncomputable def ladder : LadderSystem (ℕ →₀ ℂ) where
  lower := lower
  raise := raise
  adjoint := adjoint
  comm := comm
  vacuum := Finsupp.single 0 1
  vacuum_ne_zero := by
    simp [Finsupp.single_eq_zero]
  lower_vacuum := by
    rw [lower_single]
    simp [wt_zero]

end Fock

/-- The hypotheses of `QPhys.oscillator_spectrum` are satisfiable: there is a concrete
ladder system, on the Fock space of finitely supported complex sequences. -/

/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

lemma fockH_apply (hbar omegac : ℝ) (x : ℕ →₀ ℂ) :
    fockH hbar omegac x = ((hbar * omegac : ℝ) : ℂ) • (adagOp (aOp x) + (1 / 2 : ℂ) • x) := rfl

/-- **The Landau spectrum of the Fock model.**  For `ℏ, ω_c > 0`, a complex number `E` is an
eigenvalue of `H = ℏ ω_c (a† a + 1/2)` if and only if `E = ℏ ω_c (n + 1/2)` for some `n : ℕ`.
The forward direction is the abstract theorem `Frontier.landau_levels`; the backward direction
exhibits the `n`-th number state as an eigenvector, so that all Landau levels really occur. -/

import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

theorem landau_levels_fock (q B m hbar : ℝ) :
    ∀ n : ℕ, ladderState fockB fockVacuum n ≠ 0 ∧
      fockHamiltonian hbar (cyclotronFrequency q B m) (ladderState fockB fockVacuum n)
        = ((landauEnergy hbar (cyclotronFrequency q B m) n : ℝ) : ℂ)
          • ladderState fockB fockVacuum n :=
  landau_levels q B m hbar fockA fockB fock_comm fock_adjoint fockVacuum fockVacuum_ne_zero
    fockA_vacuum (fockHamiltonian hbar (cyclotronFrequency q B m)) (by
      intro x
      simp [fockHamiltonian])

end Frontier

import Mathlib

/-!
# A concrete Bargmann–Fock model for the Landau ladder operators

This file constructs an explicit complex inner product space carrying operators `a`, `b`
satisfying `[a, b] = 1`, with `b` adjoint to `a`, together with a nonzero vacuum vector
annihilated by `a`. It witnesses that the hypotheses of the Landau level theorem in
`RequestProject.Main` are satisfiable, so that theorem is not vacuous.

The space is `ℕ →₀ ℂ`, the space of polynomial coefficient sequences, equipped with the
Bargmann inner product `⟪p, q⟫ = ∑ n, n! * conj (p n) * q n`; `b` is multiplication by the
variable `X` and `a` is differentiation `d/dX`.
-/

open scoped ComplexConjugate Nat

namespace Frontier

/-- The Bargmann inner product on coefficient sequences. -/

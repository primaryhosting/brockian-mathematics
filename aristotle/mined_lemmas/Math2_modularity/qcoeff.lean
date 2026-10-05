/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

noncomputable def qcoeff {N : ℕ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) : ℂ :=
  (ModularFormClass.qExpansion 1 f).coeff n

/-- Modularity of an *integral* Weierstrass curve `E`:  there is a level `N ≥ 1` and a
weight-two cusp form `f` for `Γ₀(N)` which is normalised (`a₁(f) = 1`) and whose
`q`-expansion coefficients satisfy the Hecke multiplicativity relations of a normalised
eigenform of level `N`, and such that `a_p(f) = a_p(E)` for every prime `p` not dividing
the level and at which the model `E` has good reduction.

This is the classical `a_p`-form of the Shimura–Taniyama–Weil statement: the Hasse–Weil
`L`-function of `E` coincides with the `L`-function of a weight-two normalised eigenform
of level `N`, up to the finitely many Euler factors at primes dividing `N` or `Δ(E)`. -/

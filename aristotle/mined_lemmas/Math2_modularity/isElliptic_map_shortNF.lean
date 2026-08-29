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

lemma isElliptic_map_shortNF (A B : ℤ) (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, WeierstrassCurve.map_Δ,
    Delta_shortNF]
  have : (4 * A ^ 3 + 27 * B ^ 2 : ℚ) ≠ 0 := by exact_mod_cast h
  simpa using this

/-- **Reduction of the modularity theorem to integral short Weierstrass models.**

If every integral short Weierstrass curve `y² = x³ + Ax + B` (`A B : ℤ`) with non-vanishing
discriminant is modular, then every elliptic curve over `ℚ` is modular
(`Math2.ModularityStatement`, the Shimura–Taniyama–Weil statement).

The proof normalises an arbitrary elliptic curve over `ℚ` to an isomorphic integral short
Weierstrass model, using `Math2.exists_integral_shortModel`. -/

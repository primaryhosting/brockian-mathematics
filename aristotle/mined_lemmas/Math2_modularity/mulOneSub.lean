/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the statement of the modularity theorem (Taniyama–Shimura–Wiles)
for elliptic curves over `ℚ`, given by integral Weierstrass models, together with a
fully kernel-checked numerical verification of the modularity prediction for the
elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, whose associated newform is the
eta product `η(z)² η(11z)²`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math2

open WeierstrassCurve CongruenceSubgroup MatrixGroups ModularFormClass UpperHalfPlane

/-! ## Point counts of the reductions of a Weierstrass model -/

/-- The number of points of the reduction mod `p` of an integral Weierstrass model `W`:
the affine solutions of the Weierstrass equation over `ℤ/p`, plus the point at infinity.
(For `p = 0` this is junk, and it is only used for primes of good reduction.) -/

def mulOneSub (k : ℕ) (c : List ℤ) : List ℤ :=
  (List.range c.length).map fun n => c.getD n 0 - if k ≤ n then c.getD (n - k) 0 else 0

/-- The coefficients of `q * ∏_{n=1}^{M} (1 - qⁿ)² (1 - q^{11n})²`, i.e. of the eta
product `η(z)² η(11z)²`, truncated: this list has length `M + 2` and its entries in
positions `0, …, M + 1` are the true coefficients of the eta product. -/

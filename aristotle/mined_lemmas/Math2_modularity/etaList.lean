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

def etaList (M : ℕ) : List ℤ :=
  (List.range' 1 M).foldl
    (fun c n => mulOneSub n (mulOneSub n (mulOneSub (11 * n) (mulOneSub (11 * n) c))))
    (0 :: 1 :: List.replicate M 0)

/-- The `n`-th `q`-expansion coefficient of the weight-two level-eleven newform
`η(z)² η(11z)² = q ∏_{n ≥ 1} (1 - qⁿ)² (1 - q^{11n})²`. -/

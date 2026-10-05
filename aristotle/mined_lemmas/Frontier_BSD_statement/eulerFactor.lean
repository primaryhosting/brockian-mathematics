import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: in Lean 4.28 the `import` command must be the very first command in a file, so the
required header docstring appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

We work with an elliptic curve over `ℚ` presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (any elliptic curve over `ℚ` admits such a model).

* The *algebraic rank* is the rank of the Mordell–Weil group `E(ℚ)`, defined as the
  dimension of `ℚ ⊗_ℤ E(ℚ)` over `ℚ`.
* The *analytic rank* is the order of vanishing at `s = 1` of the Hasse–Weil `L`-function,
  where the `L`-function is specified by its Euler product on the half-plane of absolute
  convergence together with analytic continuation to `ℂ`.

Birch–Swinnerton-Dyer asserts that these two numbers agree.
-/

section Rank

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve given by the integral Weierstrass
model `W`, i.e. the group of rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The *algebraic rank* of `W`: the rank of the Mordell–Weil group `E(ℚ)`, defined as
`dim_ℚ (ℚ ⊗_ℤ E(ℚ))`. -/

noncomputable def eulerFactor (W : WeierstrassCurve ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  if (p : ℤ) ∣ W.Δ then
    1 - (traceOfFrobenius W p : ℂ) * (p : ℂ) ^ (-s)
  else
    1 - (traceOfFrobenius W p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s)

/-- `L` is *the* Hasse–Weil `L`-function of the elliptic curve `W`: it is entire, and on the
half-plane of absolute convergence `Re s > 3/2` it is given by the Euler product
`L(E, s) = ∏_p (local factor at p)⁻¹`.

(The Hasse–Weil `L`-function of an elliptic curve over `ℚ` is known to exist and to be
entire, by modularity; we take this predicate as the specification of `L`.) -/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

def singularFactor (d : ℕ) : ℚ :=
  ∏ p ∈ d.primeFactors.erase 2, ((p : ℚ) - 1) / ((p : ℚ) - 2)

/-- The Hardy–Littlewood singular series for the prime pair gap `d`, measured in units of
the twin prime constant `C₂`: it is `2 ∏_{p ∣ d, p odd} (p-1)/(p-2)` for even `d`, and `0`
for odd `d` (an odd gap forces one of the two numbers to be even). -/

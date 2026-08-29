/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/

theorem greenTao_of_erdosTuran (h : ErdosTuranAP) : GreenTaoStatement :=
  h {p : ℕ | p.Prime} not_summable_one_div_on_primes

/-- The family of linear forms `i * k ! + 1 * n` (`i < k`), whose simultaneous primality gives a
`k`-term arithmetic progression of primes with common difference `k !`, is admissible: for every
prime `p` there is an `n` such that `p` divides none of the `k` values.

For `p ≤ k` one takes `n = 1`: then `p ∣ k !`, so each value is `≡ 1 (mod p)`. For `p > k` the
`k` forbidden residues `-i·k !` do not exhaust `ZMod p`, so an admissible residue exists. -/

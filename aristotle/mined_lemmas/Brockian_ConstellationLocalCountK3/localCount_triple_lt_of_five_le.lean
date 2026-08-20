/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* `ν_p(H)` of a finite set of integer offsets `H` at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem localCount_triple_lt_of_five_le (a b c : ℤ) {p : ℕ} (hp : 5 ≤ p) :
    localCount ({a, b, c} : Finset ℤ) p < p :=
  lt_of_le_of_lt (localCount_triple_le_three a b c p) (by omega)

/-- **Local count criterion for `k = 3` constellations.**
A triple of integer offsets is admissible if and only if it fails to cover all residues
modulo `2` and modulo `3`; all larger primes impose no condition. -/

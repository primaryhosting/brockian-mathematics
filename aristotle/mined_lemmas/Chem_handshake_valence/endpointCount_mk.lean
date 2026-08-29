import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of times an atom `v` occurs as an endpoint of an (unordered) bond `e`.
A self-bond `s(v, v)` contributes `2`. -/

theorem endpointCount_mk (v a b : V) :
    endpointCount v s(a, b) = (if a = v then 1 else 0) + (if b = v then 1 else 0) := rfl

/-- The valence of an atom `v` in a molecule whose bonds are given by the multiset `bonds`
(so that double and triple bonds are recorded with multiplicity): the number of bond
endpoints incident to `v`. -/

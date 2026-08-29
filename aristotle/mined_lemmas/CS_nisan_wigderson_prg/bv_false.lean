import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace CS

open Finset

/-- Real-valued indicator of a boolean: `1` for `true`, `0` for `false`. -/

@[simp] lemma bv_false : bv false = 0 := rfl

/-- `g : {0,1}^l → {0,1}` is an `α`-junta: it depends on at most `α` of its input bits. -/

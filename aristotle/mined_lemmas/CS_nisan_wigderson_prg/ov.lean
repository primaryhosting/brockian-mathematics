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

noncomputable def ov (s : Fin l → Fin n) (x : Fin n → Bool) (y : Fin l → Bool) : Fin n → Bool :=
  fun t => if h : ∃ v, s v = t then y h.choose else x t


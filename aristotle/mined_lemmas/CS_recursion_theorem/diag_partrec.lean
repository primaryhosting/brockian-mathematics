import Mathlib.Computability.PartrecCode
/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Statement: Kleene's recursion theorem: every computable transformation of programs has a fixed point.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Computable Partrec Encodable

/-- The diagonal helper: `diag x y` runs the program coded by `x` on input `x`; if that
returns a code `b`, it then runs the program coded by `b` on input `y`. -/

theorem diag_partrec : Partrec₂ diag :=
  (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
    (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂

/-- **Kleene's recursion theorem** (Rogers' fixed point form): every computable
transformation `f` of programs has a fixed point, i.e. a code `c` such that `f c`
and `c` compute the same partial function. -/

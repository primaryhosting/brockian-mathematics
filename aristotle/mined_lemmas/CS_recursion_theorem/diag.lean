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

noncomputable def diag (x y : ℕ) : Part ℕ :=
  eval (Denumerable.ofNat Code x) x >>= fun b => eval (Denumerable.ofNat Code b) y


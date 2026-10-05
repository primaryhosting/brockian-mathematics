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

def succTerm {n l m : ℕ} (S : Fin m → Fin l → Fin n) (f : (Fin l → Bool) → Bool)
    (D : (Fin m → Bool) → Bool) (k : ℕ) (i : Fin m) (x : Fin n → Bool) (r : Fin m → Bool) : ℝ :=
  if xor (D (hyb S f k x r)) (!(r i)) = f (fun t => x (S i t)) then 1 else 0

/-- The elementary Boolean identity behind Yao's next-bit predictor. -/

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

lemma yao_pointwise {m : ℕ} (D : (Fin m → Bool) → Bool) (T : Fin m → Bool) (i : Fin m)
    (b c : Bool) :
    (if xor (D (Function.update T i c)) (!c) = b then (1 : ℝ) else 0)
      + (if xor (D (Function.update T i (!c))) (!(!c)) = b then (1 : ℝ) else 0)
      = 2 * bv (D (Function.update T i b)) - bv (D (Function.update T i c))
        - bv (D (Function.update T i (!c))) + 1 := by
  cases b <;> cases c <;>
    cases hu : D (Function.update T i true) <;> cases hv : D (Function.update T i false) <;>
      norm_num [bv, hu, hv]

/-- Yao's next-bit predictor: the success probability of the predictor built from a
distinguisher between two consecutive hybrids is `1/2` plus the distinguishing advantage. -/

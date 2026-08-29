/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/

private theorem boolVec_colour (c : Fin 6 → Fin 6 → Bool) (x : Fin 6) (hx : x ≠ 0) :
    boolVec (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5) x = c 0 x := by
  match x with
  | 0 => exact absurd rfl hx
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- Any 2-colouring of the edges of `K₆` contains a monochromatic triangle. -/

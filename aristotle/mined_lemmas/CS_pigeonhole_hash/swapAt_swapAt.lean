/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including module
-- docstrings, so this file is deliberately self-contained (no imports) in order to begin with
-- the header above.  A Mathlib-based generalisation to arbitrary finite types is given in
-- `RequestProject/PigeonholeHashFintype.lean`.

namespace CS

/-- The involution of `Nat` that transposes `v` and `n` and fixes everything else. -/

private theorem swapAt_swapAt (v n x : Nat) : swapAt v n (swapAt v n x) = x := by
  unfold swapAt
  by_cases h1 : x = v <;> by_cases h2 : x = n <;> simp [h1, h2] <;> omega


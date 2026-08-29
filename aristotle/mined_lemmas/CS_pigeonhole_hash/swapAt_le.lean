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

private theorem swapAt_le (v n x : Nat) (hv : v ≤ n) (hx : x ≤ n) : swapAt v n x ≤ n := by
  unfold swapAt
  split
  · omega
  · split
    · omega
    · omega

/-- Numerical form of the pigeonhole principle: a function sending each of the `n + 1` numbers
`0, …, n` into `{0, …, n - 1}` takes the same value twice. -/

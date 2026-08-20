/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, other than `(x, y) = (±1, 0)`):
take `(x, y) = (2, 1)`, since `2² − 3·1² = 1`.

(The file has no `import` line because the required header comment must be the very
first thing in the file, and Lean requires `import` commands to precede all other
commands; the proof only uses core `Int` arithmetic, so no import is needed.) -/

def pellStep : Nat → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => (2 * (pellStep n).1 + 3 * (pellStep n).2, (pellStep n).1 + 2 * (pellStep n).2)


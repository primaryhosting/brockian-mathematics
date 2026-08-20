/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/

def edsWitness : ℕ → ℤ := fun n => if n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 8 ∨ n = 9 then -1 else 1


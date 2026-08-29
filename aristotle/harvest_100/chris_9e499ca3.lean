/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean requires to be the
-- very first thing in the file; consequently no `import` line may precede it, so this
-- file is written using only Lean core (no Mathlib import is needed for the proof).

namespace Math

/-- **Pell's equation for `d = 10`.** The equation `x² − 10·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (equivalently, a solution other than `(±1, 0)`).
Witness: `(x, y) = (19, 6)`, since `19² − 10·6² = 361 − 360 = 1`. -/
theorem pell_10 : ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨19, 6, by decide, by decide⟩

#print axioms Math.pell_10

end Math


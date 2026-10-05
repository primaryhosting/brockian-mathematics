/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution,
i.e. a solution with `y ≠ 0`: for instance `(x, y) = (5, 2)`, since
`5² - 6·2² = 25 - 24 = 1`.

(The required header comment must be the very first thing in the file, which
rules out an `import` line, so the proof is stated using core `Int`
arithmetic only and is checked by `decide`.) -/
theorem pell_6 : ∃ x y : Int, x ^ 2 - 6 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨5, 2, by decide, by decide⟩

end Math


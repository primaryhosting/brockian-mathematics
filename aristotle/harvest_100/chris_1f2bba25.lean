/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: the required header above is a module doc comment, which Lean treats as a
command; therefore no `import` line may follow it.  The proof below is
self-contained in core Lean 4 (integer arithmetic only) and needs no imports.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- **Pell's equation for `d = 10`.**
`x² - 10 y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(and hence `x ≠ ±1`).  The fundamental solution is `x = 19`, `y = 6`. -/
theorem pell_10 : ∃ x y : Int, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨19, 6, by decide, by decide⟩

end Math


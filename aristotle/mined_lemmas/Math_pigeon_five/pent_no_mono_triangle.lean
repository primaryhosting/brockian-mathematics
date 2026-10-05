/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pigeonhole for five two-valued items: among five booleans, some three of them
(at three distinct positions) are equal. -/

theorem pent_no_mono_triangle : ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
    ¬ (pent x y = pent x z ∧ pent x y = pent y z) := by decide

/-- **R(3,3) = 6.**

First component: every 2-colouring `col` of the edges of the complete graph `K₆`
(a symmetric `Bool`-valued function on the vertices `Fin 6`) contains a
monochromatic triangle, i.e. three distinct vertices `x`, `y`, `z` whose three
connecting edges all get the same colour.

Second component: there is a 2-colouring of the edges of `K₅` (the pentagon
colouring) with no monochromatic triangle, so 6 is optimal.

(The symmetry hypothesis in the first component reflects that colourings are
colourings of *edges*; the proof given here does not actually need it.) -/

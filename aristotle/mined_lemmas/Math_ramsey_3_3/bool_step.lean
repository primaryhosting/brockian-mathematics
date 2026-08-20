/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is self-contained: the proof uses only core `Lean`/`Init` (`Bool`, `Fin`, `decide`),
-- so no `import` is required.  (Mathlib currently has no Ramsey-number API to reuse here.)

namespace Math

/-- Pigeonhole for five booleans: among `b1, …, b5` some three are equal. -/

private theorem bool_step :
    ∀ v x y z : Bool, x = v ∨ y = v ∨ z = v ∨ (x = y ∧ y = z) := by decide

/-- **R(3,3) = 6.**

An edge 2-colouring of the complete graph on the vertex set `Fin n` is encoded by a function
`c : Fin n → Fin n → Bool`, the colour of the edge `{i, j}` with `i < j` being `c i j`;
a monochromatic triangle is a triple `i < j < k` with `c i j = c i k = c j k`.

First conjunct: *every* 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(No symmetry assumption on `c` is needed, since only the entries with `i < j` are used.)

Second conjunct: there is a 2-colouring of the edges of `K₅` — symmetric, hence an honest
edge colouring — with no monochromatic triangle, namely the pentagon/pentagram colouring. -/

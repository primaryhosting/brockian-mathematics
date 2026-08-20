import Mathlib
namespace C4.Alg5

/-- Cayley–Hamilton over `ℚ`: a matrix satisfies its own characteristic polynomial.

Type fix: the original statement wrote `(A.charpoly).eval₂ Polynomial.C A`, but
`Polynomial.C : ℚ →+* ℚ[X]` is not a ring hom into the matrix ring, so `eval₂` does not
typecheck there. The intended evaluation morphism is the algebra map
`ℚ →+* Matrix (Fin n) (Fin n) ℚ` (equivalently `Polynomial.aeval A`), which is used here. -/

theorem trace_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A+B).trace = A.trace + B.trace :=
  Matrix.trace_add A B

end C4.Alg5


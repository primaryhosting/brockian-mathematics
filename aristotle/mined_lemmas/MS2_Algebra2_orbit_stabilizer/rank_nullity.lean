import Mathlib
namespace MS2.Algebra2

theorem rank_nullity {V W : Type*} [Field ℝ] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] W) :
    Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ V :=
  LinearMap.finrank_range_add_finrank_ker f
/-- The Vandermonde determinant. The only change to the original statement is the explicit
type ascription `(i j : Fin n)` on the matrix entries: without it, the second index was
inferred to be a natural number and the expression was not a square matrix. -/

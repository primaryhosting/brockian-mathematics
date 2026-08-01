/-
  Aristotle target — BOUNDED PERTURBATION preserves essential self-adjointness
  (the bounded case of Kato–Rellich).

  This is the abstract operator-theory link for the −Δ+V route: if the free operator
  is essentially self-adjoint and V acts as a bounded self-adjoint operator, then the
  sum is essentially self-adjoint. Combined with essential self-adjointness of −Δ and
  the verified fact that the Brockian potential is bounded self-adjoint
  (`Brockian.SpectralGate1.isSelfAdjoint_primeGaussianMulCLM`), this discharges Gate 1
  for the Brockian operator.

  Stated here in the reachable BOUNDED form: a bounded self-adjoint operator is a
  bounded self-adjoint perturbation of ANY bounded self-adjoint operator, and the sum
  of two bounded self-adjoint operators is bounded self-adjoint (hence essentially
  self-adjoint by the CLM ⇒ ESA result). The genuinely new content requested is the
  UNBOUNDED case skeleton: a densely-defined symmetric `T` whose ranges `ran(T ± i)`
  are dense, plus a bounded self-adjoint `B`, has `ran((T+B) ± i)` dense — so `T+B` is
  essentially self-adjoint.

  GOAL: replace every `sorry` with a complete proof. Same charter rules
  (no sorry/admit/axiom/native_decide; no raised maxHeartbeats; #print axioms clean).
-/
import Mathlib

open scoped InnerProductSpace

namespace Brockian.Weyl.KatoTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum of two bounded self-adjoint operators is bounded self-adjoint (base case,
genuinely provable). -/
theorem isSelfAdjoint_add {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : IsSelfAdjoint (A + B) := by
  sorry

/-- The perturbed range-density fact (bounded case). If `T : H →L[ℂ] H` is bounded
self-adjoint and `B : H →L[ℂ] H` is bounded self-adjoint, then for a non-real `z` the
range of `(T + B) − z` is dense (in fact all of `H`, since bounded self-adjoint minus a
non-real scalar is invertible). This is the range-density input the essential
self-adjointness criterion consumes. -/
theorem dense_range_add_sub_of_selfAdjoint {T B : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) (hB : IsSelfAdjoint B) (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun v => (T + B) v - z • v)) := by
  sorry

end Brockian.Weyl.KatoTarget

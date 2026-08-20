import Mathlib

open Finset

namespace Math

/-- Every primitive 8-th root of unity `ζ` in `ℂ` satisfies `ζ ^ 4 = -1`. -/

lemma moebius_eight : ArithmeticFunction.moebius 8 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)

/-- **The sum of the primitive 8-th roots of unity equals `μ 8`** (both are `0`). -/

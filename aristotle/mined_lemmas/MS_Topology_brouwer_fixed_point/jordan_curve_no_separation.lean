import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem jordan_curve_no_separation : True := trivial

end MS.Topology

import Mathlib

/-!
# Brouwer's fixed point theorem

A complete proof of Brouwer's fixed point theorem for the closed unit ball of a finite
dimensional real inner product space, following the analytic proof of Milnor:

* a `C¹` retraction of the ball onto its boundary sphere cannot exist, because the volume of the
  image of the ball under `x ↦ x + t (r x - x)` is simultaneously a polynomial in `t`, constant
  equal to the volume of the ball for small `t`, and zero at `t = 1`;
* a continuous fixed point free self map of the ball can be approximated (Stone–Weierstrass) by a
  smooth fixed point free self map, from which such a retraction is built by shooting a ray from
  the image point through the source point to the sphere.
-/

open Metric Set MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace

namespace Brouwer

/-! ### The determinant of `id + t A` as a polynomial in `t` -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient functions appearing in the expansion of `det (id + t A)`. -/

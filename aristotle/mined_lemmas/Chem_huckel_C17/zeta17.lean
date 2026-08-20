import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

noncomputable def zeta17 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)


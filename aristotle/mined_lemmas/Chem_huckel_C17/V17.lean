import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

noncomputable def V17 : Matrix (ZMod 17) (ZMod 17) ℂ := fun k j => (17 : ℂ)⁻¹ * ee (-(j * k))

/-- The diagonal matrix of eigenvalues. -/

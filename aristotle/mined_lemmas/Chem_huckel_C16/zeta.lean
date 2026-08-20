import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- A primitive 16-th root of unity. -/

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a 16-membered
annulene, up to the usual affine normalization). -/

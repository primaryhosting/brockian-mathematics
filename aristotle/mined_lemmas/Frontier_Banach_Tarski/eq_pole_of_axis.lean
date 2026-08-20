import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma eq_pole_of_axis {x : E} (hx : x ∈ sph) (h : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 = 0) :
    x = e3 ∨ x = -e3 := by
  have h0 : x.ofLp 0 = 0 := by nlinarith [sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1)]
  have h1 : x.ofLp 1 = 0 := by nlinarith [sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1)]
  have hs : x.ofLp 0 * x.ofLp 0 + x.ofLp 1 * x.ofLp 1 + x.ofLp 2 * x.ofLp 2 = 1 := by
    simpa [sph, dotProduct, Fin.sum_univ_three] using hx
  have h2 : x.ofLp 2 = 1 ∨ x.ofLp 2 = -1 := by
    have hz : (x.ofLp 2 - 1) * (x.ofLp 2 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases h2 with h2 | h2
  · refine Or.inl (PiLp.ext (fun i => ?_))
    fin_cases i <;> simp [e3, h0, h1, h2]
  · refine Or.inr (PiLp.ext (fun i => ?_))
    fin_cases i <;> simp [e3, h0, h1, h2]


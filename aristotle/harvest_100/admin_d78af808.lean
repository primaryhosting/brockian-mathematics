/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The larger eigenvalue of the real symmetric matrix `!![a, b; b, d]`. -/
noncomputable def eigTop (a b d : ℝ) : ℝ :=
  ((a + d) + Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2

/-- The smaller eigenvalue of the real symmetric matrix `!![a, b; b, d]`. -/
noncomputable def eigBot (a b d : ℝ) : ℝ :=
  ((a + d) - Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2)) / 2

/-- The trace norm (Schatten 1-norm, i.e. the sum of the singular values) of the real
symmetric matrix `!![a, b; b, d]`; for a symmetric matrix the singular values are the
absolute values of the eigenvalues. -/
noncomputable def traceNormSym2 (a b d : ℝ) : ℝ :=
  |eigTop a b d| + |eigBot a b d|

/-- The eigenvalues really are the roots of the characteristic polynomial. -/
theorem eig_isRoot (a b d x : ℝ) (hx : x = eigTop a b d ∨ x = eigBot a b d) :
    x ^ 2 - (a + d) * x + (a * d - b ^ 2) = 0 := by
  have hnn : (0:ℝ) ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt hnn
  rcases hx with h | h <;> subst h <;>
    · simp only [eigTop, eigBot]
      nlinarith [hs]

/-- Sum of the two eigenvalues is the trace. -/
theorem eig_sum (a b d : ℝ) : eigTop a b d + eigBot a b d = a + d := by
  simp only [eigTop, eigBot]; ring

/-- Sum of the squares of the eigenvalues is the squared Frobenius norm. -/
theorem eig_sq_sum (a b d : ℝ) :
    eigTop a b d ^ 2 + eigBot a b d ^ 2 = a ^ 2 + 2 * b ^ 2 + d ^ 2 := by
  have hnn : (0:ℝ) ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt hnn
  simp only [eigTop, eigBot]
  nlinarith [hs]

/-- Elementary `ℓ¹`–`ℓ²` bound in two dimensions. -/
theorem abs_add_abs_le_sqrt_two_mul (x y : ℝ) :
    |x| + |y| ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
  have hnn : (0:ℝ) ≤ x ^ 2 + y ^ 2 := by positivity
  have h1 : Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) :=
    (Real.sqrt_mul (by norm_num) _).symm
  rw [h1]
  have h2 : (|x| + |y|) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have := sq_nonneg (|x| - |y|)
    have hx : |x| ^ 2 = x ^ 2 := sq_abs x
    have hy : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith
  have h3 : |x| + |y| = Real.sqrt ((|x| + |y|) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h3]
  exact Real.sqrt_le_sqrt h2

/-- **Cos Trace Norm 2707.**  For real symmetric `2 × 2` matrices `!![a, b; b, d]`, the trace
norm dominates the absolute trace, is dominated by `√2` times the Frobenius norm, and on the
cosine family `!![r cos θ, r sin θ; r sin θ, -r cos θ]` (`r ≥ 0`) it equals exactly `2r`, so
that both bounds are attained in the sharpest possible way (the trace vanishes while the
Frobenius bound `√2 · √(2 r²) = 2r` is an equality). -/
theorem CosTraceNorm2707 :
    (∀ a b d : ℝ, |a + d| ≤ traceNormSym2 a b d) ∧
    (∀ a b d : ℝ, traceNormSym2 a b d ≤ Real.sqrt 2 * Real.sqrt (a ^ 2 + 2 * b ^ 2 + d ^ 2)) ∧
    (∀ r θ : ℝ, 0 ≤ r →
      traceNormSym2 (r * Real.cos θ) (r * Real.sin θ) (-(r * Real.cos θ)) = 2 * r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b d
    have := abs_add_le (eigTop a b d) (eigBot a b d)
    rwa [eig_sum a b d] at this
  · intro a b d
    have h := abs_add_abs_le_sqrt_two_mul (eigTop a b d) (eigBot a b d)
    rwa [eig_sq_sum a b d] at h
  · intro r θ hr
    have hpy : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
      rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
    have hval : (r * Real.cos θ - -(r * Real.cos θ)) ^ 2 + 4 * (r * Real.sin θ) ^ 2
        = (2 * r) ^ 2 := by nlinarith [hpy]
    have hs : Real.sqrt ((r * Real.cos θ - -(r * Real.cos θ)) ^ 2 + 4 * (r * Real.sin θ) ^ 2)
        = 2 * r := by
      rw [hval, Real.sqrt_sq (by linarith)]
    simp only [traceNormSym2, eigTop, eigBot, hs]
    rw [show r * Real.cos θ + -(r * Real.cos θ) = 0 by ring]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (0 + 2 * r) / 2),
      abs_of_nonpos (by linarith : ((0:ℝ) - 2 * r) / 2 ≤ 0)]
    ring

end Brockian


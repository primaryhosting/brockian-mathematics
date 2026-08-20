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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

lemma eq_sin_of_hasDerivAt {k : ℝ} (hk : 0 < k) {f f' f'' : ℝ → ℝ}
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hd' : ∀ x : ℝ, HasDerivAt f' (f'' x) x)
    (heq : ∀ x : ℝ, f'' x = -(k ^ 2) * f x) (h0 : f 0 = 0) :
    ∀ x : ℝ, f x = (f' 0 / k) * Real.sin (k * x) := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  set A : ℝ := f' 0 / k with hA
  set g : ℝ → ℝ := fun x => f x - A * Real.sin (k * x) with hg
  set g' : ℝ → ℝ := fun x => f' x - A * k * Real.cos (k * x) with hg'
  set g'' : ℝ → ℝ := fun x => f'' x + A * k ^ 2 * Real.sin (k * x) with hg''
  have hkx : ∀ x : ℝ, HasDerivAt (fun y : ℝ => k * y) k x := by
    intro x; simpa using (hasDerivAt_id x).const_mul k
  have hdg : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_sin (k * x)).comp x (hkx x)).const_mul A
    exact ((hd x).sub h1).congr_deriv (by simp [hg']; ring)
  have hdg' : ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
    intro x
    have h1 := ((Real.hasDerivAt_cos (k * x)).comp x (hkx x)).const_mul (A * k)
    exact ((hd' x).sub h1).congr_deriv (by simp [hg'']; ring)
  have hgeq : ∀ x : ℝ, g'' x = -(k ^ 2) * g x := by
    intro x; simp only [hg'', hg, heq x]; ring
  set W : ℝ → ℝ := fun x => g' x ^ 2 + k ^ 2 * g x ^ 2 with hW
  have hdW : ∀ x : ℝ, HasDerivAt W 0 x := by
    intro x
    have h1 : HasDerivAt (fun y => g' y ^ 2) (2 * g' x * g'' x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hdg' x).pow 2
    have h2 : HasDerivAt (fun y => k ^ 2 * g y ^ 2) (k ^ 2 * (2 * g x * g' x)) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using ((hdg x).pow 2).const_mul (k ^ 2)
    refine (h1.add h2).congr_deriv ?_
    rw [hgeq x]; ring
  have hWconst : ∀ x : ℝ, W x = W 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hdW y).differentiableAt)
      (fun y => (hdW y).deriv) x 0
  have hW0 : W 0 = 0 := by
    have hg0 : g 0 = 0 := by simp [hg, h0]
    have hAk : A * k = f' 0 := by rw [hA]; field_simp
    have hg'0 : g' 0 = 0 := by simp [hg', hAk]
    simp [hW, hg0, hg'0]
  intro x
  have hx : g x = 0 := by
    have h := hWconst x
    rw [hW0] at h
    have hz : k ^ 2 * g x ^ 2 = 0 := by
      simp only [hW] at h; nlinarith [sq_nonneg (g x), sq_nonneg (g' x)]
    have hk2 : k ^ 2 ≠ 0 := by positivity
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hz).resolve_left hk2)
  simpa [hg, sub_eq_zero] using hx

/-- There is no bound state of nonpositive energy in the infinite square well. -/

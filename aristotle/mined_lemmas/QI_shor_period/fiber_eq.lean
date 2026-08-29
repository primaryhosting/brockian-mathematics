/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem fiber_eq {f : ℕ → ℕ} {r Q : ℕ} (hr : 0 < r) (hrQ : r ≤ Q)
    (hper : ∀ x, f (x + r) = f x)
    (hinj : ∀ x y, x < r → y < r → f x = f y → x = y)
    {x0 : ℕ} (hx0 : x0 < r) :
    (Finset.range Q).filter (fun x => f x = f x0)
      = (Finset.range (Acnt Q r x0)).image (fun j => x0 + j * r) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hxQ, hfx⟩
    have hmod : x % r = x0 := by
      apply hinj _ _ (Nat.mod_lt _ hr) hx0
      rw [f_mod hper, hfx]
    have hdm : x % r + (x / r) * r = x := Nat.mod_add_div' x r
    refine ⟨x / r, ?_, ?_⟩
    · rw [lt_Acnt_iff hr, ← hmod]
      omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [lt_Acnt_iff hr] at hj
    exact ⟨hj, by rw [add_comm x0 (j * r), ← f_add_mul hper x0 j, add_comm]⟩

end QI


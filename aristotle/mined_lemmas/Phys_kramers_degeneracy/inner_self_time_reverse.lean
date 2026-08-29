/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space `V`: an antiunitary
(antilinear, inner-product-conjugating) involution-up-to-sign with `Θ ∘ Θ = -1`,
which is the situation of a half-integer-spin system. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  /-- Additivity. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Antilinearity. -/
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- Antiunitarity: `⟪Θ x, Θ y⟫ = conj ⟪x, y⟫ = ⟪y, x⟫`. -/
  inner_map' : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- Half-integer spin: `Θ² = -1`. -/
  sq_eq_neg' : ∀ x, toFun (toFun x) = -x

namespace TimeReversal

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

variable (Θ : TimeReversal V)


lemma inner_self_time_reverse (x : V) : ⟪x, Θ x⟫_ℂ = 0 := by
  have h := Θ.inner_map (Θ x) x
  rw [Θ.sq_eq_neg, inner_neg_left] at h
  linear_combination (-1/2 : ℂ) * h

end TimeReversal

/-- Two nonzero orthogonal vectors are linearly independent. -/

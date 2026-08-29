import Mathlib
/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
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

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of finite sets is a *sunflower with core `K`* if any two distinct members
of `S` meet exactly in `K`. -/

theorem sunflower_bound {w r : ℕ} (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = w)
    (hcard : Nat.factorial w * (r - 1) ^ w < F.card) :
    ∃ S ⊆ F, ∃ K : Finset α, S.card = r ∧ IsSunflower S K := by
  classical
  have hFpos : 0 < F.card := by omega
  match r, hcard with
  | 0, _ => exact ⟨∅, Finset.empty_subset _, ∅, rfl, by simp [IsSunflower]⟩
  | 1, _ =>
    obtain ⟨A, hA⟩ := Finset.card_pos.1 hFpos
    exact ⟨{A}, Finset.singleton_subset_iff.2 hA, ∅, Finset.card_singleton _, by
      intro X hX Z hZ hXZ
      rw [Finset.mem_singleton] at hX hZ
      exact absurd (hX.trans hZ.symm) hXZ⟩
  | (r + 2), hcard => exact sunflower_aux (r + 2) (by omega) w F hF hcard

/-- Contrapositive form of the sunflower bound: a `w`-uniform family containing no sunflower
with `r` petals has at most `w! * (r-1)^w` members. -/

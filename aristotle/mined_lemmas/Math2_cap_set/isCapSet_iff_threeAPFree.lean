import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open scoped Classical

namespace Math2

variable {n : ℕ}

/-- A subset of `𝔽₃ⁿ` is a *cap set* if it contains no line, i.e. no three points summing to
zero other than the degenerate ones `x + x + x = 0`.  Equivalently (see
`Math2.threeAPFree_of_isCapSet`) it contains no nontrivial three-term arithmetic progression. -/

lemma isCapSet_iff_threeAPFree {A : Finset (Fin n → ZMod 3)} :
    IsCapSet A ↔ ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  refine ⟨threeAPFree_of_isCapSet, fun hA x hx y hy z hz hxyz => ?_⟩
  have key : ∀ u v w : Fin n → ZMod 3, u + v + w = 0 → u + w = v + v := by
    intro u v w h
    have h' : u + w - (v + v) = u + v + w - (v + v + v) := by abel
    rw [h, add_self_add_self_self v, sub_zero, sub_eq_zero] at h'
    exact h'
  have hzyx : z + y + x = 0 := by rw [← hxyz]; abel
  exact ⟨hA hx hy hz (key x y z hxyz), (hA hz hy hx (key z y x hzyx)).symm⟩

/-- **The cap set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt, here in the qualitative
`o(3ⁿ)` form): for every `ε > 0` there is an `N` such that for all `n ≥ N`, every cap set in
`𝔽₃ⁿ` (a set containing no three-term arithmetic progression) has size at most `ε · 3ⁿ`. -/

import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem gFun_injective : Function.Injective (gFun W τ c) := by
  classical
  rintro (i | s) (i' | s') h <;> simp only [gFun, Sum.elim_inl, Sum.elim_inr] at h
  · have h1 : gIdx W τ c i = gIdx W τ c i' := Sum.inr_injective h
    have h2 := congrArg (fun z => (Sigma.fst z).1) h1
    simpa [gIdx] using h2
  · by_cases hs : s' = gIdx W τ c s'.1.1
    · rw [if_pos hs] at h; exact absurd h (by simp)
    · rw [if_neg hs] at h
      exact absurd (by rw [← Sum.inr_injective h]; rfl) hs
  · by_cases hs : s = gIdx W τ c s.1.1
    · rw [if_pos hs] at h; exact absurd h (by simp)
    · rw [if_neg hs] at h
      exact absurd (by rw [Sum.inr_injective h]; rfl) hs
  · by_cases hs : s = gIdx W τ c s.1.1 <;> by_cases hs' : s' = gIdx W τ c s'.1.1
    · rw [if_pos hs, if_pos hs'] at h
      have h2 : s.1.2 = s'.1.2 := Sum.inl_injective h
      have e1 : s.1.2 = τ s.1.1 := by
        conv_lhs => rw [hs]
        rfl
      have e2 : s'.1.2 = τ s'.1.1 := by
        conv_lhs => rw [hs']
        rfl
      have h3 : s.1.1 = s'.1.1 := τ.injective (by rw [← e1, ← e2, h2])
      rw [hs, hs', h3]
    · rw [if_pos hs, if_neg hs'] at h; exact absurd h (by simp)
    · rw [if_neg hs, if_pos hs'] at h; exact absurd h (by simp)
    · rw [if_neg hs, if_neg hs'] at h; exact h

/-- The permutation of the vertex set of the gadget determined by `(τ, c)`. -/

/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Complexification -/

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a `ℚ`-vector space `V`,
as a `ℚ`-linear automorphism. -/

noncomputable def pointDatum : HodgeDatum where
  V := ℚ
  p := 0
  Hpq := fun ab => if ab = (0, 0) then ⊤ else ⊥
  pure' := by
    rintro ⟨a, b⟩ h
    simp only [Nat.cast_zero, mul_zero] at h
    have hne : ((a, b) : ℤ × ℤ) ≠ (0, 0) := by
      intro hh
      rw [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      simp at h
    simp [hne]
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro i
      by_cases hi : i = (0, 0)
      · subst hi
        have hsup : (⨆ (j : ℤ × ℤ) (_ : j ≠ ((0 : ℤ), (0 : ℤ))),
            (fun ab : ℤ × ℤ => if ab = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) j)
            = ⊥ := by
          refine iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj => ?_
          simp [hj]
        rw [hsup]
        exact disjoint_bot_right
      · have hbot : ((fun ab : ℤ × ℤ => if ab = (0, 0) then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) i)
            = ⊥ := by simp [hi]
        rw [hbot]
        exact disjoint_bot_left
    · refine le_antisymm le_top ?_
      refine le_trans ?_ (le_iSup (fun j : ℤ × ℤ => if j = (0, 0) then
        (⊤ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) else ⊥) (0, 0))
      simp
  conj_mem := by
    intro a b x hx
    by_cases hab : (a, b) = (0, 0)
    · rw [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simp
    · have hx' : x ∈ (⊥ : Submodule ℂ (ℂ ⊗[ℚ] ℚ)) := by simpa [hab] using hx
      rw [Submodule.mem_bot] at hx'
      subst hx'
      simp
  alg := ⊤
  alg_le := le_top

/-- The Hodge conjecture holds for the datum of a point. -/

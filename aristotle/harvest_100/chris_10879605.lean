/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

set_option grind.warning false

namespace Math

/-- A 2-colouring `C` of the edges of the complete graph on `Fin n` has a monochromatic
triangle if there are three distinct vertices all of whose connecting edges receive the
same colour. -/
def HasMonoTriangle {n : ℕ} (C : Fin n → Fin n → Bool) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ C a b = C a c ∧ C a b = C b c

/-- Pigeonhole: among five objects coloured with two colours, three share a colour. -/
lemma exists_three_same_of_five (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i = f j ∧ f i = f k := by
  revert f
  decide

/-- The colouring of `K₅` given by the 5-cycle: `a` and `b` are joined by a red edge
(`true`) exactly when they are adjacent on the cycle `0-1-2-3-4-0`. -/
def pentagon : Fin 5 → Fin 5 → Bool :=
  fun a b => decide ((a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val)

lemma pentagon_symm (a b : Fin 5) : pentagon a b = pentagon b a := by
  simp only [pentagon, decide_eq_decide]
  tauto

lemma pentagon_no_mono : ¬ HasMonoTriangle pentagon := by
  unfold HasMonoTriangle
  decide

/-- Every 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(The symmetry hypothesis `hC`, which expresses that `C` really is an edge-colouring,
turns out not to be needed for this direction.) -/
lemma mono_triangle_of_six (C : Fin 6 → Fin 6 → Bool)
    (hC : ∀ a b, C a b = C b a) : HasMonoTriangle C := by
  obtain ⟨i, j, k, hij, hik, hjk, hfj, hfk⟩ :=
    exists_three_same_of_five (fun i => C 0 i.succ)
  set a : Fin 6 := i.succ with ha
  set b : Fin 6 := j.succ with hb
  set c : Fin 6 := k.succ with hc
  have hab : a ≠ b := fun h => hij (Fin.succ_injective _ h)
  have hac : a ≠ c := fun h => hik (Fin.succ_injective _ h)
  have hbc : b ≠ c := fun h => hjk (Fin.succ_injective _ h)
  have ha0 : (0 : Fin 6) ≠ a := (Fin.succ_ne_zero i).symm
  have hb0 : (0 : Fin 6) ≠ b := (Fin.succ_ne_zero j).symm
  have hc0 : (0 : Fin 6) ≠ c := (Fin.succ_ne_zero k).symm
  by_cases h1 : C a b = C 0 a
  · exact ⟨0, a, b, ha0, hb0, hab, hfj, h1.symm⟩
  · by_cases h2 : C a c = C 0 a
    · exact ⟨0, a, c, ha0, hc0, hac, hfk, h2.symm⟩
    · by_cases h3 : C b c = C 0 b
      · refine ⟨0, b, c, hb0, hc0, hbc, ?_, h3.symm⟩
        rw [← hfj, hfk]
      · -- all three edges among `a`, `b`, `c` avoid the colour `C 0 a`
        have hb' : C 0 b = C 0 a := hfj.symm
        have h3' : C b c ≠ C 0 a := by rw [hb'] at h3; exact h3
        refine ⟨a, b, c, hab, hac, hbc, ?_, ?_⟩
        · rcases Bool.eq_false_or_eq_true (C 0 a) with hx | hx <;>
            rcases Bool.eq_false_or_eq_true (C a b) with hy | hy <;>
            rcases Bool.eq_false_or_eq_true (C a c) with hz | hz <;>
            simp_all
        · rcases Bool.eq_false_or_eq_true (C 0 a) with hx | hx <;>
            rcases Bool.eq_false_or_eq_true (C a b) with hy | hy <;>
            rcases Bool.eq_false_or_eq_true (C b c) with hz | hz <;>
            simp_all

/-- **R(3,3) = 6**: every 2-colouring of the edges of `K₆` contains a monochromatic
triangle, while `K₅` admits a 2-colouring with no monochromatic triangle. -/
theorem ramsey_3_3 :
    (∀ C : Fin 6 → Fin 6 → Bool, (∀ a b, C a b = C b a) → HasMonoTriangle C) ∧
    (∃ C : Fin 5 → Fin 5 → Bool, (∀ a b, C a b = C b a) ∧ ¬ HasMonoTriangle C) :=
  ⟨mono_triangle_of_six, pentagon, pentagon_symm, pentagon_no_mono⟩

end Math


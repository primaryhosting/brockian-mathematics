/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

set_option grind.warning false

namespace Math

/-- Pigeonhole: among five booleans, three are equal. -/

theorem exists_mono_triangle_six (f : Fin 6 → Fin 6 → Bool) :
    ∃ a b c : Fin 6, a < b ∧ b < c ∧ f a b = f a c ∧ f a c = f b c := by
  obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := three_equal_of_five (fun i => f 0 i.succ)
  have h1' : f 0 i.succ = f 0 j.succ := h1
  have h2' : f 0 j.succ = f 0 k.succ := h2
  have h0I : (0 : Fin 6) < i.succ := Fin.succ_pos i
  have h0J : (0 : Fin 6) < j.succ := Fin.succ_pos j
  have hIJ : i.succ < j.succ := Fin.succ_lt_succ_iff.mpr hij
  have hJK : j.succ < k.succ := Fin.succ_lt_succ_iff.mpr hjk
  have hIK : i.succ < k.succ := lt_trans hIJ hJK
  by_cases e1 : f i.succ j.succ = f 0 i.succ
  · exact ⟨0, i.succ, j.succ, h0I, hIJ, h1', (e1.trans h1').symm⟩
  · by_cases e2 : f i.succ k.succ = f 0 i.succ
    · exact ⟨0, i.succ, k.succ, h0I, hIK, h1'.trans h2', (e2.trans (h1'.trans h2')).symm⟩
    · by_cases e3 : f j.succ k.succ = f 0 i.succ
      · exact ⟨0, j.succ, k.succ, h0J, hJK, h2', (e3.trans (h1'.trans h2')).symm⟩
      · exact ⟨i.succ, j.succ, k.succ, hIJ, hJK, bool_eq_of_ne_ne e1 e2,
          bool_eq_of_ne_ne e2 e3⟩

/-- The pentagon coloring of `K₅` has no monochromatic triangle. -/

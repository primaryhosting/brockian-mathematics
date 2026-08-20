import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem nadd_decomp_le (d : Ordinal)
    (hd : ∀ x y : Ordinal, x < ω ^ d → y < ω ^ d → x ♯ y < ω ^ d) :
    ∀ a : Ordinal, ∀ b : Ordinal, ∀ (m n : ℕ) (r s : Ordinal), r < ω ^ d → s < ω ^ d →
      a = ω ^ d * (m : Ordinal) + r → b = ω ^ d * (n : Ordinal) + s →
      a ♯ b ≤ ω ^ d * ((m + n : ℕ) : Ordinal) + (r ♯ s) := by
  have step : ∀ (k l : ℕ) (x y : Ordinal), x < ω ^ d → y < ω ^ d → k + 1 ≤ l →
      ω ^ d * ((k : ℕ) : Ordinal) + (x ♯ y) < ω ^ d * ((l : ℕ) : Ordinal) := by
    intro k l x y hx hy hkl
    have h1 : ω ^ d * ((k : ℕ) : Ordinal) + (x ♯ y)
        < ω ^ d * ((k : ℕ) : Ordinal) + ω ^ d := (add_lt_add_iff_left _).2 (hd _ _ hx hy)
    have h2 : ω ^ d * ((k : ℕ) : Ordinal) + ω ^ d = ω ^ d * (((k + 1 : ℕ)) : Ordinal) := by
      push_cast; rw [mul_add, mul_one]
    have h3 : ω ^ d * (((k + 1 : ℕ)) : Ordinal) ≤ ω ^ d * ((l : ℕ) : Ordinal) := by
      exact mul_le_mul_right (by exact_mod_cast hkl) _
    exact h1.trans_le (h2 ▸ h3)
  intro a
  induction a using Ordinal.induction with
  | _ a IHa =>
  intro b
  induction b using Ordinal.induction with
  | _ b IHb =>
  intro m n r s hr hs ha hb
  rw [Ordinal.nadd_le_iff]
  constructor
  · intro a' ha'
    have ha'lt : a' < ω ^ d * ω := ha'.trans_le (le_of_lt (ha ▸ opow_mul_nat_add_lt d m r hr))
    obtain ⟨m', r', hr', rfl⟩ := exists_decomp d a' ha'lt
    have key := IHa _ ha' b m' n r' s hr' hs rfl hb
    rcases decomp_cases d m m' r r' hr (ha ▸ ha') with hlt | ⟨rfl, hrr⟩
    · exact key.trans_lt ((step (m' + n) (m + n) r' s hr' hs (by omega)).trans_le le_self_add)
    · exact key.trans_lt ((add_lt_add_iff_left _).2 (Ordinal.nadd_lt_nadd_right hrr s))
  · intro b' hb'
    have hb'lt : b' < ω ^ d * ω := hb'.trans_le (le_of_lt (hb ▸ opow_mul_nat_add_lt d n s hs))
    obtain ⟨n', s', hs', rfl⟩ := exists_decomp d b' hb'lt
    have key := IHb _ hb' m n' r s' hr hs' ha rfl
    rcases decomp_cases d n n' s s' hs (hb ▸ hb') with hlt | ⟨rfl, hss⟩
    · exact key.trans_lt ((step (m + n') (m + n) r s' hr hs' (by omega)).trans_le le_self_add)
    · exact key.trans_lt ((add_lt_add_iff_left _).2 (Ordinal.nadd_lt_nadd_left hss r))

/-- **The ordinals `ω ^ c` are principal for natural addition.** -/

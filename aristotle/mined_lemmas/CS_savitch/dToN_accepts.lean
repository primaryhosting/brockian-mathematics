/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem dToN_accepts (D : DMachine) (sz : ℕ → ℕ) (e : (n : ℕ) → D.Conf n ↪ Fin (sz n))
    (x : List Bool) : (dToN D sz e).Accepts x ↔ D.Accepts x := by
  classical
  set n := x.length
  have hval_inj : ∀ (w w' : D.Conf n), ((e n w) : ℕ) = ((e n w') : ℕ) → w = w' := by
    intro w w' h
    exact (e n).injective (Fin.ext h)
  have hipos : ∀ w : D.Conf n, (dToN D sz e).ipos n ((e n w) : ℕ) = D.ipos n w := by
    intro w
    have hex : ∃ w' : D.Conf n, ((e n w') : ℕ) = ((e n w) : ℕ) := ⟨w, rfl⟩
    show (if h : ∃ w' : D.Conf n, ((e n w') : ℕ) = ((e n w) : ℕ) then D.ipos n h.choose else 0)
      = D.ipos n w
    rw [dif_pos hex]
    congr 1
    exact hval_inj _ _ hex.choose_spec
  have hedge : ∀ (w : D.Conf n) (j : ℕ),
      (dToN D sz e).edge x ((e n w) : ℕ) j ↔ j = ((e n (D.next x w)) : ℕ) := by
    intro w j
    rw [NMachine.edge, hipos w]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rw [hval_inj w' w hw']
      rfl
    · rintro rfl
      exact ⟨w, rfl, rfl⟩
  have hreach : ∀ v : ℕ, Relation.ReflTransGen ((dToN D sz e).edge x) ((e n (D.init n)) : ℕ) v ↔
      ∃ t : ℕ, v = ((e n (((D.next x)^[t]) (D.init n))) : ℕ) := by
    intro v
    constructor
    · intro h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail hab hbc ih =>
        obtain ⟨t, rfl⟩ := ih
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply']
        exact (hedge _ _).1 hbc
    · rintro ⟨t, rfl⟩
      induction t with
      | zero => exact Relation.ReflTransGen.refl
      | succ t ih =>
        refine ih.tail ?_
        rw [Function.iterate_succ_apply']
        exact (hedge _ _).2 rfl
  constructor
  · rintro ⟨v, hv, w, hw, hacc⟩
    obtain ⟨t, rfl⟩ := (hreach v).1 hv
    exact ⟨t, by rwa [hval_inj w _ hw] at hacc⟩
  · rintro ⟨t, ht⟩
    exact ⟨((e n (((D.next x)^[t]) (D.init n))) : ℕ), (hreach _).2 ⟨t, rfl⟩, ⟨_, rfl, ht⟩⟩

/-- Deterministic machines are a special case of nondeterministic ones. -/

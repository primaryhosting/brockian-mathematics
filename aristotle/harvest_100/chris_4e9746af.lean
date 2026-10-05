/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires `import` commands to precede every other command,
including module docstrings, so the mandated header above rules out importing
Mathlib in this file. The development below is therefore fully self-contained
(core Lean only). The companion file `RequestProject/CSMathlib.lean` records the
Mathlib proof of the same statement, via `Fintype.exists_ne_map_eq_of_card_lt`.
-/

namespace CS

/-- Pigeonhole principle in arithmetic form: if `f` maps each of the `n + 1`
numbers `0, …, n` into `{0, …, n - 1}`, then two distinct inputs collide. -/
theorem pigeonhole_nat :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i, i < n + 1 → f i < n) →
      ∃ i j, i < n + 1 ∧ j < n + 1 ∧ i ≠ j ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
      intro f hf
      have := hf 0 (by omega)
      omega
  | succ n ih =>
      intro f hf
      by_cases hcol : ∃ i, i < n + 1 ∧ f i = f (n + 1)
      · obtain ⟨i, hi, hfi⟩ := hcol
        exact ⟨i, n + 1, by omega, by omega, by omega, hfi⟩
      · -- No `i ≤ n` hashes to `f (n+1)`, so we may delete that bucket.
        have hne : ∀ i, i < n + 1 → f i ≠ f (n + 1) := by
          intro i hi hfi
          exact hcol ⟨i, hi, hfi⟩
        have hgbound : ∀ i, i < n + 1 →
            (fun k => if f k < f (n + 1) then f k else f k - 1) i < n := by
          intro i hi
          have h1 : f i < n + 1 := hf i (by omega)
          have h2 : f (n + 1) < n + 1 := hf (n + 1) (by omega)
          have h3 : f i ≠ f (n + 1) := hne i hi
          by_cases hlt : f i < f (n + 1)
          · simp only [if_pos hlt]; omega
          · simp only [if_neg hlt]; omega
        obtain ⟨i, j, hi, hj, hij, hgij⟩ := ih _ hgbound
        refine ⟨i, j, by omega, by omega, hij, ?_⟩
        have h3 : f i ≠ f (n + 1) := hne i hi
        have h4 : f j ≠ f (n + 1) := hne j hj
        by_cases hli : f i < f (n + 1) <;> by_cases hlj : f j < f (n + 1)
        · rw [if_pos hli, if_pos hlj] at hgij; omega
        · rw [if_pos hli, if_neg hlj] at hgij; omega
        · rw [if_neg hli, if_pos hlj] at hgij; omega
        · rw [if_neg hli, if_neg hlj] at hgij; omega

/-- **Pigeonhole hash.** Any hash function from an `(n+1)`-element set of keys to
an `n`-element set of buckets has a collision: two distinct keys with equal hash. -/
theorem pigeonhole_hash (n : Nat) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  have hbound : ∀ i, i < n + 1 →
      (fun k => if h : k < n + 1 then (f ⟨k, h⟩).val else 0) i < n := by
    intro i hi
    simp only [dif_pos hi]
    exact (f ⟨i, hi⟩).isLt
  obtain ⟨i, j, hi, hj, hij, hfij⟩ := pigeonhole_nat n _ hbound
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_⟩
  · intro h
    exact hij (congrArg Fin.val h)
  · simp only [dif_pos hi, dif_pos hj] at hfij
    exact Fin.eq_of_val_eq hfij

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Pigeonhole Hash — Mathlib version

The same statement as `CS.pigeonhole_hash`, proved from Mathlib's
`Fintype.exists_ne_map_eq_of_card_lt`, and stated for arbitrary finite types.
-/

namespace CS

/-- Any hash function from a finite type with `n + 1` keys to a finite type with
`n` buckets has a collision. -/
theorem pigeonhole_hash_fintype {K B : Type*} [Fintype K] [Fintype B] {n : ℕ}
    (hK : Fintype.card K = n + 1) (hB : Fintype.card B = n) (f : K → B) :
    ∃ a b : K, a ≠ b ∧ f a = f b := by
  have hlt : Fintype.card B < Fintype.card K := by omega
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  exact ⟨a, b, hab, h⟩

/-- Concrete form: any hash `f : Fin (n + 1) → Fin n` has a collision. -/
theorem pigeonhole_hash_fin (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b :=
  pigeonhole_hash_fintype (Fintype.card_fin _) (Fintype.card_fin _) f

end CS


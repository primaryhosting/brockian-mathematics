/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-
Note on imports: the required header comment must be the very first thing in this file,
and Lean does not allow an `import` command after a module doc comment, so this file is
kept import-free and self-contained.  A one-line Mathlib proof of the same statement
(using `Fintype.exists_ne_map_eq_of_card_lt`) is given in `RequestProject/CSMathlib.lean`.
-/

/-- Numerical form of the pigeonhole principle: a function `f : ℕ → ℕ` sending each of the
`n + 1` inputs `0, …, n` into `{0, …, n - 1}` takes the same value twice. -/
theorem pigeonhole_nat :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i, i < n + 1 → f i < n) →
      ∃ a b, a < n + 1 ∧ b < n + 1 ∧ a ≠ b ∧ f a = f b := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd (hf 0 (by omega)) (by omega)
  | succ n ih =>
    intro f hf
    by_cases hcol : ∃ i, i < n + 1 ∧ f i = f (n + 1)
    · obtain ⟨i, hi, hfi⟩ := hcol
      exact ⟨i, n + 1, by omega, by omega, by omega, hfi⟩
    · -- no input below `n + 1` collides with `n + 1`, so deleting the value `f (n + 1)`
      -- from the codomain gives a map into `{0, …, n - 1}`
      have hne : ∀ i, i < n + 1 → f i ≠ f (n + 1) := fun i hi h => hcol ⟨i, hi, h⟩
      have hgb : ∀ i, i < n + 1 → (if f i < f (n + 1) then f i else f i - 1) < n := by
        intro i hi
        have h1 : f i < n + 1 := hf i (by omega)
        have h2 : f (n + 1) < n + 1 := hf (n + 1) (by omega)
        have h3 := hne i hi
        split <;> omega
      obtain ⟨a, b, ha, hb, hab, hgab⟩ :=
        ih (fun i => if f i < f (n + 1) then f i else f i - 1) hgb
      refine ⟨a, b, by omega, by omega, hab, ?_⟩
      have h1 : f a < n + 1 := hf a (by omega)
      have h2 : f b < n + 1 := hf b (by omega)
      have h3 := hne a ha
      have h4 := hne b hb
      split at hgab <;> split at hgab <;> omega

/-- **Pigeonhole hash**: any hash function from a set of `n + 1` keys to a set of `n`
buckets has a collision, i.e. two distinct keys with the same hash value. -/
theorem pigeonhole_hash (n : Nat) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  have h := pigeonhole_nat n (fun i => if h : i < n + 1 then (f ⟨i, h⟩).val else 0) ?_
  · obtain ⟨a, b, ha, hb, hab, hfab⟩ := h
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
    · intro h; exact hab (congrArg Fin.val h)
    · exact Fin.ext (by simpa [ha, hb] using hfab)
  · intro i hi
    simp [hi]

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
# Pigeonhole Hash — Mathlib one-liner

The statement of `CS.pigeonhole_hash` (see `RequestProject/CS.lean`, which is import-free
so that the required header comment can be the first thing in the file) also follows
immediately from Mathlib's `Fintype.exists_ne_map_eq_of_card_lt`.
-/

namespace CS

/-- Any hash function from `Fin (n + 1)` to `Fin n` has a collision, via Mathlib's
`Fintype.exists_ne_map_eq_of_card_lt`. -/
theorem pigeonhole_hash_mathlib (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  obtain ⟨a, b, hab, h⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  exact ⟨a, b, hab, h⟩

/-- General form: any function between finite types whose codomain is strictly smaller than
its domain has a collision. -/
theorem pigeonhole_hash_general {K B : Type*} [Fintype K] [Fintype B]
    (f : K → B) (h : Fintype.card B < Fintype.card K) :
    ∃ a b : K, a ≠ b ∧ f a = f b :=
  Fintype.exists_ne_map_eq_of_card_lt f h

end CS


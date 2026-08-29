/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including module
-- docstrings, so this file is deliberately self-contained (no imports) in order to begin with
-- the header above.  A Mathlib-based generalisation to arbitrary finite types is given in
-- `RequestProject/PigeonholeHashFintype.lean`.

namespace CS

/-- The involution of `Nat` that transposes `v` and `n` and fixes everything else. -/
private def swapAt (v n x : Nat) : Nat := if x = v then n else if x = n then v else x

private theorem swapAt_swapAt (v n x : Nat) : swapAt v n (swapAt v n x) = x := by
  unfold swapAt
  by_cases h1 : x = v <;> by_cases h2 : x = n <;> simp [h1, h2] <;> omega

private theorem swapAt_le (v n x : Nat) (hv : v ≤ n) (hx : x ≤ n) : swapAt v n x ≤ n := by
  unfold swapAt
  split
  · omega
  · split
    · omega
    · omega

/-- Numerical form of the pigeonhole principle: a function sending each of the `n + 1` numbers
`0, …, n` into `{0, …, n - 1}` takes the same value twice. -/
private theorem pigeonhole_nat : ∀ (n : Nat) (f : Nat → Nat), (∀ i < n + 1, f i < n) →
    ∃ a b, a < n + 1 ∧ b < n + 1 ∧ a ≠ b ∧ f a = f b := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd (hf 0 (by omega)) (by omega)
  | succ n ih =>
    intro f hf
    have hvle : f (n + 1) ≤ n := by have := hf (n + 1) (by omega); omega
    have hlast : swapAt (f (n + 1)) n (f (n + 1)) = n := by simp [swapAt]
    by_cases hcase : ∃ i, i < n + 1 ∧ swapAt (f (n + 1)) n (f i) = n
    · obtain ⟨i, hi, hieq⟩ := hcase
      refine ⟨i, n + 1, by omega, by omega, by omega, ?_⟩
      have key : swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f i))
          = swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f (n + 1))) := by
        rw [hieq, hlast]
      rwa [swapAt_swapAt, swapAt_swapAt] at key
    · have hcase' : ∀ i, i < n + 1 → swapAt (f (n + 1)) n (f i) ≠ n :=
        fun i hi he => hcase ⟨i, hi, he⟩
      have hb : ∀ i < n + 1, swapAt (f (n + 1)) n (f i) < n := by
        intro i hi
        have h1 : f i < n + 1 := hf i (by omega)
        have h2 := swapAt_le (f (n + 1)) n (f i) hvle (by omega)
        have h3 := hcase' i hi
        omega
      obtain ⟨a, b, ha, hbb, hab, heq⟩ := ih (fun i => swapAt (f (n + 1)) n (f i)) hb
      have heq' : swapAt (f (n + 1)) n (f a) = swapAt (f (n + 1)) n (f b) := heq
      refine ⟨a, b, by omega, by omega, hab, ?_⟩
      have key : swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f a))
          = swapAt (f (n + 1)) n (swapAt (f (n + 1)) n (f b)) := by rw [heq']
      rwa [swapAt_swapAt, swapAt_swapAt] at key

/-- **Pigeonhole hash.** Any hash function from a set of `n + 1` keys into a set of `n` buckets
has a collision: there are two distinct keys with the same hash value. -/
theorem pigeonhole_hash (n : Nat) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  have key := pigeonhole_nat n (fun i => if h : i < n + 1 then (f ⟨i, h⟩).val else 0)
    (by
      intro i hi
      show (if h : i < n + 1 then (f ⟨i, h⟩).val else 0) < n
      rw [dif_pos hi]
      exact (f ⟨i, hi⟩).isLt)
  obtain ⟨a, b, ha, hb, hab, heq⟩ := key
  have heq' : (f ⟨a, ha⟩).val = (f ⟨b, hb⟩).val := by
    have h : (if h : a < n + 1 then (f ⟨a, h⟩).val else 0)
        = (if h : b < n + 1 then (f ⟨b, h⟩).val else 0) := heq
    rwa [dif_pos ha, dif_pos hb] at h
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hc => hab (congrArg Fin.val hc), Fin.eq_of_val_eq heq'⟩

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
import RequestProject.PigeonholeHash

/-!
# Pigeonhole hash for arbitrary finite types

A Mathlib-based generalisation of `CS.pigeonhole_hash`: any hash function from a finite type of
cardinality `n + 1` to a finite type of cardinality `n` has a collision.
-/

namespace CS

/-- Any hash function from a finite type with `n + 1` elements to a finite type with `n`
elements has a collision. -/
theorem pigeonhole_hash_card {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α = n + 1) (hβ : Fintype.card β = n) (f : α → β) :
    ∃ a b : α, a ≠ b ∧ f a = f b := by
  have hlt : Fintype.card β < Fintype.card α := by omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  exact ⟨a, b, hab, hfab⟩

end CS


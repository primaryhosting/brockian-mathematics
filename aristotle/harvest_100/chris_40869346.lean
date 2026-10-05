import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Computability

namespace CS

/-- Repeating a word `v` any number of times stays inside the Kleene star of `{v}`. -/
theorem flatten_replicate_mem_kstar {α : Type*} (v : List α) (n : ℕ) :
    (List.replicate n v).flatten ∈ ({v} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n v, rfl, fun y hy => ?_⟩
  rw [List.eq_of_mem_replicate hy]
  rfl

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0`: every word `x ∈ L` of length at
least `p` can be split as `x = u ++ v ++ w` with `|u| + |v| ≤ p` and `v ≠ []`, in such a way
that the pumped words `u ++ vⁿ ++ w` belong to `L` for every `n : ℕ`.
-/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ x ∈ L, p ≤ x.length →
      ∃ u v w : List α, x = u ++ v ++ w ∧ u.length + v.length ≤ p ∧ v ≠ [] ∧
        ∀ n : ℕ, u ++ (List.replicate n v).flatten ++ w ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.mpr ⟨M.start⟩, ?_⟩
  intro x hx hlen
  obtain ⟨u, v, w, hsplit, hle, hne, hsub⟩ := M.pumping_lemma hx hlen
  refine ⟨u, v, w, hsplit, hle, hne, fun n => hsub ?_⟩
  rw [Language.mem_mul]
  refine ⟨u ++ (List.replicate n v).flatten, ?_, w, rfl, rfl⟩
  rw [Language.mem_mul]
  exact ⟨u, rfl, (List.replicate n v).flatten, flatten_replicate_mem_kstar v n, rfl⟩

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


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
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/

lemma reach_bounded (s : ℕ) (hsp : ∀ w, N.Reach x N.init w → w.length ≤ s) {v : Word}
    (hv : N.Reach x N.init v) : ReachIn N x ((cands s).length) N.init v := by
  classical
  set C : Finset Word := (cands s).toFinset with hC
  set B : ℕ → Finset Word := fun k => C.filter (fun w => ReachIn N x k N.init w) with hB
  have hBsub : ∀ k, B k ⊆ C := fun k => Finset.filter_subset _ _
  have hmem : ∀ (k : ℕ) (w : Word), w ∈ B k ↔ (w ∈ cands s ∧ ReachIn N x k N.init w) := by
    intro k w
    simp [hB, hC]
  have hmono : ∀ (k k' : ℕ), k ≤ k' → B k ⊆ B k' := by
    intro k k' hkk' w hw
    rw [hmem] at hw ⊢
    exact ⟨hw.1, ReachIn_mono N x hkk' hw.2⟩
  have hstep : ∀ k, B (k + 1) = B k → B (k + 2) = B (k + 1) := by
    intro k hk
    apply Finset.Subset.antisymm _ (hmono _ _ (by omega))
    intro w hw
    rw [hmem] at hw ⊢
    refine ⟨hw.1, ?_⟩
    obtain ⟨j, hj, hs⟩ := hw.2
    by_cases hjk : j ≤ k + 1
    · exact ⟨j, hjk, hs⟩
    · have hj2 : j = k + 2 := by omega
      subst hj2
      obtain ⟨m, hm, hmw⟩ := hs
      have hmreach : N.Reach x N.init m := stepsTo_reach N x (k + 1) _ _ hm
      have hmB : m ∈ B (k + 1) := by
        rw [hmem]
        exact ⟨mem_cands.2 (hsp m hmreach), ⟨k + 1, le_rfl, hm⟩⟩
      rw [hk, hmem] at hmB
      obtain ⟨j', hj', hs'⟩ := hmB.2
      exact ⟨j' + 1, by omega, m, hs', hmw⟩
  have hstab : ∀ k, B (k + 1) = B k → ∀ j, k ≤ j → B j = B k := by
    intro k hk j hj
    induction j with
    | zero =>
      have : k = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with hlt | hge
      · have hjk : k ≤ j := by omega
        have hBj : B j = B k := ih hjk
        -- from stabilisation at `k` we propagate one more step
        have key : ∀ i, k ≤ i → B (i + 1) = B i := by
          intro i hi
          induction i with
          | zero =>
            have : k = 0 := by omega
            rw [← this]; exact hk
          | succ i ih2 =>
            rcases Nat.lt_or_ge k (i + 1) with h1 | h2
            · exact hstep i (ih2 (by omega))
            · have : k = i + 1 := by omega
              rw [this] at hk; exact hk
        rw [key j hjk, hBj]
      · have : k = j + 1 := by omega
        rw [this]
  have hex : ∃ k ≤ C.card, B (k + 1) = B k := by
    by_contra hcon
    push_neg at hcon
    have hcard : ∀ k, k ≤ C.card + 1 → k ≤ (B k).card := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro hk
        have hk' : k ≤ C.card := by omega
        have hne : B (k + 1) ≠ B k := hcon k hk'
        have hss : B k ⊂ B (k + 1) :=
          lt_of_le_of_ne (hmono k (k + 1) (by omega)) (fun h => hne h.symm)
        have := Finset.card_lt_card hss
        have := ih (by omega)
        omega
    have h1 := hcard (C.card + 1) le_rfl
    have h2 : (B (C.card + 1)).card ≤ C.card := Finset.card_le_card (hBsub _)
    omega
  obtain ⟨k, hkC, hk⟩ := hex
  obtain ⟨n, hn⟩ := (reach_iff_stepsTo N x N.init v).1 hv
  have hvC : v ∈ cands s := mem_cands.2 (hsp v hv)
  have hvB : v ∈ B (max n k) := by
    rw [hmem]
    exact ⟨hvC, ⟨n, le_max_left _ _, hn⟩⟩
  rw [hstab k hk (max n k) (le_max_right _ _), hmem] at hvB
  have hCcard : C.card ≤ (cands s).length := List.toFinset_card_le _
  exact ReachIn_mono N x (le_trans hkC hCcard) hvB.2

/-! ### The Savitch predicate -/

/-- The Savitch doubling predicate: `R N x s d u v` says that `v` can be reached from `u`
in at most `2 ^ d` steps, using only intermediate configurations of length at most `s`. -/

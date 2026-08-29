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
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/

lemma Rset_subset_n (hs : s < n) (m : ℕ) :
    Rset (n := n) (g := g) (s := s) m ⊆ Rset (n := n) (g := g) (s := s) n := by
  -- either some level repeats early, or the counts grow strictly
  have main : ∀ i : ℕ, (∃ k, k ≤ i ∧ Rset (n := n) (g := g) (s := s) (k + 1)
      = Rset (n := n) (g := g) (s := s) k) ∨ i + 1 ≤ cnt (n := n) (g := g) (s := s) i := by
    intro i
    induction i with
    | zero => right; rw [cnt_zero hs]
    | succ i ih =>
        rcases ih with ⟨k, hk, hkk⟩ | hcnt
        · exact Or.inl ⟨k, by omega, hkk⟩
        · by_cases hstep : Rset (n := n) (g := g) (s := s) (i + 1)
              = Rset (n := n) (g := g) (s := s) i
          · exact Or.inl ⟨i, by omega, hstep⟩
          · right
            have hsub := Rset_subset_succ hs (n := n) (g := g) (s := s) i
            have hlt : cnt (n := n) (g := g) (s := s) i < cnt (n := n) (g := g) (s := s) (i + 1) := by
              rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
              · exact h
              · exact absurd (Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)).symm hstep
            omega
  rcases main n with ⟨k, hk, hkk⟩ | hbad
  · rcases Nat.lt_or_ge m n with hm | hm
    · exact Rset_mono hs (le_of_lt hm)
    · have h1 : Rset (n := n) (g := g) (s := s) m = Rset (n := n) (g := g) (s := s) k := by
        have := Rset_stab (n := n) (g := g) (s := s) hkk (m - k)
        rwa [show k + (m - k) = m by omega] at this
      have h2 : Rset (n := n) (g := g) (s := s) n = Rset (n := n) (g := g) (s := s) k := by
        have := Rset_stab (n := n) (g := g) (s := s) hkk (n - k)
        rwa [show k + (n - k) = n by omega] at this
      rw [h1, h2]
  · have := cnt_le_n (n := n) (g := g) (s := s) n
    omega


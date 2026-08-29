/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: verified (builds, axiom-clean: propext, Classical.choice, Quot.sound)
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

namespace CS

/-- The `n`-fold concatenation `b ++ b ++ ... ++ b` of a word with itself. -/
abbrev pow {α : Type*} (b : List α) (n : ℕ) : List α := (List.replicate n b).flatten

/-- Any power of `b` lies in the Kleene star of the singleton language `{b}`. -/

theorem pow_mem_kstar {α : Type*} (b : List α) (n : ℕ) :
    CS.pow b n ∈ KStar.kstar ({b} : Language α) := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n b, rfl, ?_⟩
  intro y hy
  rw [List.eq_of_mem_replicate hy]
  exact Set.mem_singleton _

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0` such that every word `x ∈ L` of
length at least `p` can be split as `x = a ++ b ++ c` with `b` nonempty,
`|a| + |b| ≤ p`, and `a ++ bⁿ ++ c ∈ L` for all `n : ℕ`.

The proof takes `p` to be the number of states of a DFA recognising `L` and uses
Mathlib's `DFA.pumping_lemma`.
-/

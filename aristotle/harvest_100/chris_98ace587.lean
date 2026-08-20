import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/--
**Pumping lemma for regular languages.**

For every regular language `L` there is a pumping length `p > 0` such that every word `x ∈ L`
of length at least `p` can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p` and `b ≠ []`,
in such a way that `a ++ bⁿ ++ c ∈ L` for every `n : ℕ`.

The proof takes `p` to be the number of states of a DFA recognizing `L` and appeals to
`DFA.pumping_lemma` from Mathlib.
-/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ x ∈ L, p ≤ x.length →
      ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        ∀ n : ℕ, a ++ (List.replicate n b).flatten ++ c ∈ L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  have hne : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, fun x hx hlen => ?_⟩
  obtain ⟨a, b, c, hsplit, hlen', hb, hpump⟩ := M.pumping_lemma hx hlen
  refine ⟨a, b, c, hsplit, hlen', hb, fun n => ?_⟩
  refine hpump ?_
  rw [Language.mem_mul]
  refine ⟨a ++ (List.replicate n b).flatten, ?_, c, rfl, by simp⟩
  rw [Language.mem_mul]
  refine ⟨a, rfl, (List.replicate n b).flatten, ?_, rfl⟩
  rw [Language.mem_kstar]
  exact ⟨List.replicate n b, rfl, fun y hy => by
    simpa using (List.eq_of_mem_replicate hy)⟩

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


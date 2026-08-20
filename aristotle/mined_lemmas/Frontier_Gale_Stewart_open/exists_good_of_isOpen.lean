import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
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

namespace Frontier
namespace GaleStewart

variable {A : Type*} [Inhabited A]

/-- The initial segment of a play `f` of length `n`, padded with `default`. -/

lemma exists_good_of_isOpen [TopologicalSpace A] (hW : IsOpen W) {f : ℕ → A} (hf : f ∈ W) :
    ∃ n, Good W n (trunc f n) := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW f hf
  refine ⟨(I.sup id) + 1, ?_⟩
  intro g hg
  apply hsub
  intro i hi
  have hlt : i < (I.sup id) + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [hg i hlt, trunc_agree f _ hlt]
  exact (hu i hi).2

end GaleStewart

/-- **Gale–Stewart theorem for open games.**  Two players alternately choose moves from a
(nonempty, discrete) set `A` of moves, Player I moving at even stages and Player II at odd
stages, producing an infinite play `f : ℕ → A`.  Player I wins if `f` belongs to the payoff
set `W`, which is assumed to be open in the product topology.  Then the game is determined:
either Player I has a strategy winning against every strategy of Player II, or Player II has
a strategy winning against every strategy of Player I. -/

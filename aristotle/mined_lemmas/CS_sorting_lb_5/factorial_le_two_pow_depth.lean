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

namespace CS

/-- A comparison-sorting algorithm on `n` elements, modelled as a binary decision tree.

The hidden input is a permutation `σ : Equiv.Perm (Fin n)`, thought of as the ranking of the
`n` input elements: element `i` has rank `σ i`.  An internal node `node i j l r` compares
elements `i` and `j`; the algorithm continues in `l` if `σ i < σ j` and in `r` otherwise.
A leaf reports the permutation the algorithm has decided the input is. -/
inductive CTree (n : ℕ) : Type
  | leaf (p : Equiv.Perm (Fin n)) : CTree n
  | node (i j : Fin n) (l r : CTree n) : CTree n
  deriving Inhabited

namespace CTree

variable {n : ℕ}

/-- The output of the algorithm `t` on the input ranking `σ`. -/

theorem factorial_le_two_pow_depth (t : CTree n) (h : ∀ σ, t.run σ = σ) :
    Nat.factorial n ≤ 2 ^ t.depth := by
  classical
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ t.leaves.toFinset := by
    intro σ _
    simpa [List.mem_toFinset] using (h σ ▸ t.run_mem_leaves σ)
  have h1 : Nat.factorial n ≤ t.leaves.toFinset.card := by
    have := Finset.card_le_card hsub
    simpa [Fintype.card_perm] using this
  exact h1.trans <| (List.toFinset_card_le _).trans t.length_leaves_le

end CTree

/-- **Comparison-sorting lower bound for 5 elements.**
Any correct comparison sort of 5 elements (modelled as a binary decision tree whose internal
nodes compare two of the elements and whose leaves output a permutation) needs at least
`⌈log₂ (5!)⌉ = 7` comparisons in the worst case. -/

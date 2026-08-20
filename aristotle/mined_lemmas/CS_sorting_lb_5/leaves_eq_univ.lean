import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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

namespace CS

/-- A *comparison sorting algorithm* on `n` real-valued keys, modelled as a decision tree.
Each internal node `node i j l r` compares the keys at positions `i` and `j` of the input and
branches to `l` if `a i ≤ a j`, to `r` otherwise; each leaf outputs a permutation of the
positions (the claimed sorting order).  Only comparisons of input keys are allowed. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The permutation output by the algorithm on the input `a`. -/

theorem leaves_eq_univ {n : ℕ} (t : CompTree n)
    (hcorrect : ∀ a : Fin n → ℝ, Function.Injective a → StrictMono (a ∘ t.run a)) :
    t.leaves = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun p => ?_)
  obtain ⟨a, ha, hp⟩ := exists_input_with_sorting_perm p
  have : t.run a = p := sorting_perm_unique (hcorrect a ha) hp
  exact this ▸ t.run_mem_leaves a

/-- **Comparison-sorting lower bound.**  Any comparison sort of `5` elements, i.e. any decision
tree that only compares input keys and outputs a permutation sorting the input, must perform at
least `⌈log₂ (5!)⌉ = 7` comparisons in the worst case. -/

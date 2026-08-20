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

theorem exists_input_with_sorting_perm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∃ a : Fin n → ℝ, Function.Injective a ∧ StrictMono (a ∘ p) := by
  refine ⟨fun k => ((p.symm k : ℕ) : ℝ), ?_, ?_⟩
  · intro x y hxy
    simp only at hxy
    have h1 : (p.symm x : ℕ) = (p.symm y : ℕ) := by exact_mod_cast hxy
    have h2 : p.symm x = p.symm y := Fin.ext h1
    simpa using congrArg p h2
  · intro x y hxy
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact_mod_cast (Fin.val_strictMono hxy)

/-- A correct comparison sorting tree must have all `n!` permutations among its leaves. -/

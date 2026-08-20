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

theorem sorting_perm_unique {n : ℕ} {a : Fin n → ℝ}
    {σ p : Equiv.Perm (Fin n)} (hσ : StrictMono (a ∘ σ)) (hp : StrictMono (a ∘ p)) :
    σ = p := by
  have hρ : StrictMono ⇑(p⁻¹ * σ) := by
    intro x y hxy
    have h1 : a (σ x) < a (σ y) := hσ hxy
    by_contra hcon
    have h2 : (p⁻¹ * σ) y ≤ (p⁻¹ * σ) x := not_lt.mp hcon
    rcases eq_or_lt_of_le h2 with h3 | h3
    · have : σ y = σ x := by
        have := congrArg (fun k => p k) h3
        simpa [Equiv.Perm.mul_apply] using this
      have hxy' : x = y := σ.injective this.symm
      exact absurd (hxy' ▸ h1) (lt_irrefl _)
    · have := hp h3
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
        Equiv.Perm.inv_def] at this
      exact absurd h1 (not_lt.mpr this.le)
  have h4 : p⁻¹ * σ = 1 := (Equiv.Perm.monotone_iff _).mp hρ.monotone
  have h5 := congrArg (fun x => p * x) h4
  simpa [mul_assoc] using h5

/-- Every permutation of `Fin n` is realised as the sorting permutation of some injective input. -/

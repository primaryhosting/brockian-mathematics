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
import RequestProject.PolySpace

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Unbounded fan-in Boolean circuits and their low-degree approximation

We define constant-depth, unbounded fan-in Boolean circuits over the basis
`{¬, ∨, ∧}` and prove Razborov's approximation lemma: a circuit of size `s`
and depth `d` is computed by a function of `F₃`-degree at most `(2ℓ)^d`
on all but a `s·2^{-ℓ}` fraction of the inputs.
-/

namespace CS

open Finset

/-- Unbounded fan-in Boolean circuits on `n` inputs. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | cst : Bool → Circ n
  | neg : Circ n → Circ n
  | orG : (k : ℕ) → (Fin k → Circ n) → Circ n
  | andG : (k : ℕ) → (Fin k → Circ n) → Circ n

/-- The Boolean function computed by a circuit. -/

lemma orApprox_mem {n k ℓ D : ℕ} (g : Fin k → Fn n) (hg : ∀ i, g i ∈ V n D)
    (r : Fin ℓ → Fin k → Bool) : orApprox g r ∈ V n (2 * ℓ * D) := by
  have hfac : ∀ j : Fin ℓ,
      (1 - (∑ i : Fin k, (if r j i then g i else 0)) ^ 2) ∈ V n (2 * D) := by
    intro j
    have hs : (∑ i : Fin k, (if r j i then g i else 0)) ∈ V n D := by
      refine Submodule.sum_mem _ (fun i _ => ?_)
      by_cases h : r j i
      · simpa [h] using hg i
      · simp [h]
    have : (∑ i : Fin k, (if r j i then g i else 0)) ^ 2 ∈ V n (D + D) := by
      rw [pow_two]; exact V_mul hs hs
    refine Submodule.sub_mem _ one_mem_V (V_mono ?_ this)
    omega
  have hprod : (∏ j : Fin ℓ, (1 - (∑ i : Fin k, (if r j i then g i else 0)) ^ 2))
      ∈ V n ((Finset.univ : Finset (Fin ℓ)).card * (2 * D)) := by
    refine prod_mem_pow (V n) (fun _ => one_mem_V) (fun hf hg => V_mul hf hg) _ _ _
      (fun j _ => hfac j)
  refine Submodule.sub_mem _ one_mem_V (V_mono ?_ hprod)
  simp only [Finset.card_univ, Fintype.card_fin]
  exact le_of_eq (by ring)

/-! ### The gate lemma -/


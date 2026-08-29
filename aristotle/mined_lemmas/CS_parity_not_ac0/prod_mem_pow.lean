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

lemma prod_mem_pow {n : ℕ} {ι : Type*} (U : ℕ → Submodule F3 (Fn n))
    (hone : ∀ D, (1 : Fn n) ∈ U D)
    (hmul : ∀ {D₁ D₂ : ℕ} {f g : Fn n}, f ∈ U D₁ → g ∈ U D₂ → f * g ∈ U (D₁ + D₂))
    (s : Finset ι) (h : ι → Fn n) (D : ℕ) (hh : ∀ i ∈ s, h i ∈ U D) :
    (∏ i ∈ s, h i) ∈ U (s.card * D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hone 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : h a ∈ U D := hh a (by simp)
      have h2 : (∏ i ∈ s, h i) ∈ U (s.card * D) := ih (fun i hi => hh i (by simp [hi]))
      have h3 := hmul h1 h2
      rwa [show D + s.card * D = (s.card + 1) * D by ring] at h3


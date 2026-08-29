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

lemma W_mul {n D₁ D₂ : ℕ} {f g : Fn n} (hf : f ∈ W n D₁) (hg : g ∈ W n D₂) :
    f * g ∈ W n (D₁ + D₂) := by
  have key : W n D₁ * W n D₂ ≤ W n (D₁ + D₂) := by
    rw [W, W, Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro h ⟨a, ⟨S, hS, rfl⟩, b, ⟨T, hT, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨symmDiff S T, ?_, monY_mul S T⟩
    exact le_trans (card_symmDiff_le S T) (Nat.add_le_add hS hT)
  exact key (Submodule.mul_mem_mul hf hg)

/-- A product of `S.card` functions of degree `≤ 1` has degree `≤ S.card`. -/

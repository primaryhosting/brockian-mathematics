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

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-! ## The quantum ingredients

We work with two qubits, i.e. with `ℂ⁴` indexed by `Fin 4`, where the index `2*a + b`
stands for the product basis vector `|a⟩ ⊗ |b⟩`.
-/

/-- The inner product on `ℂ⁴` (conjugate-linear in the first argument). -/

noncomputable def psiOnticModel : OntologicalModel (Fin 2) where
  mu := fun a l => if l = a then 1 else 0
  mu_nonneg := by intro a l; split <;> norm_num
  mu_sum := by intro a; fin_cases a <;> simp
  P := fun l₁ l₂ i => Complex.normSq (ip (xi i) (phi l₁ l₂))
  P_nonneg := fun _ _ _ => Complex.normSq_nonneg _
  P_sum := fun l₁ l₂ => born_sum l₁ l₂
  born := by intro a b i; fin_cases a <;> fin_cases b <;> simp

/-- Reformulation: the supports of the two ontic distributions are disjoint sets. -/

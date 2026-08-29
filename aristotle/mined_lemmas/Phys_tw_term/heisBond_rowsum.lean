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
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma heisBond_rowsum : ∀ p, ∑ q, ‖heisBond p q‖ ≤ 1 := by
  rintro ⟨p1, p2⟩
  fin_cases p1 <;> fin_cases p2 <;>
    norm_num [heisBond, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]

/-- The hypotheses of `lieb_schultz_mattis` are consistent: they are all satisfied (for the
trivial Hamiltonian) as soon as the zero magnetization sector is nonempty. -/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
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

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ pᵢ log pᵢ` of a finite family of reals. -/

noncomputable def cutEquiv (d N x : ℕ) :
    ((Fin N) → Fin d) ≃
      (({i : Fin N // (i : ℕ) < x} → Fin d) × ({i : Fin N // ¬ (i : ℕ) < x} → Fin d)) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin N => (i : ℕ) < x) (fun _ => Fin d)

/-- The matricization (Schmidt matrix) of a state `psi` of the chain across the cut at `x`:
rows are labelled by configurations of the left block, columns by those of the right block. -/

/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace Phys

open Representation

variable {k G M N : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The range of an intertwining map, as a subrepresentation of the target. -/

def trivialSubrepOrderIso :
    Subrepresentation (Representation.trivial k G V) ≃o Submodule k V where
  toFun := Subrepresentation.toSubmodule
  invFun p := ⟨p, by intro g v hv; simpa using hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance : (Representation.trivial k G k).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff trivialSubrepOrderIso).mpr inferInstance

/-- The hypotheses of the Wigner–Eckart theorem are satisfiable: here `U = V = W = ℂ` carry the
trivial representation of `G` and the Clebsch–Gordan map is the canonical isomorphism
`ℂ ⊗ ℂ ≃ ℂ`. -/

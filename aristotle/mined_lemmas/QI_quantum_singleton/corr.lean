/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/

noncomputable def corr {n q : ℕ} (S : Finset (Fin n)) (x y : HSpace n q) (u v : Str n q) : ℂ :=
  ∑ w : Str n q, conj (x (glue S u w)) * y (glue S v w)

/-- The Knill–Laflamme error-detection condition for the sites `S`: for every error operator
supported on `S`, the operator acts on the code space as a multiple of the identity.  It is
enough to require this for the elementary errors `|u⟩⟨v|_S ⊗ I`, whose matrix elements are
computed by `corr`.  Equivalently, the erasure of the sites in `S` is correctable. -/

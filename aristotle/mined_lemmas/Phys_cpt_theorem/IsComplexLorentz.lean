import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the algebraic core of the CPT theorem in the Wightman framework.

A (scalar) `n`-point Wightman function, analytically continued to complex Minkowski
space, is a function `W : (Fin n → (Fin 4 → ℂ)) → ℂ`.

* *Lorentz invariance* (together with analyticity of the Wightman functions, which is
  what allows the real proper orthochronous group to be replaced by the complex Lorentz
  group) is expressed as invariance of `W` under every complex Lorentz matrix that is
  connected to the identity by a continuous path inside the complex Lorentz group.
* *Locality* enters through weak local commutativity: at Jost points the Wightman
  function is invariant under total reversal of its arguments.
* *CPT invariance* is the statement `W (x₁, …, x_n) = W (-x_n, …, -x₁)`.

The mathematical content is `Phys.negOne_connectedToOne`: the total space-time inversion
`-1` lies in the identity component of the complex Lorentz group (this is false for the
*real* Lorentz group), witnessed by the explicit path

`t ↦ (complex boost by rapidity `i t` in the 01-plane) ⊕ (rotation by `t` in the 23-plane)`

which joins `1` (at `t = 0`) to `-1` (at `t = π`).
-/

namespace Phys

open Matrix Complex

/-- The Minkowski metric `diag (1, -1, -1, -1)`, as a complex matrix. -/

def IsComplexLorentz (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  M.transpose * minkowskiEta * M = minkowskiEta

/-- `M` lies in the identity component of the complex Lorentz group: it is joined to the
identity by a continuous path of complex Lorentz transformations. -/

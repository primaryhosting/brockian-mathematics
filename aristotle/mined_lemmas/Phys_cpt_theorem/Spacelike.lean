/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

set_option grind.warning false

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/

def Spacelike (x y : CVec) : Prop :=
  (mform (x - y) (x - y)).im = 0 ∧ (mform (x - y) (x - y)).re < 0

/-- A Lorentz-invariant local quantum field theory, presented through its analytically
continued Wightman functions.

* `W n` is the `n`-point Wightman function on complexified Minkowski space;
* `lorentz_invariant` records Lorentz invariance: by the standard analytic continuation of
  the Wightman functions into the extended tube, invariance under the real proper
  orthochronous Lorentz group upgrades to invariance under the whole identity component of
  the complex Lorentz group;
* `local_commutativity` records locality, i.e. Bose symmetry of the Wightman functions under
  exchange of spacelike separated arguments. -/
structure QFT where
  /-- The `n`-point Wightman functions. -/
  W : (n : ℕ) → (Fin n → CVec) → ℂ
  /-- Invariance under the identity component of the complex Lorentz group. -/
  lorentz_invariant : ∀ (n : ℕ) (L : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin n → CVec),
    ConnectedToId L → W n (fun i => L.mulVec (x i)) = W n x
  /-- Locality: the Wightman functions are symmetric under exchange of spacelike separated
  arguments. -/
  local_commutativity : ∀ (n : ℕ) (x : Fin n → CVec) (i j : Fin n),
    Spacelike (x i) (x j) → W n (x ∘ Equiv.swap i j) = W n x

/-- The CPT transformation on complexified Minkowski space: total inversion `x ↦ -x` of all
spacetime coordinates. -/

/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The support of a nearest-neighbour bond gate sitting on the bond `i` of the
spin chain `ℤ`: the two sites `i` and `i + 1`. -/

def edge (i : ℤ) : Set ℤ := {i, i + 1}

/-- A net of local observable algebras over the one dimensional spin chain `ℤ`.

`loc S` is the set of observables supported in the region `S`.  The axioms are the
defining features of a quantum spin system: locality is monotone in the region,
each local set is closed under products and contains the identity, and observables
supported in disjoint regions commute. -/
structure LocalNet (A : Type*) [Ring A] where
  /-- The observables supported in a region. -/
  loc : Set ℤ → Set A
  one_mem : ∀ S : Set ℤ, (1 : A) ∈ loc S
  mul_mem : ∀ {S : Set ℤ} {x y : A}, x ∈ loc S → y ∈ loc S → x * y ∈ loc S
  mono : ∀ {S T : Set ℤ}, S ⊆ T → loc S ⊆ loc T
  commute_of_disjoint :
    ∀ {S T : Set ℤ} {x y : A}, Disjoint S T → x ∈ loc S → y ∈ loc T → x * y = y * x

variable {A : Type*} [Ring A]

/-- A nearest-neighbour gate: an invertible observable `u` (with inverse `v`)
supported on a single bond of the chain.  Conjugation by such a gate is an
elementary step of a local discrete-time dynamics. -/
structure Gate (N : LocalNet A) where
  /-- The bond on which the gate acts. -/
  bond : ℤ
  /-- The gate. -/
  u : A
  /-- Its inverse. -/
  v : A
  u_mem : u ∈ N.loc (edge bond)
  v_mem : v ∈ N.loc (edge bond)
  uv : u * v = 1
  vu : v * u = 1

variable {N : LocalNet A}

/-- Conjugation of an observable by a list of gates. -/

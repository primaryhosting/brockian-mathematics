import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

def swap12 (X Y Z : Type*) : X × Y × Z ≃ Y × X × Z where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The matrix element of a weight-restricted matrix unit, computed in a splitting of the
qudits into the region `S` carrying the operator and two further groups. -/

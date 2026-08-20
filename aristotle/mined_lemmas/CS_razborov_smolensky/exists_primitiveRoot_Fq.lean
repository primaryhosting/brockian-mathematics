import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem exists_primitiveRoot_Fq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    ∃ ζ : Fq q, IsPrimitiveRoot ζ p := by
  have : NeZero ((p : ZMod q)) := by
    constructor
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
      ((ZMod.natCast_eq_zero_iff p q).1 h)).symm
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod q)) p

/-- Padding an input with `r` ones. -/

import Mathlib

/-!
# Fermat Little
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.fermat_little
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

namespace NumberTheory

/-- **Fermat's little theorem**, stated over `ZMod p`: for a prime `p` and any
`x : ZMod p`, we have `x ^ p = x`. -/
theorem fermat_little (p : ℕ) [Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x :=
  ZMod.pow_card x

/-- Integer form of Fermat's little theorem: `a ^ p ≡ a [ZMOD p]` for `p` prime. -/
theorem fermat_little_int (p : ℕ) (hp : Nat.Prime p) (a : ℤ) :
    a ^ p ≡ a [ZMOD (p : ℤ)] := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h : ((a ^ p : ℤ) : ZMod p) = ((a : ℤ) : ZMod p) := by
    push_cast
    exact fermat_little p (a : ZMod p)
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h

end NumberTheory

#print axioms NumberTheory.fermat_little
#print axioms NumberTheory.fermat_little_int


/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because a module docstring is a
-- command and Lean 4 requires `import` lines to precede every command in a file.)

import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/-- The "simple-group input" of the Feit–Thompson theorem, in universe `u`:
every finite **simple** group of odd order is abelian (equivalently, of prime order). -/

theorem oddSimpleAbelian_of_restricted (H : OddSimpleAbelianRestricted.{u}) :
    OddSimpleAbelian.{u} := by
  intro G _ _ hodd hsimple
  haveI := hsimple
  by_cases hpp : IsPrimePow (Nat.card G)
  · obtain ⟨p, k, hp, hk, hcard⟩ := hpp
    haveI : IsSolvable G :=
      feit_thompson_primePow (p := p) (n := k) (Nat.prime_iff.mpr hp) hcard.symm
    exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr inferInstance
  · by_cases hsq : Squarefree (Nat.card G)
    · haveI : IsSolvable G := feit_thompson_squarefree hsq
      exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr inferInstance
    · exact H G hodd hsimple hpp hsq

/-- **Feit–Thompson, sharpened reduction.**  Every finite group of odd order is solvable as soon
as every finite simple group of odd order which is neither of prime power order nor of squarefree
order is abelian. -/

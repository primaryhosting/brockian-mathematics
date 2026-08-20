/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import RequestProject.CauchySelfContained

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`.

The proof is self-contained (it does not invoke Mathlib's `exists_prime_orderOf_dvd_card`):
see `Math.cauchy_of_dvd_card`, which argues by strong induction on the order of the group. -/

lemma card_conjClass_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  classical
  cases nonempty_fintype G
  have h1 : (ConjClasses.mk g).carrier = MulAction.orbit (ConjAct G) g :=
    (ConjAct.orbit_eq_carrier_conjClasses g).symm
  have h2 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have h3 : MulAction.stabilizer (ConjAct G) g = Subgroup.centralizer {ConjAct.toConjAct g} :=
    ConjAct.stabilizer_eq_centralizer g
  have h5 : Nat.card ↑(MulAction.stabilizer (ConjAct G) g)
      = Nat.card ↑(Subgroup.centralizer ({g} : Set G)) := by
    rw [h3]
    rfl
  have h4 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.ofConjAct.toEquiv
  calc Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g})
      = Nat.card (MulAction.orbit (ConjAct G) g)
          * Nat.card ↑(MulAction.stabilizer (ConjAct G) g) := by rw [h1, h5]
    _ = Nat.card (ConjAct G) := by simpa [Nat.card_eq_fintype_card] using h2
    _ = Nat.card G := h4

/-- If no proper subgroup of `G` has order divisible by the prime `p`, but `p` divides the
order of `G`, then `G` is its own centre. -/

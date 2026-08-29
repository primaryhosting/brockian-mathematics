/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A proof of Cauchy's theorem: if a prime `p` divides the order of a finite group `G`,
then `G` has an element of order `p`.

The argument here is the classical one, by strong induction on `|G|`:

* if some proper subgroup `H < G` has order divisible by `p`, apply the induction hypothesis
  to `H`;
* otherwise the class equation forces `p ∣ |Z(G)|`, so `Z(G)` is not proper, i.e. `G` is
  abelian.  Picking `x ≠ 1` and setting `H = ⟨x⟩`, either `H = G` (and then `p ∣ orderOf x`),
  or `H` is proper and `p ∣ [G : H] = |G ⧸ H| < |G|`, so the induction hypothesis produces an
  element of order `p` in the quotient, which lifts to an element of `G` whose order is
  divisible by `p`.
-/

namespace Math

namespace CauchyProof

/-- From an element whose order is divisible by the prime `p` one extracts an element of
order exactly `p`. -/

theorem cauchy_group_natCard {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p :=
  CauchyProof.exists_orderOf_eq_prime_aux hp (Nat.card G) G rfl hdvd

/-- Cauchy's theorem, subgroup form: if a prime `p` divides `|G|` then `G` has a subgroup
of order `p`. -/

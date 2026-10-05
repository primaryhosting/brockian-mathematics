/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order `|G|` of a finite group `G`,
then `G` contains an element of order exactly `p`. -/

theorem cauchy_addGroup {A : Type*} [AddGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card A) : ∃ a : A, addOrderOf a = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_addOrderOf_dvd_card' p hdvd

/-- Subgroup form of Cauchy's theorem: if a prime `p` divides `|G|`, then `G` has a
subgroup of order `p`. -/

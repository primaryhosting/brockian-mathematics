import Mathlib

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order `|G|` of a finite group `G`,
then `G` contains an element of order exactly `p`. -/
theorem cauchy_group {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p hdvd

/-- Cauchy's theorem, `Fintype.card` version. -/
theorem cauchy_group_fintype {G : Type*} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p :=
  cauchy_group hp (by rwa [Nat.card_eq_fintype_card])

/-- Subgroup form of Cauchy's theorem: if a prime `p` divides `|G|`, then `G` has a
subgroup of order `p`. -/
theorem cauchy_group_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨x, hx⟩ := cauchy_group hp hdvd
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

end Math


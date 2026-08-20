import Mathlib
namespace MS.Algebra


theorem cauchy_theorem_group {G : Type*} [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  exists_prime_orderOf_dvd_card p hd


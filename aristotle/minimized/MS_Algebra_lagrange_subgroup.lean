import Mathlib
namespace MS.Algebra

theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  classical
  simpa using Subgroup.card_subgroup_dvd_card H

/-- Cayley–Hamilton. The original statement used `Polynomial.C` as the coefficient map,
which does not typecheck (`eval₂` needs a ring hom `ℂ →+* Matrix (Fin n) (Fin n) ℂ`);
it has been replaced by the canonical `algebraMap`, which is the intended meaning. -/

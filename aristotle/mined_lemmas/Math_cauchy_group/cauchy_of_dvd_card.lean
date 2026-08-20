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

theorem cauchy_of_dvd_card (p : ℕ) (hp : p.Prime) :
    ∀ n : ℕ, p ∣ n → CauchyAt.{u} p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hdvd G _ _ hcard
    subst hcard
    by_cases hsub : ∃ H : Subgroup G, H ≠ ⊤ ∧ p ∣ Nat.card H
    · obtain ⟨H, hHne, hHdvd⟩ := hsub
      have hlt : Nat.card H < Nat.card G :=
        card_subgroup_lt_card_of_ne_top hHne
      obtain ⟨g, hg⟩ := IH (Nat.card H) hlt hHdvd H inferInstance inferInstance rfl
      exact ⟨(g : G), by simpa using hg⟩
    · push_neg at hsub
      have hcenter : Subgroup.center G = ⊤ :=
        center_eq_top_of_no_proper_subgroup hp hdvd (fun H hH => hsub H hH)
      let _ : CommGroup G := Group.commGroupOfCenterEqTop hcenter
      exact cauchy_abelian hp hdvd (fun m hm hm' => IH m hm hm')

end Math


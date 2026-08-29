/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {D : Type u} {R : Type v} {Z : Type w}

/-
A **system** is described by a response map `psi : D → R → Z`: when the disturbance
(system state) is `d` and the regulator emits the action `a`, the outcome is `psi d a`.
-/

/-- `r` is a *good regulator* for the system `psi` with respect to the target outcome `z₀`
if it always steers the outcome to `z₀`, i.e. regulation succeeds for every disturbance. -/

theorem not_isModel_imp (psi : D → R → Z) (z₀ : Z) (r : D → R)
    (h : ¬ IsModel psi r) :
    ¬ IsGoodRegulator psi z₀ r ∨ ¬ NoSpareVariety psi z₀ := by
  by_cases hgood : IsGoodRegulator psi z₀ r
  · by_cases huniq : NoSpareVariety psi z₀
    · refine absurd (fun d d' hdd' => ?_) h
      have h1 : psi d' (r d) = z₀ := by rw [← hdd']; exact hgood d
      exact huniq d' (r d) (r d') h1 (hgood d')
    · exact Or.inr huniq
  · exact Or.inl hgood

/-- **Conant–Ashby good regulator theorem (deterministic base case).**
Every good regulator of a system is (contains) a model of that system: if `r` regulates the
system `psi` to the target outcome `z₀`, and the system leaves the regulator no spare variety,
then `r` is a model of `psi` — its behaviour is a function `m` of the system's own response
map, i.e. `r d = m (psi d)` for all disturbances `d`. (The `Nonempty R` instance is only needed
in order to name such an `m` when there are no disturbances at all; the factorisation of the
regulator through the system is the content of the statement.) -/

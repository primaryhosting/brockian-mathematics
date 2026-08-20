import Mathlib

/-!
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
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

namespace Brockian
namespace ConeLine

/-- A prime `q` greater than `5` is not divisible by `5`. -/
theorem not_dvd_five_of_prime_gt_five {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) :
    q % 5 ≠ 0 := by
  intro h0
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h0
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h1 <;> omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` visits all four nonzero
residue classes mod `5`, in the order `(1, 3, 2, 4)`. -/
theorem quadruplet_visits_all_active_rays {p : ℕ} (hp : Nat.Prime p)
    (hp2 : Nat.Prime (p + 2)) (hp6 : Nat.Prime (p + 6)) (hp8 : Nat.Prime (p + 8))
    (h5 : 5 < p) :
    p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2 ∧ (p + 8) % 5 = 4 := by
  have h0 : p % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp h5
  have h2 : (p + 2) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp6 (by omega)
  have h8 : (p + 8) % 5 ≠ 0 := not_dvd_five_of_prime_gt_five hp8 (by omega)
  omega

/-- The hypotheses of `quadruplet_visits_all_active_rays` are satisfiable: `p = 11` gives the
prime quadruplet `(11, 13, 17, 19)`. So the theorem above is not vacuous. -/
theorem exists_prime_quadruplet_gt_five :
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧ Nat.Prime (p + 6) ∧ Nat.Prime (p + 8) ∧ 5 < p :=
  ⟨11, by norm_num⟩

end ConeLine
end Brockian


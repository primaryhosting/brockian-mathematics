import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
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

namespace Brockian.ConeLine

/-- A prime `q` bigger than `5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
theorem prime_gt_five_mod_five_ne_zero {q : ℕ} (hq : Nat.Prime q) (h5 : 5 < q) :
    q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  have : (5 : ℕ) = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A Sophie Germain prime `p > 5` never lies on "ray 2": `p % 5 ≠ 2`, and the pair of
residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime)
    (hgt : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨
        (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hp0 : p % 5 ≠ 0 := prime_gt_five_mod_five_ne_zero hp hgt
  have hq0 : (2 * p + 1) % 5 ≠ 0 :=
    prime_gt_five_mod_five_ne_zero hq (by omega)
  have hmod : (2 * p + 1) % 5 = (2 * (p % 5) + 1) % 5 := by omega
  have hcases : p % 5 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  refine ⟨by omega, ?_⟩
  simp only [Prod.mk.injEq]
  rcases hcases with h | h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl ⟨h, by omega⟩)
  · exact Or.inr (Or.inr ⟨h, by omega⟩)

end Brockian.ConeLine


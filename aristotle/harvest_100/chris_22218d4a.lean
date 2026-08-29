import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `q` with `5 < q` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : q.Prime) (h5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A Sophie Germain prime `p > 5` never sits on ray 2: the residue pair
`(p % 5, (2*p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime)
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧ ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
      (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have h1 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (2 * p + 1) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have h3 : p % 5 ≠ 2 := by omega
  refine ⟨h3, ?_⟩
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

import Mathlib

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


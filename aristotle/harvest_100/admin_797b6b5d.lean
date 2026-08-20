import Mathlib
/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
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

/-- A prime `n` greater than `5` is not divisible by `5`. -/
theorem five_not_dvd_of_prime_gt_five {n : ℕ} (hn : n.Prime) (h : 5 < n) : n % 5 ≠ 0 := by
  intro hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hn 5 (Nat.dvd_of_mod_eq_zero hmod)) with h1 | h2
  · omega
  · omega

/-- **Sexy prime roads.** If `p` and `p + 6` are both prime and `p > 5`, then the pair of
residues `(p % 5, (p + 6) % 5)` is one of `(1,2)`, `(2,3)`, `(3,4)`: in particular
`p + 6 ≡ p + 1 (mod 5)` and neither endpoint lies on the residue-`0` ray. -/
theorem sexy_prime_roads (p : ℕ) (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : p % 5 ≠ 0 := five_not_dvd_of_prime_gt_five hp h5
  have h2 : (p + 6) % 5 ≠ 0 := five_not_dvd_of_prime_gt_five hq (by omega)
  have h3 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  simp only [Prod.mk.injEq]
  omega

end ConeLine
end Brockian


/-
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/

lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) : q % 5 ≠ 0 := by
  intro h0
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h0
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h1 | h1 <;> omega

/-- A Sophie Germain prime `p > 5` never sits on ray 2 (`p % 5 ≠ 2`), and the pair of
residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/

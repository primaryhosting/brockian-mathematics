/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

theorem dvd_sub_of_mod_eq {p a b : Nat} (hm : a % p = b % p) : p ∣ (b - a) := by
  refine ⟨b / p - a / p, ?_⟩
  have h1 := Nat.div_add_mod b p
  have h2 := Nat.div_add_mod a p
  rw [Nat.mul_sub]
  omega

/-- A prime not dividing `m` is coprime to `m`. -/

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, stated in the usual way: `p ≥ 2` and every divisor of `p`
is `1` or `p`. (Spelled out here so that this file is fully self-contained.) -/

theorem isPrimeNat_two : IsPrimeNat 2 := by
  refine ⟨by omega, ?_⟩
  intro m hm
  have h1 : m ≤ 2 := Nat.le_of_dvd (by omega) hm
  cases m with
  | zero => exact absurd (Nat.eq_zero_of_zero_dvd hm) (by omega)
  | succ n => omega

/-- A gap pattern `H` (a finite list of shifts) is *admissible* when, for every prime `p`, the
residues of its members modulo `p` omit at least one residue class.  Admissibility is exactly the
condition under which the Hardy–Littlewood singular series attached to `H` is nonzero. -/

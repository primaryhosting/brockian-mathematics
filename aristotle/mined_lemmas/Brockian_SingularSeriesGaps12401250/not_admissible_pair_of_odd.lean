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

theorem not_admissible_pair_of_odd {g : Nat} (ho : g % 2 = 1) : ¬ IsAdmissibleGapSet [0, g] := by
  intro H
  have ⟨r, hr, hres⟩ := H 2 isPrimeNat_two
  have h0 := hres 0 (by simp)
  have h1 := hres g (by simp)
  omega

end Brockian


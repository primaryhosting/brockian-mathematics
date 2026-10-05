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

theorem admissible_iff_no_prime_covers (H : List Nat) :
    Admissible H ↔ ∀ p : Nat, IsPrime p → ¬ (∀ r : Nat, r < p → ∃ h ∈ H, h % p = r) := by
  constructor
  · intro hA p hp hcov
    obtain ⟨r, hr⟩ := hA p hp
    have hp0 : 0 < p := by have := hp.1; omega
    obtain ⟨h, hmem, hh⟩ := hcov (r % p) (Nat.mod_lt _ hp0)
    exact hr h hmem hh
  · intro hA p hp
    have hp0 : 0 < p := by have := hp.1; omega
    apply Classical.byContradiction
    intro hcon
    apply hA p hp
    intro r hr
    apply Classical.byContradiction
    intro hcon2
    exact hcon ⟨r, fun h hmem hh => hcon2 ⟨h, hmem, by rw [hh, Nat.mod_eq_of_lt hr]⟩⟩

/-! ## Elementary arithmetic facts -/

/-- Equal residues give a divisible difference. -/

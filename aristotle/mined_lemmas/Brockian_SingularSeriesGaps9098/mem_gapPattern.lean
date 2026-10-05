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

theorem mem_gapPattern {k M h : Nat} (hh : h ∈ gapPattern k M) : ∃ i, i < k ∧ h = i * M := by
  rw [gapPattern, List.mem_map] at hh
  obtain ⟨i, hi, rfl⟩ := hh
  exact ⟨i, List.mem_range.mp hi, rfl⟩

/-- **Singular Series Gaps 9098.**

New admissible gap ranges: for every common difference `M` that is divisible by all primes up
to the length `k`, the `k`-term arithmetic progression `{0, M, 2M, …, (k-1)M}` is an admissible
gap pattern, i.e. its Hardy–Littlewood singular series does not vanish.

The proof works via the contrapositive at each prime `p`: if `p ∣ M` the whole pattern sits in
the class `0 mod p`, so the class `1 mod p` is free; otherwise `p` is coprime to `M`, and the
class `k·M mod p` is free, since a collision would force `p ∣ k - i ≤ k`, hence `p ∣ M`. -/

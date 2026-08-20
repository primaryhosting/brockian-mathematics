import Mathlib
/-!
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- **Van der Waerden's theorem**: for any coloring `C : ℕ → κ` of the naturals by a finite
set of colors `κ`, and any length `k`, there is a monochromatic arithmetic progression
`b, b + a, …, b + (k-1) * a` with common difference `a > 0`.

This is deduced from the Hales–Jewett theorem, via Mathlib's
`Combinatorics.exists_mono_homothetic_copy`. -/

theorem van_der_waerden {κ : Type*} [Finite κ] (C : ℕ → κ) (k : ℕ) :
    ∃ a > 0, ∃ b, ∃ c, ∀ i < k, C (b + i * a) = c := by
  obtain ⟨a, ha, b, c, hc⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) C
  refine ⟨a, ha, b, c, fun i hi => ?_⟩
  have := hc i (Finset.mem_range.mpr hi)
  simpa [smul_eq_mul, Nat.add_comm, Nat.mul_comm] using this

/-- Set-theoretic form of van der Waerden's theorem: if `ℕ` is covered by finitely many
sets `S : ι → Set ℕ` (`ι` finite), then for every `k` one of the `S i` contains a
`k`-term arithmetic progression `{b + i * a | i < k}` with `a > 0`. -/

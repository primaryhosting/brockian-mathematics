/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` line to precede all other commands, while the
required header above is itself a command (a module docstring).  The development below is
therefore written against the Lean 4 core library only, with no `import` line, so that the
file both begins with the exact required header and compiles.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality, spelled out without Mathlib: `p ≥ 2` and the only divisors of `p` are `1` and
`p`. -/

theorem exists_index_of_covers {p : Nat} {h₀ h₁ h₂ h₃ : Int}
    (cov : CoversMod [h₀, h₁, h₂, h₃] p) (a : Int) :
    ∃ i : Nat, i < 4 ∧ (p : Int) ∣ (entry h₀ h₁ h₂ h₃ i - a) := by
  obtain ⟨h, hmem, hdvd⟩ := cov a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨1, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨2, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨3, by omega, by simpa [entry] using hdvd⟩

/-! ## The pigeonhole step: four integers cannot cover a modulus `p ≥ 5` -/

/-- **Contrapositive form of the reduction.** A `4`-tuple never covers a modulus `p ≥ 5`:
the five residues `0, 1, 2, 3, 4` would have to be represented by only four integers. -/

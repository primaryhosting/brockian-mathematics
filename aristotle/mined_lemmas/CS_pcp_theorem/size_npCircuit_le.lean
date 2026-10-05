import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
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

set_option grind.warning false

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem size_npCircuit_le :
    V.npCircuit.size ≤
      (2 ^ V.rlen + (2 ^ V.rlen * V.qnum) * (2 ^ V.rlen * V.qnum)) *
        (8 * V.size * V.size + 6 * V.size + 13) + 1 := by
  have hb : ∀ c ∈ V.npList, c.size ≤ 8 * V.size * V.size + 6 * V.size + 12 := by
    intro c hc
    simp only [npList, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hc
    rcases hc with ⟨r, rfl⟩ | ⟨p, rfl⟩
    · have := size_decC_le V r
      nlinarith [this, Nat.zero_le V.size]
    · exact size_consC_le V (Fin.pos p.1.2) p.1.1 p.1.2 p.2.1 p.2.2
  have := Circuit.size_bigAnd_le V.npList _ hb
  rw [length_npList] at this
  simpa [npCircuit] using this

end

end PCPVerifier

/-! ## The easy inclusion `PCP(log n, 1) ⊆ NP` -/

/-- **Every language with a logarithmic randomness, constant query PCP verifier is in NP.**
The certificate is a locally consistent table of answers to all the (polynomially many)
queries the verifier can make, and the NP circuit checks acceptance for every random
string together with the consistency of the table. -/

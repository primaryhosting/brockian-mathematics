/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is written as a
-- plain block comment rather than a `/-!` module docstring.)

import Mathlib

open scoped BigOperators
open scoped Matrix

namespace QI

/-! ## The 9-qubit register

We label the nine qubits by `Site = Fin 3 × Fin 3`: the first coordinate is the *block*
(one of three three-qubit repetition blocks) and the second the position inside the block.
A computational basis state is a bit string `Bits = Site → ZMod 2`, and a state vector is
its amplitude function `Amp = Bits → ℂ`.
-/

abbrev Site : Type := Fin 3 × Fin 3

abbrev Bits : Type := Site → ZMod 2

abbrev Amp : Type := Bits → ℂ

/-- The Hermitian inner product `⟪u, v⟫ = ∑_b conj (u b) * v b`. -/

lemma isCode_eq_zero_of_supp (M : Bits) (q q' : Site)
    (h : ∀ p, M p ≠ 0 → p = q ∨ p = q') (hM : isCode M) : M = 0 := by
  funext p
  simp only [Pi.zero_apply]
  by_contra hne
  obtain ⟨r, s⟩ := p
  have hb : M (r, 0) ≠ 0 := by rw [← hM r s]; exact hne
  have h0 : M (r, 0) ≠ 0 := hb
  have h1 : M (r, 1) ≠ 0 := by rw [hM r 1]; exact hb
  have h2 : M (r, 2) ≠ 0 := by rw [hM r 2]; exact hb
  have e0 := h (r, 0) h0
  have e1 := h (r, 1) h1
  have e2 := h (r, 2) h2
  have key : ∀ (s1 s2 : Fin 3) (x : Site), ((r, s1) : Site) = x → ((r, s2) : Site) = x → s1 = s2 :=
    fun s1 s2 x k1 k2 => congrArg Prod.snd (k1.trans k2.symm)
  clear h hne hb h0 h1 h2 hM
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact absurd (key 0 1 q e0 e1) (by decide)
  · exact absurd (key 0 1 q e0 e1) (by decide)
  · exact absurd (key 0 2 q e0 e2) (by decide)
  · exact absurd (key 1 2 q' e1 e2) (by decide)
  · exact absurd (key 1 2 q e1 e2) (by decide)
  · exact absurd (key 0 2 q' e0 e2) (by decide)
  · exact absurd (key 0 1 q' e0 e1) (by decide)
  · exact absurd (key 0 1 q' e0 e1) (by decide)

/-! ### The diagonal case `M = 0` -/


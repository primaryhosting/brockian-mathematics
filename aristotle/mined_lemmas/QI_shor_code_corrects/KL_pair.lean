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

lemma KL_pair (q q' : Site) (m z m' z' : Bits)
    (hm : ∀ p, m p ≠ 0 → p = q) (hz : ∀ p, z p ≠ 0 → p = q)
    (hm' : ∀ p, m' p ≠ 0 → p = q') (hz' : ∀ p, z' p ≠ 0 → p = q') :
    ipf (apU m z zeroL) (apU m' z' oneL) = 0 ∧
    ipf (apU m z oneL) (apU m' z' zeroL) = 0 ∧
    ipf (apU m z zeroL) (apU m' z' zeroL) = ipf (apU m z oneL) (apU m' z' oneL) := by
  have hsupp : ∀ (x y : Bits), (∀ p, x p ≠ 0 → p = q) → (∀ p, y p ≠ 0 → p = q') →
      ∀ p, (x + y) p ≠ 0 → p = q ∨ p = q' := by
    intro x y hx hy p hp
    simp only [Pi.add_apply] at hp
    by_cases h1 : x p = 0
    · right
      refine hy p ?_
      intro h2
      exact hp (by rw [h1, h2, add_zero])
    · exact Or.inl (hx p h1)
  rw [ipf_apU, ipf_apU, ipf_apU, ipf_apU]
  by_cases hM : isCode (m + m')
  · have hM0 : m + m' = 0 :=
      isCode_eq_zero_of_supp _ q q' (hsupp m m' hm hm') hM
    obtain ⟨r0, hr0, hr0'⟩ := exists_free_block q q'
    have hZ : ∀ s : Fin 3, (z + z') (r0, s) = 0 := by
      intro s
      simp only [Pi.add_apply]
      have h1 : z (r0, s) = 0 := by
        by_contra h
        exact hr0 (congrArg Prod.fst (hz _ h))
      have h2 : z' (r0, s) = 0 := by
        by_contra h
        exact hr0' (congrArg Prod.fst (hz' _ h))
      rw [h1, h2, add_zero]
    rw [hM0]
    refine ⟨?_, ?_, ?_⟩
    · rw [G_offdiag_zeroL_oneL _ r0 hZ, mul_zero]
    · rw [G_offdiag_oneL_zeroL _ r0 hZ, mul_zero]
    · rw [G_diag]
  · have h0 : ∀ u v : Amp, (∀ b, ¬ isCode b → u b = 0) → (∀ b, ¬ isCode b → v b = 0) →
        G (m + m') (z + z') u v = 0 :=
      fun u v hu hv => G_eq_zero_of_not_isCode _ _ u v hu hv hM
    rw [h0 zeroL oneL (fun _ => zeroL_off) (fun _ => oneL_off),
      h0 oneL zeroL (fun _ => oneL_off) (fun _ => zeroL_off),
      h0 zeroL zeroL (fun _ => zeroL_off) (fun _ => zeroL_off),
      h0 oneL oneL (fun _ => oneL_off) (fun _ => oneL_off)]
    simp

/-! ## Linearity of the inner product -/


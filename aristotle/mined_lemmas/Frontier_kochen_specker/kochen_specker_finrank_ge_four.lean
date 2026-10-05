/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The Kochen–Specker theorem states that in a Hilbert space of dimension at least three there is
no noncontextual hidden-variable assignment: one cannot assign to every ray a value in `{0, 1}`,
independently of the measurement context, in such a way that every orthonormal basis contains
exactly one ray of value `1`.

We formalise the four dimensional case, which is the base case admitting a purely combinatorial
(parity) proof, due to Cabello, Estebaranz and García-Alcaine: there are `18` vectors in
`ℝ⁴` arranged into `9` orthogonal frames so that every vector lies in exactly two frames.
Summing the value `1` over the nine frames counts each vector twice, giving `9 = 2 * k`,
which is impossible.

The main statement is `Frontier.kochen_specker`, with `Frontier.kochen_specker_basis` an
equivalent restatement in terms of `OrthonormalBasis`.
-/

set_option maxHeartbeats 1000000

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of four vectors which is *orthogonal and nondegenerate*: the inner product of
`v i` and `v j` vanishes exactly when `i ≠ j`.  Equivalently, the `v i` are nonzero and
pairwise orthogonal. -/

theorem kochen_specker_finrank_ge_four
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 4 ≤ finrank ℝ E) (f : E → Bool) :
    ¬ ∀ b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E, ∃! i, f (b i) = true := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = 4 + m := ⟨finrank ℝ E - 4, by omega⟩
  set b0 : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hb0
  obtain ⟨k, hk, hku⟩ := h b0
  set e0 : Fin 4 ⊕ Fin m ≃ Fin (finrank ℝ E) := finSumFinEquiv.trans (finCongr hm.symm) with he0
  set ε : Fin 4 ⊕ Fin m ≃ Fin (finrank ℝ E) := e0.trans (Equiv.swap (e0 (Sum.inl 0)) k) with hε
  have hεinl0 : ε (Sum.inl 0) = k := by simp [hε]
  set u : Fin 4 → E := fun i => b0 (ε (Sum.inl i)) with hu_def
  have hu : Orthonormal ℝ u :=
    b0.orthonormal.comp (fun i => ε (Sum.inl i)) (fun a b hab => by simpa using ε.injective hab)
  have hfalse : ∀ j : Fin m, f (b0 (ε (Sum.inr j))) = false := by
    intro j
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have hjk := hku _ hcon
    rw [← hεinl0] at hjk
    exact absurd (ε.injective hjk) (by simp)
  refine kochen_specker ⟨fun x => f (frameMap u x), ?_⟩
  intro v hv
  set w : Fin 4 ⊕ Fin m → E :=
    Sum.elim (fun i => frameMap u (v i)) (fun j => b0 (ε (Sum.inr j))) with hw_def
  have hperp : ∀ (i : Fin 4) (j : Fin m), inner ℝ (u i) (b0 (ε (Sum.inr j))) = (0 : ℝ) := by
    intro i j
    exact b0.orthonormal.2 (fun hcon => absurd (ε.injective hcon) (by simp))
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro s t
    cases s with
    | inl i =>
      cases t with
      | inl i' =>
        simpa [hw_def] using (orthonormal_iff_ite.mp (orthonormal_frameMap hu hv)) i i'
      | inr j =>
        simp only [hw_def, Sum.elim_inl, Sum.elim_inr]
        rw [inner_frameMap_eq_zero (fun kk => hperp kk j)]
        simp
    | inr j =>
      cases t with
      | inl i =>
        simp only [hw_def, Sum.elim_inl, Sum.elim_inr]
        rw [real_inner_comm, inner_frameMap_eq_zero (fun kk => hperp kk j)]
        simp
      | inr j' =>
        simp only [hw_def, Sum.elim_inr]
        rcases eq_or_ne j j' with rfl | hne
        · simp [b0.orthonormal.1 _]
        · have hne2 : ε (Sum.inr j) ≠ ε (Sum.inr j') :=
            fun hcon => hne (by simpa using ε.injective hcon)
          rw [b0.orthonormal.2 hne2]
          simp [hne]
  have hcard : Fintype.card (Fin 4 ⊕ Fin m) = finrank ℝ E := by simp [hm]
  set bb : OrthonormalBasis (Fin 4 ⊕ Fin m) ℝ E :=
    (basisOfOrthonormalOfCardEqFinrank hw hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hw) with hbb_def
  have hbb : ⇑bb = w := by
    rw [hbb_def, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  have h2 : ∃! s : Fin 4 ⊕ Fin m, f (w s) = true := by
    refine existsUnique_of_equiv e0 ?_
    simpa [OrthonormalBasis.reindex_apply, hbb] using h (bb.reindex e0)
  exact existsUnique_inl h2 (fun j => by simp [hw_def, hfalse j])

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


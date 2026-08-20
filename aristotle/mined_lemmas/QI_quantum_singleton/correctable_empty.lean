/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma correctable_empty (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (hV : Vᴴ * V = 1) :
    Correctable V (∅ : Finset (Fin n)) := by
  classical
  refine ⟨1, fun i j x y => ?_⟩
  have hglue : ∀ (w : Fin n → Fin q) (u : {i : Fin n // i ∈ (∅ : Finset (Fin n))} → Fin q),
      glue ∅ u (emptyComplEquiv n q w) = w := by
    intro w u
    funext t
    simp [glue, emptyComplEquiv]
  rw [← Equiv.sum_comp (emptyComplEquiv n q) (fun z => V (glue ∅ x z) i * conj (V (glue ∅ y z) j))]
  have hterm : ∀ w : Fin n → Fin q,
      V (glue ∅ x (emptyComplEquiv n q w)) i * conj (V (glue ∅ y (emptyComplEquiv n q w)) j)
      = conj (V w j) * V w i := by
    intro w; rw [hglue w x, hglue w y]; ring
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  have h1 : (Vᴴ * V) j i = ∑ w, conj (V w j) * V w i := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← h1, hV]
  have hxy : x = y := Subsingleton.elim _ _
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply, hxy]
  · simp [Matrix.one_apply, hij, Ne.symm hij]

/-- Merge configurations on three disjoint parts (`S1`, the rest, `S2`). -/

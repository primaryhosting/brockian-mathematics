/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

lemma card_le_pow_of_distance {d : ℕ} (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hMne : M ≠ 0)
    (hd : HasDistanceGE M d) (ha : a < d) (hb : b < d) :
    K ≤ q ^ c := by
  classical
  set M' : Matrix ((Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) (Fin K) ℂ :=
    Matrix.of fun P i => M (glue e P) i with hM'
  have hM'ne : M' ≠ 0 := by
    intro h0
    apply hMne
    ext x i
    obtain ⟨P, rfl⟩ := (glue_bijective e).surjective x
    simpa [hM'] using congrFun (congrFun h0 P) i
  choose σA0 hσA0 using fun u u' => correctable_of_distance e M hd ha u u'
  set e' : ((Fin b ⊕ Fin a) ⊕ Fin c) ≃ Fin n :=
    (Equiv.sumCongr (Equiv.sumComm (Fin b) (Fin a)) (Equiv.refl (Fin c))).trans e with he'
  have hglue' : ∀ (v : Fin b → Fin q) (u : Fin a → Fin q) (w : Fin c → Fin q),
      glue (q := q) e' (v, u, w) = glue (q := q) e (u, v, w) := by
    intro v u w
    funext i
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s <;> simp [glue, he']
  choose σB0 hσB0 using fun v v' => correctable_of_distance e' M hd hb v v'
  have hA' : ∀ (u u' : Fin a → Fin q) (i j : Fin K),
      ∑ p : (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M' (u, p.1, p.2) i) * M' (u', p.1, p.2) j
        = (Matrix.of σA0) u u' * (if i = j then 1 else 0) := by
    intro u u' i j
    simpa [hM'] using hσA0 u u' i j
  have hB' : ∀ (v v' : Fin b → Fin q) (i j : Fin K),
      ∑ p : (Fin a → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M' (p.1, v, p.2) i) * M' (p.1, v', p.2) j
        = (Matrix.of σB0) v v' * (if i = j then 1 else 0) := by
    intro v v' i j
    have h := hσB0 v v' i j
    simp only [hglue'] at h
    simpa [hM'] using h
  have hcard := card_le_of_two_correctable M' hM'ne (Matrix.of σA0) hA' (Matrix.of σB0) hB'
  simpa using hcard

/-- **The quantum Singleton bound.**  Let `M` be an isometric encoding of `K = q ^ k` logical
states into `n` qudits of local dimension `q ≥ 2` (the columns of `M` are an orthonormal basis
of the code), and suppose the code satisfies the Knill–Laflamme condition for distance `d`.
Then `2 * (d - 1) + k ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The hypothesis `1 ≤ k` is needed: a one-dimensional code satisfies the Knill–Laflamme
condition vacuously for every `d`. -/

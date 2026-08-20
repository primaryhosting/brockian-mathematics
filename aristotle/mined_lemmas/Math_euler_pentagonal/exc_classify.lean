import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma exc_classify {n : ℕ} (hn : 1 ≤ n) {s : Finset ℕ} (hs : s ∈ (D n).filter isExc) :
    ∃ m : ℕ, 1 ≤ m ∧
      ((s = Finset.Icc m (2 * m - 1) ∧ s.card = m ∧ fmax s + 1 = 2 * fmin s ∧
          2 * n = m * (3 * m - 1)) ∨
       (s = Finset.Icc (m + 1) (2 * m) ∧ s.card = m ∧ fmax s + 1 ≠ 2 * fmin s ∧
          2 * n = m * (3 * m + 1))) := by
  rw [Finset.mem_filter, mem_D_iff] at hs
  obtain ⟨⟨h0, hsum⟩, hexc⟩ := hs
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
    omega
  obtain ⟨hIcc, hcase⟩ := exc_eq h0 hne hexc
  have hσM : fmin s ≤ fmax s := le_fmax (fmin_mem hne)
  have hσpos : 0 < fmin s := fmin_pos h0 hne
  have hcard : s.card = fmax s + 1 - fmin s := by
    conv_lhs => rw [hIcc]
    rw [Nat.card_Icc]
  have hsum2 : n * 2 + fmin s * (fmin s - 1) = (fmax s + 1) * fmax s := by
    have h := sum_Icc_id (fmin s) (fmax s) (by omega)
    rw [← hIcc, hsum] at h
    exact h
  rcases hcase with hE | hE
  · refine ⟨fmin s, hσpos, Or.inl ⟨?_, ?_, hE, ?_⟩⟩
    · have e1 : 2 * fmin s - 1 = fmax s := by omega
      rw [e1]; exact hIcc
    · omega
    · obtain ⟨m, hm⟩ : ∃ m, fmin s = m + 1 := ⟨fmin s - 1, by omega⟩
      have hM : fmax s = 2 * m + 1 := by omega
      rw [hm, hM] at hsum2
      simp only [Nat.add_sub_cancel] at hsum2
      rw [hm]
      have h1 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
      rw [h1]
      nlinarith [hsum2]
  · have hτ : 2 ≤ fmin s := by omega
    refine ⟨fmin s - 1, by omega, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · have e1 : fmin s - 1 + 1 = fmin s := by omega
      have e2 : 2 * (fmin s - 1) = fmax s := by omega
      rw [e1, e2]; exact hIcc
    · omega
    · omega
    · obtain ⟨m, hm⟩ : ∃ m, fmin s = m + 1 := ⟨fmin s - 1, by omega⟩
      have hM : fmax s = 2 * m := by omega
      rw [hm, hM] at hsum2
      simp only [Nat.add_sub_cancel] at hsum2
      have h2 : fmin s - 1 = m := by omega
      rw [h2]
      nlinarith [hsum2]


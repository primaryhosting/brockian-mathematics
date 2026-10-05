import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Complex

/-- The graph Laplacian `L(C n)` of the cycle graph on `n` vertices: the `n × n` circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/

lemma cycleLaplacian_row (hn : 3 ≤ n) (f : Fin n → ℂ) (i : Fin n) :
    ∑ j, cycleLaplacian n i j * f j = 2 * f i - f (i + 1) - f (i - 1) := by
  have hone : ((1 : Fin n) : ℕ) = 1 := val_one (by omega)
  have hsucc : ∀ a : Fin n, ((a + 1 : Fin n) : ℕ) = (a.val + 1) % n :=
    fun a => val_add_one (by omega) a
  have hne1 : (1 : Fin n) ≠ 0 := by
    intro h; have h' := congrArg Fin.val h; simp at h'; omega
  have h11 : ((1 : Fin n) + 1) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [hsucc 1, hone, Nat.mod_eq_of_lt (by omega : 1 + 1 < n)] at h'
    simp at h'
  have hii1 : i ≠ i + 1 := by
    intro h
    have h' : i + 0 = i + 1 := by simpa using h
    exact hne1 (add_left_cancel h').symm
  have hii2 : i ≠ i - 1 := fun h => hne1 (sub_eq_self.1 h.symm)
  have h12 : (i + 1 : Fin n) ≠ i - 1 := by
    intro h
    refine h11 (add_left_cancel (a := i) ?_)
    rw [← add_assoc, h]
    simp
  have key : ∀ j : Fin n, cycleLaplacian n i j
      = 2 * (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0)
        - (if j = i - 1 then 1 else 0) := by
    intro j
    have ha : ((i.val + 1) % n = j.val) ↔ j = i + 1 := by
      rw [← hsucc i]
      exact ⟨fun h => (Fin.val_eq_val _ _).1 h.symm, fun h => by rw [h]⟩
    have hb : ((j.val + 1) % n = i.val) ↔ j = i - 1 := by
      rw [← hsucc j, eq_sub_iff_add_eq]
      exact ⟨fun h => (Fin.val_eq_val _ _).1 h, fun h => (Fin.val_eq_val _ _).2 h⟩
    simp only [cycleLaplacian, Matrix.of_apply, ha, hb]
    rcases eq_or_ne j i with hj | hj
    · subst hj
      rw [if_neg hii1, if_neg hii2]
      simp
    · rw [if_neg (Ne.symm hj), if_neg hj]
      rcases eq_or_ne j (i + 1) with hj1 | hj1
      · subst hj1
        rw [if_neg h12]
        simp
      · rcases eq_or_ne j (i - 1) with hj2 | hj2
        · subst hj2
          rw [if_neg (Ne.symm h12)]
          simp
        · simp [hj1, hj2]
  rw [Finset.sum_congr rfl (fun j _ => by rw [key j])]
  simp [sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq']

end Aux

/-- **Spectrum of the cycle Laplacian.**  For `n ≥ 3` the eigenvalues of the graph Laplacian
of the cycle `C n` are exactly the numbers `2 - 2 cos (2 π k / n)`, `k = 0, …, n-1`. -/

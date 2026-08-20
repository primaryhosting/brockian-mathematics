/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma exists_orth_nonorth {n : ℕ} (s t : Bits n) (hs : s ≠ 0) (ht0 : t ≠ 0) (hts : t ≠ s) :
    ∃ y : Bits n, bdot y s = 0 ∧ bdot y t = 1 := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ y : Bits n, bdot y s = 0 → bdot y t = 0 := by
    intro y hy
    rcases zmod_two_cases (bdot y t) with h | h
    · exact h
    · exact absurd h (hcon y hy)
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs (funext h)
  set e : Bits n := Pi.single i 1 with he
  have hes : bdot e s = 1 := by
    rw [bdot_comm, bdot_single]
    rcases zmod_two_cases (s i) with h | h
    · exact absurd h hi
    · exact h
  set a : ZMod 2 := bdot e t with ha
  have key : ∀ u : Bits n, bdot (t + a • s) u = 0 := by
    intro u
    have h1 : bdot (u + (bdot u s) • e) s = 0 := by
      rw [bdot_add_left, bdot_smul_left, hes, mul_one, zmod_two_add_self]
    have h2 := hcon' _ h1
    rw [bdot_add_left, bdot_smul_left, ← ha] at h2
    have h3 : bdot u t = bdot u s * a := zmod_two_eq_of_add_eq_zero h2
    rw [bdot_add_left, bdot_smul_left, bdot_comm t u, bdot_comm s u, h3, mul_comm,
      zmod_two_add_self]
  have : t + a • s = 0 := (bdot_eq_zero_iff _).1 key
  rcases zmod_two_cases a with h | h
  · rw [h] at this; simp at this; exact ht0 this
  · rw [h, one_smul] at this
    have hts' : t = s := by
      have h4 := congrArg (fun z => z + s) this
      simp only [add_assoc, bits_add_self, add_zero, zero_add] at h4
      exact h4
    exact hts hts'

/-- Translation by `y₀` splits a translation-invariant set in half according to the value of
the pairing with `t`, provided `⟨y₀, t⟩ = 1`. -/

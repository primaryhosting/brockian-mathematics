/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kraft's inequality for prefix-free binary codes

A finite set `S` of binary codewords (lists of booleans) is *prefix-free* if no codeword
is a prefix of a different codeword.  The main result, `CS.pcp_pigeon_bound`, states
Kraft's inequality: `∑ w ∈ S, (1/2) ^ w.length ≤ 1`.
-/

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of
another codeword. -/

lemma sum_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S) :
    ∑ v ∈ tailsOf b S, (1 / 2 : ℝ) ^ v.length
      = 2 * ∑ w ∈ S.filter (fun w => w.headI = b), (1 / 2 : ℝ) ^ w.length := by
  classical
  have hinj : ∀ x ∈ S.filter (fun w => w.headI = b), ∀ y ∈ S.filter (fun w => w.headI = b),
      x.tail = y.tail → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    have hxne : x ≠ [] := by rintro rfl; exact h0 hx.1
    have hyne : y ≠ [] := by rintro rfl; exact h0 hy.1
    have hx' : x.headI :: x.tail = x := List.cons_head!_tail hxne
    have hy' : y.headI :: y.tail = y := List.cons_head!_tail hyne
    rw [← hx', ← hy', hx.2, hy.2, hxy]
  rw [tailsOf, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h), Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro w hw
  simp only [Finset.mem_filter] at hw
  have hne : w ≠ [] := by rintro rfl; exact h0 hw.1
  obtain ⟨a, t, rfl⟩ : ∃ a t, w = a :: t := by
    cases w with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, t, rfl⟩
  simp [pow_succ]
  ring


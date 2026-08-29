/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem corrects_of_unitary_change {P : Matrix n n ℂ} {E F : ι → Matrix n n ℂ}
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (hF : ∀ a, F a = ∑ i, U i a • E i)
    (h : Corrects P F) : Corrects P E := by
  obtain ⟨m, R, h1, h2⟩ := h
  refine ⟨m, R, h1, fun v hv hn => ?_⟩
  have h3 := h2 v hv hn
  rw [Finset.sum_congr rfl fun k _ =>
      (Finset.sum_congr rfl fun a _ => congrArg outer (mul_mixed_mulVec hF v a) :
        ∑ a, outer ((R k * F a) *ᵥ v) = ∑ a, outer (∑ i, U i a • ((R k * E i) *ᵥ v))),
    Finset.sum_congr rfl fun k _ => sum_outer_unitary hU (fun i => (R k * E i) *ᵥ v)] at h3
  rw [h3]
  congr 1
  have hE1 : ∀ a, F a *ᵥ v = ∑ i, U i a • (E i *ᵥ v) := by
    intro a
    have hone := mul_mixed_mulVec (A := (1 : Matrix n n ℂ)) hF v a
    simpa using hone
  rw [Finset.sum_congr rfl fun a _ => congrArg (fun x => ip x x) (hE1 a),
    sum_ip_unitary hU (fun i => E i *ᵥ v)]

omit [Fintype n] [DecidableEq n] in

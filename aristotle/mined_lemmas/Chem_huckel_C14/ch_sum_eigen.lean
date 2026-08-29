/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma ch_sum_eigen (μ : ℂ) (v : ZMod 14 → ℂ) (hv : C14adj.mulVec v = μ • v) (k : ZMod 14) :
    (μ - (ch k + ch (-k))) * (∑ j : ZMod 14, v j * ch (-(k * j))) = 0 := by
  set w := ∑ j : ZMod 14, v j * ch (-(k * j)) with hw
  have hvj : ∀ j, v (j + 1) + v (j - 1) = μ * v j := by
    intro j
    have h := congrFun hv j
    rw [C14adj_mulVec] at h
    simpa using h
  have h1 : ∑ j : ZMod 14, v (j + 1) * ch (-(k * j)) = ch k * w := by
    have key : ∀ j : ZMod 14, v (j + 1) * ch (-(k * j))
        = ch k * (v (j + 1) * ch (-(k * (j + 1)))) := by
      intro j
      have hex : (-(k * (j + 1)) : ZMod 14) = -(k * j) + -k := by ring
      rw [hex, ch_add]
      linear_combination (-(v (j + 1) * ch (-(k * j)))) * ch_mul_neg k
    calc ∑ j : ZMod 14, v (j + 1) * ch (-(k * j))
        = ∑ j : ZMod 14, (fun i : ZMod 14 => ch k * (v i * ch (-(k * i)))) (j + 1) :=
          Finset.sum_congr rfl (fun j _ => key j)
      _ = ∑ i : ZMod 14, ch k * (v i * ch (-(k * i))) :=
          sum_shift (fun i : ZMod 14 => ch k * (v i * ch (-(k * i)))) 1
      _ = ch k * w := by rw [hw, Finset.mul_sum]
  have h2 : ∑ j : ZMod 14, v (j - 1) * ch (-(k * j)) = ch (-k) * w := by
    have key : ∀ j : ZMod 14, v (j - 1) * ch (-(k * j))
        = ch (-k) * (v (j + -1) * ch (-(k * (j + -1)))) := by
      intro j
      have hex : (-(k * (j + -1)) : ZMod 14) = -(k * j) + k := by ring
      have hj : (j + -1 : ZMod 14) = j - 1 := by ring
      rw [hex, hj, ch_add]
      linear_combination (-(v (j - 1) * ch (-(k * j)))) * ch_mul_neg k
    calc ∑ j : ZMod 14, v (j - 1) * ch (-(k * j))
        = ∑ j : ZMod 14, (fun i : ZMod 14 => ch (-k) * (v i * ch (-(k * i)))) (j + -1) :=
          Finset.sum_congr rfl (fun j _ => key j)
      _ = ∑ i : ZMod 14, ch (-k) * (v i * ch (-(k * i))) :=
          sum_shift (fun i : ZMod 14 => ch (-k) * (v i * ch (-(k * i)))) (-1)
      _ = ch (-k) * w := by rw [hw, Finset.mul_sum]
  have hmain : μ * w = (ch k + ch (-k)) * w := by
    calc μ * w = ∑ j : ZMod 14, (μ * v j) * ch (-(k * j)) := by
          rw [hw, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j : ZMod 14, (v (j + 1) + v (j - 1)) * ch (-(k * j)) := by
          exact Finset.sum_congr rfl (fun j _ => by rw [hvj j])
      _ = (∑ j : ZMod 14, v (j + 1) * ch (-(k * j)))
            + ∑ j : ZMod 14, v (j - 1) * ch (-(k * j)) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = (ch k + ch (-k)) * w := by rw [h1, h2]; ring
  linear_combination hmain

/-- Fourier inversion: if all Fourier coefficients vanish, the vector vanishes. -/

import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_gate_bad_le {m k q t : ℕ} (hq : 2 ≤ q) (S : Finset (Fin k)) (up : Fin k → Fin m)
    (hup : Function.Injective up) (w : Fin k → Bool) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (hw : w j₀ = true) (i : Fin m) (Bad : Finset (Fin m → Fin t → Fin m → Bool))
    (hsub : ∀ ρ ∈ Bad, ∀ κ : Fin t,
      q ∣ (S.filter (fun j => ρ i κ (up j) = true ∧ w j = true)).card) :
    Bad.card * 2 ^ t ≤ Fintype.card (Fin m → Fin t → Fin m → Bool) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin t → Fin m → Bool) → Prop, ∀ b, Q b ↔
      (∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hbridge : (univ.filter Q) = univ.filter (fun b : Fin t → Fin m → Bool =>
      ∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card) := by
    ext b; simp [hQ]
  have hQcard : (univ.filter Q).card * 2 ^ t ≤ Fintype.card (Fin t → Fin m → Bool) := by
    rw [hbridge]
    have hset : (univ.filter (fun b : Fin t → Fin m → Bool =>
        ∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card))
        = Fintype.piFinset (fun _ : Fin t => univ.filter (fun r : Fin m → Bool =>
            q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card)) := by
      ext b; simp [Fintype.mem_piFinset]
    rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_pow]
    have h2 : Fintype.card (Fin t → Fin m → Bool) = (2 ^ m) ^ t := by simp
    rw [h2]
    exact Nat.pow_le_pow_left (by have := card_dvd_le hq S up hup w j₀ hj₀ hw; omega) t
  refine card_coord_bad_le i Q t hQcard Bad ?_
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hQ _).2 (hsub ρ hρ)

end CS

import Mathlib
import RequestProject.Poly
import RequestProject.Circuit

/-!
The Smolensky counting argument: if the function `x ↦ ζ^(popcount x)` (for `ζ` a root of
unity) agrees on a set `A ⊆ {0,1}ⁿ`, `n = 2m+1`, with a function of degree at most `D`,
then `|A| ≤ ∑_{i ≤ m + D} C(n,i)`.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `x ↦ ζ ^ (x i)`. -/

import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

theorem and_approx {m : ℕ} (ℓ D : ℕ) (G : Finset (Cube n))
    (s : Finset (Fin m)) (p : Fin m → Cube n → ZMod 3) (w : Cube n → Fin m → Bool)
    (hp : ∀ j ∈ s, p j ∈ Deg n D)
    (hpw : ∀ j ∈ s, ∀ x ∈ G, p j x = bit (w x j)) :
    ∃ q : Cube n → ZMod 3, q ∈ Deg n (2 * ℓ * D) ∧ ∃ E : Finset (Cube n),
      2 ^ ℓ * E.card ≤ 2 ^ n ∧
      ∀ x ∈ G, x ∉ E → q x = bit (decide (∀ j ∈ s, w x j = true)) := by
  obtain ⟨q, hq, E, hE, hqval⟩ := or_approx ℓ D G s (fun j => 1 - p j) (fun x j => !(w x j))
    (fun j hj => Submodule.sub_mem _ (one_mem_Deg D) (hp j hj))
    (fun j hj x hx => by
      simp only [Pi.sub_apply, Pi.one_apply, hpw j hj x hx]
      rw [bit_not])
  refine ⟨1 - q, Submodule.sub_mem _ (one_mem_Deg _) hq, E, hE, ?_⟩
  intro x hxG hxE
  simp only [Pi.sub_apply, Pi.one_apply, hqval x hxG hxE]
  by_cases hall : ∀ j ∈ s, w x j = true
  · have hnex : ¬ ∃ j ∈ s, (!(w x j)) = true := by
      rintro ⟨j, hj, h⟩
      rw [hall j hj] at h
      exact absurd h (by decide)
    rw [decide_eq_false hnex, decide_eq_true hall]
    simp only [bit_false, bit_true]
    decide
  · push_neg at hall
    obtain ⟨j, hj, hjv⟩ := hall
    have hex : ∃ j ∈ s, (!(w x j)) = true := by
      refine ⟨j, hj, ?_⟩
      cases hw : w x j
      · rfl
      · exact absurd hw hjv
    have hnall : ¬ ∀ j ∈ s, w x j = true := by
      intro h
      exact hjv (h j hj)
    rw [decide_eq_true hex, decide_eq_false hnall]
    simp only [bit_false, bit_true]
    decide

/-- **Approximation of a whole circuit.** -/

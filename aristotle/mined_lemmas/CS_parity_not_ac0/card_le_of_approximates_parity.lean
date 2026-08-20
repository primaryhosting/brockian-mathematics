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

theorem card_le_of_approximates_parity {N D : ℕ} {n : ℕ} (hn : n = 2 * N)
    (A : Finset (Cube n)) (R : Cube n → ZMod 3) (hR : R ∈ Deg n D)
    (hA : ∀ x ∈ A, R x = mon (Finset.univ : Finset (Fin n)) x) :
    A.card ≤ ∑ k ∈ Finset.range (N + D + 1), n.choose k := by
  classical
  set K := N + D with hK
  set res : (Cube n → ZMod 3) →ₗ[ZMod 3] (↥A → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (fun a : ↥A => (a : Cube n)) with hres
  -- every monomial restricts into the image of `Deg n K`
  have hmon : ∀ S : Finset (Fin n), res (mon S) ∈ Submodule.map res (Deg n K) := by
    intro S
    by_cases hS : S.card ≤ K
    · exact Submodule.mem_map_of_mem (mon_mem_Deg hS)
    · push_neg at hS
      have hcompl : (Sᶜ).card ≤ N := by
        have hc : (Sᶜ).card = n - S.card := by
          rw [Finset.card_compl]; simp
        have hle : S.card ≤ n := by
          simpa using Finset.card_le_card (Finset.subset_univ S)
        omega
      have hmem : R * mon Sᶜ ∈ Deg n K := by
        refine Deg_mono (?_ : D + (Sᶜ).card ≤ K) (Deg_mul hR (mon_mem_Deg (le_refl _)))
        omega
      refine ⟨R * mon Sᶜ, hmem, ?_⟩
      funext a
      have ha : (a : Cube n) ∈ A := a.2
      simp only [hres, LinearMap.funLeft_apply, Pi.mul_apply]
      rw [hA _ ha]
      have : mon (Finset.univ : Finset (Fin n)) * mon Sᶜ = mon S := by
        rw [mon_mul]
        congr 1
        ext i
        simp [Finset.mem_symmDiff]
      calc mon (Finset.univ : Finset (Fin n)) (a : Cube n) * mon Sᶜ (a : Cube n)
          = (mon (Finset.univ : Finset (Fin n)) * mon Sᶜ) (a : Cube n) := rfl
        _ = mon S (a : Cube n) := by rw [this]
  -- hence the restriction map is surjective from `Deg n K`
  have htop : Submodule.map res (Deg n K) = ⊤ := by
    refine eq_top_iff.mpr (fun g hg => ?_)
    clear hg
    obtain ⟨f, rfl⟩ : ∃ f, res f = g := by
      refine ⟨fun x => if h : ∃ a : ↥A, (a : Cube n) = x then g h.choose else 0, ?_⟩
      funext a
      have hex : ∃ b : ↥A, (b : Cube n) = (a : Cube n) := ⟨a, rfl⟩
      simp only [hres, LinearMap.funLeft_apply, dif_pos hex]
      congr 1
      exact Subtype.ext hex.choose_spec
    have hfmem : f ∈ Deg n n := by rw [Deg_top_eq]; trivial
    clear_value res
    induction hfmem using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨S, _, rfl⟩ := hh
        exact hmon S
    | zero => simp
    | add f1 f2 _ _ ih1 ih2 => rw [map_add]; exact Submodule.add_mem _ ih1 ih2
    | smul a f _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih
  -- dimension count
  have h1 : Module.finrank (ZMod 3) (↥A → ZMod 3) = A.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank (ZMod 3) (Submodule.map res (Deg n K))
      ≤ Module.finrank (ZMod 3) (Deg n K) := Submodule.finrank_map_le _ _
  rw [htop] at h2
  rw [finrank_top] at h2
  rw [h1] at h2
  exact le_trans h2 (finrank_Deg_le n K)

end CS

import Mathlib
import RequestProject.Approx
import RequestProject.Smolensky
import RequestProject.Binomial
import RequestProject.Universality

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
`PARITY ∉ AC⁰`.

The proof is the polynomial method of Razborov and Smolensky: every `AC⁰`
circuit of depth `d` and size `s` agrees, outside a set of at most `s · 2^{n-ℓ}`
inputs, with a function of degree `(2ℓ)^d` over `ZMod 3`
(`CS.circuit_approx`); but a function of degree `D` can agree with parity only
on a set of at most `∑_{k ≤ n/2 + D} C(n,k)` inputs (`CS.card_le_of_approximates_parity`).
Choosing `ℓ` polylogarithmically in `n` makes these two facts contradictory.

Note: the module docstring required by the task statement is placed just below
the `import` lines, since Lean 4 requires `import` commands to come first in a
file.
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

set_option grind.warning false

namespace CS

open Finset

/-- **Quantitative lower bound.** No circuit of depth `d` and size `s ≤ 2^ℓ / 4`
computes parity on `2N` bits, as soon as `64 · ((2ℓ)^d + 1)^2 ≤ 3N + 1`. -/

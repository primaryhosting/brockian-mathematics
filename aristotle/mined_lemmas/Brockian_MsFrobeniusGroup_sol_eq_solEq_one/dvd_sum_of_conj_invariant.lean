import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma dvd_sum_of_conj_invariant [Fintype G] {d : ℕ} (f : G → ℕ)
    (hf : ∀ g w : G, f (g * w * g⁻¹) = f w)
    (A : Finset G) (hA : ∀ g w : G, w ∈ A → g * w * g⁻¹ ∈ A)
    (h : ∀ w ∈ A, d ∣ (Subgroup.centralizer ({w} : Set G)).index * f w) :
    d ∣ ∑ w ∈ A, f w := by
  -- Define the equivalence relation of conjugacy
  let e : Setoid G := {
    r := fun x y => IsConj x y
    iseqv := {
      refl := fun x => IsConj.refl x
      symm := fun h => h.symm
      trans := fun h1 h2 => h1.trans h2
    }
  }
  -- A is closed under conjugacy, so it's a union of full conjugacy classes
  have hA_conj : ∀ w ∈ A, ∀ x : G, e.r w x → x ∈ A := by
    intro w hw x hx
    obtain ⟨g, hg⟩ := hx
    have : x = (g : G) * w * (g : G)⁻¹ := by
      rw [SemiconjBy] at hg
      calc x = x * (g : G) * (g : G)⁻¹ := by group
        _ = (g : G) * w * (g : G)⁻¹ := by rw [hg]
    rw [this]
    exact hA g w hw
  -- Map A to the quotient
  let A' : Finset (Quotient e) := A.image Quotient.mk''
  -- The sum over A equals sum over A' of (sum over fiber)
  have hsum : ∑ w ∈ A, f w = ∑ q ∈ A', ∑ w ∈ A.filter (fun x => Quotient.mk'' x = q), f w := by
    have hdisj : ∀ q₁ ∈ A', ∀ q₂ ∈ A', q₁ ≠ q₂ → Disjoint (A.filter (fun x => Quotient.mk'' x = q₁))
        (A.filter (fun x => Quotient.mk'' x = q₂)) := by
      intro q₁ hq₁ q₂ hq₂ heq
      simp only [Finset.disjoint_filter]
      intro x _ h1 h2
      rw [← h1, ← h2] at heq
      exact (heq rfl).elim
    calc ∑ w ∈ A, f w
        = ∑ w ∈ A'.biUnion (fun q => A.filter (fun x => Quotient.mk'' x = q)), f w := by
          congr 1
          ext x
          simp only [Finset.mem_biUnion]
          constructor
          · intro hx
            refine ⟨Quotient.mk'' x, ?_, ?_⟩
            · simp [A', Finset.mem_image]
              exact ⟨x, hx, rfl⟩
            · simp [Finset.mem_filter]
              exact hx
          · rintro ⟨q, hq, hq'⟩
            simp [A', Finset.mem_image] at hq
            obtain ⟨a, ha, rfl⟩ := hq
            simp [Finset.mem_filter] at hq'
            simp [hq'] at *
      _ = ∑ q ∈ A', ∑ w ∈ A.filter (fun x => Quotient.mk'' x = q), f w := by
          rw [Finset.sum_biUnion hdisj]
  -- For each conjugacy class, the sum is |class| * f(w) for any w in the class
  -- and |class| = index of centralizer, so d divides each term
  rw [hsum]
  apply Finset.dvd_sum
  intro q hq
  simp [A'] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  -- The filter is the conjugacy class of w
  have hfilter_eq : A.filter (fun x : G => (Quotient.mk'' x : Quotient e) = Quotient.mk'' w) =
      (univ.filter (fun x : G => IsConj w x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rw [Quotient.eq] at hx
      obtain ⟨g, hg⟩ := hx.2
      exact IsConj.symm ⟨g, hg⟩
    · intro hconj
      obtain ⟨u, hu⟩ := hconj
      have heq : (Quotient.mk'' w : Quotient e) = Quotient.mk'' x := Quotient.sound ⟨u, hu⟩
      exact ⟨hA_conj w hw x ⟨u, hu⟩, heq.symm⟩
  -- Rewrite the sum using hfilter_eq
  have hsum' : ∑ x ∈ univ.filter (fun x : G => IsConj w x), f x = ↑(univ.filter (fun x : G => IsConj w x)).card * f w := by
    have hconst : ∀ y ∈ univ.filter (fun x : G => IsConj w x), f y = f w := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨u, hu⟩ := hy
      have heq : y = (u : G) * w * (u⁻¹ : G) := by
        have hu' : (u : G) * w = y * (u : G) := hu
        have : y * (u : G) * (u : G)⁻¹ = (u : G) * w * (u : G)⁻¹ := by rw [hu']
        simp at this
        rw [this]
      rw [heq]
      rw [hf (u : G) w]
    rw [Finset.sum_eq_card_nsmul hconst]
    rfl
  rw [hfilter_eq, hsum']
  have hcard : (univ.filter (fun x : G => IsConj w x)).card = (Subgroup.centralizer ({w} : Set G)).index := by
    exact card_conj_class w
  rw [hcard]
  exact h w hw

/-- If the `p`-part of `|H|` divides `c`, then the `p`-part of `|G|` divides `H.index * c`. -/

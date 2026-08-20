/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

lemma clp_mem {n d : ℕ} {P : V n → F} (hP : P ∈ W n d) :
    (fun p : V n × V n => P (p.1 + p.2)) ∈ Rank1 n (d / 2) := by
  have key : W n d ≤ Submodule.comap (shiftMap n) (Rank1 n (d / 2)) := by
    rw [W, Submodule.span_le]
    rintro f ⟨a, ha, rfl⟩
    have hda : deg a ≤ d := (mem_M_iff a).1 ha
    show (fun p : V n × V n => mon a (p.1 + p.2)) ∈ Rank1 n (d / 2)
    have hsum : (fun p : V n × V n => mon a (p.1 + p.2))
        = ∑ b : E n, (fun p : V n × V n =>
            (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b p.1 * mon (asub a b) p.2)) := by
      funext p
      rw [Finset.sum_apply]
      exact mon_add a p.1 p.2
    rw [hsum]
    refine Submodule.sum_mem _ (fun b _ => ?_)
    by_cases hc : (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) = 0
    · have hz : (fun p : V n × V n =>
          (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) * (mon b p.1 * mon (asub a b) p.2)) = 0 := by
        funext p; rw [hc]; simp
      rw [hz]; exact Submodule.zero_mem _
    · have hc' : (∏ i, (((a i : ℕ).choose (b i : ℕ) : ℕ) : F)) ≠ 0 := hc
      have hle : ∀ i, (b i : ℕ) ≤ (a i : ℕ) := by
        intro i
        rw [Finset.prod_ne_zero_iff] at hc'
        have h2 := hc' i (Finset.mem_univ i)
        by_contra hlt
        push_neg at hlt
        rw [Nat.choose_eq_zero_of_lt hlt] at h2
        simp at h2
      have hd := deg_asub_add a b hle
      rcases le_or_gt (deg b) (d / 2) with h | h
      · exact Rank1_left h _ _
      · exact Rank1_right (by omega) _ _
  exact key hP

/-- The rank bound: a two-variable function in `Rank1 n e` which is "diagonal" on `S × S` with
nonzero diagonal entries forces `|S| ≤ 2 * |M n e|`. -/

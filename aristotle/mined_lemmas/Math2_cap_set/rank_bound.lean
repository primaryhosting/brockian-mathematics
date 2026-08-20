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

lemma rank_bound {n e : ℕ} {h : V n × V n → F} (hh : h ∈ Rank1 n e)
    {S : Finset (V n)} (hdiag : ∀ x ∈ S, h (x, x) ≠ 0)
    (hoff : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → h (x, y) = 0) :
    S.card ≤ 2 * (M n e).card := by
  classical
  obtain ⟨w, w', hw⟩ := hh
  by_contra hcon
  push_neg at hcon
  have hnli : ¬ LinearIndependent F (fun x : {x : V n // x ∈ S} =>
      (Sum.elim (fun b : {a : E n // a ∈ M n e} => mon (b : E n) (x : V n))
        (fun c : {a : E n // a ∈ M n e} => w' (c : E n) (x : V n)) :
        ({a : E n // a ∈ M n e} ⊕ {a : E n // a ∈ M n e}) → F)) := by
    intro hli
    have hcc := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_coe,
      Fintype.card_coe] at hcc
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, x₀, hx₀⟩ := hnli
  have hcoordl : ∀ b ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * mon b (x : V n) = 0 := by
    intro b hb
    have := congrFun hg (Sum.inl ⟨b, hb⟩)
    simpa [Finset.sum_apply] using this
  have hcoordr : ∀ c ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * w' c (x : V n) = 0 := by
    intro c hc
    have := congrFun hg (Sum.inr ⟨c, hc⟩)
    simpa [Finset.sum_apply] using this
  have hzero : ∑ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n)) = 0 := by
    have hexp : ∀ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n))
        = (∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n))) := by
      intro x
      rw [hw ((x : V n), (x₀ : V n))]
      simp [Finset.mul_sum, mul_add]
    calc ∑ x : {x : V n // x ∈ S}, g x * h ((x : V n), (x₀ : V n))
        = ∑ x : {x : V n // x ∈ S}, ((∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n)))) :=
          Finset.sum_congr rfl (fun x _ => hexp x)
      _ = (∑ x : {x : V n // x ∈ S}, ∑ b ∈ M n e, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ x : {x : V n // x ∈ S}, ∑ c ∈ M n e, g x * (w' c (x : V n) * mon c (x₀ : V n))) :=
          Finset.sum_add_distrib
      _ = (∑ b ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n)))
          + (∑ c ∈ M n e, ∑ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))) := by
          congr 1 <;> exact Finset.sum_comm
      _ = 0 := by
          have h1 : ∀ b ∈ M n e,
              (∑ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n))) = 0 := by
            intro b hb
            have hrw : ∀ x : {x : V n // x ∈ S}, g x * (mon b (x : V n) * w b (x₀ : V n))
                = (g x * mon b (x : V n)) * w b (x₀ : V n) := fun x => by ring
            rw [Finset.sum_congr rfl (fun x _ => hrw x), ← Finset.sum_mul, hcoordl b hb, zero_mul]
          have h2 : ∀ c ∈ M n e,
              (∑ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))) = 0 := by
            intro c hc
            have hrw : ∀ x : {x : V n // x ∈ S}, g x * (w' c (x : V n) * mon c (x₀ : V n))
                = (g x * w' c (x : V n)) * mon c (x₀ : V n) := fun x => by ring
            rw [Finset.sum_congr rfl (fun x _ => hrw x), ← Finset.sum_mul, hcoordr c hc, zero_mul]
          rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
          simp
  rw [Finset.sum_eq_single x₀] at hzero
  · exact (mul_ne_zero hx₀ (hdiag (x₀ : V n) x₀.2)) hzero
  · intro x _ hne
    rw [hoff (x : V n) x.2 (x₀ : V n) x₀.2 (fun heq => hne (Subtype.ext heq)), mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ x₀) hmem

end CLP

section Support

/-- A subspace of functions admits a "separating" set of points of size at most its dimension. -/

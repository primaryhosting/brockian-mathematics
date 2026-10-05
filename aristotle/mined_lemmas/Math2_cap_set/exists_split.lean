import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

lemma exists_split {n : ℕ} (d e : ℕ) (hde : d ≤ 2 * e + 1) (P : Pt n → ZMod 3)
    (hP : P ∈ polySpace n d) :
    ∃ q c : Exp n → (Pt n → ZMod 3), ∀ x y : Pt n,
      P (x + y) = (∑ β ∈ Dset n e, mono β x * q β y) + ∑ γ ∈ Dset n e, c γ x * mono γ y := by
  induction hP using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨α, hα, rfl⟩ := hf
      have hαd : edeg α ≤ d := mem_Dset.1 (by simpa using hα)
      refine ⟨fun β y => ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono γ y,
              fun γ x => ∑ β : Exp n, KK α β γ * mono β x, ?_⟩
      intro x y
      have hsplit : ∀ β : Exp n, (∑ γ : Exp n, KK α β γ * mono β x * mono γ y)
          = (∑ γ ∈ Dset n e, KK α β γ * mono β x * mono γ y)
            + ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y :=
        fun β => (Finset.sum_add_sum_compl _ _).symm
      have hA : (∑ β : Exp n, ∑ γ ∈ Dset n e, KK α β γ * mono β x * mono γ y)
          = ∑ γ ∈ Dset n e, (∑ β : Exp n, KK α β γ * mono β x) * mono γ y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Finset.sum_mul]
      have hB : (∑ β : Exp n, ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y)
          = ∑ β ∈ Dset n e, mono β x * ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono γ y := by
        rw [← Finset.sum_add_sum_compl (Dset n e)
          (fun β => ∑ γ ∈ (Dset n e)ᶜ, KK α β γ * mono β x * mono γ y)]
        have hzero : (∑ β ∈ (Dset n e)ᶜ, ∑ γ ∈ (Dset n e)ᶜ,
            KK α β γ * mono β x * mono γ y) = 0 := by
          refine Finset.sum_eq_zero fun β hβ => Finset.sum_eq_zero fun γ hγ => ?_
          have hβd : ¬ (edeg β ≤ e) := fun h => (Finset.mem_compl.1 hβ) (mem_Dset.2 h)
          have hγd : ¬ (edeg γ ≤ e) := fun h => (Finset.mem_compl.1 hγ) (mem_Dset.2 h)
          have hK : KK α β γ = 0 := by
            by_contra hK
            have := KK_ne_zero_deg hK
            omega
          simp [hK]
        rw [hzero, add_zero]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun γ _ => by ring
      rw [mono_add_expand α x y, Finset.sum_congr rfl (fun β _ => hsplit β),
        Finset.sum_add_distrib, hA, hB, add_comm]
  | zero => exact ⟨0, 0, by intro x y; simp⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨q1, c1, h1⟩ := ihf
      obtain ⟨q2, c2, h2⟩ := ihg
      refine ⟨q1 + q2, c1 + c2, fun x y => ?_⟩
      simp only [Pi.add_apply, h1 x y, h2 x y, mul_add, add_mul, Finset.sum_add_distrib]
      ring
  | smul a f hf ih =>
      obtain ⟨q, c, h⟩ := ih
      refine ⟨fun β => a • q β, fun γ => a • c γ, fun x y => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, h x y, mul_add, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Counting monomials -/

/-- Reversing all exponents (`a ↦ 2 - a`) complements the total degree. -/

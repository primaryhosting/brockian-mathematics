import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

namespace Brockian

/-- The **local count** of a constellation (tuple of shifts) `H` modulo `p`:
the number of residues `a` mod `p` such that none of the shifted values `a + h`,
`h ∈ H`, is divisible by `p`.  This is the local factor `ν_p(H)` appearing in the
Hardy–Littlewood prime-tuple heuristics. -/
def localCount (p : ℕ) [NeZero p] (H : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + h ≠ 0)).card

/-- The set of forbidden residues for a constellation `H` is the image of `H`
under negation, so the local count is `p` minus the number of distinct residues
of the shifts. -/
theorem localCount_eq (p : ℕ) [NeZero p] (H : Finset (ZMod p)) :
    localCount p H = p - (H.image (fun h => -h)).card := by
  classical
  have hset :
      (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + h ≠ 0))
        = (H.image (fun h => -h))ᶜ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_image, not_exists, not_and]
    constructor
    · rintro h x hx rfl
      exact h x hx (by ring)
    · intro h x hx hax
      exact h x hx (by linear_combination -hax)
  rw [localCount, hset, Finset.card_compl, ZMod.card]

/-- Local constellation count for `k = 1`: a single shift forbids exactly one residue. -/
theorem ConstellationLocalCountK1 (p : ℕ) [NeZero p] (h₁ : ZMod p) :
    localCount p {h₁} = p - 1 := by
  rw [localCount_eq]
  simp

/-- Local constellation count for `k = 2`: two distinct shifts forbid exactly two residues. -/
theorem ConstellationLocalCountK2 (p : ℕ) [NeZero p] (h₁ h₂ : ZMod p) (h12 : h₁ ≠ h₂) :
    localCount p {h₁, h₂} = p - 2 := by
  rw [localCount_eq]
  congr 1
  have himg : ({h₁, h₂} : Finset (ZMod p)).image (fun h => -h) = {-h₁, -h₂} := by
    simp [Finset.image_insert]
  rw [himg, Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]

/-- **Local constellation count for `k = 3`.**  If the three shifts `h₁, h₂, h₃`
are pairwise distinct modulo `p`, then exactly `p - 3` residue classes mod `p`
avoid all three forbidden classes. -/
theorem ConstellationLocalCountK3 (p : ℕ) [NeZero p] (h₁ h₂ h₃ : ZMod p)
    (h12 : h₁ ≠ h₂) (h13 : h₁ ≠ h₃) (h23 : h₂ ≠ h₃) :
    localCount p {h₁, h₂, h₃} = p - 3 := by
  classical
  rw [localCount_eq]
  congr 1
  have himg : ({h₁, h₂, h₃} : Finset (ZMod p)).image (fun h => -h)
      = {-h₁, -h₂, -h₃} := by
    simp [Finset.image_insert]
  rw [himg, Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]

/-- Elementary restatement of the `k = 3` local count: among the `p` residues
`n ∈ {0, …, p-1}`, exactly `p - 3` are such that none of `n + a`, `n + b`, `n + c`
is divisible by `p`, provided `a, b, c` are pairwise distinct modulo `p`. -/
theorem ConstellationLocalCountK3_nat (p : ℕ) [NeZero p] (a b c : ℕ)
    (hab : (a : ZMod p) ≠ (b : ZMod p)) (hac : (a : ZMod p) ≠ (c : ZMod p))
    (hbc : (b : ZMod p) ≠ (c : ZMod p)) :
    ((Finset.range p).filter
        (fun n => ¬ p ∣ (n + a) ∧ ¬ p ∣ (n + b) ∧ ¬ p ∣ (n + c))).card = p - 3 := by
  classical
  rw [← ConstellationLocalCountK3 p (a : ZMod p) (b : ZMod p) (c : ZMod p) hab hac hbc,
    localCount]
  refine Finset.card_bij' (fun n _ => ((n : ZMod p))) (fun x _ => ZMod.val x) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rintro h (rfl | rfl | rfl) <;>
      · rw [← Nat.cast_add, Ne, ZMod.natCast_eq_zero_iff]
        tauto
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_range, ZMod.val_lt, true_and]
    refine ⟨?_, ?_, ?_⟩ <;>
      · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id]
        exact hx _ (by simp)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact ZMod.val_natCast_of_lt hn.1
  · intro x _
    simp

end Brockian


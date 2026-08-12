import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace AdditiveComb

open Classical in
/-- For an integer `d`, a chosen pair `(a, c) ∈ A × C` with `a - c = d`, whenever `d ∈ A - C`
(and a junk value otherwise). -/
noncomputable def subWitness (A C : Finset ℤ) (d : ℤ) : ℤ × ℤ :=
  if h : ∃ p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ C ∧ p.1 - p.2 = d then h.choose else (0, 0)

/-- The defining property of `subWitness`: for `d ∈ A - C` it is a genuine representation of `d`
as a difference of an element of `A` and an element of `C`. -/
lemma subWitness_spec {A C : Finset ℤ} {d : ℤ} (hd : d ∈ A - C) :
    (subWitness A C d).1 ∈ A ∧ (subWitness A C d).2 ∈ C ∧
      (subWitness A C d).1 - (subWitness A C d).2 = d := by
  have h : ∃ p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ C ∧ p.1 - p.2 = d := by
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_sub.1 hd
    exact ⟨(a, c), ha, hc, rfl⟩
  classical
  rw [subWitness, dif_pos h]
  exact h.choose_spec

/-- **Ruzsa's triangle inequality** (the engine of the Plünnecke–Ruzsa inequality):
for finite sets `A`, `B`, `C` of integers,
`|A - C| * |B| ≤ |A - B| * |B - C|`.

The proof is self-contained: it exhibits an injection
`(A - C) ×ˢ B → (A - B) ×ˢ (B - C)`, `(d, b) ↦ (a_d - b, b - c_d)`, where `d = a_d - c_d` is a
fixed representation of `d` with `a_d ∈ A`, `c_d ∈ C`. Injectivity holds because the two
coordinates of the image sum to `d`, which recovers `d` and then `b`.

The nonemptiness hypotheses `_hA`, `_hB`, `_hC` are stated as requested, but they turn out to be
unnecessary: the inequality holds for arbitrary finite sets. -/
theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  rw [← Finset.card_product (A - C) B, ← Finset.card_product (A - B) (B - C)]
  refine Finset.card_le_card_of_injOn
    (fun p => ((subWitness A C p.1).1 - p.2, p.2 - (subWitness A C p.1).2)) ?_ ?_
  · rintro ⟨d, b⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product] at hp ⊢
    obtain ⟨hd, hb⟩ := hp
    obtain ⟨ha, hc, -⟩ := subWitness_spec hd
    exact ⟨Finset.sub_mem_sub ha hb, Finset.sub_mem_sub hb hc⟩
  · rintro ⟨d, b⟩ hp ⟨d', b'⟩ hp' h
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨-, -, hsum⟩ := subWitness_spec hp.1
    obtain ⟨-, -, hsum'⟩ := subWitness_spec hp'.1
    simp only [Prod.mk.injEq] at h hsum hsum' ⊢
    have hdd : d = d' := by omega
    subst hdd
    exact ⟨rfl, by omega⟩

end AdditiveComb


/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
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

namespace Math2

open Finset
open Finset.Colex

variable {n : ℕ}

/-- The (lower) shadow of a family of finite sets: all sets obtained from a member of the
family by deleting a single element. -/
def shadow (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  𝒜.biUnion fun A => A.image A.erase

/-- `ColexLt A B` says that `A` is smaller than `B` in the colexicographic order: the largest
element of the symmetric difference of `A` and `B` belongs to `B`. -/
def ColexLt (A B : Finset (Fin n)) : Prop :=
  ∃ a ∈ B, a ∉ A ∧ ∀ b ∈ A, b ∉ B → b < a

/-- `𝒞` is an initial segment of the colexicographic order on `r`-sets: all its members have
size `r`, and any `r`-set below a member of `𝒞` in colex is again in `𝒞`. -/
def IsColexInitSeg (𝒞 : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  (∀ A ∈ 𝒞, A.card = r) ∧
    ∀ A ∈ 𝒞, ∀ B : Finset (Fin n), ColexLt B A → B.card = r → B ∈ 𝒞

/-- Our `shadow` agrees with Mathlib's `Finset.shadow`. -/
lemma shadow_eq (𝒜 : Finset (Finset (Fin n))) : shadow 𝒜 = Finset.shadow 𝒜 := by
  rw [shadow, Finset.shadow, Finset.sup_eq_biUnion]

/-- Our colex relation agrees with Mathlib's colex order. -/
lemma colexLt_iff {A B : Finset (Fin n)} :
    ColexLt A B ↔ _root_.toColex A < _root_.toColex B :=
  Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt.symm

/-- Our notion of colex initial segment agrees with Mathlib's `Finset.Colex.IsInitSeg`. -/
lemma isColexInitSeg_iff {𝒞 : Finset (Finset (Fin n))} {r : ℕ} :
    IsColexInitSeg 𝒞 r ↔ Finset.Colex.IsInitSeg 𝒞 r := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun A hA => h₁ A hA, ?_⟩
    rintro A B hA ⟨hlt, hcard⟩
    exact h₂ A hA B (colexLt_iff.2 hlt) hcard
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun A hA => h₁ hA, ?_⟩
    intro A hA B hlt hcard
    exact h₂ hA ⟨colexLt_iff.1 hlt, hcard⟩

/-- **The Kruskal–Katona theorem.** If `𝒜` is a family of `r`-element subsets of `Fin n` and
`𝒞` is an initial segment of the colexicographic order on `r`-sets with `#𝒞 ≤ #𝒜`, then the
shadow of `𝒞` is no larger than the shadow of `𝒜`. In particular, among families of `r`-sets of
a given size, the minimum shadow size is attained by initial segments of the colex order. -/
theorem kruskal_katona {r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜 : ∀ A ∈ 𝒜, A.card = r) (hcard : 𝒞.card ≤ 𝒜.card) (h𝒞 : IsColexInitSeg 𝒞 r) :
    (shadow 𝒞).card ≤ (shadow 𝒜).card := by
  rw [shadow_eq, shadow_eq]
  exact Finset.kruskal_katona (fun A hA => h𝒜 A hA) hcard (isColexInitSeg_iff.1 h𝒞)

/-- **Kruskal–Katona, Lovász form.** If `𝒜` is a family of `r`-element subsets of `Fin n` with
at least `k.choose r` members (where `i ≤ r ≤ k ≤ n`), then its `i`-th iterated shadow has at
least `k.choose (r - i)` members. -/
theorem kruskal_katona_lovasz {r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h𝒜 : ∀ A ∈ 𝒜, A.card = r)
    (hcard : k.choose r ≤ 𝒜.card) :
    k.choose (r - i) ≤ (shadow^[i] 𝒜).card := by
  have hfun : (shadow : Finset (Finset (Fin n)) → Finset (Finset (Fin n))) = Finset.shadow :=
    funext shadow_eq
  rw [hfun]
  exact Finset.kruskal_katona_lovasz_form hir hrk hkn (fun A hA => h𝒜 A hA) hcard

end Math2


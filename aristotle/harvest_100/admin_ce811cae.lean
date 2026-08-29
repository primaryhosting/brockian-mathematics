import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
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

variable {n : ℕ}

/-- The shadow of a family `𝒜` of finite sets: all the sets obtained from a member of `𝒜` by
deleting one element. -/
def shadow (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  𝒜.sup fun s => s.image fun a => s.erase a

lemma shadow_eq (𝒜 : Finset (Finset (Fin n))) : shadow 𝒜 = Finset.shadow 𝒜 := rfl

lemma mem_shadow_iff {𝒜 : Finset (Finset (Fin n))} {t : Finset (Fin n)} :
    t ∈ shadow 𝒜 ↔ ∃ s ∈ 𝒜, ∃ a ∈ s, s.erase a = t := by
  rw [shadow_eq, Finset.mem_shadow_iff]

/-- The colexicographic (colex) order on finite sets: `s` is smaller than `t` when the largest
element in which they differ belongs to `t`. -/
def ColexLt (s t : Finset (Fin n)) : Prop := ∃ a ∈ t, a ∉ s ∧ ∀ b ∈ s, b ∉ t → b < a

lemma colexLt_iff {s t : Finset (Fin n)} :
    ColexLt s t ↔ toColex s < toColex t :=
  Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt.symm

/-- **The Kruskal–Katona theorem.**

Let `𝒜` be a family of `r`-element subsets of `Fin n`, and let `𝒞` be an initial segment of the
colexicographic order on `r`-element sets (that is, `𝒞` consists of `r`-sets and is downwards
closed in colex among `r`-sets) with `#𝒞 ≤ #𝒜`. Then the shadow of `𝒞` is no larger than the
shadow of `𝒜`; in other words, among families of `r`-sets of a given size, the initial segments
of colex minimise the size of the shadow. -/
theorem kruskal_katona {r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜 : ∀ s ∈ 𝒜, #s = r) (h𝒞 : ∀ s ∈ 𝒞, #s = r)
    (h𝒞init : ∀ s ∈ 𝒞, ∀ t : Finset (Fin n), ColexLt t s → #t = r → t ∈ 𝒞)
    (hcard : #𝒞 ≤ #𝒜) :
    #(shadow 𝒞) ≤ #(shadow 𝒜) := by
  simp only [shadow_eq]
  refine Finset.kruskal_katona (r := r) (fun s hs => h𝒜 s hs) hcard ⟨fun s hs => h𝒞 s hs, ?_⟩
  rintro s t hs ⟨hts, htr⟩
  exact h𝒞init s hs t (colexLt_iff.2 hts) htr

/-- The `i`-th iterated shadow. -/
def shadowIter (i : ℕ) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  shadow^[i] 𝒜

lemma shadowIter_eq (i : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    shadowIter i 𝒜 = (Finset.shadow)^[i] 𝒜 := rfl

/-- **The Lovász form of the Kruskal–Katona theorem.**

If `𝒜` is a family of `r`-element subsets of `Fin n` with `k.choose r ≤ #𝒜` (where
`i ≤ r ≤ k ≤ n`), then its `i`-th iterated shadow has at least `k.choose (r - i)` elements. -/
theorem kruskal_katona_lovasz {r k i : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n)
    (h𝒜 : ∀ s ∈ 𝒜, #s = r) (hcard : k.choose r ≤ #𝒜) :
    k.choose (r - i) ≤ #(shadowIter i 𝒜) := by
  rw [shadowIter_eq]
  exact Finset.kruskal_katona_lovasz_form hir hrk hkn (fun s hs => h𝒜 s hs) hcard

end Math2

#print axioms Math2.kruskal_katona
#print axioms Math2.kruskal_katona_lovasz


import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

lemma exists_isSimon_id_on {s : BV n} (hs : s ≠ 0) (X : Finset (BV n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s) :
    ∃ f : BV n → BV n, IsSimon f s ∧ ∀ x ∈ X, f x = x := by
  classical
  obtain ⟨i, hi⟩ := exists_ne_zero_coord hs
  set r : BV n → BV n := repOf s i with hr
  -- `r` is injective on `X`
  have hinj : ∀ x ∈ X, ∀ y ∈ X, r x = r y → x = y := by
    intro x hx y hy hxy
    rcases (repOf_eq_iff hi x y).1 hxy with h | h
    · exact h.symm
    · exact absurd (by rw [h, ← add_assoc, bv_add_self, zero_add] : x + y = s) (hX x hx y hy)
  set R : Finset (BV n) := X.image r with hR
  have hmap : ∀ a : {a : BV n // a ∈ X}, r a.1 ∈ R := fun a =>
    Finset.mem_image_of_mem r a.2
  let g : {a : BV n // a ∈ X} → {b : BV n // b ∈ R} := fun a => ⟨r a.1, hmap a⟩
  have hgbij : Function.Bijective g := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab))
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : {a : BV n // a ∈ X} ≃ {b : BV n // b ∈ R} := Equiv.ofBijective g hgbij
  let L : Equiv.Perm (BV n) := e.symm.extendSubtype
  refine ⟨fun z => L (r z), ⟨hs, ?_⟩, ?_⟩
  · intro x y
    constructor
    · intro h
      exact (repOf_eq_iff hi x y).1 (L.injective h)
    · intro h
      exact congrArg L ((repOf_eq_iff hi x y).2 h)
  · intro x hx
    have hmem : r x ∈ R := Finset.mem_image_of_mem r hx
    show L (r x) = x
    rw [show L (r x) = (e.symm ⟨r x, hmem⟩ : BV n) from
      Equiv.extendSubtype_apply_of_mem e.symm (r x) hmem]
    have : e ⟨x, hx⟩ = ⟨r x, hmem⟩ := rfl
    rw [← this, Equiv.symm_apply_apply]

/-- Simon instances exist for every nonzero hidden shift, so the promise is not
vacuous. -/

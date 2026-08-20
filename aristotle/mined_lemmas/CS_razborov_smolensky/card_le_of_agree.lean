import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_le_of_agree (F : Type*) [Field F] {n d : ℕ} (A : Finset (Fin n → Bool))
    (h : ∀ f : (Fin n → Bool) → F, ∃ g ∈ Deg F n d, ∀ x ∈ A, g x = f x) :
    A.card ≤ ∑ i ∈ range (d + 1), n.choose i := by
  classical
  set res : ((Fin n → Bool) → F) →ₗ[F] ({x // x ∈ A} → F) :=
    { toFun := fun f x => f x.1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } with hres
  set L : (Deg F n d) →ₗ[F] ({x // x ∈ A} → F) := res.comp (Deg F n d).subtype with hL
  have hsurj : Function.Surjective L := by
    intro f'
    obtain ⟨g, hg, hgf⟩ := h (fun x => if hx : x ∈ A then f' ⟨x, hx⟩ else 0)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext x
    have := hgf x.1 x.2
    simpa [hL, hres, x.2] using this
  have h1 : Module.finrank F ({x // x ∈ A} → F) ≤ Module.finrank F (Deg F n d) := by
    have := LinearMap.finrank_range_le L
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have h2 : Module.finrank F ({x // x ∈ A} → F) = A.card := by
    rw [Module.finrank_pi]; simp
  rw [h2] at h1
  exact h1.trans (Deg_finrank_le F n d)

end CS

import Mathlib
import RequestProject.Poly
import RequestProject.Circuit
import RequestProject.Count

/-!
Razborov's approximation lemma: a circuit of size `S` and depth `d` with AND/OR/NOT and
`MOD q` gates is computed, on all but a `S / 2^t` fraction of the inputs, by a function of
degree at most `((q-1) t) ^ d` over a field of characteristic `q`.
-/

namespace CS

open Finset
open scoped Classical

/-- `0/1` valued indicator of a Boolean. -/

/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Interp

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
`NSPACE f ⊆ DSPACE (16 * (f + 1)^2)`, i.e. Savitch's theorem, and the corollary
`PSPACE = NPSPACE`.

The model of computation is set up in `RequestProject.Savitch.Model`: a device is
a configuration graph with read-only access to the input tape, and the space it
uses is the number of bits needed to encode a configuration.

The proof follows the classical argument.  Given a nondeterministic device `M`
using `s` bits of space, its configuration graph (extended by a single absorbing
accepting vertex) has at most `2 ^ (s+1)` vertices, so acceptance amounts to
reachability in a graph of that size.  Reachability is computed deterministically
by the midpoint recursion `reach` of `RequestProject.Savitch.Reach`, of depth
`K = s + 1`, and this recursion is executed by the explicit stack machine of
`RequestProject.Savitch.Interp`, whose states consist of at most `K` frames, each
holding three vertices and a bit.  That machine therefore has at most
`2 ^ (16 * K ^ 2)` configurations, i.e. it runs in space `O(s²)`.
-/

namespace CS

/-! ### Counting the states of the evaluator -/

section Card

variable {C : Type} [Fintype C] (K : ℕ)

/-- Encoding of a state of the evaluator by its mode and the (padded) list of its
frames. -/

lemma walk_splice {v : ℕ → C} {ℓ i j : ℕ} {a b : C} (hw : Walk R v ℓ a b)
    (hij : i < j) (hj : j ≤ ℓ) (heq : v i = v j) :
    Walk R (fun t => if t ≤ i then v t else v (t + (j - i))) (ℓ - (j - i)) a b := by
  obtain ⟨h0, hl, hstep⟩ := hw
  set d := j - i with hd
  have hd0 : 0 < d := by omega
  refine ⟨by simpa using h0, ?_, ?_⟩
  · by_cases h : ℓ - d ≤ i
    · have hjl : j = ℓ := by omega
      have hli : ℓ - d = i := by omega
      simp only [if_pos h]
      rw [hli, heq, hjl]
      exact hl
    · simp only [if_neg h, show ℓ - d + d = ℓ by omega]
      exact hl
  · intro t ht
    rcases lt_trichotomy t i with h | h | h
    · have h1 : t ≤ i := h.le
      have h2 : t + 1 ≤ i := h
      simp only [if_pos h1, if_pos h2]
      exact hstep t (by omega)
    · subst h
      simp only [if_pos (le_refl t), if_neg (by omega : ¬ t + 1 ≤ t)]
      rw [heq, show t + 1 + d = j + 1 by omega]
      exact hstep j (by omega)
    · simp only [if_neg (by omega : ¬ t ≤ i), if_neg (by omega : ¬ t + 1 ≤ i)]
      rw [show t + 1 + d = (t + d) + 1 by omega]
      exact hstep (t + d) (by omega)

variable [Fintype C]

/-- In a finite graph, any walk can be shortened to one of length less than the
number of vertices. -/

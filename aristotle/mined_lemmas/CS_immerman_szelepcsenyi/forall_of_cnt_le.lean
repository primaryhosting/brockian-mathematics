import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


lemma forall_of_cnt_le (P Q : Fin m → Prop) (h : cnt P ≤ cnt (fun u => P u ∧ Q u)) :
    ∀ u, P u → Q u := by
  have hsub : {u : Fin m | P u ∧ Q u} ⊆ {u : Fin m | P u} := fun _ hu => hu.1
  have heq := Set.eq_of_subset_of_ncard_le hsub h (Set.toFinite _)
  intro u hu
  have : u ∈ {u : Fin m | P u ∧ Q u} := by rw [heq]; exact hu
  exact this.2

/-! ### The state space -/

/-- Configurations of the counting machine.

* `lvl i c` : starting level `i`, having established that level `i` has `c` vertices.
* `outer i c j c'` : looping over vertices, `j` vertices processed, `c'` of which were
  found to be in level `i+1`.
* `walkY i c j c' w k` : certifying that vertex number `j` is in level `i+1`, currently
  at vertex `w` after `k` steps.
* `no i c j c' v jj d` : certifying that `v` is not in level `i+1`, having processed `jj`
  vertices and certified `d` of them to be in level `i` and unrelated to `v`.
* `walkN i c j c' v jj d w k` : certifying that vertex number `jj` is in level `i`,
  currently at vertex `w` after `k` steps.
* `acc` : the accepting configuration.
-/
inductive St (m : ℕ) where
  | lvl (i c : Fin (m + 2)) : St m
  | outer (i c j c' : Fin (m + 2)) : St m
  | walkY (i c j c' : Fin (m + 2)) (w : Fin m) (k : Fin (m + 2)) : St m
  | no (i c j c' : Fin (m + 2)) (v : Fin m) (jj d : Fin (m + 2)) : St m
  | walkN (i c j c' : Fin (m + 2)) (v : Fin m) (jj d : Fin (m + 2)) (w : Fin m)
      (k : Fin (m + 2)) : St m
  | acc : St m
  deriving DecidableEq

/-- A vertex, viewed as an index. -/

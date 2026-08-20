/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision tree.
A `node i j l r` compares the elements at positions `i` and `j`, continuing with `l` if the
`i`-th element is smaller and with `r` otherwise.  A `leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type where
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed, i.e. the depth of the decision tree. -/

def sortTree4 : CompTree 4 :=
  (.node 0 1
    (.node 0 2
      (.node 1 2
        (.node 1 3
          (.node 2 3
            (.leaf (mkPerm ![0, 1, 2, 3] ![0, 1, 2, 3]))
            (.leaf (mkPerm ![0, 1, 3, 2] ![0, 1, 3, 2])))
          (.node 0 3
            (.leaf (mkPerm ![0, 2, 3, 1] ![0, 3, 1, 2]))
            (.leaf (mkPerm ![1, 2, 3, 0] ![3, 0, 1, 2]))))
        (.node 2 3
          (.node 1 3
            (.leaf (mkPerm ![0, 2, 1, 3] ![0, 2, 1, 3]))
            (.leaf (mkPerm ![0, 3, 1, 2] ![0, 2, 3, 1])))
          (.node 0 3
            (.leaf (mkPerm ![0, 3, 2, 1] ![0, 3, 2, 1]))
            (.leaf (mkPerm ![1, 3, 2, 0] ![3, 0, 2, 1])))))
      (.node 0 3
        (.node 1 3
          (.leaf (mkPerm ![1, 2, 0, 3] ![2, 0, 1, 3]))
          (.leaf (mkPerm ![1, 3, 0, 2] ![2, 0, 3, 1])))
        (.node 2 3
          (.leaf (mkPerm ![2, 3, 0, 1] ![2, 3, 0, 1]))
          (.leaf (mkPerm ![2, 3, 1, 0] ![3, 2, 0, 1])))))
    (.node 0 2
      (.node 0 3
        (.node 2 3
          (.leaf (mkPerm ![1, 0, 2, 3] ![1, 0, 2, 3]))
          (.leaf (mkPerm ![1, 0, 3, 2] ![1, 0, 3, 2])))
        (.node 1 3
          (.leaf (mkPerm ![2, 0, 3, 1] ![1, 3, 0, 2]))
          (.leaf (mkPerm ![2, 1, 3, 0] ![3, 1, 0, 2]))))
      (.node 1 2
        (.node 2 3
          (.node 0 3
            (.leaf (mkPerm ![2, 0, 1, 3] ![1, 2, 0, 3]))
            (.leaf (mkPerm ![3, 0, 1, 2] ![1, 2, 3, 0])))
          (.node 1 3
            (.leaf (mkPerm ![3, 0, 2, 1] ![1, 3, 2, 0]))
            (.leaf (mkPerm ![3, 1, 2, 0] ![3, 1, 2, 0]))))
        (.node 1 3
          (.node 0 3
            (.leaf (mkPerm ![2, 1, 0, 3] ![2, 1, 0, 3]))
            (.leaf (mkPerm ![3, 1, 0, 2] ![2, 1, 3, 0])))
          (.node 2 3
            (.leaf (mkPerm ![3, 2, 0, 1] ![2, 3, 1, 0]))
            (.leaf (mkPerm ![3, 2, 1, 0] ![3, 2, 1, 0])))))))


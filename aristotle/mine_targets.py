#!/usr/bin/env python3
"""mine_targets.py — keep the overnight fleet fueled: generate fresh, well-posed
parametrized proof targets so night_submit never runs dry. Emits mined_queue.json.

All targets are parametrized INSTANCES of standard results (true, formalizable) —
never fabricated theorems. Idempotent: regenerates the full mined set each run.
"""
import json
import pathlib

OUT = pathlib.Path(__file__).resolve().parent / "mined_queue.json"


def q(target, tier, statement, rank=3):
    return {"target": target, "tier": tier, "goal": "Prove in Lean 4 (Mathlib), axiom-clean.",
            "statement": statement, "rank": rank}


def main():
    items = []
    # Hückel / spectral graph theory: cycle & path eigenvalues
    for n in range(3, 21):
        items.append(q(f"Chem.huckel_C{n}", "DOMAIN-chem",
                       f"The adjacency eigenvalues of the cycle graph C_{n} are 2·cos(2πk/{n}) for k=0..{n-1}.", 2))
    # QC: n-qubit QFT unitary + GHZ_n
    for n in range(2, 9):
        items.append(q(f"QC.qft_unitary_{n}", "DOMAIN-qc", f"The {n}-qubit QFT matrix is unitary.", 0))
        items.append(q(f"QC.ghz{n}_normalized", "DOMAIN-qc",
                       f"The {n}-qubit GHZ state (|0…0⟩+|1…1⟩)/√2 is a unit vector.", 0))
    # Number theory: sum of two squares for specific primes p ≡ 1 (mod 4)
    for p in [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113]:
        items.append(q(f"Math.two_squares_{p}", "DOMAIN-math",
                       f"The prime {p} is a sum of two squares.", 1))
    # Cassini/Catalan-type Fibonacci identities at specific n
    for n in range(2, 16):
        items.append(q(f"Math.cassini_{n}", "DOMAIN-math",
                       f"Cassini: F({n-1})·F({n+1}) − F({n})² = (−1)^{n}.", 1))
    # Ramsey / combinatorics small known values
    for (a, b, r) in [(3, 3, 6), (3, 4, 9), (4, 4, 18), (3, 5, 14)]:
        items.append(q(f"Math.ramsey_{a}_{b}", "DOMAIN-math",
                       f"R({a},{b}) = {r}: the two-color Ramsey number.", 1))
    # Pell equation fundamental solutions x²−D y²=1 for non-square D
    for D in [2, 3, 5, 6, 7, 8, 10, 11, 13]:
        items.append(q(f"Math.pell_{D}", "DOMAIN-math",
                       f"x² − {D}·y² = 1 has a nontrivial integer solution (Pell).", 2))
    # Cyclotomic: sum of primitive n-th roots of unity = μ(n)
    for n in range(1, 13):
        items.append(q(f"Math.mobius_root_sum_{n}", "DOMAIN-math",
                       f"The sum of the primitive {n}-th roots of unity equals μ({n}).", 2))
    # CS: sorting-network / correctness at specific sizes; comparator count lower bounds
    for k in [3, 4, 5]:
        items.append(q(f"CS.sorting_lb_{k}", "DOMAIN-cs",
                       f"Any comparison sort of {k} elements needs ≥ ⌈log₂({k}!)⌉ comparisons in the worst case.", 1))
    # Quantum physics: particle-in-box level ratios
    for n in range(1, 8):
        items.append(q(f"QPhys.box_level_{n}", "DOMAIN-qphys",
                       f"The infinite-well energy ratio E_{n}/E_1 = {n}².", 2))

    OUT.write_text(json.dumps({"count": len(items), "queue": items}, indent=1))
    print(f"wrote {OUT} with {len(items)} mined targets")


if __name__ == "__main__":
    main()

# The biplanar clique blow-ups of the five-cycle

Deep Bhattacharjee

**Theorem.** For `w = (w_1, ..., w_5)` with positive integer entries, let `C5[w]` be the graph with
bags `A_1, ..., A_5` of sizes `w_i`, two vertices being adjacent when their bags are equal or
consecutive on the five-cycle. Then `C5[w]` is biplanar if and only if
`max(w_i + w_{i+1}) <= 8` and `w_1 + ... + w_5 <= 16`.

**Corollary.** Every biplanar clique blow-up of the five-cycle is 8-colourable, and
`C5[3,3,3,3,4]` is biplanar with chromatic number 8. So none is 9-chromatic, which answers
Question 7.3 of A. Trivedi, *Biplanar clique blow-ups of C5 are 9-colourable*
([doi:10.5281/zenodo.22074335](https://doi.org/10.5281/zenodo.22074335)) in the negative.

> **Status, 12 October 2026: the proof is not yet complete.** The refutations of Theorem 5.1 are
> certified for 18 of the 26 seventeen-vertex vectors. For the other eight, `(2,2,5,3,5)`,
> `(2,3,4,3,5)`, `(2,3,4,4,4)`, `(2,3,5,3,4)`, `(2,4,3,3,5)`, `(2,4,3,4,4)`, `(3,3,3,4,4)` and
> `(3,3,4,3,4)`, the decision-tree certification is still running (cubes in
> [`verification/data/cubes/`](verification/data/cubes/)). Until all eight are certified, the theorem
> and the answer to Question 7.3 are not proved, and no release is made.

**Longer odd cycles (Section 7, complete).** For every `k >= 1` and every `w` with nonnegative
entries, `chi(C_{2k+1}[w]) = max(max(w_i + w_{i+1}), ceil(n/k))`, which Trivedi proposed in Question 7.1.
So every biplanar clique blow-up of an odd cycle of length at least five is 9-colourable, as asked
there. This part does not use the certificates. The formula and the arithmetic of the corollary are
proved in Lean (`Biplanar.OddCycle.chromatic`, `nine_of_long`, `nine_of_seven`, in
[`verification/lean/BiplanarC5/OddCycle.lean`](verification/lean/BiplanarC5/OddCycle.lean)), with the
non-biplanarity of `K_9` and the bound `2s-4` for triangle-free planar graphs as hypotheses.
Weighted cycles are coloured optimally by an algorithm of Narayanan and Shende (Algorithmica 29,
2001); we have not found the formula stated in that literature.

The paper is in [`preprint/`](preprint/main.tex); the built PDF, the LaTeX source with PNG figures
and the arXiv tarball are attached to each release. [PRIORITY-CHECK.md](PRIORITY-CHECK.md) records the
check, dated 11 October 2026, that the question was still open.

## How the proof goes

1. **Reduction** (Lemma 2.1). Lowering an entry keeps `max(w_i + w_{i+1}) <= 8`, and a short argument
   about tight pairs lets one raise entries up to 16 vertices. So it suffices to draw 36 graphs on
   16 vertices and to refute 26 graphs on 17 vertices, each up to the symmetries of the five-cycle.
2. **Drawings** (Proposition 2.3). Each of the 36 graphs comes with two edge lists and, for each, a
   plane straight-line drawing at integer points of `[0,28] x [0,14]`, checked by exact orientation
   tests.
3. **A contraction lemma** (Lemma 3.1). If a component of one layer outside an 8-clique `Q` sees
   enough of `Q`, contracting it gives a ninth vertex joined to all of `Q`, and the two layers then
   contain `K_9`, which is not biplanar (Battle–Harary–Kodama 1962, Tutte 1963).
4. **Encoding and certificates** (Sections 4 and 5). Schnyder's order characterisation of planarity
   plus the clauses of the contraction lemma and clauses implied by planarity of each layer (no
   `K_5` or `K_{3,3}` inside a layer, at most `3s-6` edges of an `s`-clique inside a layer) give a
   formula `Φ(w)` that is satisfiable whenever `C5[w]` is biplanar. CaDiCaL 3.0.1 is to refute `Φ(w)` for all 26 vectors (18 done so far, see the status above), lrat-trim shortens the LRAT
   proofs, and Lean 4 checks each proof against the formula produced by the Lean encoder.

## What is checked, and how

| Part | Lean 4 | Other checks |
| --- | --- | --- |
| Lemma 2.2: the 26 and 36 classes | `cands17_spec`, `wits16_spec` (kernel) | C++, shell (awk), Python, Julia |
| Lemma 2.1 by enumeration of `{1..7}^5` | `reduction`, `entries_lt_8` (kernel) | C++, Python, Julia |
| Proposition 2.3: 36 pairs of plane drawings | `biplanar_*` (kernel, exact integers) | C, Python (exact tests and networkx), Julia |
| 8-colourings of the 36 graphs | `colouring_*` (kernel) | C, Python, Julia |
| Formula (1.1) on all 62 graphs | | Python (exhaustive colouring) |
| Theorem 7.1 and Corollary 7.2 (odd cycles) | `Biplanar.OddCycle.chromatic`, `nine_of_long`, `nine_of_seven` (proofs for all `k`) | Python (exact dynamic programme, `k <= 5`) |
| Theorem 5.1: `Φ(w)` unsatisfiable, 26 vectors | `Biplanar.unsat_*` via `scripts/certify.sh` (verified LRAT checker of the standard library) | lrat-trim |

`verification/lean/Check.lean` audits the axioms of every theorem of the library: all of them use
only `propext`, `Classical.choice` and `Quot.sound`. Each certificate theorem additionally uses the
one axiom that `native_decide` introduces, which trusts the Lean compiler; `certify.sh` rejects any
other axiom.

Not formalised, and stated as such in the paper: Schnyder's theorem; that `K_5` and `K_{3,3}` are
not planar and a planar graph on `s >= 3` vertices has at most `3s-6` edges; that minors of planar graphs
are planar and that joining two components of a planar graph by an edge keeps it planar; the
non-biplanarity of `K_9`; and the soundness of the encoding (Proposition 4.2, proved in the paper).

## Running the checks

```sh
scripts/run_all.sh                 # C, C++, shell, Python, Julia and the Lean library
LEAN=0 scripts/run_all.sh          # without Lean
scripts/get_tools.sh               # build the pinned CaDiCaL 3.0.1 and lrat-trim 0.2.0
scripts/certify.sh 1,1,7,1,7       # refute one formula and check the refutation in Lean
scripts/build_paper.sh             # the PDF, tex.zip and arXiv tarball in dist/
```

The Python check needs `networkx`; the Lean project needs elan (toolchain `v4.34.1`, no Mathlib).
`certify.sh` re-solves the formula unless the trimmed proof `dist/certificates/W.lrat.xz` is
present; the 26 trimmed proofs are attached to the release as `.xz` files, with their SHA-256 sums.
The slowest formulas take about half an hour to solve on one core.

## Layout

```
preprint/                 main.tex and the TikZ figures (built to PNG)
verification/data/        the 26 and 36 weight vectors, the drawings and the colourings
verification/lean/        Lean 4 project BiplanarC5: encoder, drawings, colourings, reduction
verification/c|cpp|shell|python|julia/   independent checks
scripts/                  run_all.sh, certify.sh, get_tools.sh, build_paper.sh
```

## Citation

See [CITATION.cff](CITATION.cff). Licence: MIT.

The biplanar clique blow-ups of the five-cycle, by Deep Bhattacharjee.

A clique blow-up `C5[w]` of the five-cycle is biplanar if and only if it has at most sixteen vertices and clique number at most eight. So every biplanar clique blow-up of the five-cycle is 8-colourable, and none is 9-chromatic, which answers Question 7.3 of A. Trivedi (doi:10.5281/zenodo.22074335) in the negative.

Files:
- `biplanar-c5-blowups.pdf`: the paper.
- `biplanar-c5-blowups-tex.zip`: LaTeX source with the figures as PNG and their TikZ sources.
- `biplanar-c5-blowups-arxiv.tar.gz`: LaTeX source ready for arXiv.
- `W.lrat.xz` for each of the 26 weight vectors `W` of Table 2: the trimmed LRAT refutation of the formula `Φ(W)`, produced by this release's workflow with CaDiCaL 3.0.1 and lrat-trim 0.2.0 and checked in Lean 4 before upload.
- `SHA256SUMS-lrat.txt` and `SHA256SUMS-xz.txt`: hashes of the proofs and of the compressed files.

The repository at this tag also holds the dated priority check (`PRIORITY-CHECK.md`), the weight vectors, drawings and colourings, the Lean 4 project (`verification/lean`: the encoder, the finite reduction, the 36 drawings and colourings by kernel evaluation, and `scripts/certify.sh`, which checks a proof with the verified LRAT checker of the Lean standard library), and checks in C, C++, Bash, Python and Julia.

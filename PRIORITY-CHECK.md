# Priority check, 11 October 2026

Question: is some clique blow-up `C5[w]` of the five-cycle biplanar and 9-chromatic? This is
Question 7.3 of A. Trivedi, *Biplanar clique blow-ups of C5 are 9-colourable*, Zenodo, August 2026,
[doi:10.5281/zenodo.22074335](https://doi.org/10.5281/zenodo.22074335). Trivedi reduces it to 35
weight vectors (26 with 17 vertices, 9 with 18) and leaves all of them open.

The answer given here is no: `C5[w]` is biplanar exactly when `max(w_i + w_{i+1}) <= 8` and
`w_1 + ... + w_5 <= 16`, so every biplanar clique blow-up of the five-cycle is 8-colourable.

## Where we looked

| Source | Search | What it shows |
| --- | --- | --- |
| OpenRefute ([the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing/issues)) | issues and PRs for "biplanar", "Trivedi", "Earth-Moon", "thickness", "chromatic" | no issue or PR on biplanar graphs, thickness two or clique blow-ups |
| Zenodo | records matching "biplanar", newest first; all versions of record 22074335 | Trivedi's record has one version (5 August 2026) and does not answer the question; the only other graph-theory record is Szeider's Lean development for arXiv:2609.28102 (record 22913639) |
| arXiv | all fields "biplanar", newest first; abstracts with "thickness two", "Earth-Moon", "blow-up" | the only related paper is S. Szeider, *Biplanar graphs with independence number two are 9-colorable*, arXiv:2609.28102 (23 September 2026): every biplanar graph with independence number at most 2 has at most 18 vertices and is 9-colourable. It cites Trivedi's bound for clique blow-ups and does not decide the 17- and 18-vertex blow-ups |
| Web | "biplanar clique blow-up five-cycle", "C5[w] biplanar 9-chromatic Question 7.3" | Trivedi's record, Szeider's paper, and D. Eppstein, *On the biplanarity of blowups*, JGAA 28 (2024), which studies blow-ups by independent copies (Gethner's 2-blowup conjecture) and not clique blow-ups |
| Earlier literature | Kirchweger, Scheucher and Szeider (SAT 2023); Gethner and Sulanke (2009); Boutin, Gethner and Sulanke (2008); Albertson, Boutin and Gethner (2010); Gethner (2018) | `C5[4,4,4,4,3]` is not biplanar (KSS, by SAT); `C_m[K_3]` is biplanar; none decides the 35 vectors |

Epoch AI lists the Earth–Moon problem among its FrontierMath open problems
([epoch.ai/frontiermath/open-problems/earth-moon](https://epoch.ai/frontiermath/open-problems/earth-moon),
read on 11 October 2026). It asks for a biplanar graph with chromatic number at least 10, is marked
unsolved, and does not mention clique blow-ups. The question is not an Erdős problem, so
erdosproblems.com does not apply; GitHub's code search of openai/math needs a signed-in session and
was not run.

## Conclusion

As of 11 October 2026 nobody has answered Trivedi's Question 7.3 or determined which clique blow-ups
of the five-cycle are biplanar. The 17-vertex non-biplanarity results here are new; the 16-vertex
drawings are new as well, but the biplanarity of individual 16-vertex blow-ups is not claimed as the
main result.

# Priority check for Question 7.1, 13 October 2026

Question 7.1 of the same preprint asks whether `chi(C_{2k+1}[w]) = max(max(w_i + w_{i+1}), ceil(n/k))`
holds for clique blow-ups of the odd cycles `C_{2k+1}` with `k >= 3`, and notes that it would make every
biplanar one 9-colourable. Section 7 of the paper proves the formula for every `k >= 1`.

| Source | Search | What it shows |
| --- | --- | --- |
| OpenRefute | issues for "biplanar" | none |
| Zenodo | "biplanar", "clique blow-up", "odd cycle blow-up chromatic", newest first | no record after Szeider's (22913639, 23 September 2026) on the question; Trivedi's record still has one version |
| arXiv | Szeider, arXiv:2609.28102, Section 7 | uses the `112 > 104` edge count of Question 7.1 to show that `C_7[K_4]` is not biplanar, and does not address the formula |
| Web | "weighted colouring odd cycle chromatic number", McDiarmid–Reed, Gerke–McDiarmid, Narayanan–Shende | Narayanan and Shende, *Static frequency assignment in cellular networks*, Algorithmica 29 (2001), give an algorithm that multicolours weighted cycles optimally; we did not find the closed formula stated, and the paper cites them for this |

As of 13 October 2026 nobody has answered Question 7.1. The formula may be implicit in the channel
assignment literature, which the paper says.

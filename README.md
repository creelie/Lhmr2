# Lehmer's Totient Problem for Ideals of Dedekind Domains

Deep Bhattacharjee

Paper: [paper/LehmerPaper.pdf](paper/LehmerPaper.pdf)

Code and data DOI: [10.5281/zenodo.24181687](https://doi.org/10.5281/zenodo.24181687)

Code and data for the paper:

- `c/` — tree search in C with GMP (`lms4.c`; `lms5.c` adds the size limit used for the integer bound). Build: `gcc -O2 -o lms4 lms4.c -lgmp`; run: `./lms4 MODE SIGN K [Mmin Mmax]` with MODE in `int uni quad gauss eis`, SIGN `-1` (Lehmer) or `1` (companion).
- `julia/` — independent Julia traversal and the binary and one-prime enumerations (Julia 1.11).
- `lean/` — `LehmerIdeals.lean`, 381 theorems checked by `decide +kernel` (Lean 4.24.0, core only): `lean LehmerIdeals.lean`.
- `python/` — the binary classification programs and their data.
- `logs/` — complete outputs of all searches reported in the paper.
- `figures-src/` — script for the figures.

Lehmer's original question for integers remains open.

# A projective plane of order 18 admits no collineation of order 17

> **Status.** Computer-assisted result, **not peer reviewed**; novelty not verified against the literature.
> Most derivations, programs and verification were done by AI (Claude, Anthropic) under the author's direction; the author set the problem, directed the research and judged the results.
> The search programs are in `code/`; the original run output is not distributed because the computation is deterministic and can be re-run (about 4 hours; see `code/README.md`).
> This does **not** settle whether a projective plane of order 18 exists.

**Main result.** A finite projective plane of order 18 has no collineation of order 17 (the argument does not use Baer's theorem on involutions). The case of three fixed points is reduced to a finite problem on 58,161 classes of orthomorphisms of Z/17 and settled by computer.

- Paper: [`paper/main.pdf`](paper/main.pdf) (source: `paper/main.tex`, `paper/refs.bib`; build: `make -C paper`).
- Search code: [`code/`](code/) (`orth.cpp`, `fast4.cpp`; build and run instructions in `code/README.md`).
- Licence: paper and documents CC BY 4.0 (`LICENSE`), source code MIT (`code/LICENSE`); attribution required. Citation: `CITATION.cff`.

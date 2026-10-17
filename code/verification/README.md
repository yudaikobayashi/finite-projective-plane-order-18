# Verification programs

These are the auxiliary programs used to check the main computation (`../fast4.cpp`, `../orth.cpp`).
They are published as they were used: not polished, little documented, each a stand-alone file.
Usage is in the comment at the top of each source. Nothing here is needed to reproduce the main result.

| File | Purpose |
|---|---|
| `indep2.cpp` | Reproduction from the paper alone (families, orthomorphisms, classes, per-class decision). |
| `indep.cpp` | Independent re-implementation of the per-net decision; compared with the main program on row sets. |
| `mine.cpp`, `mine17b.cpp` | Independent re-implementations for p = 3,5,7,11,13 and p = 17. |
| `cnt.cpp` | Depth-first count of orthomorphisms (94,471,089 normalised; x17 = 1,606,008,513). |
| `orbsum.cpp`, `orb.cpp` | Explicit orbit enumeration for the class list. |
| `fam.cpp` | Count of the perfect difference families (490,801). |
| `oracle_pairs.py` | Geometric oracle for row-pair compatibility. |
| `plane.py` | Checks that a found structure is a projective plane (p = 7 control). |
| `fast4_p.cpp`, `ctrl_p.cpp` | Parametrised copy of `fast4.cpp` and the p = 31 control. |
| `watchdog.sh` | Restarts the resumable full run if it exits early (edit the paths in it). |

The class list `classes17.txt` and the run output `run_out.txt` are not distributed;
`./orth classes classes17.txt` and the run command in the paper regenerate them.

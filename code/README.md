# Search code for the order-17 triangle case

- `orth.cpp`: enumerates the normalised orthomorphisms of Z_17 and writes the 58,161 class representatives (the equivalence classes of the paper).
- `fast4.cpp`: decides, for each class, whether the row-compatibility graph has a 17-clique (a solution). Compile-time parameter `-DP=17` (the case of the paper) or `-DP=7` (control, PG(2,8)).
- `nets7_all.txt`: the 133 orthomorphisms of Z_7 (input of the p=7 control).

Requirements: g++ with OpenMP and AVX2 (`-march=native`). Use fewer threads (`OMP_NUM_THREADS`) if the machine is shared.

    # p = 7 control (seconds): expect 133 nets, 35 with solutions, 70 solutions
    g++ -O3 -march=native -fopenmp -DP=7 fast4.cpp -o netrun7
    ./netrun7 nets7_all.txt 0 133 out7.txt run
    awk '$19>0{n++; s+=$19} END{print n, s}' out7.txt        # 35 70

    # p = 17: class list, then the full search (about 4 h on 12 threads; resumable)
    g++ -O3 -march=native -fopenmp orth.cpp -o orth
    ./orth count                       # 94471089
    ./orth classes classes17.txt       # 58161 lines
    g++ -O3 -march=native -fopenmp -DP=17 fast4.cpp -o netrun17
    OMP_NUM_THREADS=12 ./netrun17 classes17.txt 0 58161 run_out.txt run
    awk '{a2+=$7;s+=$13;c+=$17} END{print NR,a2,s,c}' run_out.txt   # 58161 627 0 0

Partial check: ids 0..299 take about 2 minutes. Checksums of the sources are listed in the paper (Appendix on reproduction). Source licence: MIT (`LICENSE` in this directory).

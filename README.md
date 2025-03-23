# por_alloy

This repository contains the formalization in Alloy 6 (v6.1.0) of five partial-order reduction methods with known errors. In `lib/blsts.als` is a base formalism for the system to be reduced.
Below is a list of the partial-order reduction methods and where to find them in the code.

- Stubborn sets applied to labelled-state transition systems [1,2,3]: `stubborn_lsts.als`
- Stubborn sets applied to parity games [4]: `stubborn_pg.als` 
- Stubborn sets applied to reachability games [5,6]: `stubborn_rg.als`
- Ample sets applied to labelled Kripke structures [7]: `ample_lks.als`
- Ample sets applied to product automata [8,9] based on an existing Alloy formalization [10]: `ample_pa.als`

In the literature, there are counterexamples for the known errors [3,4,10] as well as proposed fixes [3,4,7,10]. The code to reproduce the counterexample for each method is in a file prefixed with just `test_`, and the files prefixed with `test_fix_` verify that the fixes eliminate the counterexamples. 

# References
[1] Valmari, A. (1991). Stubborn sets for reduced state space generation (pp. 491-515). Springer Berlin Heidelberg.

[2] Valmari, A., & Hansen, H. (2017). Stubborn set intuition explained. In Transactions on Petri Nets and Other Models of Concurrency XII (pp. 140-165). Berlin, Heidelberg: Springer Berlin Heidelberg.

[3] Neele, T., Valmari, A., & Willemse, T. A. (2021). A detailed account of the inconsistent labelling problem of stutter-preserving partial-order reduction. Logical Methods in Computer Science, 17.

[4] Neele, T., Willemse, T. A., Wesselink, W., & Valmari, A. (2022). Partial-order reduction for parity games and parameterised Boolean equation systems. International Journal on Software Tools for Technology Transfer, 24(5), 735-756.

[5] Bønneland, F. M., Jensen, P. G., Larsen, K. G., Muñiz, M., & Srba, J. (2019). Partial order reduction for reachability games. In 30th International Conference on Concurrency Theory (CONCUR 2019) (pp. 23-1). Schloss Dagstuhl–Leibniz-Zentrum für Informatik.

[6] Bønneland, F. M., Jensen, P. G., Larsen, K. G., Muñiz, M., & Srba, J. (2021). Stubborn set reduction for two-player reachability games. Logical Methods in Computer Science, 17.

[7] Beneš, N., Brim, L., Buhnova, B., Černá, I., Sochor, J., & Vařeková, P. (2011). Partial order reduction for state/event LTL with application to component-interaction automata. Science of Computer Programming, 76(10), 877-890.

[8] Peled, D. (1994). Combining partial order reductions with on-the-fly model-checking. In Computer Aided Verification: 6th International Conference, CAV'94 Stanford, California, USA, June 21–23, 1994 Proceedings 6 (pp. 377-390). Springer Berlin Heidelberg.

[9] Peled, D. (1996). Combining partial order reductions with on-the-fly model-checking. Formal Methods in System Design, 8, 39-64.

[10] Siegel, S. F. (2019, July). What’s wrong with on-the-fly partial order reduction. In International Conference on Computer Aided Verification (pp. 478-495). Cham: Springer International Publishing.
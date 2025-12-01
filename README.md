# por_alloy

This repository contains the formalization in Alloy 6 (v6.2.0) of five partial-order reduction methods with known errors. In `lib/blsts.als` is a base formalism for the system to be reduced.
Below is a list of the partial-order reduction methods and where to find them in the code.

- Stubborn sets applied to labelled-state transition systems [1,2,3]: `stubborn_lsts.als`
- Stubborn sets applied to parity games [4,5]: `stubborn_pg.als` 
- Stubborn sets applied to reachability games [6,7]: `stubborn_rg.als`
- Ample sets applied to labelled Kripke structures [8]: `ample_lks.als`
- Ample sets applied to product automata [9,10] based on an existing Alloy formalization [11]: `ample_pa.als`

In the literature, there are counterexamples for the known errors as well as proposed fixes. The code to reproduce the counterexample for each method is in a file prefixed with just `test_`, and the files prefixed with `test_fix_` verify that the fixes eliminate the counterexamples. 

# References
[1] Valmari, A.: A Stubborn Attack on State Explosion. Formal Methods Syst. Des.1(4), 297–322 (1992). https://doi.org/10.1007/BF00709154

[2] Valmari, A., Hansen, H.: Stubborn Set Intuition Explained. Trans. Petri
Nets Other Model. Concurr. 12, 140–165 (2017). https://doi.org/10.1007/978-3-662-55862-1_7

[3] Neele, T., Valmari, A., Willemse, T.A.C.: A Detailed Account of The Inconsistent Labelling Problem of Stutter-Preserving Partial-Order Reduction. Log. Methods Comput. Sci. 17(3) (2021). https://doi.org/10.46298/LMCS-17(3:8)2021

[4] Neele, T., Willemse, T.A.C., Wesselink, W.: Partial-Order Reduction for Parity Games with an Application on Parameterised Boolean Equation Systems. In:
TACAS (2). Lecture Notes in Computer Science, vol. 12079, pp. 307–324. Springer
(2020). https://doi.org/10.1007/978-3-030-45237-7_19

[5] Neele, T., Willemse, T.A.C., Wesselink, W., Valmari, A.: Partial-order reduction for parity games and parameterised Boolean equation systems. Int. J.
Softw. Tools Technol. Transf. 24(5), 735–756 (2022). https://doi.org/10.1007/
S10009-022-00672-0

[6] Bønneland, F.M., Jensen, P.G., Larsen, K.G., Muñiz, M., Srba, J.: Partial Order Reduction for Reachability Games. In: CONCUR. LIPIcs, vol. 140, pp. 23:1–23:15. Schloss Dagstuhl - Leibniz-Zentrum für Informatik (2019). https://doi.org/10.4230/LIPICS.CONCUR.2019.23

[7] Bønneland, F.M., Jensen, P.G., Larsen, K.G., Muñiz, M., Srba, J.: Stubborn Set Reduction for Two-Player Reachability Games. Log. Methods Comput. Sci. 17(1) (2021). https://doi.org/10.23638/LMCS-17(1:21)2021

[8] Benes, N., Brim, L., Buhnova, B., Cerná, I., Sochor, J., Vareková, P.: Partial order reduction for state/event LTL with application to component-interaction automata. Sci. Comput. Program. 76(10), 877–890 (2011). https://doi.org/10.1016/J.SCICO.2010.02.008

[9] Peled, D.A.: Combining Partial Order Reductions with On-the-fly Model-Checking. In: CAV. Lecture Notes in Computer Science, vol. 818, pp. 377–390. Springer (1994). https://doi.org/10.1007/3-540-58179-0_69

[10] Peled, D.A.: Combining Partial Order Reductions with On-the-Fly Model-
Checking. Formal Methods Syst. Des. 8(1), 39–64 (1996). https://doi.org/10.1007/BF00121262

[11] Siegel, S.F.: What’s Wrong with On-the-Fly Partial Order Reduction. In: CAV (2). Lecture Notes in Computer Science, vol. 11562, pp. 478–495. Springer (2019). https://doi.org/10.1007/978-3-030-25543-5_27
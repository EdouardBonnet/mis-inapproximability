Unless $NP\subseteq BPP$, for every constant $\varepsilon>0$, Max
Independent Set on $N$-vertex triangle-free graphs admits no polynomial-time
$N^{1/2-\varepsilon}$-approximation algorithm. This is the main
inapproximability theorem of *Tight Inapproximability of Max Independent Set
in Triangle-Free Graphs*. Its proof derives the general-graph promise-gap
hardness from the proved PCP-to-clique reduction in lax-253009. The derivation
complements the graph, converts the relative clique gap to the absolute
independent-set promises, handles the solver's finite cutoff by bounded
exhaustive search, and amplifies and composes the randomized tests.

The reduction blows each vertex of an $n$-vertex graph up into $n$
vertices, samples the blow-up edges independently, and resamples the edges of
present triangles.  The formalization proves triangle-freeness, completeness,
the fixed-set soundness estimate, the finite-seed probability bound, and the
final gap arithmetic.  The infinite product table occurs only in the
probabilistic analysis; the program itself reads a polynomially bounded finite
family of uniform bits.

Polynomial time is certified by a finite Turing machine. The proof derives
explicit polynomial bounds for the reduction, the approximation-machine
call, decoding, threshold arithmetic, and the number of random bits.

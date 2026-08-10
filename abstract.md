This submission formalizes the main inapproximability theorem of *Tight
Inapproximability of Max Independent Set in Triangle-Free Graphs*.  Assuming
Håstad's promise hardness of Max Independent Set, it proves that,
for every constant $\varepsilon>0$, a polynomial-time
$N^{1/2-\varepsilon}$-approximation algorithm on $N$-vertex triangle-free
graphs implies $NP\subseteq BPP$.

The reduction blows each vertex of an $n$-vertex graph up into $n$
vertices, samples the blow-up edges independently, and resamples the edges of
present triangles.  The formalization proves triangle-freeness, completeness,
the fixed-set soundness estimate, the finite-seed probability bound, and the
final gap arithmetic.  The infinite product table occurs only in the
probabilistic analysis; the program itself reads a polynomially bounded finite
family of uniform bits.

Polynomial time, $NP$, and $BPP$ use a bounded interpreter for fixed finite
binary multi-stack Turing machines.  Every semantic answer is the output of
that interpreter.  The composed triangle-removal program has a fixed recursive
evaluator whose state and operation count are produced by the same execution,
and the proof derives explicit polynomial bounds for the reduction, the
approximation-machine call, decoding, threshold arithmetic, and random bits.

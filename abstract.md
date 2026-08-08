This submission formalizes the main inapproximability theorem of *Tight
Inapproximability of Max Independent Set in Triangle-Free Graphs*.  Assuming
the Håstad--Zuckerman promise hardness of Max Independent Set, it proves that,
for every constant $\varepsilon>0$, a polynomial-time
$N^{1/2-\varepsilon}$-approximation algorithm on $N$-vertex triangle-free
graphs implies $NP\subseteq BPP$.

The reduction blows each vertex of an $n$-vertex graph up into $n$
vertices, samples the blow-up edges independently, and resamples the edges of
present triangles.  Its termination and output-distribution estimates use the
kernel-checked Moser--Tardos and Haeupler--Saha--Srinivasan proofs from
submission Lax41.  The formalization proves triangle-freeness, completeness,
the fixed-set soundness estimate, and the final gap arithmetic.  Computations
carry an explicit number of elementary steps; polynomial time, $NP$, and
$BPP$ are defined directly through polynomial bounds on those step counts,
without choosing a machine model.

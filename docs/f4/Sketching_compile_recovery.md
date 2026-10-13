# Sketching compile recovery after F4 upstream changes

This continuation repairs downstream consumers of the completed Matrix and Probability
API changes. It does not claim completion of A2 consistency work or redesign Sparse.

Verified failed leaves (locked targeted build, `/tmp/m2-sketch-leaves1.log`, 3984 dependency jobs):

- `Sampling/UniformIidSampling` and `Sampling/LeverageSampling`: split matrix Chernoff tails,
  PSD assumptions derived from existing hypotheses, and named spectral-norm Gram bridge.
- `Properties/JL/JL`: real-valued Gaussian-vector tails, transported to the existing ENNReal
  statement without changing its constants or mathematical event.
- `Gaussian/GaussianEmbedding`: last-column singular value replacing deleted `sigmaMin`,
  with the generalized norm lower bound and the real square-root bridge.
- `Sparse/CountSketchMoments`: renamed Rademacher-vector quadratic moment lemmas only.

`Sampling/SamplingWithoutReplacementTails` also compiled in `/tmp/m2-sketch-srht1.log` after
migration to the split matrix Laplace tails.

The SRHT real-sign migration is compiled. Its public signs and laws now use real-valued vectors and
`rademacherVector`; deterministic sign-isometry lemmas require coordinate squares equal to
one, while probabilistic callers obtain this almost everywhere from the canonical law.
The sharp row tail uses P's reusable finite-support measure wrapper, and conditioning uses
P's measurable-product event lemma. `SRHTWithReplacement` and its complete dependency chain
compiled in `/tmp/m2-sketch-srht8.log` (3391 dependency jobs), including the exact full-row and
rank-zero endpoints. Added measurability lemmas justify the real-sign product events; this
replaces the finite/discrete sample-space shortcut without changing the tail constants.
The changed diagonal argument and deterministic support hypotheses are recorded in
`docs/renames/2026-10-F4-Sketching.json`.

The final locked area build `lake build NLAlib.Sketching` completed successfully in
`/tmp/m2-sketch-final.log` (4162 dependency jobs). `git diff --check` passed for these changes.

No new sorry, scaffold or axiom was added. Full-tree validation and atlas synchronization
remain coordinated by the root agent after compilation is restored.

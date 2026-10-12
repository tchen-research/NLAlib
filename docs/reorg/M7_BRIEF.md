# M7: placing files that arrived from `main` after the reorganisation

After the tree move, `main` merged codex's matrix-toolkit rounds (#21, #24): about 377 new files
directly under `NLAlib/Matrix/` and about 32 under new `NLAlib/ForMathlib/{Analysis,LinearAlgebra,
Algebra,Order,Logic,Data,Combinatorics}` paths. They must be placed into the topic tree with the
same rules as `docs/REORG_BRIEF.md` (read it first, including the layer rule and rule 1 about
aggregator names). Only files that are *not yet* inside a leaf directory need mapping:
`python3 scripts/reorg.py --check docs/reorg/mapping/M7-<part>.json` lists what is unmapped.

Destinations: `NLAlib/Matrix/{Basic,Norms,Spectral,Subspaces,Factorizations,Perturbation,
Inequalities,OperatorTheory,Functions,Structured,Calculus}` for the Matrix files;
ForMathlib files map to themselves (their new subdirectories are now allowed) unless they sit
directly in `NLAlib/ForMathlib/` (then into the matching area).

Hints from the file names (verify against the module docstrings): `Schatten*`, `KyFan*`,
`Majorization*`, `SchurHorn*`, `Hadamard*`, `Sylvester*` (inertia) → `Inequalities` or `Spectral`
as content dictates; `Eigenvalue*`, `SimpleEigenvalue*`, `Interlacing*`, `Normal*`,
`Singular*`, `Schur*` (triangularisation) → `Spectral`; `PrincipalAngle*`, `ObliqueProject*`,
`ComplexOblique*`, `DavisKahan*`, `Wedin*` → `Subspaces` (angles) or `Perturbation` (bounds);
`QR*`, `Pseudoinverse*`, `LeastSquares*` → `Factorizations` / `Basic`; `MatrixPower*`,
`Gershgorin*` → `Spectral` or `Perturbation`; `Simultaneous*` → `Spectral`. Group by family: a
family's files go to one leaf. Keep base names; record renames only for collisions.

Output: `docs/reorg/mapping/M7-<part>.json` with `"group": "M7"` and the usual `moves`,
`renames`, `notes`, `flags`. Do not move or edit any Lean file.

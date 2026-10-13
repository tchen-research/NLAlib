import NLAlib.Matrix.Subspaces.RangeProjector

/-!
# Complex column-range orthogonal projectors

The generic `columnSpace` and `rangeProjector` interfaces apply directly to complex
matrices, including dependent columns and empty shapes. The equality
`toEuclideanLin_symm_starProjection_eq_rangeProjector` identifies the transported
Hilbert projection with the Moore–Penrose construction; no second complex projector
or column-space definition is needed.
-/

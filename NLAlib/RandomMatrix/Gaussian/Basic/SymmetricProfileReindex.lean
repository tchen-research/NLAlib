import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Norms.SchattenEndpoints
import NLAlib.Matrix.Norms.SchattenContinuity
import NLAlib.Matrix.Measurability.SpectralMeasurable

/-!
# Reindexing the actual symmetric Gaussian profile law

An arbitrary coordinate permutation need not preserve the chosen lower
triangle. An explicit permutation of all independent Gaussian coordinates
preserves the lower/upper orientation while carrying each unordered pair
to its relabelled pair. This gives the actual reindexing law rather than
assuming invariance of the canonical sample construction.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

private def orientedPairMap {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (p : ι × ι) : κ × κ :=
  if p.2 ≤ p.1 then (max (e p.1) (e p.2), min (e p.1) (e p.2))
    else (min (e p.1) (e p.2), max (e p.1) (e p.2))

private theorem orientedPairMap_inverse {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (p : ι × ι) : orientedPairMap e.symm (orientedPairMap e p) = p := by
  rcases p with ⟨i, j⟩
  by_cases hij : j ≤ i
  · by_cases he : e i ≤ e j
    · simp [orientedPairMap, hij, he]
    · have he' : e j ≤ e i := le_of_not_ge he
      simp [orientedPairMap, hij, he']
  · have hij' : i < j := lt_of_not_ge hij
    have hne : e i ≠ e j := fun h => hij'.ne (e.injective h)
    by_cases he : e i ≤ e j
    · have he' : e i < e j := lt_of_le_of_ne he hne
      simp [orientedPairMap, hij, he'.not_ge, max_eq_right he, min_eq_left he,
        max_eq_right hij'.le, min_eq_left hij'.le]
    · have he' : e j < e i := lt_of_not_ge he
      simp [orientedPairMap, hij, he, max_eq_left he'.le, min_eq_right he'.le,
        max_eq_left hij'.le, min_eq_right hij'.le]

private def orientedPairEquiv {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) : (ι × ι) ≃ (κ × κ) where
  toFun := orientedPairMap e
  invFun := orientedPairMap e.symm
  left_inv := orientedPairMap_inverse e
  right_inv := orientedPairMap_inverse e.symm

/-- Relabel all independent Gaussian coordinates while preserving their
lower/upper orientation. This map realizes a simultaneous permutation of
the symmetric ensemble, including permutations that cross the diagonal. -/
def reindexSymmetricGaussianSample {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (G : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => G (orientedPairEquiv e (i, j)).1 (orientedPairEquiv e (i, j)).2

/-- The orientation-preserving coordinate relabelling carries the actual
standard Gaussian matrix law to the standard Gaussian matrix law. -/
theorem hasLaw_reindexSymmetricGaussianSample
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ] (e : ι ≃ κ) :
    HasLaw (reindexSymmetricGaussianSample e) (gaussianMatrix ι ι) (gaussianMatrix κ κ) := by
  apply hasLaw_gaussianMatrix_of_iIndepFun
  · intro ij
    exact (measurePreserving_gaussianMatrix_entry
      (orientedPairEquiv e ij).1 (orientedPairEquiv e ij).2).hasLaw
  · exact iIndepFun.precomp (orientedPairEquiv e).injective iIndepFun_gaussianMatrix_entry

/-- The sample relabelling intertwines the actual symmetric Gaussian
construction with simultaneous profile and output reindexing. -/
theorem symmetricGaussianMatrix_reindex_sample
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) (G : Matrix κ κ ℝ) :
    symmetricGaussianMatrix (b.submatrix e e) (reindexSymmetricGaussianSample e G) =
      (symmetricGaussianMatrix b G).submatrix e e := by
  ext i j
  by_cases hij : i ≤ j
  · simp [symmetricGaussianMatrix, reindexSymmetricGaussianSample, orientedPairEquiv,
      orientedPairMap, max_eq_right hij, min_eq_left hij, hb.apply, max_comm, min_comm]
    left
    by_cases he : e i ≤ e j
    · simp [max_eq_right he, min_eq_left he, hb.apply]
    · simp [max_eq_left (le_of_not_ge he), min_eq_right (le_of_not_ge he)]
  · have hij' : j ≤ i := le_of_not_ge hij
    simp [symmetricGaussianMatrix, reindexSymmetricGaussianSample, orientedPairEquiv,
      orientedPairMap, max_eq_left hij', min_eq_right hij']
    left
    by_cases he : e i ≤ e j
    · simp [max_eq_right he, min_eq_left he, hb.apply]
    · simp [max_eq_left (le_of_not_ge he), min_eq_right (le_of_not_ge he)]

/-- Simultaneous relabelling of a symmetric Gaussian profile has the same
actual law as relabelling the output matrix of the original ensemble. -/
theorem identDistrib_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) :
    IdentDistrib (fun G => (symmetricGaussianMatrix b G).submatrix e e)
      (symmetricGaussianMatrix (b.submatrix e e)) (gaussianMatrix κ κ) (gaussianMatrix ι ι) := by
  have hs := hasLaw_reindexSymmetricGaussianSample e
  have hi : IdentDistrib (reindexSymmetricGaussianSample e) id
      (gaussianMatrix κ κ) (gaussianMatrix ι ι) :=
    ⟨hs.aemeasurable, aemeasurable_id, by simpa only [Measure.map_id] using hs.map_eq⟩
  have h := hi.comp (measurable_symmetricGaussianMatrix (b.submatrix e e))
  simpa only [Function.comp_def, id_eq, symmetricGaussianMatrix_reindex_sample e b hb] using h

/-- Simultaneous finite reindexing preserves every native extended
Schatten norm, including the spectral infinity endpoint. -/
theorem schattenNorm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ κ ℝ) (e : κ ≃ ι) (p : ℝ≥0∞) :
    schattenNorm (A.reindex e e) p = schattenNorm A p := by
  by_cases hp : p = ⊤
  · simp only [hp, schattenNorm_top, specNorm_reindex]
  · rw [schattenNorm_eq_of_ne_top _ hp, schattenNorm_eq_of_ne_top _ hp,
      schattenNormReal_reindex]

/-- Expected native operator norms are unchanged by an arbitrary finite
simultaneous permutation of a symmetric Gaussian profile. -/
theorem integral_specNorm_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) :
    (∫ G, specNorm (symmetricGaussianMatrix (b.submatrix e e) G) ∂gaussianMatrix ι ι) =
      ∫ G, specNorm (symmetricGaussianMatrix b G) ∂gaussianMatrix κ κ := by
  have h := ((identDistrib_symmetricGaussianMatrix_submatrix e b hb).comp
    (measurable_specNorm_of_entries (fun i j => Matrix.measurable_entry i j))).integral_eq
  have hr (A : Matrix κ κ ℝ) : specNorm (A.submatrix e e) = specNorm A :=
    specNorm_reindex A e.symm e.symm
  simpa only [Function.comp_def, hr] using h.symm

/-- Reindexing a symmetric Gaussian profile preserves the actual law of
every native Schatten norm at exponent at least one, including infinity. -/
theorem identDistrib_schattenNorm_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    IdentDistrib (fun G => schattenNorm (symmetricGaussianMatrix b G) p)
      (fun G => schattenNorm (symmetricGaussianMatrix (b.submatrix e e) G) p)
        (gaussianMatrix κ κ) (gaussianMatrix ι ι) := by
  have hmeas : Measurable (fun A : Matrix ι ι ℝ => schattenNorm A p) := by
    by_cases hpt : p = ⊤
    · simp only [hpt, schattenNorm_top]
      exact measurable_specNorm_of_entries (fun i j => Matrix.measurable_entry i j)
    · have hpr : 0 < p.toReal := ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt
      simp only [schattenNorm_eq_of_ne_top _ hpt]
      exact (continuous_schattenNormReal hpr).measurable
  have h := (identDistrib_symmetricGaussianMatrix_submatrix e b hb).comp hmeas
  have hr (A : Matrix κ κ ℝ) : schattenNorm (A.submatrix e e) p = schattenNorm A p :=
    schattenNorm_reindex A e.symm p
  simpa only [Function.comp_def, hr] using h

/-- Expected native Schatten norms are invariant under simultaneous
permutations of the Gaussian coefficient profile, at all finite exponents
at least one and at the infinity endpoint. -/
theorem integral_schattenNorm_symmetricGaussianMatrix_submatrix
    {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (b : Matrix κ κ ℝ) (hb : b.IsSymm) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (∫ G, schattenNorm (symmetricGaussianMatrix (b.submatrix e e) G) p ∂gaussianMatrix ι ι) =
      ∫ G, schattenNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix κ κ :=
  (identDistrib_schattenNorm_symmetricGaussianMatrix_submatrix e b hb p hp).integral_eq.symm

end NLAlib

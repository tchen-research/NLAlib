import NLAlib.Matrix.Spectral.CStarRectangularDilationComparison
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # A genuine positive-gap row linearization of shifted Gram matrices

The extra deterministic square-root block produces the exact shifted
Gram matrix and a proved positive spectral gap. Its construction is
native to arbitrary C*-matrix algebras, so it applies to continuous free
spectra as well as ordinary complex matrices.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {n A : Type*} [Fintype n] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The literal row `[X,Q]` of two native square matrices. -/
def rowPair (X Q : CStarMatrix n n A) : Matrix n (n ⊕ n) A :=
  fun i => Sum.elim (X i) (Q i)

omit [DecidableEq n] [PartialOrder A] [StarOrderedRing A] in
/-- The actual Gram matrix of the concatenated row is the sum of the two
native Gram matrices; no scalar-entry commutativity is used. -/
theorem rowPair_gram (X Q : CStarMatrix n n A) :
    ofMatrix (rowPair X Q * (rowPair X Q)ᴴ) = X * star X + Q * star Q := by
  ext i j
  simp [rowPair, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    CStarMatrix.mul_apply, CStarMatrix.star_apply]

/-- The actual deterministic square-root row used by the quadratic
Gaussian spectral comparison. The same row is defined for all inputs. -/
def positiveGramRow (X B : CStarMatrix n n A) (b δ : ℝ) : Matrix n (n ⊕ n) A :=
  rowPair X (CFC.sqrt (B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)))

/-- A self-adjoint native matrix becomes positive after a real scalar
shift dominating its actual norm. Empty shapes are included. -/
theorem nonneg_add_algebraMap_of_norm_le (B : CStarMatrix n n A)
    (hB : IsSelfAdjoint B) {b : ℝ} (hb : ‖B‖ ≤ b) :
    0 ≤ B + algebraMap ℝ (CStarMatrix n n A) b := by
  have hlow : algebraMap ℝ (CStarMatrix n n A) (-b) ≤ B := by
    apply (algebraMap_le_iff_le_spectrum hB).mpr
    intro r hr
    have hn := spectrum.norm_le_norm_mul_of_mem hr
    have hunit : ‖(1 : CStarMatrix n n A)‖ ≤ 1 := by
      have hsq := CStarRing.norm_self_mul_star (x := (1 : CStarMatrix n n A))
      simp only [star_one, one_mul] at hsq
      nlinarith [norm_nonneg (1 : CStarMatrix n n A)]
    have hnorm : ‖r‖ ≤ ‖B‖ := hn.trans (by nlinarith [norm_nonneg B])
    rw [Real.norm_eq_abs] at hnorm
    have := (abs_le.mp hnorm).1
    linarith
  have := sub_nonneg.mpr hlow
  simpa only [map_neg, sub_neg_eq_add] using this

/-- The actual square-root row has exactly the intended scalar-shifted
Gram matrix. -/
theorem positiveGramRow_gram (X B : CStarMatrix n n A) (hB : IsSelfAdjoint B)
    {b : ℝ} (hb : ‖B‖ ≤ b) (δ : ℝ) :
    ofMatrix (positiveGramRow X B b δ * (positiveGramRow X B b δ)ᴴ) =
      X * star X + B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2) := by
  have hbase := nonneg_add_algebraMap_of_norm_le B hB hb
  have hδ : 0 ≤ algebraMap ℝ (CStarMatrix n n A) (4 * δ ^ 2) :=
    map_nonneg (StarAlgHom.ofId ℝ (CStarMatrix n n A)) (by positivity)
  have hq : 0 ≤ B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2) := by
    simpa only [map_add, add_assoc] using add_nonneg hbase hδ
  have hsqstar := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg
    (B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)))).star_eq
  unfold positiveGramRow
  rw [rowPair_gram, hsqstar, CFC.sqrt_mul_sqrt_self _ hq]
  simp only [add_assoc]

/-- The constructed row has the genuine positive spectral gap `4δ²`.
The gap is derived from its actual Gram identity and the norm bound on
`B`, rather than assumed as a linearization certificate. -/
theorem le_spectrum_positiveGramRow_gram (X B : CStarMatrix n n A)
    (hB : IsSelfAdjoint B) {b : ℝ} (hb : ‖B‖ ≤ b) (δ : ℝ)
    {r : ℝ} (hr : r ∈ spectrum ℝ
      (ofMatrix (positiveGramRow X B b δ * (positiveGramRow X B b δ)ᴴ))) :
    4 * δ ^ 2 ≤ r := by
  have hbase := nonneg_add_algebraMap_of_norm_le B hB hb
  have hgram : algebraMap ℝ (CStarMatrix n n A) (4 * δ ^ 2) ≤
      X * star X + B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2) := by
    rw [map_add, ← add_assoc]
    have hn : 0 ≤ X * star X + B + algebraMap ℝ (CStarMatrix n n A) b := by
      simpa only [add_assoc] using add_nonneg (mul_star_self_nonneg X) hbase
    simpa only [zero_add] using add_le_add hn
      (le_refl (algebraMap ℝ (CStarMatrix n n A) (4 * δ ^ 2)))
  rw [positiveGramRow_gram X B hB hb δ] at hr
  exact (algebraMap_le_iff_le_spectrum
    ((IsSelfAdjoint.mul_star_self X).add hB |>.add ((IsSelfAdjoint.all _).algebraMap (CStarMatrix n n A)))).mp hgram r hr

variable [Nonempty n] [Nontrivial A]

/-- The reference row-Gram radius is controlled by the actual reference
matrix norm, the deterministic shift budget, and the chosen gap. -/
theorem sqrt_norm_positiveGramRow_gram_le
    (X B : CStarMatrix n n A) (hB : IsSelfAdjoint B)
    {b δ : ℝ} (hb : ‖B‖ ≤ b) (hδ : 0 ≤ δ) :
    Real.sqrt ‖ofMatrix (positiveGramRow X B b δ * (positiveGramRow X B b δ)ᴴ)‖ ≤
      ‖X‖ + 2 * Real.sqrt b + 2 * δ := by
  have hb0 : 0 ≤ b := (norm_nonneg B).trans hb
  rw [positiveGramRow_gram X B hB hb δ]
  have hnorm : ‖X * star X + B + algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)‖ ≤
      ‖X‖ ^ 2 + 2 * b + 4 * δ ^ 2 := by
    calc
      _ ≤ ‖X * star X + B‖ + ‖algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)‖ := norm_add_le _ _
      _ ≤ (‖X * star X‖ + ‖B‖) + ‖algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖X‖ ^ 2 + 2 * b + 4 * δ ^ 2 := by
        rw [CStarRing.norm_self_mul_star, norm_algebraMap', Real.norm_of_nonneg (by positivity)]
        nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt hb0
  have hs0 := Real.sqrt_nonneg b
  nlinarith [mul_nonneg (norm_nonneg X) hs0, mul_nonneg (norm_nonneg X) hδ,
    mul_nonneg hs0 hδ]


variable {BAlg : Type*} [CStarAlgebra BAlg] [PartialOrder BAlg] [StarOrderedRing BAlg]
  [Nontrivial BAlg]

/-- The constructed positive square-root row turns a true Hermitian
linearized spectral comparison into the actual shifted quadratic spectral
comparison, with no finite-spectrum assumption and no spurious zero match.
Source: arXiv:2406.11453v2, Section 5.3.
atlas: gaussian-quadratic-free-spectrum (partial). -/
theorem hausdorffDist_spectrum_shiftedGram_le_of_positiveGramRow
    (X BA : CStarMatrix n n A) (Z BB : CStarMatrix n n BAlg)
    (hBA : IsSelfAdjoint BA) (hBB : IsSelfAdjoint BB)
    {b δ : ℝ} (hBA_norm : ‖BA‖ ≤ b) (hBB_norm : ‖BB‖ ≤ b) (hδ : 0 < δ)
    (hd : Metric.hausdorffDist
      (spectrum ℝ (rectangularDilation (positiveGramRow X BA b δ)))
      (spectrum ℝ (rectangularDilation (positiveGramRow Z BB b δ))) ≤ δ) :
    Metric.hausdorffDist (spectrum ℝ (X * star X + BA))
      (spectrum ℝ (Z * star Z + BB)) ≤
        4 * (‖Z‖ + Real.sqrt b) * δ + 5 * δ ^ 2 := by
  have hs := hausdorffDist_spectrum_rowGram_le_of_dilation_gap
    (positiveGramRow X BA b δ) (positiveGramRow Z BB b δ) hδ
    (fun _ hr => le_spectrum_positiveGramRow_gram X BA hBA hBA_norm δ hr)
    (fun _ hr => le_spectrum_positiveGramRow_gram Z BB hBB hBB_norm δ hr) hd
  rw [positiveGramRow_gram X BA hBA hBA_norm δ,
    positiveGramRow_gram Z BB hBB hBB_norm δ] at hs
  have hshiftA : spectrum ℝ (X * star X + BA +
      algebraMap ℝ (CStarMatrix n n A) (b + 4 * δ ^ 2)) =
      (fun r : ℝ => r + (b + 4 * δ ^ 2)) '' spectrum ℝ (X * star X + BA) := by
    rw [← spectrum.add_singleton_eq, Set.add_singleton]
  have hshiftB : spectrum ℝ (Z * star Z + BB +
      algebraMap ℝ (CStarMatrix n n BAlg) (b + 4 * δ ^ 2)) =
      (fun r : ℝ => r + (b + 4 * δ ^ 2)) '' spectrum ℝ (Z * star Z + BB) := by
    rw [← spectrum.add_singleton_eq, Set.add_singleton]
  rw [hshiftA, hshiftB] at hs
  have hiso : Isometry (fun r : ℝ => r + (b + 4 * δ ^ 2)) :=
    Isometry.of_dist_eq fun x y => by simp only [Real.dist_eq, add_sub_add_right_eq_sub]
  rw [Metric.hausdorffDist_image hiso] at hs
  have hrad := sqrt_norm_positiveGramRow_gram_le Z BB hBB hBB_norm hδ.le
  rw [positiveGramRow_gram Z BB hBB hBB_norm δ] at hrad
  have hrad' := mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2 * δ by positivity)
  nlinarith [mul_nonneg (norm_nonneg Z) hδ.le]

end CStarMatrix

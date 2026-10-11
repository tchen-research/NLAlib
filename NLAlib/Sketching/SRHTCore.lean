import NLAlib.Sketching.SRHTFlattening
import NLAlib.ForMathlib.Probability.UniformSamplingCoupling
import NLAlib.Matrix.RealComplexNorm
import NLAlib.Concentration.Matrix.SamplingSpectralBounds
import Mathlib.Data.Finset.Sort

/-!
# The literal classical SRHT sketch and its Gram matrix

Uniform exact-size row sets are enumerated in increasing order, giving the
actual `√(n/k) R H D` matrix. Source: `sh:srht-ose`, atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

/-- The literal selector of the distinct rows, in increasing order.
Source: operator re-derivation `sh:srht-ose`. -/
def srhtRowSelector {n k : ℕ} (T : ExactRowSubset (Fin n) k) :
    Matrix (Fin k) (Fin n) ℝ :=
  fun a j => if j = T.val.orderEmbOfFin T.prop a then 1 else 0

/-- The actual classical SRHT matrix with one shared sign diagonal.
Source: operator re-derivation `sh:srht-ose`. -/
def srhtSketch {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → Bool) (T : ExactRowSubset (Fin n) k) : Matrix (Fin k) (Fin n) ℝ :=
  Real.sqrt ((n : ℝ) / k) •
    (srhtRowSelector T * H * Matrix.diagonal (fun i => rademacherBoolSign (ξ i)))

/-- The literal selector picks the requested row.
Source: `sh:srht-ose`; no sampling law is required for this algebraic identity. -/
theorem srhtRowSelector_mul {n k d : ℕ} (T : ExactRowSubset (Fin n) k)
    (V : Matrix (Fin n) (Fin d) ℝ) (a : Fin k) (b : Fin d) :
    (srhtRowSelector T * V) a b = V (T.val.orderEmbOfFin T.prop a) b := by
  simp [srhtRowSelector, Matrix.mul_apply, ite_mul]

/-- The actual sketch's action on a frame is the rescaled selected row of
the one-diagonal transformed frame. Source: `sh:srht-ose`. -/
theorem srhtSketch_mul_apply {n k d : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ) (ξ : Fin n → Bool)
    (T : ExactRowSubset (Fin n) k) (a : Fin k) (b : Fin d) :
    (srhtSketch H ξ T * U) a b = Real.sqrt ((n : ℝ) / k) *
      srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop a) b := by
  simp only [srhtSketch, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_assoc, srhtSignedFrame]
  rw [srhtRowSelector_mul]

/-- Summing the literal distinct selected labels is summing the subset.
Source: the increasing row enumeration; supports `sh:srht-ose`. -/
theorem sum_srhtRowEnumeration {n k : ℕ} (T : ExactRowSubset (Fin n) k)
    {E : Type*} [AddCommMonoid E] (f : Fin n → E) :
    (∑ a : Fin k, f (T.val.orderEmbOfFin T.prop a)) = ∑ j ∈ T.val, f j := by
  calc
    _ = ∑ j ∈ Finset.univ.map (T.val.orderEmbOfFin T.prop).toEmbedding, f j :=
      (Finset.sum_map _ _ _).symm
    _ = _ := by rw [T.val.map_orderEmbOfFin_univ T.prop]

/-- The literal sampled Gram matrix is the uniform distinct-row average.
Source: operator re-derivation `sh:srht-ose`. -/
theorem transpose_srhtSketch_mul_self {n k d : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ) (ξ : Fin n → Bool)
    (T : ExactRowSubset (Fin n) k) :
    (srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) =
      ((n : ℝ) / k) • ∑ j ∈ T.val,
        Matrix.vecMulVec (srhtSignedFrame H U ξ j) (srhtSignedFrame H U ξ j) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  simp_rw [srhtSketch_mul_apply]
  have hm (j : Fin k) :
      (Real.sqrt ((n : ℝ) / k) * srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) a) *
      (Real.sqrt ((n : ℝ) / k) * srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) b) =
      ((n : ℝ) / k) * (srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) a *
        srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) b) := by
    calc
      _ = Real.sqrt ((n : ℝ) / k) ^ 2 *
          (srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) a *
            srhtSignedFrame H U ξ (T.val.orderEmbOfFin T.prop j) b) := by ring
      _ = _ := by rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) / k by positivity)]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ => ((n : ℝ) / k) * z)
    (sum_srhtRowEnumeration T (fun j => srhtSignedFrame H U ξ j a * srhtSignedFrame H U ξ j b))

/-- The actual complex rank-one Chernoff population induced by a real frame.
Source: `sh:srht-ose`, with `A_j=n v_j v_jᵀ`. -/
def srhtPopulationAtom {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) :
    Matrix (Fin d) (Fin d) ℂ :=
  (n : ℝ) • Matrix.vecMulVec (star fun a => (V j a : ℂ)) (fun a => (V j a : ℂ))

/-- Every actual population atom is positive semidefinite.
Source: `sh:srht-ose`, genuine rank-one PSD property. -/
theorem srhtPopulationAtom_posSemidef {n d : ℕ}
    (V : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) : (srhtPopulationAtom V j).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_star_self (fun a => (V j a : ℂ))).smul (Nat.cast_nonneg n)

/-- Its trace is exactly the normalized squared row norm.
Source: `sh:srht-ose`, genuine eigenvalue-bound input from flattening. -/
theorem trace_srhtPopulationAtom {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℝ) (j : Fin n) :
    (srhtPopulationAtom V j).trace.re = (n : ℝ) * (V j ⬝ᵥ V j) := by
  change (∑ a, ((n : ℝ) • (star (V j a : ℂ) * (V j a : ℂ)))).re =
    (n : ℝ) * ∑ a, V j a * V j a
  simp only [Complex.re_sum, Complex.smul_re, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re, smul_eq_mul, Finset.mul_sum]

/-- The actual uniform population has mean identity when its frame is
orthonormal. Source: `sh:srht-ose`, no assumed isotropy certificate. -/
theorem mean_srhtPopulationAtom {n d : ℕ} [NeZero n]
    (V : Matrix (Fin n) (Fin d) ℝ) (hV : HasOrthonormalCols V) :
    (1 / (Fintype.card (Fin n) : ℝ)) • ∑ j, srhtPopulationAtom V j = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have he := hV
  change Vᵀ * V = 1 at he
  ext a b
  have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) he
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hab
  simp only [srhtPopulationAtom, Fintype.card_fin, ← Finset.smul_sum,
    smul_smul, one_div_mul_cancel hn, one_smul, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [hab]
  by_cases h : a = b <;> simp [Matrix.one_apply, h]

/-- The complex Chernoff empirical mean is precisely the complex extension
of the actual real sketch Gram matrix. Source: `sh:srht-ose`. -/
theorem map_ofReal_srhtSketch_gram {n k d : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin d) ℝ) (ξ : Fin n → Bool)
    (T : ExactRowSubset (Fin n) k) :
    ((srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U)).map Complex.ofReal =
      (1 / (k : ℝ)) • ∑ j ∈ T.val, srhtPopulationAtom (srhtSignedFrame H U ξ) j := by
  rw [transpose_srhtSketch_mul_self]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, srhtPopulationAtom,
    Matrix.vecMulVec_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sum,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.real_smul,
    ← Finset.mul_sum, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- Selecting all rows gives the exact input isometry after the actual
shared sign diagonal and orthogonal transform. Source: `sh:srht-ose`, the
full-row branch of the capped row prescription. -/
theorem transpose_srhtSketch_full_rows_mul_self {n d : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ * H = 1)
    (U : Matrix (Fin n) (Fin d) ℝ) (hU : HasOrthonormalCols U)
    (ξ : Fin n → Bool) (T : ExactRowSubset (Fin n) n) :
    (srhtSketch H ξ T * U)ᵀ * (srhtSketch H ξ T * U) = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hT : T.val = Finset.univ := Finset.eq_univ_of_card T.val (by simpa using T.prop)
  rw [transpose_srhtSketch_mul_self, hT, div_self hn, one_smul]
  calc
    _ = (srhtSignedFrame H U ξ)ᵀ * srhtSignedFrame H U ξ := by
      ext a b
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply]
    _ = 1 := hasOrthonormalCols_srhtSignedFrame H hH U hU ξ

end NLAlib

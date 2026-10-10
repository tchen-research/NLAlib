import NLAlib.Matrix.Spectral
import Mathlib.Analysis.Matrix.PosDef

/-!
# A deterministic quadratic probe for the spectral norm

A positive semidefinite matrix has a unit top eigenvector. Its quadratic
form dominates the rank-one quadratic form of that vector times the
spectral norm. This is the deterministic input to the Gaussian
quadratic-probe proof of inverse spectral moments; the vector is selected
for one fixed matrix, so no measurable eigenvector selection is involved.

Source: `Re-derivations/operator_rederivations.tex`, master inverse spectral
moment. Atlas: `inverse-wishart-spectral-moment` (helper).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- The spectral norm of a real symmetric matrix is the supremum norm of
its eigenvalue list. Source: Mathlib's spectral theorem and unitary norm
invariance. Atlas: `inverse-wishart-spectral-moment` (helper).
atlas: quadratic-probe-spectral-detection -/
theorem specNorm_eq_norm_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : specNorm A = ‖hA.eigenvalues‖ := by
  unfold specNorm
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  rfl

/-- The spectral norm of a positive semidefinite matrix is bounded by
its trace. Source: nonnegative eigenvalues and the spectral theorem;
atlas `norms-frob-spec` (helper). -/
theorem specNorm_le_trace_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : specNorm A ≤ Matrix.trace A := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    have hzero : A = 0 := Subsingleton.elim _ _
    simp [hzero, specNorm, Matrix.trace]
  | inr hi =>
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.isHermitian.eigenvalues).1
    dsimp only at hi
    rw [specNorm_eq_norm_eigenvalues hA.isHermitian, ← hi,
      Real.norm_of_nonneg (hA.eigenvalues_nonneg i), hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A positive semidefinite real matrix has a unit eigenvector with
eigenvalue equal to its spectral norm. Source: finite-dimensional spectral
theorem. Atlas: `inverse-wishart-spectral-moment` (helper).
atlas: quadratic-probe-spectral-detection -/
theorem exists_unit_mulVec_eq_specNorm_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ v : ι → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = specNorm A • v := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.isHermitian.eigenvalues).1
  dsimp only at hi
  have heig : hA.isHermitian.eigenvalues i = specNorm A := by
    rw [specNorm_eq_norm_eigenvalues hA.isHermitian, ← hi,
      Real.norm_of_nonneg (hA.eigenvalues_nonneg i)]
  let v : ι → ℝ := (hA.isHermitian.eigenvectorBasis i).ofLp
  have hv : v ⬝ᵥ v = 1 := by
    have hn := hA.isHermitian.eigenvectorBasis.orthonormal.1 i
    have hs := congrArg (fun t : ℝ => t ^ 2) hn
    rw [norm_eq_sqrt_dotProduct, Real.sq_sqrt (dotProduct_self_nonneg _), one_pow] at hs
    exact hs
  refine ⟨v, hv, ?_⟩
  simpa only [heig] using hA.isHermitian.mulVec_eigenvectorBasis i

/-- The quadratic form of a positive semidefinite matrix dominates a
unit rank-one probe scaled by its spectral norm. Source: direct
quadratic-probe proof; expand positivity at `z - (v ⋅ z) v` for a top
eigenvector. Atlas: `inverse-wishart-spectral-moment` (helper).
atlas: quadratic-probe-spectral-detection -/
theorem exists_unit_specNorm_mul_dotProduct_sq_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ v : ι → ℝ, v ⬝ᵥ v = 1 ∧
      ∀ z : ι → ℝ, specNorm A * (v ⬝ᵥ z) ^ 2 ≤ z ⬝ᵥ (A *ᵥ z) := by
  obtain ⟨v, hv, heig⟩ := exists_unit_mulVec_eq_specNorm_smul hA
  refine ⟨v, hv, fun z => ?_⟩
  have hsym : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have hvAz : v ⬝ᵥ (A *ᵥ z) = specNorm A * (v ⬝ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, heig,
      smul_dotProduct, smul_eq_mul]
  have hzAv : z ⬝ᵥ (A *ᵥ v) = specNorm A * (v ⬝ᵥ z) := by
    rw [heig, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hvAv : v ⬝ᵥ (A *ᵥ v) = specNorm A := by
    rw [heig, dotProduct_smul, smul_eq_mul, hv, mul_one]
  have hpos := hA.dotProduct_mulVec_nonneg (z - (v ⬝ᵥ z) • v)
  simp only [star_trivial] at hpos
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, dotProduct_smul, smul_eq_mul, hvAz, hzAv, hvAv] at hpos
  simp only [smul_eq_mul] at hpos
  nlinarith

end NLAlib

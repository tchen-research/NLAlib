import NLAlib.Matrix.Functions.LyapunovReal

/-! # The kernel and rank of an actual real controllability Gramian -/
noncomputable section
open Polynomial MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]

omit [DecidableEq s] in
/-- A controllability Gramian's kernel is exactly the finite unobservable
space. The finite cutoff `j < card n` is proved sufficient by Cayley–Hamilton.
Source: user derivations, equation (G2).
atlas: lyapunov-stability-gramian (partial) -/
theorem realLyapunovGramian_mulVec_eq_zero_iff (A : Matrix n n ℝ) (B : Matrix n s ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) (v : n → ℝ) :
    realLyapunovGramian A (B * Bᴴ) *ᵥ v = 0 ↔
      ∀ j < Fintype.card n, Bᴴ *ᵥ ((Aᴴ) ^ j *ᵥ v) = 0 := by
  let G := realLyapunovGramian A (B * Bᴴ)
  have hX : G.PosSemidef := posSemidef_realLyapunovGramian A _ hA (Matrix.posSemidef_self_mul_conjTranspose B)
  have heq : A * G + G * Aᴴ + B * Bᴴ = 0 := (realLyapunovGramian_equation_unique A _ hA).1
  constructor
  · intro hv
    change G *ᵥ v = 0 at hv
    have hker (j : ℕ) : G *ᵥ ((Aᴴ) ^ j *ᵥ v) = 0 := by
      induction j with
      | zero => simpa only [pow_zero, Matrix.one_mulVec] using hv
      | succ j hj =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact (kernel_lyapunov_invariant A B G hX heq _ hj).2
    intro j _
    exact (kernel_lyapunov_invariant A B G hX heq _ (hker j)).1
  · intro hv
    have hall := mulVec_pow_zero_of_lt_card Aᴴ Bᴴ v hv
    have he (t : ℝ) : Bᴴ *ᵥ ((matrixExp (t • A))ᴴ *ᵥ v) = 0 := by
      have hstar : (matrixExp (t • A))ᴴ = matrixExp (t • Aᴴ) := by
        change star (NormedSpace.exp (t • A)) = NormedSpace.exp (t • star A)
        rw [NormedSpace.star_exp, star_smul, star_trivial]
      rw [hstar]
      exact mulVec_matrixExp_zero_of_pow_zero Aᴴ Bᴴ v hall t
    let F : Matrix n n ℝ →ₗ[ℝ] n → ℝ := (LinearMap.applyₗ v).comp Matrix.toLin'.toLinearMap
    have hi := F.toContinuousLinearMap.integral_comp_comm (integrableOn_realLyapunovIntegrand A (B * Bᴴ) hA)
    change (∫ t in Ioi (0 : ℝ), realLyapunovIntegrand A (B * Bᴴ) t *ᵥ v) =
      realLyapunovGramian A (B * Bᴴ) *ᵥ v at hi
    rw [← hi]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun t => by
      change realLyapunovIntegrand A (B * Bᴴ) t *ᵥ v = 0
      simp only [realLyapunovIntegrand, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_zero]

/-- The Gramian rank equals the controllable dimension, with no low-rank
conclusion inferred merely from the forcing rank. Source: user derivations,
equation (G2).
atlas: lyapunov-stability-gramian (partial) -/
theorem rank_realLyapunovGramian_eq_rank_controllabilityMatrix (A : Matrix n n ℝ)
    (B : Matrix n s ℝ) (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ)) :
    (realLyapunovGramian A (B * Bᴴ)).rank = (controllabilityMatrix A B).rank := by
  have hker : LinearMap.ker (realLyapunovGramian A (B * Bᴴ)).mulVecLin =
      LinearMap.ker (controllabilityMatrix A B)ᴴ.mulVecLin := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, realLyapunovGramian_mulVec_eq_zero_iff A B hA]
    constructor
    · intro h
      ext j
      have hj := h j.1 j.1.isLt
      have he : ((controllabilityMatrix A B)ᴴ *ᵥ v) j =
          (Bᴴ *ᵥ ((Aᴴ) ^ (j.1 : ℕ) *ᵥ v)) j.2 := by
        change (((A ^ (j.1 : ℕ) * B)ᴴ) *ᵥ v) j.2 = _
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, ← Matrix.mulVec_mulVec]
      rw [he, hj]
      rfl
    · intro h j hj
      ext a
      change (Bᴴ *ᵥ ((Aᴴ) ^ j *ᵥ v)) a = 0
      have he := congrFun h (⟨j, hj⟩, a)
      change (((A ^ j * B)ᴴ) *ᵥ v) a = 0 at he
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, ← Matrix.mulVec_mulVec] using he
  have h₁ := (realLyapunovGramian A (B * Bᴴ)).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (controllabilityMatrix A B)ᴴ.mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at h₁
  change (realLyapunovGramian A (B * Bᴴ)).rank + _ = _ at h₁
  change (controllabilityMatrix A B)ᴴ.rank + _ = _ at h₂
  rw [Matrix.rank_conjTranspose] at h₂
  omega

end NLAlib

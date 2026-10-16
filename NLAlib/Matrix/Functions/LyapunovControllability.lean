import NLAlib.Matrix.Functions.LyapunovIntegral
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The kernel and rank of a continuous controllability Gramian

The finite power cutoff is the ambient dimension, justified by actual
Cayley–Hamilton reduction. The exponential series and improper integral
then identify precisely the unobservable vectors.
-/

noncomputable section
open Polynomial MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]

omit [Fintype s] [DecidableEq s] in
/-- Cayley–Hamilton reduces finite-dimensional annihilation to powers below the dimension. -/
theorem mulVec_pow_zero_of_lt_card {K : Type*} [RCLike K] (A : Matrix n n K) (L : Matrix s n K)
    (v : n → K) (h : ∀ j < Fintype.card n, L *ᵥ (A ^ j *ᵥ v) = 0) (j : ℕ) :
    L *ᵥ (A ^ j *ᵥ v) = 0 := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn => ext i; simp [Matrix.mulVec, dotProduct]
  | inr hn =>
    let p : K[X] := (X ^ j) %ₘ A.charpoly
    have hchar : A.charpoly ≠ 1 := by
      intro hc
      have hd := congrArg Polynomial.natDegree hc
      rw [Matrix.charpoly_natDegree_eq_dim, natDegree_one] at hd
      exact (Fintype.card_pos.ne' hd)
    have hp : p.natDegree < Fintype.card n := by
      simpa only [Matrix.charpoly_natDegree_eq_dim] using natDegree_modByMonic_lt (X ^ j) A.charpoly_monic hchar
    rw [Matrix.pow_eq_aeval_mod_charpoly]
    change L *ᵥ (aeval A p *ᵥ v) = 0
    rw [aeval_eq_sum_range' hp, Matrix.sum_mulVec, Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, h i (Finset.mem_range.mp hi), smul_zero]

omit [Fintype s] [DecidableEq s] in
/-- Annihilation of every power annihilates the actual exponential series. -/
theorem mulVec_matrixExp_zero_of_pow_zero {K : Type*} [RCLike K] (A : Matrix n n K) (L : Matrix s n K)
    (v : n → K) (h : ∀ j : ℕ, L *ᵥ (A ^ j *ᵥ v) = 0) (t : ℝ) :
    L *ᵥ (matrixExp (t • A) *ᵥ v) = 0 := by
  let F : Matrix n n K →ₗ[K] s → K :=
    L.mulVecLin.comp ((LinearMap.applyₗ v).comp Matrix.toLin'.toLinearMap)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := K) (t • A)).map
    F.toContinuousLinearMap F.toContinuousLinearMap.continuous
  have hz : (F.toContinuousLinearMap ∘ fun j : ℕ => (((j.factorial : K)⁻¹) • (t • A) ^ j)) = 0 := by
    funext j
    change F (((j.factorial : K)⁻¹) • (t • A) ^ j) = 0
    change L *ᵥ ((((j.factorial : K)⁻¹) • (t • A) ^ j) *ᵥ v) = 0
    rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h j, smul_zero, smul_zero]
  change HasSum _ (L *ᵥ (matrixExp (t • A) *ᵥ v)) at hs
  rw [hz] at hs
  exact hs.unique hasSum_zero

omit [DecidableEq n] [DecidableEq s] in
/-- The kernel of a PSD Lyapunov solution is invariant and unobserved by the forcing factor. -/
theorem kernel_lyapunov_invariant {K : Type*} [RCLike K] (A : Matrix n n K) (B : Matrix n s K)
    (X : Matrix n n K) (hX : X.PosSemidef) (heq : A * X + X * Aᴴ + B * Bᴴ = 0)
    (v : n → K) (hv : X *ᵥ v = 0) : Bᴴ *ᵥ v = 0 ∧ X *ᵥ (Aᴴ *ᵥ v) = 0 := by
  have hrow : star v ᵥ* X = 0 := by
    have h := Matrix.star_mulVec X v
    rw [hv, star_zero, hX.isHermitian.eq] at h
    exact h.symm
  have hq := congrArg (fun M : Matrix n n K => star v ⬝ᵥ (M *ᵥ v)) heq
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.zero_mulVec,
    dotProduct_zero] at hq
  have h₁ : star v ⬝ᵥ ((A * X) *ᵥ v) = 0 := by rw [← Matrix.mulVec_mulVec, hv]; simp
  have h₂ : star v ⬝ᵥ ((X * Aᴴ) *ᵥ v) = 0 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hrow]
    simp
  rw [h₁, h₂, zero_add, zero_add] at hq
  have hBB : (B * Bᴴ) *ᵥ v = 0 :=
    ((Matrix.posSemidef_self_mul_conjTranspose B).dotProduct_mulVec_zero_iff v).mp hq
  have hB : Bᴴ *ᵥ v = 0 := (Matrix.self_mul_conjTranspose_mulVec_eq_zero B v).mp hBB
  refine ⟨hB, ?_⟩
  have he := congrArg (fun M : Matrix n n K => M *ᵥ v) heq
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv, hB, Matrix.mulVec_zero,
    Matrix.zero_mulVec, zero_add, add_zero] at he
  exact he

omit [DecidableEq s] in
/-- A controllability Gramian's kernel is exactly the finite unobservable
space. The finite cutoff `j < card n` is proved sufficient by Cayley–Hamilton.
Source: user derivations, equation (G2).
atlas: lyapunov-stability-gramian (partial) -/
theorem lyapunovGramian_mulVec_eq_zero_iff (A : Matrix n n ℂ) (B : Matrix n s ℂ)
    (hA : IsHurwitz A) (v : n → ℂ) :
    lyapunovGramian A (B * Bᴴ) *ᵥ v = 0 ↔
      ∀ j < Fintype.card n, Bᴴ *ᵥ ((Aᴴ) ^ j *ᵥ v) = 0 := by
  let G := lyapunovGramian A (B * Bᴴ)
  have hX : G.PosSemidef := posSemidef_lyapunovGramian A _ hA (Matrix.posSemidef_self_mul_conjTranspose B)
  have heq : A * G + G * Aᴴ + B * Bᴴ = 0 := by
    change A * lyapunovGramian A (B * Bᴴ) + lyapunovGramian A (B * Bᴴ) * Aᴴ + B * Bᴴ = 0
    rw [lyapunovGramian_eq_of_solution A _ _ hA (lyapunovCayleySolution_equation A _ hA)]
    exact lyapunovCayleySolution_equation A _ hA
  constructor
  · intro hv
    have hker (j : ℕ) : G *ᵥ ((Aᴴ) ^ j *ᵥ v) = 0 := by
      induction j with
      | zero => simpa using hv
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
    let F : Matrix n n ℂ →ₗ[ℂ] n → ℂ := (LinearMap.applyₗ v).comp Matrix.toLin'.toLinearMap
    have hi := F.toContinuousLinearMap.integral_comp_comm (integrableOn_lyapunovIntegrand A (B * Bᴴ) hA)
    change (∫ t in Ioi (0 : ℝ), lyapunovIntegrand A (B * Bᴴ) t *ᵥ v) =
      lyapunovGramian A (B * Bᴴ) *ᵥ v at hi
    rw [← hi]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun t => by
      change lyapunovIntegrand A (B * Bᴴ) t *ᵥ v = 0
      simp only [lyapunovIntegrand, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_zero]

/-- The actual finite controllability matrix, ordered by power and input index. -/
def controllabilityMatrix {K : Type*} [RCLike K] (A : Matrix n n K) (B : Matrix n s K) :
    Matrix n (Fin (Fintype.card n) × s) K := fun i j => (A ^ (j.1 : ℕ) * B) i j.2

/-- The Gramian rank equals the controllable dimension, with no low-rank
conclusion inferred merely from the forcing rank. Source: user derivations,
equation (G2).
atlas: lyapunov-stability-gramian (partial) -/
theorem rank_lyapunovGramian_eq_rank_controllabilityMatrix (A : Matrix n n ℂ)
    (B : Matrix n s ℂ) (hA : IsHurwitz A) :
    (lyapunovGramian A (B * Bᴴ)).rank = (controllabilityMatrix A B).rank := by
  have hker : LinearMap.ker (lyapunovGramian A (B * Bᴴ)).mulVecLin =
      LinearMap.ker (controllabilityMatrix A B)ᴴ.mulVecLin := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, lyapunovGramian_mulVec_eq_zero_iff A B hA]
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
  have h₁ := (lyapunovGramian A (B * Bᴴ)).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (controllabilityMatrix A B)ᴴ.mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at h₁
  change (lyapunovGramian A (B * Bᴴ)).rank + _ = _ at h₁
  change (controllabilityMatrix A B)ᴴ.rank + _ = _ at h₂
  rw [Matrix.rank_conjTranspose] at h₂
  omega

end NLAlib

import NLAlib.Matrix.Functions.SignNewtonPositive
import NLAlib.Matrix.Functions.SignExistence
import NLAlib.Matrix.Norms.Core

/-!
# Matrix sign by the actual Newton iteration

The positive-stable product with the sign reduces the iteration to
Cayley squaring. The resulting formula, nonsingularity, convergence,
and quadratic residual identity all hold for nonnormal matrices.
Higham, Functions of Matrices, Chapter 5; toolkit `eq-sign-newton`.
-/

noncomputable section
open Matrix Filter
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every Newton iterate commutes with any matrix commuting with its input. -/
theorem commute_signNewtonIterate {A S : Matrix n n ℂ} (h : Commute S A) (k : ℕ) :
    Commute S (signNewtonIterate A k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change S*((2 : ℂ)⁻¹ • (_+_))=((2 : ℂ)⁻¹ • (_+_))*S
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      ih.eq, ih.matrix_inv_right.eq]

/-- Multiplication by a commuting involution intertwines the exact
Newton recursions, including their total inverse conventions. -/
theorem involution_mul_signNewtonIterate {A S : Matrix n n ℂ}
    (h : Commute S A) (hS : S^2=1) (k : ℕ) :
    S*signNewtonIterate A k=signNewtonIterate (S*A) k := by
  have hSi : S⁻¹=S := Matrix.inv_eq_right_inv (by simpa only [pow_two] using hS)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [signNewtonIterate, signNewtonIterate, ← ih, Matrix.mul_inv_rev, hSi]
    simp only [Matrix.mul_smul, Matrix.mul_add, (commute_signNewtonIterate h k).matrix_inv_right.eq]

/-- The source's sign Cayley matrix equals the positive Cayley transform
of the positive-stable product `SA`. -/
theorem IsMatrixSign.cayley_eq_positiveCayley {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    (A-S)*(A+S)⁻¹=positiveCayley (S*A) := by
  have hs : S*S=1 := by simpa only [pow_two] using hS.1
  have hSi : S⁻¹=S := Matrix.inv_eq_right_inv hs
  have hSA : A*S=S*A := hS.2.1.eq
  have hc : Commute S (S*A) := by change S*(S*A)=(S*A)*S; noncomm_ring [hSA, hs]
  have hm : A-S=S*(S*A-1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hs, Matrix.one_mul, Matrix.mul_one]
  have hp : A+S=S*(S*A+1) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hs, Matrix.one_mul, Matrix.mul_one]
  rw [hm, hp, Matrix.mul_inv_rev, hSi]
  have ht : Commute S ((S*A-1)*(S*A+1)⁻¹) :=
    (hc.sub_right (Commute.one_right _)).mul_right ((hc.add_right (Commute.one_right _)).matrix_inv_right)
  change S*(S*A-1)*((S*A+1)⁻¹*S)=(S*A-1)*(S*A+1)⁻¹
  calc
    _ = S*((S*A-1)*(S*A+1)⁻¹)*S := by noncomm_ring
    _ = ((S*A-1)*(S*A+1)⁻¹)*(S*S) := by rw [ht.eq]; noncomm_ring
    _ = _ := by rw [hs, Matrix.mul_one]

/-- The source's Cayley coordinate is spectrally contractive. -/
theorem IsMatrixSign.spectralRadius_cayley_lt_one {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    spectralRadius ℂ ((A-S)*(A+S)⁻¹)<1 := by
  rw [hS.cayley_eq_positiveCayley]
  exact hS.2.2.spectralRadius_positiveCayley_lt_one

/-- The actual sign Newton recursion has the source's exact right-sign
Cayley formula at every iteration. -/
theorem IsMatrixSign.signNewtonIterate_eq {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (k : ℕ) :
    signNewtonIterate A k=inverseCayley (((A-S)*(A+S)⁻¹)^(2^k))*S := by
  have hs : S*S=1 := by simpa only [pow_two] using hS.1
  have hi := involution_mul_signNewtonIterate hS.2.1.symm hS.1 k
  have he := (hS.2.2.signNewtonIterate_eq_and_isUnit k).1
  have hm : signNewtonIterate A k=S*inverseCayley ((positiveCayley (S*A))^(2^k)) := by
    have hh := congrArg (fun X => S*X) (hi.trans he)
    simpa only [← Matrix.mul_assoc, hs, Matrix.one_mul] using hh
  have hc : Commute S (signNewtonIterate A k) := commute_signNewtonIterate hS.2.1.symm k
  have hv : S*signNewtonIterate A k=inverseCayley ((positiveCayley (S*A))^(2^k)) := hi.trans he
  rw [hS.cayley_eq_positiveCayley, ← hv, hc.eq, Matrix.mul_assoc, hs, Matrix.mul_one]

/-- Every actual sign Newton iterate is nonsingular. -/
theorem IsMatrixSign.isUnit_signNewtonIterate {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (k : ℕ) : IsUnit (signNewtonIterate A k) := by
  rw [hS.signNewtonIterate_eq]
  have hp := tendsto_matrix_pow_zero_of_spectralRadius_lt_one hS.spectralRadius_cayley_lt_one
  obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hp (pow_pos (by norm_num : 0<(2 : ℕ)) k)
  have hSu : IsUnit S := ⟨⟨S,S,by simpa only [pow_two] using hS.1,
    by simpa only [pow_two] using hS.1⟩, rfl⟩
  exact (isUnit_inverseCayley hm hp).mul hSu

/-- Sign Newton iteration converges for arbitrary spectrally separated
matrices; spectral contraction does not require norm contraction. -/
theorem IsMatrixSign.tendsto_signNewtonIterate {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) : Tendsto (signNewtonIterate A) atTop (𝓝 S) := by
  have hp := tendsto_matrix_pow_zero_of_spectralRadius_lt_one hS.spectralRadius_cayley_lt_one
  have ht := (tendsto_inverseCayley_one (hp.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ)<2)))).mul_const S
  convert! ht using 1
  · funext k; exact hS.signNewtonIterate_eq k
  · simp

/-- The exact Newton error identity for a commuting involution. -/
theorem half_smul_add_inv_sub_involution {X S : Matrix n n ℂ}
    (hX : IsUnit X) (hS : S^2=1) (hc : Commute X S) :
    (2 : ℂ)⁻¹ • (X+X⁻¹)-S=(2 : ℂ)⁻¹ • (X⁻¹*(X-S)^2) := by
  have hi := Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det _).mp hX)
  have hs : S*S=1 := by simpa only [pow_two] using hS
  have hp : (X-S)^2=X*X-(2 : ℂ) • (X*S)+1 := by
    simp only [two_smul]
    noncomm_ring [← hc.eq, hs]
  have hq : X⁻¹*(X-S)^2=X+X⁻¹-(2 : ℂ) • S := by
    rw [hp]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
      hi, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hq, smul_sub, smul_smul]
  norm_num

/-- All advertised sign Newton guarantees for the canonical matrix sign:
nonsingularity, exact Cayley formula, convergence, exact quadratic error,
and its spectral-norm bound.
atlas: matrix-sign-newton -/
theorem matrix_sign_newton [Nonempty n] {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) :
    let S := matrixSign A
    let G := (A-S)*(A+S)⁻¹
    spectralRadius ℂ G<1 ∧
      (∀ k, IsUnit (signNewtonIterate A k) ∧
        signNewtonIterate A k=inverseCayley (G^(2^k))*S) ∧
      Tendsto (signNewtonIterate A) atTop (𝓝 S) ∧
      ∀ k, signNewtonIterate A (k+1)-S=
        (2 : ℂ)⁻¹ • ((signNewtonIterate A k)⁻¹*(signNewtonIterate A k-S)^2) ∧
        specNorm (signNewtonIterate A (k+1)-S) ≤
          (1/2 : ℝ)*specNorm ((signNewtonIterate A k)⁻¹)*specNorm (signNewtonIterate A k-S)^2 := by
  dsimp
  have hs := isMatrixSign_matrixSign hA
  refine ⟨hs.spectralRadius_cayley_lt_one, fun k =>
    ⟨hs.isUnit_signNewtonIterate k, hs.signNewtonIterate_eq k⟩, hs.tendsto_signNewtonIterate, ?_⟩
  intro k
  have he := half_smul_add_inv_sub_involution (hs.isUnit_signNewtonIterate k) hs.1
    (commute_signNewtonIterate hs.2.1.symm k).symm
  change signNewtonIterate A (k+1)-matrixSign A=_ at he
  refine ⟨he, ?_⟩
  rw [he, specNorm_eq_norm, norm_smul]
  have hn : ‖(2 : ℂ)⁻¹‖=(1/2 : ℝ) := by norm_num
  rw [hn]
  calc
    _ ≤ (1/2 : ℝ)*(specNorm ((signNewtonIterate A k)⁻¹)*specNorm ((signNewtonIterate A k-matrixSign A)^2)) := by
      exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by norm_num)
    _ ≤ _ := by
      simpa only [mul_assoc, specNorm_eq_norm] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_pow_le (signNewtonIterate A k-matrixSign A) 2)
          (specNorm_nonneg ((signNewtonIterate A k)⁻¹))) (by norm_num : (0 : ℝ)≤1/2)

end NLAlib

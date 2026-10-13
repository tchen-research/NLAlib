import NLAlib.Matrix.Perturbation.ResidualBounds
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Functions.CFCTrace

/-!
# Eigenspace projectors and one-vector sine bounds

The projector is the existing matrix functional calculus of the spectral
indicator. Finite spectral expansion controls its complementary residual,
including an empty complementary spectrum. Parlett §11.7;
atlas `eigenvalue-residual-bounds`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The orthogonal projector onto a complete eigenspace, defined using
Mathlib's functional calculus and a singleton spectral indicator.
Parlett §11.7; no eigenvalue simplicity is assumed. -/
def eigenvalueProjector {A : Matrix n n ℝ} (hA : A.IsHermitian) (ℓ : ℝ) : Matrix n n ℝ :=
  hA.cfc (fun t => if t=ℓ then 1 else 0)

/-- Squared length after finite matrix functional calculus, in eigenbasis
coordinates. Parlett §4.5; bare functions are continuous on the finite spectrum. -/
theorem dotProduct_cfc_mulVec_self_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (x : n → ℝ) :
    (hA.cfc f *ᵥ x) ⬝ᵥ (hA.cfc f *ᵥ x) =
      ∑ i, f (hA.eigenvalues i)^2*(⇑(hA.eigenvectorBasis i) ⬝ᵥ x)^2 := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hU : Uᵀ*U=1 := transpose_eigenvectorUnitary_mul_self hA
  have heq : hA.cfc f = U*Matrix.diagonal (fun i => f (hA.eigenvalues i))*Uᵀ := by
    exact cfc_eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA f
  rw [heq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols (U := U) hU]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [transpose_eigenvectorUnitary_mulVec_apply hA]
  unfold dotProduct
  ring

/-- The eigenvalue projector is symmetric. Parlett §11.7, spectral calculus. -/
theorem eigenvalueProjector_isSymm {A : Matrix n n ℝ} (hA : A.IsHermitian) (ℓ : ℝ) :
    (eigenvalueProjector hA ℓ).IsSymm := by
  change (eigenvalueProjector hA ℓ)ᵀ=eigenvalueProjector hA ℓ
  rw [eigenvalueProjector, cfc_eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The spectral singleton indicator is idempotent, so its functional
calculus is a projector. Parlett §11.7. -/
theorem eigenvalueProjector_isIdempotentElem {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (ℓ : ℝ) : IsIdempotentElem (eigenvalueProjector hA ℓ) := by
  change eigenvalueProjector hA ℓ*eigenvalueProjector hA ℓ=eigenvalueProjector hA ℓ
  simp only [eigenvalueProjector, Matrix.IsHermitian.cfc]
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i j
  simp only [Matrix.diagonal_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  split_ifs <;> simp

/-- The complementary eigenspace projector retains precisely the squared
coordinates outside the target eigenvalue. Parlett §11.7. -/
theorem dotProduct_complement_eigenvalueProjector_eq_sum {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (ℓ : ℝ) (x : n → ℝ) :
    ((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx) =
      ∑ i, if hA.eigenvalues i=ℓ then 0 else (⇑(hA.eigenvectorBasis i) ⬝ᵥ x)^2 := by
  have heq : 1-eigenvalueProjector hA ℓ = hA.cfc (fun t => if t=ℓ then 0 else 1) := by
    let φ := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
    change 1-φ (Matrix.diagonal (fun i => if hA.eigenvalues i=ℓ then 1 else 0)) =
      φ (Matrix.diagonal (fun i => if hA.eigenvalues i=ℓ then 0 else 1))
    rw [← map_one φ, ← map_sub]
    apply congrArg φ
    ext i j
    by_cases hij : i=j
    · subst j
      simp
      split_ifs <;> norm_num
    · simp [hij]
  rw [heq, dotProduct_cfc_mulVec_self_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The separated-eigenspace one-vector sine estimate. Parlett §11.7;
the positive lower bound on the complementary spectral distances includes
the empty-complement case without introducing an undefined minimum.
atlas: eigenvalue-residual-bounds (partial) -/
theorem sqrt_complement_eigenvalueProjector_le_residual_div {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x : n → ℝ) {ℓ δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, hA.eigenvalues i ≠ ℓ → δ ≤ |hA.eigenvalues i-quadForm A x|) :
    Real.sqrt (((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx)) ≤
      Real.sqrt ((A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x))/δ := by
  have hh : δ^2*(((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx)) ≤
      (A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x) := by
    rw [dotProduct_complement_eigenvalueProjector_eq_sum,
      dotProduct_shifted_residual_eq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : hA.eigenvalues i=ℓ
    · simp only [if_pos hi, mul_zero]
      positivity
    · rw [if_neg hi]
      have hb : δ^2 ≤ (hA.eigenvalues i-quadForm A x)^2 := by
        nlinarith [hsep i hi, sq_abs (hA.eigenvalues i-quadForm A x),
          abs_nonneg (hA.eigenvalues i-quadForm A x)]
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  apply (le_div_iff₀ hδ).2
  have hp := dotProduct_self_nonneg ((1-eigenvalueProjector hA ℓ)*ᵥx)
  have hr := dotProduct_self_nonneg (A*ᵥx-quadForm A x•x)
  have hpn := Real.sqrt_nonneg (((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx))
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hr, Real.sqrt_nonneg
    ((A*ᵥx-quadForm A x•x) ⬝ᵥ (A*ᵥx-quadForm A x•x))]

/-- Multiplication by the original matrix acts as the eigenvalue on the
whole eigenvalue projector. Parlett §11.7; all multiplicities are included. -/
theorem mul_eigenvalueProjector_eq_smul {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (ℓ : ℝ) : A*eigenvalueProjector hA ℓ = ℓ•eigenvalueProjector hA ℓ := by
  have hid : hA.cfc id=A := by rw [← hA.cfc_eq]; exact cfc_id ℝ A
  calc
    _ = hA.cfc id*eigenvalueProjector hA ℓ := congrArg (fun T => T*eigenvalueProjector hA ℓ) hid.symm
    _ = _ := by
      let φ := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
      change φ (Matrix.diagonal hA.eigenvalues)*
        φ (Matrix.diagonal (fun i => if hA.eigenvalues i=ℓ then 1 else 0)) =
          ℓ•φ (Matrix.diagonal (fun i => if hA.eigenvalues i=ℓ then 1 else 0))
      rw [← map_mul, ← map_smul]
      apply congrArg φ
      ext i j
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
        Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> simp_all

/-- An eigenvector is fixed by its complete eigenspace projector. Parlett
§11.7, proved from zero shifted variance rather than a simple-eigenvalue assumption. -/
theorem eigenvalueProjector_mulVec_eq_self {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (ℓ : ℝ) {x : n → ℝ} (hx : A*ᵥx=ℓ•x) :
    eigenvalueProjector hA ℓ*ᵥx=x := by
  have hsum : ∑ i, (hA.eigenvalues i-ℓ)^2*(⇑(hA.eigenvectorBasis i) ⬝ᵥ x)^2=0 := by
    rw [← dotProduct_shifted_residual_eq_sum hA x ℓ, hx, sub_self, zero_dotProduct]
  have hterm : ∀ i, (hA.eigenvalues i-ℓ)^2*(⇑(hA.eigenvectorBasis i) ⬝ᵥ x)^2=0 := by
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hsum i (Finset.mem_univ i)
  have hc : ∀ i, hA.eigenvalues i ≠ ℓ → (⇑(hA.eigenvectorBasis i) ⬝ᵥ x)^2=0 := by
    intro i hi
    exact (mul_eq_zero.mp (hterm i)).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hi))
  have hz : ((1-eigenvalueProjector hA ℓ)*ᵥx) ⬝ᵥ ((1-eigenvalueProjector hA ℓ)*ᵥx)=0 := by
    rw [dotProduct_complement_eigenvalueProjector_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · rfl
    · exact hc i hi
  have hv : (1-eigenvalueProjector hA ℓ)*ᵥx=0 := by
    apply dotProduct_star_self_eq_zero.mp
    simpa only [star_trivial] using hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  exact (sub_eq_zero.mp hv).symm

/-- The projector range is exactly the entire eigenspace of the matrix.
Parlett §11.7; this is the bridge from the functional-calculus definition to
Mathlib's actual eigenspace, with all multiplicities and empty cases. -/
theorem range_eigenvalueProjector_eq_eigenspace {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (ℓ : ℝ) :
    LinearMap.range (eigenvalueProjector hA ℓ).mulVecLin =
      Module.End.eigenspace A.mulVecLin ℓ := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨y, rfl⟩
    change A*ᵥ(eigenvalueProjector hA ℓ*ᵥy)=ℓ•(eigenvalueProjector hA ℓ*ᵥy)
    rw [Matrix.mulVec_mulVec, mul_eigenvalueProjector_eq_smul, Matrix.smul_mulVec]
  · intro hx
    exact ⟨x, eigenvalueProjector_mulVec_eq_self hA ℓ hx⟩

end NLAlib

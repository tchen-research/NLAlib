import NLAlib.Matrix.Spectral.Core

/-!
# Identifying the smallest eigenvalue from an eigenvector or a diagonalization

Two finite deterministic facts about the smallest sorted eigenvalue
`hA.eigenvalues₀ ⟨card n - 1, _⟩` of a real symmetric matrix:

* `Matrix.IsHermitian.eigenvalues₀_last_eq_of_unit_eigenvector_of_le`: a unit eigenvector with
 eigenvalue `a` and the Loewner bound `a • 1 ≤ A` identify `λ_min(A) = a`;
* `Matrix.IsHermitian.eigenvalues₀_last_eq_of_conjTranspose_mul_mul_eq_diagonal`: an orthogonal
 diagonalization `Uᵀ A U = diag l` gives `λ_min(A) = min l`.

They connect inverse-power limits to the smallest-singular-value vocabulary of the Gaussian
theorems. Source: Horn–Johnson 2013, Thm 4.2.2 (Rayleigh–Ritz).
Atlas: `wishart-lambda-min-tail`, `norm-lipschitz` (helpers).
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A unit eigenvector `v` of `A` with eigenvalue `a`, together with the Loewner bound
`a • 1 ≤ A`, identifies the smallest sorted eigenvalue: `λ_min(A) = a`. Horn–Johnson 2013,
Thm 4.2.2; helper for `wishart-lambda-min-tail`. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_last_eq_of_unit_eigenvector_of_le [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {a : ℝ} (hle : a • (1 : Matrix ι ι ℝ) ≤ A)
    {v : ι → ℝ} (hv : ‖WithLp.toLp 2 v‖ = 1) (heig : A *ᵥ v = a • v) :
    hA.eigenvalues₀ ⟨Fintype.card ι - 1, Nat.sub_one_lt_of_lt Fintype.card_pos⟩ = a := by
  rw [hA.eigenvalues₀_last_eq_iInf Fintype.card_pos]
  have hpos : (A - a • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.le_iff.mp hle
  have hlow : ∀ x : ι → ℝ, ‖WithLp.toLp 2 x‖ = 1 → a ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := by
    intro x hx
    have hx' : x ⬝ᵥ x = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
    have hp := hpos.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hx', mul_one, RCLike.re_to_real] at hp ⊢
    linarith
  have hbdd : BddBelow (Set.range fun x : {x : ι → ℝ // ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (star x.1 ⬝ᵥ (A *ᵥ x.1))) := ⟨a, by rintro _ ⟨x, rfl⟩; exact hlow x.1 x.2⟩
  apply le_antisymm
  · refine (ciInf_le hbdd (⟨v, hv⟩ : {x : ι → ℝ // ‖WithLp.toLp 2 x‖ = 1})).trans_eq ?_
    show RCLike.re (star v ⬝ᵥ (A *ᵥ v)) = a
    have hvv : v ⬝ᵥ v = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hv, one_pow]
    simp only [star_trivial, heig, dotProduct_smul, smul_eq_mul, hvv, mul_one, RCLike.re_to_real]
  · have : Nonempty {x : ι → ℝ // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨v, hv⟩⟩
    exact le_ciInf fun x => hlow x.1 x.2

/-- The smallest sorted eigenvalue of an orthogonally diagonalized real matrix `Uᵀ A U = diag l`
is the smallest diagonal entry. Horn–Johnson 2013, Thm 4.2.2; helper for
`wishart-lambda-min-tail`. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_last_eq_of_conjTranspose_mul_mul_eq_diagonal
    [Nonempty ι] {A U : Matrix ι ι ℝ} (hA : A.IsHermitian) (hU : HasOrthonormalCols U)
    (l : ι → ℝ) (hdiag : Uᵀ * A * U = Matrix.diagonal l) (i₀ : ι) (hmin : ∀ i, l i₀ ≤ l i) :
    hA.eigenvalues₀ ⟨Fintype.card ι - 1, Nat.sub_one_lt_of_lt Fintype.card_pos⟩ = l i₀ := by
  have hU' : Uᵀ * U = 1 := hU
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU'
  have hA' : A = U * Matrix.diagonal l * Uᵀ := by
    rw [← hdiag]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc A U Uᵀ, hUU]
    simp
  have hdif : Matrix.diagonal (fun i => l i - l i₀) =
      Matrix.diagonal l - l i₀ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  have hpd : (Matrix.diagonal (fun i => l i - l i₀)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr (hmin i)
  have hpos := hpd.mul_mul_conjTranspose_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hdif, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU] at hpos
  rw [← hA'] at hpos
  let e : ι → ℝ := Pi.single i₀ 1
  let v : ι → ℝ := U *ᵥ e
  have hv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [show (U *ᵥ e) ⬝ᵥ (U *ᵥ e) = e ⬝ᵥ ((Uᵀ * U) *ᵥ e) from
        star_mulVec_dotProduct_mulVec_self U e, hU', Matrix.one_mulVec]
    simp [e, dotProduct, Pi.single_apply]
  have hv' : ‖WithLp.toLp 2 v‖ = 1 := by
    rw [← sqrt_dotProduct_self_eq_norm, hv, Real.sqrt_one]
  have heig : A *ᵥ v = l i₀ • v := by
    rw [hA']
    dsimp [v]
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc, hU', Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    simp [e]
  exact hA.eigenvalues₀_last_eq_of_unit_eigenvector_of_le (Matrix.le_iff.mpr hpos) hv' heig

end NLAlib

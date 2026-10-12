import NLAlib.Matrix.Perturbation.BauerFikeAbsolute
import NLAlib.Matrix.Spectral.RankOneEigenvalue
import NLAlib.Matrix.Spectral.NormalSpectral
/-!
# Spectral-norm and normal Bauer–Fike bounds

The Euclidean specialization of the absolute-norm theorem gives the usual
condition-number bound. Unitary eigenbases reduce its constant to one.
Source: Horn–Johnson (2013), Theorem 6.3.2, Corollary 6.3.4 and Theorem 6.3.14;
atlas `bauer-fike`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every entry of a diagonalized spectrum is a spectral point of the
original matrix. Source: Horn–Johnson (2013), Theorem 1.3.7; invertibility
ensures that the corresponding eigenvector column is nonzero. -/
theorem mem_spectrum_of_diagonal_intertwining {A V : Matrix n n ℂ} {d : n → ℂ}
    (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal d) (i : n) :
    d i ∈ spectrum ℂ A := by
  have hcol : Matrix.col V i ≠ 0 := (Matrix.linearIndependent_cols_iff_isUnit.mpr hV).ne_zero i
  have hAi : A *ᵥ Matrix.col V i = d i • Matrix.col V i := by
    funext j
    have h := congrArg (fun M : Matrix n n ℂ => M j i) hA
    rw [Matrix.mul_diagonal] at h
    simpa only [Matrix.mul_apply, Matrix.col_apply, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  exact Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_charpoly_of_mulVec_eq_smul hcol hAi)

/-- The Euclidean residual Bauer–Fike bound in a form without division.
Source: Horn–Johnson (2013), Corollary 6.3.4; the norm on matrices is the
Euclidean operator norm, and the vector norm is explicitly Euclidean.
atlas: bauer-fike (partial) -/
theorem exists_eigenvalue_distance_mul_euclidean_norm_le_residual
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (x : n → ℂ) (hx : x ≠ 0) (μ : ℂ) :
    ∃ i, ‖d i - μ‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ≤
      ‖V‖ * ‖V⁻¹‖ * ‖(WithLp.toLp 2 (A *ᵥ x - μ • x) : EuclideanSpace ℂ n)‖ := by
  let N : AddGroupNorm (n → ℂ) :=
    { toFun x := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖
      map_zero' := by simp
      add_le' x y := by
        simpa only [WithLp.toLp_add] using
          (norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y))
      neg' x := by simp only [WithLp.toLp_neg, norm_neg]
      eq_zero_of_map_eq_zero' x h := by
        have hzero : (WithLp.toLp 2 x : EuclideanSpace ℂ n) = 0 := norm_eq_zero.mp h
        exact congrArg WithLp.ofLp hzero }
  have hhom : ∀ (c : ℂ) (z : n → ℂ), N (c • z) = ‖c‖ * N z := by
    intro c z
    exact norm_smul c (WithLp.toLp 2 z : EuclideanSpace ℂ n)
  have habs : ∀ (z w : n → ℂ), (∀ i, ‖z i‖ ≤ ‖w i‖) → N z ≤ N w := by
    intro z w hzw
    change ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ ≤
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hzw i) 2
  have haction : ∀ (M : Matrix n n ℂ) z, N (M *ᵥ z) ≤ ‖M‖ * N z := by
    intro M z
    exact M.l2_opNorm_mulVec (WithLp.toLp 2 z : EuclideanSpace ℂ n)
  exact exists_eigenvalue_distance_mul_norm_le_residual_of_absolute_norm
    N hhom habs (fun M => ‖M‖) norm_nonneg haction hV hA x hx μ

/-- Euclidean Bauer–Fike residual inclusion in quotient form. Source:
Horn–Johnson (2013), Corollary 6.3.4; nonzero vectors make the denominator
strictly positive.
atlas: bauer-fike (partial) -/
theorem exists_eigenvalue_distance_le_euclidean_residual_div
    {A V : Matrix n n ℂ} {d : n → ℂ} (hV : IsUnit V)
    (hA : A * V = V * Matrix.diagonal d) (x : n → ℂ) (hx : x ≠ 0) (μ : ℂ) :
    ∃ i, ‖d i - μ‖ ≤ (‖V‖ * ‖V⁻¹‖) *
      ‖(WithLp.toLp 2 (A *ᵥ x - μ • x) : EuclideanSpace ℂ n)‖ /
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
  obtain ⟨i, hi⟩ := exists_eigenvalue_distance_mul_euclidean_norm_le_residual hV hA x hx μ
  have hxnorm : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ :=
    norm_pos_iff.mpr (fun h => hx (congrArg WithLp.ofLp h))
  exact ⟨i, (le_div_iff₀ hxnorm).mpr hi⟩

/-- A complex normal matrix satisfies residual spectral inclusion with
constant one. Source: Horn–Johnson (2013), Theorem 6.3.14; this is valid for
every nonzero approximate eigenvector and arbitrary complex approximate
eigenvalue, without a Hermitian or real-spectrum restriction.
atlas: bauer-fike (partial) -/
theorem exists_mem_spectrum_distance_le_euclidean_residual_div_of_normal
    {A : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) (x : n → ℂ) (hx : x ≠ 0) (μ : ℂ) :
    ∃ ν ∈ spectrum ℂ A, ‖ν - μ‖ ≤
      ‖(WithLp.toLp 2 (A *ᵥ x - μ • x) : EuclideanSpace ℂ n)‖ /
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
  cases isEmpty_or_nonempty n with
  | inl hn => exact (hx (Subsingleton.elim _ _)).elim
  | inr hn =>
    obtain ⟨U, d, hUd⟩ := exists_unitary_diagonalization_of_normal hA
    have hUU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
    have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal d := by
      rw [hUd, Matrix.mul_assoc, hUU, Matrix.mul_one]
    have hUinv : (U : Matrix n n ℂ)⁻¹ = (U : Matrix n n ℂ)ᴴ :=
      Matrix.inv_eq_left_inv hUU
    obtain ⟨i, hi⟩ := exists_eigenvalue_distance_le_euclidean_residual_div
      (Unitary.isUnit_coe (U := U)) hAU x hx μ
    refine ⟨d i, mem_spectrum_of_diagonal_intertwining (Unitary.isUnit_coe (U := U)) hAU i, ?_⟩
    simpa only [hUinv, Matrix.l2_opNorm_conjTranspose, CStarRing.norm_coe_unitary,
      one_mul] using hi

/-- Every perturbed eigenvalue of a complex normal matrix is within its
perturbation's spectral norm of the original spectrum. Source: Horn–Johnson
(2013), Theorem 6.3.14; the perturbed matrix may be nonnormal.
atlas: bauer-fike (partial) -/
theorem exists_mem_spectrum_distance_le_norm_perturbation_of_normal
    {A E : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ ν ∈ spectrum ℂ A, ‖ν - μ‖ ≤ ‖E‖ := by
  obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
  obtain ⟨ν, hν, hbound⟩ := exists_mem_spectrum_distance_le_euclidean_residual_div_of_normal hA x hx μ
  have hres : A *ᵥ x - μ • x = -(E *ᵥ x) := by
    rw [Matrix.add_mulVec] at hAx
    calc
      A *ᵥ x - μ • x = A *ᵥ x - (A *ᵥ x + E *ᵥ x) := by rw [hAx]
      _ = -(E *ᵥ x) := by abel
  refine ⟨ν, hν, hbound.trans ?_⟩
  rw [hres, WithLp.toLp_neg, norm_neg]
  have hxnorm : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ :=
    norm_pos_iff.mpr (fun h => hx (congrArg WithLp.ofLp h))
  exact (div_le_iff₀ hxnorm).mpr (E.l2_opNorm_mulVec (WithLp.toLp 2 x : EuclideanSpace ℂ n))

/-- The full Bauer–Fike contract: perturbation and residual inclusion for
every induced absolute vector norm, together with constant-one Euclidean
perturbation and residual bounds for normal matrices. Source: Horn–Johnson
(2013), Theorem 6.3.2, Corollary 6.3.4 and Theorem 6.3.14. Homogeneity and
coordinate-magnitude monotonicity express the absolute vector norm; the
matrix-action bound is the defining induced-norm inequality.
atlas: bauer-fike -/
theorem bauer_fike_properties (N : AddGroupNorm (n → ℂ))
    (hhom : ∀ (c : ℂ) (x : n → ℂ), N (c • x) = ‖c‖ * N x)
    (habs : ∀ (x y : n → ℂ), (∀ i, ‖x i‖ ≤ ‖y i‖) → N x ≤ N y)
    (Φ : Matrix n n ℂ → ℝ) (hΦ : ∀ M, 0 ≤ Φ M)
    (haction : ∀ M x, N (M *ᵥ x) ≤ Φ M * N x)
    (A V : Matrix n n ℂ) (d : n → ℂ) (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) :
    (∀ (E : Matrix n n ℂ) (μ : ℂ), μ ∈ spectrum ℂ (A + E) →
      ∃ i, ‖d i - μ‖ ≤ (Φ V * Φ V⁻¹) * Φ E) ∧
    (∀ (x : n → ℂ), x ≠ 0 → ∀ μ : ℂ,
      ∃ i, ‖d i - μ‖ ≤ (Φ V * Φ V⁻¹) * N (A *ᵥ x - μ • x) / N x) ∧
    (A * Aᴴ = Aᴴ * A → ∀ (x : n → ℂ), x ≠ 0 → ∀ μ : ℂ,
      ∃ ν ∈ spectrum ℂ A, ‖ν - μ‖ ≤
        ‖(WithLp.toLp 2 (A *ᵥ x - μ • x) : EuclideanSpace ℂ n)‖ /
          ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖) ∧
    (A * Aᴴ = Aᴴ * A → ∀ (E : Matrix n n ℂ) (μ : ℂ), μ ∈ spectrum ℂ (A + E) →
      ∃ ν ∈ spectrum ℂ A, ‖ν - μ‖ ≤ ‖E‖) :=
  ⟨fun _ _ hμ => exists_eigenvalue_distance_le_perturbation_of_absolute_norm
      N hhom habs Φ hΦ haction hV hAV hμ,
    fun x hx μ => exists_eigenvalue_distance_le_residual_div_of_absolute_norm
      N hhom habs Φ hΦ haction hV hAV x hx μ,
    fun hA x hx μ => exists_mem_spectrum_distance_le_euclidean_residual_div_of_normal hA x hx μ,
    fun hA _ _ hμ => exists_mem_spectrum_distance_le_norm_perturbation_of_normal hA hμ⟩

end NLAlib

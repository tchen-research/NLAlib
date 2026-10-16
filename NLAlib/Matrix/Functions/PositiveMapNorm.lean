import NLAlib.Matrix.Functions.PositiveBlockNorm
import NLAlib.Matrix.Functions.ContractionUnitaries
import NLAlib.Matrix.Spectral.NormalSpectral

/-!
# Positive-map norm at the identity

Finite spectral projectors control the image of a unitary. The SVD
two-unitary construction then controls all contractions, without assuming
unitality, complete positivity, or invertibility of the image of one.
Tropp (2022), Theorem 12.22 and Proposition 12.24.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A positive map sends every unitary to a matrix of norm at most its
value at the identity. This includes singular and zero images of one. -/
theorem norm_map_unitary_le_norm_map_one
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (U : unitary (Matrix n n ℂ)) :
    ‖Φ U‖ ≤ ‖Φ 1‖ := by
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  have hU'U : (U : Matrix n n ℂ).conjTranspose * U = 1 := Unitary.coe_star_mul_self U
  obtain ⟨V, d, hd⟩ := exists_unitary_diagonalization_of_normal (hUU.trans hU'U.symm)
  let D := star V * U * V
  have hD : (D : Matrix n n ℂ) = diagonal d := by
    change (V : Matrix n n ℂ).conjTranspose * U * V = diagonal d
    rw [hd]
    have hV : (V : Matrix n n ℂ).conjTranspose * V = 1 := Unitary.coe_star_mul_self V
    calc
      _ = ((V : Matrix n n ℂ).conjTranspose * V) * diagonal d *
        ((V : Matrix n n ℂ).conjTranspose * V) := by noncomm_ring
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hz (i : n) : d i * star (d i) = 1 := by
    have h := D.property.2
    change (D : Matrix n n ℂ) * (D : Matrix n n ℂ).conjTranspose = 1 at h
    rw [hD] at h
    simpa using congrFun (congrFun h i) i
  let B (i : n) := Φ (unitarySpectralProjector V i)
  have hB (i : n) : (B i).PosSemidef := posSemidef_map_unitarySpectralProjector Φ V i
  have hsum : ∑ i, B i = Φ 1 := by
    dsimp [B]
    rw [← map_sum, sum_unitarySpectralProjector]
  have hfirst : ∑ i, d i • B i = Φ U := by
    rw [hd, unitary_mul_diagonal_mul_conjTranspose_eq_sum, map_sum]
    simp only [map_smul]
    rfl
  have hsecond : ∑ i, star (d i) • B i = (Φ U).conjTranspose := by
    rw [← hfirst, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.conjTranspose_smul, (hB i).isHermitian.eq]
  have hb (i : n) : (fromBlocks (B i) (d i • B i) (star (d i) • B i) (B i)).PosSemidef := by
    simpa only [star_one, mul_one, one_mul, one_smul, hz] using
      posSemidef_scalar_gram_fromBlocks (hB i) (d i) 1
  have hp := Matrix.posSemidef_sum Finset.univ (fun i _ => hb i)
  have heq : (∑ i, fromBlocks (B i) (d i • B i) (star (d i) • B i) (B i)) =
      fromBlocks (∑ i, B i) (∑ i, d i • B i) (∑ i, star (d i) • B i) (∑ i, B i) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.sum_apply, fromBlocks]
  rw [heq, hsum, hfirst, hsecond] at hp
  exact norm_le_of_posSemidef_equal_fromBlocks
    (Matrix.nonneg_iff_posSemidef.mp (Φ.map_nonneg zero_le_one)) hp

/-- Every contraction is bounded by the image of one under a positive map. -/
theorem norm_map_le_norm_map_one_of_specNorm_le_one {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₚ[ℂ] Matrix (Fin b) (Fin b) ℂ)
    {A : Matrix (Fin a) (Fin a) ℂ} (hA : specNorm A ≤ 1) :
    ‖Φ A‖ ≤ ‖Φ 1‖ := by
  obtain ⟨U, V, h⟩ := exists_unitary_average_of_specNorm_le_one A hA
  rw [h, map_smul, map_add, norm_smul]
  have hn : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [hn]
  have hUV := (norm_add_le (Φ U) (Φ V)).trans
    (add_le_add (norm_map_unitary_le_norm_map_one Φ U)
      (norm_map_unitary_le_norm_map_one Φ V))
  linarith

/-- Russo--Dye's norm-at-one theorem, stated as attainment of the
supremum on the spectral-norm unit ball. Neither complete positivity nor
invertibility or normalization of `Φ 1` is assumed.
Tropp (2022), Theorem 12.22 and Corollary 12.23.
atlas: positive-map-norm-at-identity -/
theorem isGreatest_norm_map_unitBall {a b : ℕ} [NeZero a]
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₚ[ℂ] Matrix (Fin b) (Fin b) ℂ) :
    IsGreatest ((fun A => ‖Φ A‖) '' {A | specNorm A ≤ 1}) ‖Φ 1‖ := by
  constructor
  · exact ⟨1, (specNorm_one_le (𝕜 := ℂ) (n := Fin a)), rfl⟩
  · rintro x ⟨A, hA, rfl⟩
    exact norm_map_le_norm_map_one_of_specNorm_le_one Φ hA

end NLAlib

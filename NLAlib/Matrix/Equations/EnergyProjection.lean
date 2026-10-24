import NLAlib.Matrix.Norms.FrobeniusProducts
import Mathlib.Order.Filter.Extr

/-!
# Energy optimality of matrix-equation Galerkin projections

A Frobenius self-adjoint positive definite linear matrix operator defines a
quadratic energy. Residual orthogonality characterizes its unique minimizing
projection onto a linear trial space. Two-sided matrix trial spaces give the
usual reduced Galerkin equation, including unequal reduced row and column sizes.

Source: Palitta–Simoncini (2019), Definition 2.1 and Proposition 2.2.
Atlas: `matrix-equation-galerkin-optimality`.
-/

noncomputable section

open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The quadratic Frobenius energy of a linear matrix operator. It is defined
for every operator; positivity and symmetry are hypotheses of the projection results. -/
def frobEnergy (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) (X : Matrix m n ℝ) : ℝ :=
  frobInner X (S X)

/-- The energy of the zero matrix is zero. -/
@[simp] theorem frobEnergy_zero (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) :
    frobEnergy S 0 = 0 := by simp [frobEnergy]

/-- A real scalar acts quadratically on operator energy. -/
theorem frobEnergy_smul (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) (c : ℝ)
    (X : Matrix m n ℝ) : frobEnergy S (c • X) = c ^ 2 * frobEnergy S X := by
  simp only [frobEnergy, map_smul, frobInner_smul_left, frobInner_smul_right]
  ring

/-- Symmetry expands an energy of a sum with a single real cross pairing. -/
theorem frobEnergy_add (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V) (U V : Matrix m n ℝ) :
    frobEnergy S (U + V) = frobEnergy S U + 2 * frobInner V (S U) + frobEnergy S V := by
  simp only [frobEnergy, map_add, frobInner_add_left, frobInner_add_right]
  rw [hS U V, frobInner_comm (S U) V]
  ring

/-- Symmetry expands an energy of a difference with a single real cross pairing. -/
theorem frobEnergy_sub (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V) (U V : Matrix m n ℝ) :
    frobEnergy S (U - V) = frobEnergy S U - 2 * frobInner V (S U) + frobEnergy S V := by
  simp only [frobEnergy, map_sub, frobInner_sub_left, frobInner_sub_right]
  rw [hS U V, frobInner_comm (S U) V]
  ring

/-- Residual orthogonality gives the exact operator-energy Pythagorean identity. -/
theorem frobEnergy_sub_eq_add_of_frobInner_eq_zero
    (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V)
    (X Xh Z : Matrix m n ℝ) (horth : frobInner (Xh - Z) (S (X - Xh)) = 0) :
    frobEnergy S (X - Z) = frobEnergy S (X - Xh) + frobEnergy S (Xh - Z) := by
  rw [show X - Z = (X - Xh) + (Xh - Z) by abel, frobEnergy_add S hS, horth]
  ring

/-- For a positive definite self-adjoint matrix operator, a trial matrix minimizes
energy error exactly when its residual is Frobenius-orthogonal to the trial subspace.
Source: Palitta–Simoncini, Proposition 2.2, in an arbitrary linear trial space. -/
theorem isMinOn_frobEnergy_sub_iff_forall_frobInner_eq_zero
    (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V)
    (hpos : ∀ Z : Matrix m n ℝ, Z ≠ 0 → 0 < frobEnergy S Z)
    (U : Submodule ℝ (Matrix m n ℝ)) (X Xh : Matrix m n ℝ) (hXh : Xh ∈ U) :
    IsMinOn (fun Z => frobEnergy S (X - Z)) (U : Set (Matrix m n ℝ)) Xh ↔
      ∀ Z ∈ U, frobInner Z (S (X - Xh)) = 0 := by
  classical
  rw [isMinOn_iff]
  constructor
  · intro hmin Z hZ
    by_cases hz : Z = 0
    · simp [hz]
    let a := frobEnergy S Z
    let c := frobInner Z (S (X - Xh))
    have ha : 0 < a := hpos Z hz
    have hm := hmin (Xh + (c / a) • Z) (U.add_mem hXh (U.smul_mem (c / a) hZ))
    rw [show X - (Xh + (c / a) • Z) = (X - Xh) - (c / a) • Z by abel,
      frobEnergy_sub S hS (X - Xh) ((c / a) • Z), frobEnergy_smul,
      frobInner_smul_left] at hm
    change frobEnergy S (X - Xh) ≤
      frobEnergy S (X - Xh) - 2 * (c / a * c) + (c / a) ^ 2 * a at hm
    have hc : -2 * (c / a * c) + (c / a) ^ 2 * a = -(c ^ 2 / a) := by
      field_simp [ha.ne']
      ring
    have hnonpos : c ^ 2 / a ≤ 0 := by linarith
    have hs : c ^ 2 = 0 :=
      le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ ha).mp hnonpos) (sq_nonneg c)
    exact sq_eq_zero_iff.mp hs
  · intro horth Z hZ
    rw [frobEnergy_sub_eq_add_of_frobInner_eq_zero S hS X Xh Z
      (horth _ (U.sub_mem hXh hZ))]
    by_cases hz : Xh - Z = 0
    · simp [hz]
    · exact le_add_of_nonneg_right (hpos _ hz).le

/-- A minimizing matrix for a positive definite operator is unique as a trial
matrix, independently of the coordinates used to represent that matrix. -/
theorem eq_of_frobEnergy_sub_le_of_isMinOn
    (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V)
    (hpos : ∀ Z : Matrix m n ℝ, Z ≠ 0 → 0 < frobEnergy S Z)
    (U : Submodule ℝ (Matrix m n ℝ)) (X Xh : Matrix m n ℝ) (hXh : Xh ∈ U)
    (hmin : IsMinOn (fun Z => frobEnergy S (X - Z)) (U : Set (Matrix m n ℝ)) Xh)
    {Z : Matrix m n ℝ} (hZ : Z ∈ U)
    (hle : frobEnergy S (X - Z) ≤ frobEnergy S (X - Xh)) : Z = Xh := by
  classical
  have horth := (isMinOn_frobEnergy_sub_iff_forall_frobInner_eq_zero S hS hpos U X Xh hXh).mp hmin
  by_contra hne
  have hp := hpos (Xh - Z) (sub_ne_zero.mpr (Ne.symm hne))
  rw [frobEnergy_sub_eq_add_of_frobInner_eq_zero S hS X Xh Z
    (horth _ (U.sub_mem hXh hZ))] at hle
  linarith

section TwoSided

variable {p q : Type*} [Fintype p] [Fintype q]

/-- The real-linear two-sided matrix trial map, with arbitrary rectangular factors. -/
def twoSidedTrialMap (V : Matrix m p ℝ) (W : Matrix n q ℝ) :
    Matrix p q ℝ →ₗ[ℝ] Matrix m n ℝ where
  toFun T := V * T * Wᴴ
  map_add' T U := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- The reduced Galerkin equation is equivalent to unique minimum operator-energy
error on the two-sided trial space. Orthonormal factors are allowed but unnecessary
for this equivalence; uniqueness concerns the represented matrix, not its coefficients.
Source: Palitta–Simoncini (2019), Definition 2.1 and Proposition 2.2, including unequal
reduced dimensions and arbitrary Frobenius self-adjoint positive definite operators.
atlas: matrix-equation-galerkin-optimality (partial) -/
theorem conjTranspose_residual_mul_eq_zero_iff_unique_frobEnergy_minimizer
    (S : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hS : ∀ U V, frobInner U (S V) = frobInner (S U) V)
    (hpos : ∀ Z : Matrix m n ℝ, Z ≠ 0 → 0 < frobEnergy S Z)
    (V : Matrix m p ℝ) (W : Matrix n q ℝ) (X F : Matrix m n ℝ) (hX : S X = F)
    (Y : Matrix p q ℝ) :
    Vᴴ * (F - S (V * Y * Wᴴ)) * W = 0 ↔
      (∀ T : Matrix p q ℝ,
        frobEnergy S (X - V * Y * Wᴴ) ≤ frobEnergy S (X - V * T * Wᴴ)) ∧
      (∀ T : Matrix p q ℝ,
        frobEnergy S (X - V * T * Wᴴ) ≤ frobEnergy S (X - V * Y * Wᴴ) →
          V * T * Wᴴ = V * Y * Wᴴ) := by
  let U := LinearMap.range (twoSidedTrialMap V W)
  let Xh := V * Y * Wᴴ
  have hXh : Xh ∈ U := ⟨Y, rfl⟩
  have hgal : Vᴴ * (F - S Xh) * W = 0 ↔
      ∀ Z ∈ U, frobInner Z (S (X - Xh)) = 0 := by
    constructor
    · intro h Z hZ
      obtain ⟨T, rfl⟩ := hZ
      change frobInner (V * T * Wᴴ) (S (X - Xh)) = 0
      rw [frobInner_mul_mul_conjTranspose, map_sub, hX, h]
      simp
    · intro h
      let R := Vᴴ * (F - S Xh) * W
      have hr := h ((twoSidedTrialMap V W) R) ⟨R, rfl⟩
      change frobInner (V * R * Wᴴ) (S (X - Xh)) = 0 at hr
      rw [frobInner_mul_mul_conjTranspose, map_sub, hX] at hr
      exact (frobSq_eq_zero_iff R).mp hr
  have hm := isMinOn_frobEnergy_sub_iff_forall_frobInner_eq_zero S hS hpos U X Xh hXh
  constructor
  · intro h
    have hmin := hm.mpr (hgal.mp h)
    constructor
    · intro T
      exact (isMinOn_iff.mp hmin) _ ⟨T, rfl⟩
    · intro T hT
      exact eq_of_frobEnergy_sub_le_of_isMinOn S hS hpos U X Xh hXh hmin ⟨T, rfl⟩ hT
  · intro h
    apply hgal.mpr
    apply hm.mp
    rw [isMinOn_iff]
    rintro Z ⟨T, rfl⟩
    exact h.1 T

end TwoSided

section Multiterm

variable {ι : Type*} [Fintype ι]

/-- The actual multiterm matrix operator `X ↦ ∑ i, A i * X * B i` as a real
linear map. Symmetry and positivity concern the whole operator, not each coefficient.
Source: Palitta–Simoncini (2019), equation (2.3). -/
def matrixMultitermLinearMap (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ) :
    Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ where
  toFun X := ∑ i, A i * X * B i
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

/-- Evaluation of the multiterm operator is the displayed finite matrix sum. -/
@[simp] theorem matrixMultitermLinearMap_apply
    (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ) (X : Matrix m n ℝ) :
    matrixMultitermLinearMap A B X = ∑ i, A i * X * B i := rfl

/-- The concrete multiterm Galerkin equation characterizes its unique minimizing
trial matrix when the whole operator is Frobenius self-adjoint and positive definite.
Individual coefficient matrices need not be positive definite or symmetric.
Source: Palitta–Simoncini (2019), Proposition 2.2.
atlas: matrix-equation-galerkin-optimality (partial) -/
theorem conjTranspose_multiterm_residual_mul_eq_zero_iff_unique_frobEnergy_minimizer
    {p q : Type*} [Fintype p] [Fintype q]
    (A : ι → Matrix m m ℝ) (B : ι → Matrix n n ℝ)
    (hS : ∀ U V, frobInner U (matrixMultitermLinearMap A B V) =
      frobInner (matrixMultitermLinearMap A B U) V)
    (hpos : ∀ Z : Matrix m n ℝ, Z ≠ 0 → 0 < frobEnergy (matrixMultitermLinearMap A B) Z)
    (V : Matrix m p ℝ) (W : Matrix n q ℝ) (X F : Matrix m n ℝ)
    (hX : matrixMultitermLinearMap A B X = F) (Y : Matrix p q ℝ) :
    Vᴴ * (F - ∑ i, A i * (V * Y * Wᴴ) * B i) * W = 0 ↔
      (∀ T : Matrix p q ℝ,
        frobEnergy (matrixMultitermLinearMap A B) (X - V * Y * Wᴴ) ≤
          frobEnergy (matrixMultitermLinearMap A B) (X - V * T * Wᴴ)) ∧
      (∀ T : Matrix p q ℝ,
        frobEnergy (matrixMultitermLinearMap A B) (X - V * T * Wᴴ) ≤
          frobEnergy (matrixMultitermLinearMap A B) (X - V * Y * Wᴴ) →
            V * T * Wᴴ = V * Y * Wᴴ) := by
  simpa only [matrixMultitermLinearMap_apply] using
    conjTranspose_residual_mul_eq_zero_iff_unique_frobEnergy_minimizer
      (matrixMultitermLinearMap A B) hS hpos V W X F hX Y

end Multiterm
end NLAlib

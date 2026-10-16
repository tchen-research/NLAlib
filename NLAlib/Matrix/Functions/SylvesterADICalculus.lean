import NLAlib.Matrix.Structured.SylvesterADI
import NLAlib.Matrix.Functions.RationalCalculus

/-! # Exact scalar spectral norms of normal-matrix ADI products -/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar product of shifted rational factors used by ADI. -/
def adiScalarProduct (α β : ℕ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range j, (z - α i) / (z - β i)

private theorem continuousOn_adiScalarProduct {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (α β : ℕ → ℂ)
    (hβ : ∀ i z, z ∈ spectrum ℂ A → z ≠ β i) (j : ℕ) :
    ContinuousOn (adiScalarProduct α β j) (spectrum ℂ A) := by
  unfold adiScalarProduct
  apply continuousOn_finsetProd
  intro i _
  exact (continuous_id.sub continuous_const).continuousOn.div
    (continuous_id.sub continuous_const).continuousOn (fun z hz => sub_ne_zero.mpr (hβ i z hz))

private theorem cfc_shifted_ratio {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A) (α β : ℂ)
    (hβ : ∀ z ∈ spectrum ℂ A, z ≠ β) :
    cfc (fun z => (z - α) / (z - β)) A = (A - α • 1) * (A - β • 1)⁻¹ := by
  let : IsStarNormal A := ⟨hA.symm⟩
  have hcalc := cfc_map_div (fun z : ℂ => z - α) (fun z => z - β) A
    (fun z hz => sub_ne_zero.mpr (hβ z hz))
  have ha : cfc (fun z : ℂ => z - α) A = A - α • 1 := by
    rw [cfc_sub (fun z : ℂ => z) (fun _ => α) A, cfc_id' ℂ A, cfc_const α A]
    rw [Algebra.algebraMap_eq_smul_one]
  have hb : cfc (fun z : ℂ => z - β) A = A - β • 1 := by
    rw [cfc_sub (fun z : ℂ => z) (fun _ => β) A, cfc_id' ℂ A, cfc_const β A]
    rw [Algebra.algebraMap_eq_smul_one]
  rw [ha, hb, ← Matrix.nonsing_inv_eq_ringInverse] at hcalc
  exact hcalc

/-- The left ADI matrix product is the functional calculus of its actual
scalar product, for a normal matrix. -/
theorem sylvesterADILeft_eq_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A) (α β : ℕ → ℂ)
    (hβ : ∀ i z, z ∈ spectrum ℂ A → z ≠ β i) (j : ℕ) :
    sylvesterADILeft A α β j = cfc (adiScalarProduct α β j) A := by
  let : IsStarNormal A := ⟨hA.symm⟩
  induction j with
  | zero =>
    change 1 = cfc (fun _ : ℂ => 1) A
    rw [cfc_const_one ℂ A]
  | succ j hj =>
    have hscalar : adiScalarProduct α β (j + 1) =
        fun z => ((z - α j) / (z - β j)) * adiScalarProduct α β j z := by
      funext z
      change (∏ i ∈ Finset.range (j + 1), (z - α i) / (z - β i)) = _
      rw [Finset.prod_range_succ, mul_comm]
      rfl
    rw [sylvesterADILeft, hj, hscalar, cfc_mul
      (fun z : ℂ => (z - α j) / (z - β j)) (adiScalarProduct α β j) A
      ((continuous_id.sub continuous_const).continuousOn.div
        (continuous_id.sub continuous_const).continuousOn
        (fun z hz => sub_ne_zero.mpr (hβ j z hz)))
      (continuousOn_adiScalarProduct A α β hβ j), cfc_shifted_ratio A hA _ _ (hβ j)]

/-- The right product has the reciprocal shifted scalar factors in the same
normal functional calculus. -/
theorem sylvesterADIRight_eq_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : B * Bᴴ = Bᴴ * B) (α β : ℕ → ℂ)
    (hα : ∀ i z, z ∈ spectrum ℂ B → z ≠ α i) (j : ℕ) :
    sylvesterADIRight B α β j = cfc (adiScalarProduct β α j) B := by
  let : IsStarNormal B := ⟨hB.symm⟩
  induction j with
  | zero =>
    change 1 = cfc (fun _ : ℂ => 1) B
    rw [cfc_const_one ℂ B]
  | succ j hj =>
    have hscalar : adiScalarProduct β α (j + 1) =
        fun z => adiScalarProduct β α j z * ((z - β j) / (z - α j)) := by
      funext z
      exact Finset.prod_range_succ _ j
    rw [sylvesterADIRight, hj, hscalar, cfc_mul (adiScalarProduct β α j)
      (fun z : ℂ => (z - β j) / (z - α j)) B
      (continuousOn_adiScalarProduct B β α hα j)
      ((continuous_id.sub continuous_const).continuousOn.div
        (continuous_id.sub continuous_const).continuousOn
        (fun z hz => sub_ne_zero.mpr (hα j z hz))), cfc_shifted_ratio B hB _ _ (hα j)]

/-- For a normal matrix, the spectral norm of the left ADI product is exactly
the maximum scalar rational product over its spectrum. Source: user
derivations, normal spectral ADI specialization.
atlas: adi-sylvester-rational-error -/
theorem isGreatest_norm_adiScalarProduct_left {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A) (α β : ℕ → ℂ)
    (hβ : ∀ i z, z ∈ spectrum ℂ A → z ≠ β i) (j : ℕ) :
    IsGreatest ((fun z => ‖adiScalarProduct α β j z‖) '' spectrum ℂ A)
      (specNorm (sylvesterADILeft A α β j)) := by
  let : IsStarNormal A := ⟨hA.symm⟩
  rw [sylvesterADILeft_eq_cfc A hA α β hβ, specNorm_eq_norm]
  exact IsGreatest.norm_cfc _ _ (continuousOn_adiScalarProduct A α β hβ j)

/-- The corresponding exact maximum for the right ADI product. -/
theorem isGreatest_norm_adiScalarProduct_right {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (B : Matrix n n ℂ) (hB : B * Bᴴ = Bᴴ * B) (α β : ℕ → ℂ)
    (hα : ∀ i z, z ∈ spectrum ℂ B → z ≠ α i) (j : ℕ) :
    IsGreatest ((fun z => ‖adiScalarProduct β α j z‖) '' spectrum ℂ B)
      (specNorm (sylvesterADIRight B α β j)) := by
  let : IsStarNormal B := ⟨hB.symm⟩
  rw [sylvesterADIRight_eq_cfc B hB α β hα, specNorm_eq_norm]
  exact IsGreatest.norm_cfc _ _ (continuousOn_adiScalarProduct B β α hα j)

end NLAlib

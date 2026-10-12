import NLAlib.Matrix.Inequalities.SeparatingPSDVector
import NLAlib.Matrix.Inequalities.HadamardPowerOrder
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The finite Vandermonde certificate for entrywise exponential

Distinct scalar nodes make the factorial-weighted rank-one power features
through degree `card n-1` strictly positive. A separating rank-one PSD
lower bound transfers this certificate to every PSD matrix with distinct
rows. Source: Horn--Johnson (2013), Theorem 7.5.9;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A natural entrywise power of a rank-one Gram matrix has the squared
scalar moment as quadratic form. Exponent zero gives the constant feature.
Horn--Johnson (2013), proof of Theorem 7.5.9;
helper for the finite Vandermonde certificate. -/
theorem quadForm_map_pow_vecMulVec_self (b x : n → ℝ) (k : ℕ) :
    quadForm ((vecMulVec b b).map (fun t => t ^ k)) x = (∑ i, x i * b i ^ k) ^ 2 := by
  have he : (vecMulVec b b).map (fun t => t ^ k) =
      vecMulVec (fun i => b i ^ k) (fun i => b i ^ k) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, mul_pow]
  rw [he, quadForm_vecMulVec_self]
  rfl

omit [DecidableEq n] in
/-- Pairwise distinct scalar coordinates give a positive definite finite
factorial-weighted power Gram matrix through degree `card n-1`.
This includes zero and one dimensions. Horn--Johnson (2013),
Theorem 7.5.9; finite Vandermonde helper. -/
theorem posDef_sum_inv_factorial_map_pow_vecMulVec_of_injective (b : n → ℝ)
    (hb : Function.Injective b) :
    (∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ •
      (vecMulVec b b).map (fun t => t ^ k)).PosDef := by
  let H : Matrix n n ℝ := ∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ •
    (vecMulVec b b).map (fun t => t ^ k)
  have hBB : (vecMulVec b b).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
  have hH : H.PosSemidef := Matrix.posSemidef_sum _
    (fun k _ => (posSemidef_map_pow hBB k).smul (by positivity))
  have hform (x : n → ℝ) : quadForm H x =
      ∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ * (∑ i, x i * b i ^ k) ^ 2 := by
    change x ⬝ᵥ (∑ k ∈ Finset.range (Fintype.card n),
      (k.factorial : ℝ)⁻¹ • (vecMulVec b b).map (fun t => t ^ k)) *ᵥ x = _
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← quadForm, quadForm_map_pow_vecMulVec_self]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH.isHermitian
  intro x hx
  simp only [star_trivial]
  change 0 < quadForm H x
  by_contra hn
  have hnonneg : 0 ≤ quadForm H x := by simpa only [quadForm, star_trivial] using hH.dotProduct_mulVec_nonneg x
  have hz : quadForm H x = 0 := le_antisymm (not_lt.mp hn) hnonneg
  rw [hform] at hz
  have hmom (k : Fin (Fintype.card n)) : (∑ i, x i * b i ^ (k : ℕ)) = 0 := by
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j.factorial)) (sq_nonneg _))).mp hz
      k (Finset.mem_range.mpr k.isLt)
    have hf : ((k.val).factorial : ℝ)⁻¹ ≠ 0 := by positivity
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hk0).resolve_left hf)
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hzero : (fun i : Fin (Fintype.card n) => x (e i)) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hb.comp e.injective) (fun k => by
      simp only [Function.comp_apply]
      rw [e.sum_comp (fun i => x i * b i ^ (k : ℕ))]
      exact hmom k)
  apply hx
  funext i
  simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hzero (e.symm i)

/-- Distinct rows of a PSD real matrix already make its first `card n`
entrywise exponential terms positive definite. Singular input and a zero
row are allowed, as are empty and singleton dimensions.
Horn--Johnson (2013), Theorem 7.5.9; strengthened finite certificate.
atlas: schur-product-inequalities (partial) -/
theorem posDef_sum_inv_factorial_map_pow_of_rows_injective {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (hrows : Function.Injective A.row) :
    (∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)).PosDef := by
  obtain ⟨b, hb, hBA⟩ := exists_injective_vecMulVec_le_of_posSemidef_rows_injective hA hrows
  have hBB : (vecMulVec b b).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
  exact posDef_of_posDef_le (posDef_sum_inv_factorial_map_pow_vecMulVec_of_injective b hb)
    (sum_inv_factorial_smul_map_pow_le_of_posSemidef_le hBB hBA (Fintype.card n))

end NLAlib

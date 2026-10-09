import NLAlib.Gaussian.Basic
import NLAlib.Matrix.Norms
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourth moments of a standard Gaussian matrix

For a standard Gaussian `p × m` matrix `G` and fixed `S`, `T`,
`E ‖S G T‖_F⁴ = (‖S‖_F² ‖T‖_F²)² + 2 ‖SᵀS‖_F² ‖TTᵀ‖_F²`
(`integral_frobSq_mul_gaussianMatrix_mul_sq`, atlas `gaussian-frob-fourth-moment`).

The proof is the Isserlis (Wick) formula for four entries of `G`, provided here as reusable
lemmas:

* `integral_pow_four_gaussianReal`, `integral_pow_three_gaussianReal`: `E X⁴ = 3`, `E X³ = 0`;
* `integral_prod_entry_gaussianMatrix`, `integrable_prod_entry_gaussianMatrix`: independence of
  the entries, `E ∏ₑ fₑ(G_e) = ∏ₑ E fₑ(X)`;
* `integral_entry_mul_four_gaussianMatrix`: `E[G_{e₁} G_{e₂} G_{e₃} G_{e₄}] =
  δ₁₂δ₃₄ + δ₁₃δ₂₄ + δ₁₄δ₂₃`;
* `integral_linear_mul_four_gaussianMatrix`, `integral_linear_mul_two_gaussianMatrix` (and the
  `integrable_` versions): the same for linear forms `⟨u, G⟩ = ∑ₑ uₑ G_e`,
  `E[⟨u,G⟩⟨v,G⟩⟨w,G⟩⟨z,G⟩] = ⟨u,v⟩⟨w,z⟩ + ⟨u,w⟩⟨v,z⟩ + ⟨u,z⟩⟨v,w⟩`.

Proof source: Prove2me workspace, Gaussian Random Matrices series (solution
`frobenius_fourth_moment`, namespace `GaussianMatrix.FourthMomentAux`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Moments of a standard Gaussian -/

/-- Every monomial `x ↦ x^k` is integrable for the standard Gaussian. Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`gint`). -/
theorem integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : NNReal)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

private lemma integral_pow_one_gaussianReal : ∫ x, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
  simp [integral_id_gaussianReal (μ := 0) (v := 1)]

private lemma integral_pow_two_gaussianReal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id
    (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
  simpa using h

/-- The third moment of a standard Gaussian vanishes: `E X³ = 0` (symmetry). Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`gm3`). -/
theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have h : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := 0) (v := 1)]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) = - ∫ x, x ^ 3 ∂(gaussianReal 0 1) := by
    rw [← integral_neg]; congr 1; ext x; ring
  linarith

/-- The fourth moment of a standard Gaussian: `E X⁴ = 3`. Atlas: `gaussian-frob-fourth-moment`
(helper). Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment` (`gm4`). -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    have e4 : |x| ^ (4:ℝ) = x ^ 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_abs]
      exact abs_of_nonneg (by positivity)
    have e2 : |x| ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e4, e2]; ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ =>
      (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((4 + 1) / 2) = 3 / 4 * √Real.pi := by
    have := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at this
    rw [show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, this]; ring
  rw [hg]
  have hb : (1/2 : ℝ) ^ (-(4 + 1) / 2 : ℝ) = 4 * √2 := by
    rw [show (-(4 + 1) / 2 : ℝ) = -(2 + 1/2) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_add (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [hb, Real.sqrt_mul (by norm_num)]
  have : (0:ℝ) < √2 := by positivity
  have : (0:ℝ) < √Real.pi := by positivity
  field_simp

/-- `k`-th moment of the standard Gaussian. -/
private def mom (k : ℕ) : ℝ := ∫ x, x ^ k ∂(gaussianReal 0 1)

@[simp] private lemma mom_zero : mom 0 = 1 := by simp [mom]
@[simp] private lemma mom_one : mom 1 = 0 := integral_pow_one_gaussianReal
@[simp] private lemma mom_two : mom 2 = 1 := integral_pow_two_gaussianReal
@[simp] private lemma mom_three : mom 3 = 0 := integral_pow_three_gaussianReal
@[simp] private lemma mom_four : mom 4 = 3 := integral_pow_four_gaussianReal

/-! ### Products of entries -/

variable {p m : ℕ}

/-- **Independence of the entries.** For functions `f_e : ℝ → ℝ` indexed by the entries,
`E ∏ₑ f_e(G_e) = ∏ₑ E f_e(X)` with `X ∼ N(0,1)`. Atlas: `gaussian-frob-fourth-moment` (helper).
Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment` (`integral_prod_coord`). -/
theorem integral_prod_entry_gaussianMatrix (f : Fin p × Fin m → ℝ → ℝ) :
    ∫ G, ∏ e : Fin p × Fin m, f e (G e.1 e.2) ∂(gaussianMatrix p m)
      = ∏ e : Fin p × Fin m, ∫ x, f e x ∂(gaussianReal 0 1) := by
  simp_rw [Fintype.prod_prod_type]
  unfold gaussianMatrix
  rw [integral_fintype_prod_eq_prod (fun (a : Fin p) (g : Fin m → ℝ) => ∏ b, f (a, b) (g b))]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact integral_fintype_prod_eq_prod (fun b x => f (a, b) x)

/-- `G ↦ ∏ₑ f_e(G_e)` is integrable when every `f_e` is. Atlas: `gaussian-frob-fourth-moment`
(helper). Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment`
(`integrable_prod_coord`). -/
theorem integrable_prod_entry_gaussianMatrix (f : Fin p × Fin m → ℝ → ℝ)
    (hf : ∀ e, Integrable (f e) (gaussianReal 0 1)) :
    Integrable (fun G : Fin p → Fin m → ℝ => ∏ e : Fin p × Fin m, f e (G e.1 e.2))
      (gaussianMatrix p m) := by
  simp_rw [Fintype.prod_prod_type]
  unfold gaussianMatrix
  exact Integrable.fintype_prod (f := fun (a : Fin p) (g : Fin m → ℝ) => ∏ b, f (a, b) (g b))
    (fun a => Integrable.fintype_prod (fun b => hf (a, b)))

/-- Multiplicity of the index `e` among `e1, e2, e3, e4`. -/
private def cnt4 (e1 e2 e3 e4 e : Fin p × Fin m) : ℕ :=
  (if e1 = e then 1 else 0) + (if e2 = e then 1 else 0) + (if e3 = e then 1 else 0)
    + (if e4 = e then 1 else 0)

private lemma mono4 (G : Fin p → Fin m → ℝ) (e1 e2 e3 e4 : Fin p × Fin m) :
    G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2
      = ∏ e, G e.1 e.2 ^ cnt4 e1 e2 e3 e4 e := by
  simp only [cnt4, pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ,
    if_true]

/-- A product of four entries of a Gaussian matrix is integrable. Atlas:
`gaussian-frob-fourth-moment` (helper). -/
theorem integrable_entry_mul_four_gaussianMatrix (e1 e2 e3 e4 : Fin p × Fin m) :
    Integrable (fun G : Fin p → Fin m → ℝ =>
      G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) (gaussianMatrix p m) := by
  simp_rw [mono4]
  exact integrable_prod_entry_gaussianMatrix (fun e x => x ^ cnt4 e1 e2 e3 e4 e)
    (fun e => integrable_pow_gaussianReal _)

private lemma prod_mom_cnt4 (e1 e2 e3 e4 : Fin p × Fin m) :
    ∏ e, mom (cnt4 e1 e2 e3 e4 e) = ∏ e ∈ {e1, e2, e3, e4}, mom (cnt4 e1 e2 e3 e4 e) := by
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun e _ he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  simp [cnt4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

/-- **Isserlis (Wick) formula for four entries** of a standard Gaussian matrix:
`E[G_{e₁} G_{e₂} G_{e₃} G_{e₄}] = δ₁₂δ₃₄ + δ₁₃δ₂₄ + δ₁₄δ₂₃`. Isserlis 1918.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`isserlis_idx`). -/
theorem integral_entry_mul_four_gaussianMatrix (e1 e2 e3 e4 : Fin p × Fin m) :
    ∫ G, G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2 ∂(gaussianMatrix p m)
      = (if e1 = e2 then 1 else 0) * (if e3 = e4 then 1 else 0)
        + (if e1 = e3 then 1 else 0) * (if e2 = e4 then 1 else 0)
        + (if e1 = e4 then 1 else 0) * (if e2 = e3 then 1 else 0) := by
  simp_rw [mono4]
  rw [integral_prod_entry_gaussianMatrix (fun e x => x ^ cnt4 e1 e2 e3 e4 e)]
  change ∏ e, mom (cnt4 e1 e2 e3 e4 e) = _
  rw [prod_mom_cnt4]
  by_cases h12 : e1 = e2 <;> by_cases h13 : e1 = e3 <;> by_cases h14 : e1 = e4 <;>
    by_cases h23 : e2 = e3 <;> by_cases h24 : e2 = e4 <;> by_cases h34 : e3 = e4 <;>
    subst_vars <;> (simp_all [Finset.prod_insert, cnt4, eq_comm]; try norm_num)

private lemma mono2 (G : Fin p → Fin m → ℝ) (e1 e2 : Fin p × Fin m) :
    G e1.1 e1.2 * G e2.1 e2.2
      = ∏ e, G e.1 e.2 ^ ((if e1 = e then 1 else 0) + (if e2 = e then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]

private lemma integrable_mono2 (e1 e2 : Fin p × Fin m) :
    Integrable (fun G : Fin p → Fin m → ℝ => G e1.1 e1.2 * G e2.1 e2.2)
      (gaussianMatrix p m) := by
  simp_rw [mono2]
  exact integrable_prod_entry_gaussianMatrix _ (fun e => integrable_pow_gaussianReal _)

private lemma integral_mono2 (e1 e2 : Fin p × Fin m) :
    ∫ G, G e1.1 e1.2 * G e2.1 e2.2 ∂(gaussianMatrix p m) = if e1 = e2 then 1 else 0 := by
  simp_rw [mono2]
  rw [integral_prod_entry_gaussianMatrix
    (fun e x => x ^ ((if e1 = e then 1 else 0) + (if e2 = e then 1 else 0)))]
  change ∏ e, mom _ = _
  by_cases h : e1 = e2
  · subst h
    rw [Finset.prod_eq_single e1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ e1) (by simp [Ne.symm h])

/-! ### Linear forms in a Gaussian matrix -/

/-- The linear form `G ↦ ∑ₑ u e * G e`. -/
private def L (u : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ := ∑ e, u e * G e.1 e.2

/-- Euclidean inner product of coefficient vectors. -/
private def ip (u v : Fin p × Fin m → ℝ) : ℝ := ∑ e, u e * v e

private lemma L2_expand (u v : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    L u G * L v G = ∑ e2, ∑ e1, (u e1 * v e2) * (G e1.1 e1.2 * G e2.1 e2.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma L4_expand (u v w z : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    L u G * L v G * L w G * L z G = ∑ e4, ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- The product of two linear forms in a Gaussian matrix is integrable. Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integrable_L2`). -/
theorem integrable_linear_mul_two_gaussianMatrix (u v : Fin p × Fin m → ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ =>
      (∑ e, u e * G e.1 e.2) * (∑ e, v e * G e.1 e.2)) (gaussianMatrix p m) := by
  change Integrable (fun G => L u G * L v G) _
  simp_rw [L2_expand]
  exact integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono2 e1 e2).const_mul _

/-- The product of four linear forms in a Gaussian matrix is integrable. Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integrable_L4`). -/
theorem integrable_linear_mul_four_gaussianMatrix (u v w z : Fin p × Fin m → ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ =>
      (∑ e, u e * G e.1 e.2) * (∑ e, v e * G e.1 e.2) * (∑ e, w e * G e.1 e.2) *
        (∑ e, z e * G e.1 e.2)) (gaussianMatrix p m) := by
  change Integrable (fun G => L u G * L v G * L w G * L z G) _
  simp_rw [L4_expand]
  exact integrable_finsetSum _ fun e4 _ => integrable_finsetSum _ fun e3 _ =>
    integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_entry_mul_four_gaussianMatrix e1 e2 e3 e4).const_mul _

/-- **Covariance of linear forms**: `E[⟨u,G⟩⟨v,G⟩] = ⟨u,v⟩` for a standard Gaussian matrix `G`.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integral_L2`). -/
theorem integral_linear_mul_two_gaussianMatrix (u v : Fin p × Fin m → ℝ) :
    ∫ G, (∑ e, u e * G e.1 e.2) * (∑ e, v e * G e.1 e.2) ∂(gaussianMatrix p m)
      = ∑ e, u e * v e := by
  change ∫ G, L u G * L v G ∂(gaussianMatrix p m) = ip u v
  simp_rw [L2_expand]
  rw [integral_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono2 e1 e2).const_mul _]
  have : ∀ e2, ∫ G, ∑ e1, (u e1 * v e2) * (G e1.1 e1.2 * G e2.1 e2.2) ∂(gaussianMatrix p m)
      = ∑ e1, (u e1 * v e2) * (if e1 = e2 then 1 else 0) := by
    intro e2
    rw [integral_finsetSum _ fun e1 _ => (integrable_mono2 e1 e2).const_mul _]
    exact Finset.sum_congr rfl fun e1 _ => by rw [integral_const_mul, integral_mono2]
  simp_rw [this]
  simp [ip, mul_ite]

/-- **Isserlis (Wick) formula for linear forms**: for a standard Gaussian matrix `G`,
`E[⟨u,G⟩⟨v,G⟩⟨w,G⟩⟨z,G⟩] = ⟨u,v⟩⟨w,z⟩ + ⟨u,w⟩⟨v,z⟩ + ⟨u,z⟩⟨v,w⟩`, where
`⟨u,G⟩ = ∑ₑ uₑ G_e`. Isserlis 1918. Atlas: `gaussian-frob-fourth-moment` (helper). Ported from
Prove2me solution `GaussianMatrix.frobenius_fourth_moment` (`integral_L4`). -/
theorem integral_linear_mul_four_gaussianMatrix (u v w z : Fin p × Fin m → ℝ) :
    ∫ G, (∑ e, u e * G e.1 e.2) * (∑ e, v e * G e.1 e.2) * (∑ e, w e * G e.1 e.2) *
        (∑ e, z e * G e.1 e.2) ∂(gaussianMatrix p m)
      = (∑ e, u e * v e) * (∑ e, w e * z e) + (∑ e, u e * w e) * (∑ e, v e * z e)
        + (∑ e, u e * z e) * (∑ e, v e * w e) := by
  change ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix p m)
      = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w
  simp_rw [L4_expand]
  have hI : ∀ e1 e2 e3 e4 : Fin p × Fin m, Integrable (fun G : Fin p → Fin m → ℝ =>
      (u e1 * v e2 * w e3 * z e4) * (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2))
      (gaussianMatrix p m) := fun e1 e2 e3 e4 =>
    (integrable_entry_mul_four_gaussianMatrix e1 e2 e3 e4).const_mul _
  rw [integral_finsetSum _ fun e4 _ => integrable_finsetSum _ fun e3 _ =>
    integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
  have : ∀ e4, ∫ G, ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) ∂(gaussianMatrix p m)
      = ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      ((if e1 = e2 then 1 else 0) * (if e3 = e4 then 1 else 0)
        + (if e1 = e3 then 1 else 0) * (if e2 = e4 then 1 else 0)
        + (if e1 = e4 then 1 else 0) * (if e2 = e3 then 1 else 0)) := by
    intro e4
    rw [integral_finsetSum _ fun e3 _ => integrable_finsetSum _ fun e2 _ =>
      integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e3 _ => ?_
    rw [integral_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e2 _ => ?_
    rw [integral_finsetSum _ fun e1 _ => hI e1 e2 e3 e4]
    refine Finset.sum_congr rfl fun e1 _ => ?_
    rw [integral_const_mul, integral_entry_mul_four_gaussianMatrix]
  simp_rw [this]
  simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq']
  simp only [ip, Finset.sum_mul_sum]
  congr 1; congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### The Frobenius fourth moment -/

private lemma sum_sq_gram_comm {ι κ : Type*} [Fintype ι] [Fintype κ] (S : ι → κ → ℝ) :
    ∑ i, ∑ k, (∑ c, S i c * S k c) ^ 2 = ∑ c, ∑ d, (∑ i, S i c * S i d) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  calc _ = ∑ i, ∑ c, ∑ k, ∑ d, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ k, ∑ d, S i c * S k c * (S i d * S k d) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ d, ∑ k, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ i, ∑ k, S i c * S k c * (S i d * S k d) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {a n : ℕ}

/-- Coefficient vector of the entry `(S G T)_x` as a linear form in `G`. -/
private def uST (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin a × Fin n) : Fin p × Fin m → ℝ :=
  fun e => S x.1 e.1 * T e.2 x.2

private lemma entry_eq (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) (i : Fin a) (j : Fin n) :
    (S * Matrix.of G * T) i j = L (uST S T (i, j)) G := by
  simp only [Matrix.mul_apply, Matrix.of_apply, L, uST, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma ip_uST (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (x y : Fin a × Fin n) :
    ip (uST S T x) (uST S T y) = (∑ c, S x.1 c * S y.1 c) * (∑ b, T b x.2 * T b y.2) := by
  simp only [ip, uST, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma frobSq_sq_eq (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (G : Fin p → Fin m → ℝ) :
    frobSq (S * Matrix.of G * T) ^ 2 = ∑ x : Fin a × Fin n, ∑ y : Fin a × Fin n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G := by
  have : frobSq (S * Matrix.of G * T) = ∑ x : Fin a × Fin n, L (uST S T x) G ^ 2 := by
    simp only [frobSq_eq_sum_sq, entry_eq, Fintype.sum_prod_type]
  rw [this, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Fourth moment of a Gaussian sandwich.** For a standard Gaussian `p × m` matrix `G` and
fixed `S : a × p`, `T : m × n`,
`E ‖S G T‖_F⁴ = (‖S‖_F² ‖T‖_F²)² + 2 ‖SᵀS‖_F² ‖T Tᵀ‖_F²`.

Isserlis formula applied to the entries `(S G T)_{ij} = ⟨S_i ⊗ T_j, G⟩`. Used for the variance of
Gaussian sketches (Tropp–Webber 2023, App. A; HMT 2011, Prop 10.1 second-moment companions).
Atlas: `gaussian-frob-fourth-moment`. Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment`. -/
theorem integral_frobSq_mul_gaussianMatrix_mul_sq (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ^ 2 ∂(gaussianMatrix p m)
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
  have hL4 : ∀ u v w z : Fin p × Fin m → ℝ,
      ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix p m)
        = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w :=
    integral_linear_mul_four_gaussianMatrix
  have hI4 : ∀ u v w z : Fin p × Fin m → ℝ,
      Integrable (fun G => L u G * L v G * L w G * L z G) (gaussianMatrix p m) :=
    integrable_linear_mul_four_gaussianMatrix
  simp_rw [frobSq_sq_eq]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hI4 _ _ _ _]
  have h1 : ∀ x : Fin a × Fin n, ∫ G, ∑ y : Fin a × Fin n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G
        ∂(gaussianMatrix p m)
      = ∑ y : Fin a × Fin n, (ip (uST S T x) (uST S T x) * ip (uST S T y) (uST S T y)
          + 2 * ip (uST S T x) (uST S T y) ^ 2) := by
    intro x
    rw [integral_finsetSum _ fun y _ => hI4 _ _ _ _]
    exact Finset.sum_congr rfl fun y _ => by rw [hL4]; ring
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ip_uST]
  have hS : ∑ i, ∑ c, S i c * S i c = frobSq S := by simp [frobSq_eq_sum_sq, sq]
  have hT : ∑ j, ∑ b, T b j * T b j = frobSq T := by
    rw [Finset.sum_comm]; simp [frobSq_eq_sum_sq, sq]
  have hP : ∑ x : Fin a × Fin n, (∑ c, S x.1 c * S x.1 c) * (∑ b, T b x.2 * T b x.2)
      = frobSq S * frobSq T := by
    rw [Fintype.sum_prod_type, ← hS, ← hT, Finset.sum_mul_sum]
  have hS2 : ∑ i, ∑ k, (∑ c, S i c * S k c) ^ 2 = frobSq (Sᵀ * S) := by
    have := sum_sq_gram_comm (fun i c => S i c)
    rw [this]; simp [frobSq_eq_sum_sq, Matrix.mul_apply]
  have hT2 : ∑ j, ∑ l, (∑ b, T b j * T b l) ^ 2 = frobSq (T * Tᵀ) := by
    have := sum_sq_gram_comm (fun j b => T b j)
    rw [this]; simp [frobSq_eq_sum_sq, Matrix.mul_apply]
  have hQ : ∑ x : Fin a × Fin n, ∑ y : Fin a × Fin n,
      ((∑ c, S x.1 c * S y.1 c) * (∑ b, T b x.2 * T b y.2)) ^ 2
      = frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
    rw [← hS2, ← hT2]
    simp only [Fintype.sum_prod_type, mul_pow]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  rw [← Finset.sum_mul, hP, hQ]
  ring

end NLAlib

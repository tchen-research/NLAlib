import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Fourth moments of a standard Gaussian matrix

For a standard Gaussian `p × m` matrix `G` and fixed `S`, `T`,
`E ‖S G T‖_F⁴ = (‖S‖_F² ‖T‖_F²)² + 2 ‖SᵀS‖_F² ‖TTᵀ‖_F²`
(`integral_frobSq_mul_gaussianMatrix_mul_sq`, atlas `gaussian-frob-fourth-moment`).

The proof is the Isserlis (Wick) formula for four entries of `G`, provided here as reusable
lemmas:

* `integral_pow_four_gaussianReal`, `integral_pow_three_gaussianReal`: `E X⁴ = 3`, `E X³ = 0`
  (in `NLAlib.Probability.Gaussian.Basic.StandardGaussian`);
* `integral_prod_entry_gaussianMatrix`, `integrable_prod_entry_gaussianMatrix`: independence of
  the entries, `E ∏ₑ fₑ(G_e) = ∏ₑ E fₑ(X)`;
* `integral_entry_mul_four_gaussianMatrix`: `E[G_{e₁} G_{e₂} G_{e₃} G_{e₄}] =
  δ₁₂δ₃₄ + δ₁₃δ₂₄ + δ₁₄δ₂₃`;
* `integral_linForm_mul_four_gaussianMatrix`, `integral_linForm_mul_two_gaussianMatrix` (and the
  `integrable_` versions): the same for linear forms `⟨u, G⟩ = linForm u G = ∑ᵢⱼ uᵢⱼ Gᵢⱼ`,
  `E[⟨u,G⟩⟨v,G⟩⟨w,G⟩⟨z,G⟩] = ⟨u,v⟩⟨w,z⟩ + ⟨u,w⟩⟨v,z⟩ + ⟨u,z⟩⟨v,w⟩`.

Proof source: Prove2me workspace, Gaussian Random Matrices series (solution
`frobenius_fourth_moment`, namespace `GaussianMatrix.FourthMomentAux`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Moments of a standard Gaussian -/

private lemma integral_pow_one_gaussianReal : ∫ x, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
  simp [integral_id_gaussianReal (μ := 0) (v := 1)]

private lemma integral_pow_two_gaussianReal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero aemeasurable_id
    (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
  simpa using h

/-- `k`-th moment of the standard Gaussian. -/
private def mom (k : ℕ) : ℝ := ∫ x, x ^ k ∂(gaussianReal 0 1)

@[simp] private lemma mom_zero : mom 0 = 1 := by simp [mom]
@[simp] private lemma mom_one : mom 1 = 0 := integral_pow_one_gaussianReal
@[simp] private lemma mom_two : mom 2 = 1 := integral_pow_two_gaussianReal
@[simp] private lemma mom_three : mom 3 = 0 := integral_pow_three_gaussianReal
@[simp] private lemma mom_four : mom 4 = 3 := integral_pow_four_gaussianReal

/-! ### Products of entries -/

variable {p m : Type*} [Fintype p] [Fintype m] [DecidableEq p] [DecidableEq m]

/-- **Independence of the entries.** For functions `f_e : ℝ → ℝ` indexed by the entries,
`E ∏ₑ f_e(G_e) = ∏ₑ E f_e(X)` with `X ∼ N(0,1)`. Atlas: `gaussian-frob-fourth-moment` (helper).
Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment` (`integral_prod_coord`). -/
theorem integral_prod_entry_gaussianMatrix (f : p × m → ℝ → ℝ) :
    ∫ G, ∏ e : p × m, f e (G e.1 e.2) ∂(gaussianMatrix p m)
      = ∏ e : p × m, ∫ x, f e x ∂(gaussianReal 0 1) := by
  simp_rw [Fintype.prod_prod_type]
  rw [integral_gaussianMatrix_eq]
  simp only [Matrix.of_apply]
  rw [integral_fintype_prod_eq_prod (fun (a : p) (g : m → ℝ) => ∏ b, f (a, b) (g b))]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact integral_fintype_prod_eq_prod (fun b x => f (a, b) x)

/-- `G ↦ ∏ₑ f_e(G_e)` is integrable when every `f_e` is. Atlas: `gaussian-frob-fourth-moment`
(helper). Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment`
(`integrable_prod_coord`). -/
theorem integrable_prod_entry_gaussianMatrix (f : p × m → ℝ → ℝ)
    (hf : ∀ e, Integrable (f e) (gaussianReal 0 1)) :
    Integrable (fun G : Matrix p m ℝ => ∏ e : p × m, f e (G e.1 e.2))
      (gaussianMatrix p m) := by
  simp_rw [Fintype.prod_prod_type]
  rw [integrable_gaussianMatrix_iff]
  simp only [Matrix.of_apply]
  exact Integrable.fintype_prod (f := fun (a : p) (g : m → ℝ) => ∏ b, f (a, b) (g b))
    (fun a => Integrable.fintype_prod (fun b => hf (a, b)))

/-- Multiplicity of the index `e` among `e1, e2, e3, e4`. -/
private def cnt4 (e1 e2 e3 e4 e : p × m) : ℕ :=
  (if e1 = e then 1 else 0) + (if e2 = e then 1 else 0) + (if e3 = e then 1 else 0)
    + (if e4 = e then 1 else 0)

private lemma mono4 (G : Matrix p m ℝ) (e1 e2 e3 e4 : p × m) :
    G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2
      = ∏ e, G e.1 e.2 ^ cnt4 e1 e2 e3 e4 e := by
  simp only [cnt4, pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ,
    if_true]

/-- A product of four entries of a Gaussian matrix is integrable. Atlas:
`gaussian-frob-fourth-moment` (helper). -/
theorem integrable_entry_mul_four_gaussianMatrix (e1 e2 e3 e4 : p × m) :
    Integrable (fun G : Matrix p m ℝ =>
      G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) (gaussianMatrix p m) := by
  simp_rw [mono4]
  exact integrable_prod_entry_gaussianMatrix (fun e x => x ^ cnt4 e1 e2 e3 e4 e)
    (fun e => integrable_pow_gaussianReal _)

private lemma prod_mom_cnt4 (e1 e2 e3 e4 : p × m) :
    ∏ e, mom (cnt4 e1 e2 e3 e4 e) = ∏ e ∈ {e1, e2, e3, e4}, mom (cnt4 e1 e2 e3 e4 e) := by
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun e _ he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  simp [cnt4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

/-- **Isserlis (Wick) formula for four entries** of a standard Gaussian matrix:
`E[G_{e₁} G_{e₂} G_{e₃} G_{e₄}] = δ₁₂δ₃₄ + δ₁₃δ₂₄ + δ₁₄δ₂₃`. Isserlis 1918.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`isserlis_idx`).
atlas: gaussian-frob-fourth-moment -/
theorem integral_entry_mul_four_gaussianMatrix (e1 e2 e3 e4 : p × m) :
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

private lemma mono2 (G : Matrix p m ℝ) (e1 e2 : p × m) :
    G e1.1 e1.2 * G e2.1 e2.2
      = ∏ e, G e.1 e.2 ^ ((if e1 = e then 1 else 0) + (if e2 = e then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]

private lemma integrable_mono2 (e1 e2 : p × m) :
    Integrable (fun G : Matrix p m ℝ => G e1.1 e1.2 * G e2.1 e2.2)
      (gaussianMatrix p m) := by
  simp_rw [mono2]
  exact integrable_prod_entry_gaussianMatrix _ (fun e => integrable_pow_gaussianReal _)

private lemma integral_mono2 (e1 e2 : p × m) :
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
private def L (u : p × m → ℝ) (G : Matrix p m ℝ) : ℝ := ∑ e, u e * G e.1 e.2

/-- Euclidean inner product of coefficient vectors. -/
private def ip (u v : p × m → ℝ) : ℝ := ∑ e, u e * v e

private lemma L2_expand (u v : p × m → ℝ) (G : Matrix p m ℝ) :
    L u G * L v G = ∑ e2, ∑ e1, (u e1 * v e2) * (G e1.1 e1.2 * G e2.1 e2.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma L4_expand (u v w z : p × m → ℝ) (G : Matrix p m ℝ) :
    L u G * L v G * L w G * L z G = ∑ e4, ∑ e3, ∑ e2, ∑ e1, (u e1 * v e2 * w e3 * z e4) *
      (G e1.1 e1.2 * G e2.1 e2.2 * G e3.1 e3.2 * G e4.1 e4.2) := by
  simp only [L, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

private lemma integrable_L2 (u v : p × m → ℝ) :
    Integrable (fun G => L u G * L v G) (gaussianMatrix p m) := by
  simp_rw [L2_expand]
  exact integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_mono2 e1 e2).const_mul _

private lemma integrable_L4 (u v w z : p × m → ℝ) :
    Integrable (fun G => L u G * L v G * L w G * L z G) (gaussianMatrix p m) := by
  simp_rw [L4_expand]
  exact integrable_finsetSum _ fun e4 _ => integrable_finsetSum _ fun e3 _ =>
    integrable_finsetSum _ fun e2 _ => integrable_finsetSum _ fun e1 _ =>
    (integrable_entry_mul_four_gaussianMatrix e1 e2 e3 e4).const_mul _

private lemma integral_L2 (u v : p × m → ℝ) :
    ∫ G, L u G * L v G ∂(gaussianMatrix p m) = ip u v := by
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

private lemma integral_L4 (u v w z : p × m → ℝ) :
    ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix p m)
      = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w := by
  simp_rw [L4_expand]
  have hI : ∀ e1 e2 e3 e4 : p × m, Integrable (fun G : Matrix p m ℝ =>
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

private lemma linForm_eq_L (c : p → m → ℝ) (G : Matrix p m ℝ) :
    linForm c G = L (Function.uncurry c) G := by
  simp only [linForm, L, Fintype.sum_prod_type, Function.uncurry]

private lemma sum_sum_mul_eq_ip (u v : p → m → ℝ) :
    ∑ i, ∑ j, u i j * v i j = ip (Function.uncurry u) (Function.uncurry v) := by
  simp only [ip, Fintype.sum_prod_type, Function.uncurry]

/-- The product of two linear forms `⟨u,G⟩⟨v,G⟩` in a Gaussian matrix is integrable. Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integrable_L2`). -/
theorem integrable_linForm_mul_two_gaussianMatrix (u v : p → m → ℝ) :
    Integrable (fun G => linForm u G * linForm v G) (gaussianMatrix p m) := by
  simp_rw [linForm_eq_L]
  exact integrable_L2 _ _

/-- The product of four linear forms `⟨u,G⟩⟨v,G⟩⟨w,G⟩⟨z,G⟩` in a Gaussian matrix is integrable.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integrable_L4`). -/
theorem integrable_linForm_mul_four_gaussianMatrix (u v w z : p → m → ℝ) :
    Integrable (fun G => linForm u G * linForm v G * linForm w G * linForm z G)
      (gaussianMatrix p m) := by
  simp_rw [linForm_eq_L]
  exact integrable_L4 _ _ _ _

/-- **Covariance of linear forms**: `E[⟨u,G⟩⟨v,G⟩] = ⟨u,v⟩ = ∑ᵢⱼ uᵢⱼ vᵢⱼ` for a standard Gaussian
matrix `G`; `u = v` gives `integral_linForm_sq_gaussianMatrix`.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integral_L2`). -/
theorem integral_linForm_mul_two_gaussianMatrix (u v : p → m → ℝ) :
    ∫ G, linForm u G * linForm v G ∂(gaussianMatrix p m) = ∑ i, ∑ j, u i j * v i j := by
  simp_rw [linForm_eq_L, sum_sum_mul_eq_ip]
  exact integral_L2 _ _

/-- **Isserlis (Wick) formula for linear forms**: for a standard Gaussian matrix `G`,
`E[⟨u,G⟩⟨v,G⟩⟨w,G⟩⟨z,G⟩] = ⟨u,v⟩⟨w,z⟩ + ⟨u,w⟩⟨v,z⟩ + ⟨u,z⟩⟨v,w⟩`, where
`⟨u,G⟩ = linForm u G = ∑ᵢⱼ uᵢⱼ Gᵢⱼ` and `⟨u,v⟩ = ∑ᵢⱼ uᵢⱼ vᵢⱼ`. Isserlis 1918.
Atlas: `gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`integral_L4`).
atlas: gaussian-frob-fourth-moment -/
theorem integral_linForm_mul_four_gaussianMatrix (u v w z : p → m → ℝ) :
    ∫ G, linForm u G * linForm v G * linForm w G * linForm z G ∂(gaussianMatrix p m)
      = (∑ i, ∑ j, u i j * v i j) * (∑ i, ∑ j, w i j * z i j)
        + (∑ i, ∑ j, u i j * w i j) * (∑ i, ∑ j, v i j * z i j)
        + (∑ i, ∑ j, u i j * z i j) * (∑ i, ∑ j, v i j * w i j) := by
  simp_rw [linForm_eq_L, sum_sum_mul_eq_ip]
  exact integral_L4 _ _ _ _

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

variable {a n : Type*} [Fintype a] [Fintype n]

/-- Coefficient vector of the entry `(S G T)_x` as a linear form in `G`. -/
private def uST (S : Matrix a p ℝ) (T : Matrix m n ℝ)
    (x : a × n) : p × m → ℝ :=
  fun e => S x.1 e.1 * T e.2 x.2

private lemma entry_eq (S : Matrix a p ℝ) (T : Matrix m n ℝ)
    (G : Matrix p m ℝ) (i : a) (j : n) :
    (S * G * T) i j = L (uST S T (i, j)) G := by
  simp only [Matrix.mul_apply, L, uST, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma ip_uST (S : Matrix a p ℝ) (T : Matrix m n ℝ)
    (x y : a × n) :
    ip (uST S T x) (uST S T y) = (∑ c, S x.1 c * S y.1 c) * (∑ b, T b x.2 * T b y.2) := by
  simp only [ip, uST, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma frobSq_sq_eq (S : Matrix a p ℝ) (T : Matrix m n ℝ)
    (G : Matrix p m ℝ) :
    frobSq (S * G * T) ^ 2 = ∑ x : a × n, ∑ y : a × n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G := by
  have : frobSq (S * G * T) = ∑ x : a × n, L (uST S T x) G ^ 2 := by
    simp only [frobSq_eq_sum_sq, entry_eq, Fintype.sum_prod_type]
  rw [this, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Fourth moment of a Gaussian sandwich.** For a standard Gaussian `p × m` matrix `G` and
fixed `S : a × p`, `T : m × n`,
`E ‖S G T‖_F⁴ = (‖S‖_F² ‖T‖_F²)² + 2 ‖SᵀS‖_F² ‖T Tᵀ‖_F²`.

Isserlis formula applied to the entries `(S G T)_{ij} = ⟨S_i ⊗ T_j, G⟩`. Used for the variance of
Gaussian sketches (Tropp–Webber 2023, App. A; HMT 2011, Prop 10.1 second-moment companions).
Atlas: `gaussian-frob-fourth-moment`. Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment`.
atlas: gaussian-frob-fourth-moment -/
theorem integral_frobSq_mul_gaussianMatrix_mul_sq (S : Matrix a p ℝ)
    (T : Matrix m n ℝ) :
    ∫ G, frobSq (S * G * T) ^ 2 ∂(gaussianMatrix p m)
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
  have hL4 : ∀ u v w z : p × m → ℝ,
      ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix p m)
        = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w :=
    integral_L4
  have hI4 : ∀ u v w z : p × m → ℝ,
      Integrable (fun G => L u G * L v G * L w G * L z G) (gaussianMatrix p m) :=
    integrable_L4
  simp_rw [frobSq_sq_eq]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hI4 _ _ _ _]
  have h1 : ∀ x : a × n, ∫ G, ∑ y : a × n,
      L (uST S T x) G * L (uST S T x) G * L (uST S T y) G * L (uST S T y) G
        ∂(gaussianMatrix p m)
      = ∑ y : a × n, (ip (uST S T x) (uST S T x) * ip (uST S T y) (uST S T y)
          + 2 * ip (uST S T x) (uST S T y) ^ 2) := by
    intro x
    rw [integral_finsetSum _ fun y _ => hI4 _ _ _ _]
    exact Finset.sum_congr rfl fun y _ => by rw [hL4]; ring
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ip_uST]
  have hS : ∑ i, ∑ c, S i c * S i c = frobSq S := by simp [frobSq_eq_sum_sq, sq]
  have hT : ∑ j, ∑ b, T b j * T b j = frobSq T := by
    rw [Finset.sum_comm]; simp [frobSq_eq_sum_sq, sq]
  have hP : ∑ x : a × n, (∑ c, S x.1 c * S x.1 c) * (∑ b, T b x.2 * T b x.2)
      = frobSq S * frobSq T := by
    rw [Fintype.sum_prod_type, ← hS, ← hT, Finset.sum_mul_sum]
  have hS2 : ∑ i, ∑ k, (∑ c, S i c * S k c) ^ 2 = frobSq (Sᵀ * S) := by
    have := sum_sq_gram_comm (fun i c => S i c)
    rw [this]; simp [frobSq_eq_sum_sq, Matrix.mul_apply]
  have hT2 : ∑ j, ∑ l, (∑ b, T b j * T b l) ^ 2 = frobSq (T * Tᵀ) := by
    have := sum_sq_gram_comm (fun j b => T b j)
    rw [this]; simp [frobSq_eq_sum_sq, Matrix.mul_apply]
  have hQ : ∑ x : a × n, ∑ y : a × n,
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

/-- `integral_frobSq_mul_gaussianMatrix_mul_sq` for a random matrix `X` with
`HasLaw X (gaussianMatrix p m) μ`. Atlas: `gaussian-frob-fourth-moment`. -/
theorem integral_frobSq_mul_gaussianMatrix_mul_sq_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → Matrix p m ℝ} (hX : HasLaw X (gaussianMatrix p m) μ)
    (S : Matrix a p ℝ) (T : Matrix m n ℝ) :
    ∫ ω, frobSq (S * X ω * T) ^ 2 ∂μ
      = (frobSq S * frobSq T) ^ 2 + 2 * frobSq (Sᵀ * S) * frobSq (T * Tᵀ) := by
  have hc : Continuous fun G : Matrix p m ℝ => frobSq (S * G * T) ^ 2 := by
    simp only [frobSq_eq_sum_sq]; fun_prop
  rw [← integral_frobSq_mul_gaussianMatrix_mul_sq S T]
  exact hX.integral_comp hc.aestronglyMeasurable

end NLAlib

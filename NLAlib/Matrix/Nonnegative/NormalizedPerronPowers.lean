import NLAlib.Matrix.Nonnegative.PrimitivePerron

/-! # Normalized Perron iteration for every nonnegative starting vector

The rank-one power limit has a positive scalar coefficient on every nonzero
nonnegative vector. Dividing by the sum of the coordinates removes that
coefficient. Homogeneous normalization also removes the scalar Perron power.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/
noncomputable section
open Matrix Finset Filter
open scoped Matrix Topology
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem sum_normalize_smul_eq (x : ι → ℝ) {a : ℝ} (ha : a ≠ 0) :
    (∑ i, (a • x) i)⁻¹ • (a • x) = (∑ i, x i)⁻¹ • x := by
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, smul_smul]
  congr 1
  by_cases hs : (∑ i, x i) = 0
  · simp [hs]
  · field_simp [ha, hs]

open scoped Matrix.Norms.L2Operator in
/-- A positive rank-one matrix-power limit gives normalized vector convergence
for every nonzero nonnegative starting vector. -/
theorem tendsto_sum_normalized_power_mulVec_of_perron_limit
    {T : Matrix ι ι ℝ} {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1)
    (hlim : Tendsto (fun k : ℕ => T ^ k) atTop
      (𝓝 ((q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q)))
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxne : x ≠ 0) :
    Tendsto (fun k : ℕ => (∑ i, (T ^ k *ᵥ x) i)⁻¹ • (T ^ k *ᵥ x)) atTop (𝓝 p) := by
  have hqp : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxne
  have hxj : 0 < x j := lt_of_le_of_ne (hx j) hj.symm
  have hqx : 0 < q ⬝ᵥ x := (mul_pos (hq j) hxj).trans_le
    (Finset.single_le_sum (fun i _ => mul_nonneg (hq i).le (hx i)) (mem_univ j))
  let c : ℝ := (q ⬝ᵥ x) / (q ⬝ᵥ p)
  have hc : 0 < c := div_pos hqx hqp
  have hproj : ((q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q) *ᵥ x = c • p := by
    ext i
    simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Pi.smul_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, c, div_eq_mul_inv]
    ring
  have hcont : Continuous (fun M : Matrix ι ι ℝ => M *ᵥ x) := by fun_prop
  have hvlim : Tendsto (fun k : ℕ => T ^ k *ᵥ x) atTop (𝓝 (c • p)) := by
    simpa only [Function.comp_def, hproj] using hcont.continuousAt.tendsto.comp hlim
  have hsumcont : Continuous (fun v : ι → ℝ => ∑ i, v i) := by fun_prop
  have hsumlim : Tendsto (fun k : ℕ => ∑ i, (T ^ k *ᵥ x) i) atTop (𝓝 c) := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      hps, mul_one] using hsumcont.continuousAt.tendsto.comp hvlim
  have hresult := (hsumlim.inv₀ hc.ne').smul hvlim
  simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hresult

open scoped Matrix.Norms.L2Operator in
/-- Normalized powers of a primitive matrix converge to one common positive
unit-sum Perron vector for every nonzero nonnegative initial vector.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsPrimitive.exists_tendsto_normalized_power_mulVec {A : Matrix ι ι ℝ}
    (hA : A.IsPrimitive) (hAne : A ≠ 0) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ (∑ i, p i = 1) ∧
      ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → x ≠ 0 →
        Tendsto (fun k : ℕ => (∑ i, (A ^ k *ᵥ x) i)⁻¹ • (A ^ k *ᵥ x)) atTop (𝓝 p) := by
  obtain ⟨p, q, hr, hp, hq, hps, _, hAp, hqA⟩ := hA.isIrreducible.exists_positive_perron_pair hAne
  have hlim := (hA.isIrreducible.perron_power_limit_and_rate hAne hp hq hAp hqA
    ((hA.isIrreducible.isPrimitive_iff_unique_peripheral hAne).mp hA)).1
  refine ⟨p, hp, hps, fun x hx hxne => ?_⟩
  have hnormalized := tendsto_sum_normalized_power_mulVec_of_perron_limit hp hq hps hlim hx hxne
  convert hnormalized using 1
  funext k
  rw [smul_pow, Matrix.smul_mulVec,
    sum_normalize_smul_eq _ (pow_ne_zero k (inv_ne_zero hr.ne'))]

end Matrix

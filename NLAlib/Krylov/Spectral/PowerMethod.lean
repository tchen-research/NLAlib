import NLAlib.Krylov.Spectral.Ritz
import NLAlib.Krylov.Spaces.Block
import NLAlib.Matrix.Subspaces.PrincipalAngles
import NLAlib.Matrix.Norms.SingleColumn
/-!
# Power iteration and inverse iteration

`NLAlib/Krylov/Spectral/` holds the eigenvalue algorithms that are not Krylov methods but share
the Ritz/subspace vocabulary: the power method and inverse iteration (this file), subspace
iteration (`SubspaceIteration`) and the QR algorithm (`QRAlgorithm`), next to the Krylov
eigenvalue bounds (`Ritz`, `CharacteristicPolynomial`, `MeasurableRitz`).

The power method is the `s = 1` case of subspace iteration (`subspaceIterate`): the iterate is
the direction of `A^k x₀`, and normalisation is bookkeeping. Statements take a unit eigenvector
`u` for the eigenvalue at a sorted position `i₀` (`A *ᵥ u = hA.eigenvalues₀ i₀ • u`,
`‖WithLp.toLp 2 u‖ = 1`); "the other eigenvalues" are the other sorted positions.

* `NLAlib.powerIterate A x₀ k = A^k x₀` (unnormalised; `powerIterate_succ`,
  `powerIterate_mem_krylovSpace`, `span_powerIterate_eq_subspaceIterate`);
  `NLAlib.powerStep A x = A x/‖A x‖` is the textbook normalised step and
  `powerStep_iterate_succ` says that `k + 1` normalised steps give `A^{k+1} x₀/‖A^{k+1} x₀‖`;
  angles and Rayleigh quotients are scale invariant (`overlapTangentSq_smul`,
  `rayleighQuotient_smul`), so every statement transfers.
* `NLAlib.rayleighQuotient A x = xᵀAx/xᵀx` (`NLAlib.Matrix.Basic.QuadForm`).
* **Angle bound** (`overlapTangentSq_powerIterate_le`): for symmetric `A`, a unit eigenvector `u` of
  `λ₁ = λ_{i₀}` and `|λᵢ| ≤ ρ` at the other sorted positions,
  `tan² ∠(u, A^k x₀) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u, x₀)` (the `p = X^k` case of
  `overlapTangentSq_aeval_mulVec_le`); the normalised form `overlapTangentSq_powerStep_iterate_le`.
* **Rayleigh quotient** (`abs_rayleighQuotient_sub_le_mul_overlapTangentSq`):
  `|ρ(x) − λ₁| ≤ D tan² ∠(u, x)` whenever `|λᵢ − λ₁| ≤ D` for all `i`, so the Rayleigh quotient
  of the power iterates converges at the squared rate (`abs_rayleighQuotient_powerIterate_sub_le`).
  For the top eigenvalue the one-sided form with `D = λ₁ − λ_min` is Ritz.lean's
  `eigenvalues_sub_eigenvalues_le_mul_overlapTangentSq` (Rayleigh–Ritz on a one-column `Q`).
* **Inverse iteration** (`inverseIterate A μ x₀ k = (A − μI)^{-k} x₀`, power iteration on the
  resolvent): `tan² ∠(u, x_k) ≤ (|λ_{i₀} − μ|/d)^{2k} tan² ∠(u, x₀)` when every other
  eigenvalue is at distance `≥ d > 0` from `μ` (`overlapTangentSq_inverseIterate_le`), with the
  Rayleigh-quotient corollary. The resolvent shares the eigenvectors of `A`
  (`eigenvectorBasis_dotProduct_inv_sub_mulVec`).

Source: Trefethen–Bau (1997) [`tb97`], Thm 27.1 (power iteration), Thm 27.2 (inverse iteration);
Golub–Van Loan (2013) [`gvl13`], Thm 8.2.1, §8.2.2; Saad (2011) [`saad11`], §4.1.
Atlas: `power-iteration`, `inverse-iteration`.
-/

noncomputable section

open scoped Matrix
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The iterates -/

/-- The `k`-th (unnormalised) power iterate `A^k x₀`. Normalisation does not change its
direction (`powerStep_iterate_succ`). Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.1 (Lect.
27); Golub–Van Loan (2013) [`gvl13`], §8.2.1. Helper for `power-iteration`. -/
def powerIterate (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) : n → ℝ := (A ^ k) *ᵥ x₀

/-- `x_0 = x₀`. Helper for `power-iteration`. -/
@[simp]
theorem powerIterate_zero (A : Matrix n n ℝ) (x₀ : n → ℝ) : powerIterate A x₀ 0 = x₀ := by
  simp [powerIterate]

/-- One power step: `x_{k+1} = A x_k`. Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.1.
Helper for `power-iteration`. -/
theorem powerIterate_succ (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    powerIterate A x₀ (k + 1) = A *ᵥ powerIterate A x₀ k := by
  rw [powerIterate, powerIterate, pow_succ', ← Matrix.mulVec_mulVec]

/-- `A^k x₀ ∈ K_{k+1}(A, x₀)`. Source: Saad (2011) [`saad11`], §4.1 and §6.1. Helper for
`power-iteration`. -/
theorem powerIterate_mem_krylovSpace (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    powerIterate A x₀ k ∈ krylovSpace A x₀ (k + 1) :=
  pow_mulVec_mem_krylovSpace A x₀ (Nat.lt_succ_self k)

/-- Power iteration is subspace iteration with one column: `span {A^k x₀} = S_k(A, x₀)`.
Source: Saad (2011) [`saad11`], §5.1. Helper for `power-iteration`. -/
theorem span_powerIterate_eq_subspaceIterate (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    ℝ ∙ powerIterate A x₀ k = subspaceIterate A (Matrix.replicateCol Unit x₀) k := by
  rw [subspaceIterate, Matrix.range_mulVecLin]
  have h : Set.range (A ^ k * Matrix.replicateCol Unit x₀).col = {powerIterate A x₀ k} := by
    rw [Set.range_unique, col_mul_eq_mulVec_col]
    rfl
  rw [h]

/-- The normalised power step `x ↦ A x/‖A x‖` (junk value `0` when `A x = 0`). Source:
Trefethen–Bau (1997) [`tb97`], Alg. 27.1. Helper for `power-iteration`. -/
def powerStep (A : Matrix n n ℝ) (x : n → ℝ) : n → ℝ :=
  ‖WithLp.toLp 2 (A *ᵥ x)‖⁻¹ • (A *ᵥ x)

omit [Fintype n] [DecidableEq n] in
/-- Scaling does not change an angle: `tan² ∠(u, c x) = tan² ∠(u, x)` for `c ≠ 0`. Helper for
`power-iteration`. -/
theorem overlapTangentSq_smul [Fintype n] (u x : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    overlapTangentSq u (c • x) = overlapTangentSq u x := by
  simp only [overlapTangentSq, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  by_cases hx : u ⬝ᵥ x = 0
  · simp [hx]
  · field_simp

omit [DecidableEq n] in
/-- Scaling does not change the Rayleigh quotient: `ρ(c x) = ρ(x)` for `c ≠ 0`. Helper for
`power-iteration`. -/
theorem rayleighQuotient_smul (A : Matrix n n ℝ) (x : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    rayleighQuotient A (c • x) = rayleighQuotient A x := by
  simp only [rayleighQuotient_def, RCLike.re_to_real, quadForm_def, star_trivial,
    Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  by_cases hx : x ⬝ᵥ x = 0
  · simp [hx]
  · field_simp

omit [DecidableEq n] in
/-- Normalising a positive multiple: `c w/‖c w‖ = w/‖w‖` for `c > 0`. Helper for
`power-iteration`. -/
theorem inv_norm_smul_smul (w : n → ℝ) {c : ℝ} (hc : 0 < c) :
    ‖WithLp.toLp 2 (c • w)‖⁻¹ • (c • w) = ‖WithLp.toLp 2 w‖⁻¹ • w := by
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
    smul_smul, mul_inv, mul_comm c⁻¹ ‖WithLp.toLp 2 w‖⁻¹,
    mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- Normalisation is bookkeeping: `k + 1` normalised power steps from `x₀` give
`A^{k+1} x₀/‖A^{k+1} x₀‖` (both sides `0` if `A^{k+1} x₀ = 0`). Source: Trefethen–Bau (1997)
[`tb97`], Lect. 27. Helper for `power-iteration`. -/
theorem powerStep_iterate_succ (A : Matrix n n ℝ) (x₀ : n → ℝ) (k : ℕ) :
    (powerStep A)^[k + 1] x₀ =
      ‖WithLp.toLp 2 (powerIterate A x₀ (k + 1))‖⁻¹ • powerIterate A x₀ (k + 1) := by
  induction k with
  | zero => simp [powerStep, powerIterate]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    set v := powerIterate A x₀ (k + 1)
    have hv : powerIterate A x₀ (k + 1 + 1) = A *ᵥ v := powerIterate_succ A x₀ (k + 1)
    rw [hv, powerStep, Matrix.mulVec_smul]
    set c := ‖WithLp.toLp 2 v‖⁻¹
    by_cases hc : c = 0
    · have hv0 : v = 0 := by
        have h1 : ‖WithLp.toLp 2 v‖ = 0 := inv_eq_zero.1 hc
        have h2 := norm_eq_zero.1 h1
        simpa using congrArg WithLp.ofLp h2
      simp [hv0]
    · exact inv_norm_smul_smul _ (lt_of_le_of_ne (inv_nonneg.2 (norm_nonneg _)) (Ne.symm hc))

/-! ### Eigen-coordinates of powers -/

/-- Eigen-coordinates of powers of a spectral multiplier: if `uᵢ ⬝ (B y) = fᵢ (uᵢ ⬝ y)` for all
`y`, then `uᵢ ⬝ (B^k v) = fᵢ^k (uᵢ ⬝ v)`. Helper for `power-iteration`, `inverse-iteration`. -/
theorem eigenvectorBasis_dotProduct_pow_mulVec_eq {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    {f : n → ℝ} (hB : ∀ i y, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (B *ᵥ y) =
      f i * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ y)) (k : ℕ) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((B ^ k) *ᵥ v) =
      f i ^ k * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hB, ih, pow_succ']; ring

/-! ### Power iteration -/

/-- **Power iteration, angle bound.** Let `A` be real symmetric, `u` a unit eigenvector for the
eigenvalue `λ₁ = λ_{i₀}` at sorted position `i₀`, and `|λᵢ| ≤ ρ` at every other sorted
position. Then `tan² ∠(u, A^k x₀) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u, x₀)`. No hypothesis on `x₀` or on
the gap is needed for the inequality (a right angle has the junk value `0` on both sides); it
is informative when `ρ < |λ₁|` and `u ⬝ x₀ ≠ 0`. Source: Trefethen–Bau (1997) [`tb97`],
Thm 27.1; Golub–Van Loan (2013) [`gvl13`], Thm 8.2.1. Deviations: squared tangents; `ρ` any
bound on the other eigenvalues (T&B: `ρ = |λ₂|`); unnormalised iterates
(`overlapTangentSq_powerStep_iterate_le` for the normalised ones).
atlas: power-iteration -/
theorem overlapTangentSq_powerIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {ρ : ℝ} (hρ : ∀ i, i ≠ i₀ → |hA.eigenvalues₀ i| ≤ ρ)
    (x₀ : n → ℝ) (k : ℕ) :
    overlapTangentSq u (powerIterate A x₀ k) ≤
      (ρ / |hA.eigenvalues₀ i₀|) ^ (2 * k) * overlapTangentSq u x₀ := by
  have hM : ∀ i, i ≠ i₀ → |(X ^ k : ℝ[X]).eval (hA.eigenvalues₀ i)| ≤ ρ ^ k := fun i hi => by
    rw [eval_pow, eval_X, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hρ i hi) k
  have h := overlapTangentSq_aeval_mulVec_le hA hu hu1 hM x₀
  rw [aeval_X_pow, eval_pow, eval_X] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← div_pow, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, div_pow, div_pow ρ, sq_abs]

/-- **Power iteration, normalised iterates.** Under the hypotheses of
`overlapTangentSq_powerIterate_le`, the textbook iterates `x_k = (powerStep A)^[k] x₀` (normalised at
every step) satisfy `tan² ∠(u, x_k) ≤ (ρ/|λ₁|)^{2k} tan² ∠(u, x₀)`. Source: Trefethen–Bau
(1997) [`tb97`], Thm 27.1.
atlas: power-iteration -/
theorem overlapTangentSq_powerStep_iterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {ρ : ℝ} (hρ : ∀ i, i ≠ i₀ → |hA.eigenvalues₀ i| ≤ ρ)
    (x₀ : n → ℝ) (k : ℕ) :
    overlapTangentSq u ((powerStep A)^[k] x₀) ≤
      (ρ / |hA.eigenvalues₀ i₀|) ^ (2 * k) * overlapTangentSq u x₀ := by
  cases k with
  | zero => simp
  | succ k =>
    rw [powerStep_iterate_succ]
    set v := powerIterate A x₀ (k + 1)
    by_cases hc : ‖WithLp.toLp 2 v‖⁻¹ = 0
    · rw [hc, zero_smul]
      have h0 : overlapTangentSq u 0 = 0 := by simp [overlapTangentSq]
      rw [h0]
      exact mul_nonneg ((even_two_mul _).pow_nonneg _) (overlapTangentSq_nonneg u x₀)
    · rw [overlapTangentSq_smul _ _ hc]
      exact overlapTangentSq_powerIterate_le hA hu hu1 hρ x₀ (k + 1)

/-- **Rayleigh quotient error from the angle.** For real symmetric `A`, a unit eigenvector `u`
for the eigenvalue `λ₁ = λ_{i₀}` at sorted position `i₀`, `D` with `|λᵢ − λ₁| ≤ D` for every
`i` (e.g. `D = λ_max − λ_min`), and `x` with `u ⬝ x ≠ 0`: `|ρ(x) − λ₁| ≤ D tan² ∠(u, x)`.
Proof: split `x = (u ⬝ x) u + w` with `w ⟂ u`; then
`ρ(x) − λ₁ = (wᵀAw − λ₁ ‖w‖²)/‖x‖²` and `|wᵀAw − λ₁ ‖w‖²| ≤ D ‖w‖²`. Source:
Trefethen–Bau (1997) [`tb97`], Thm 27.1 (second bound) and Lect. 27 (`ρ(x) − λ = O(‖x − u‖²)`);
Saad (2011) [`saad11`], §4.1. Deviation: explicit constant `D` instead of `O(·)`; two-sided.
atlas: power-iteration -/
theorem abs_rayleighQuotient_sub_le_mul_overlapTangentSq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {D : ℝ}
    (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues₀ i₀| ≤ D) {x : n → ℝ} (hx : u ⬝ᵥ x ≠ 0) :
    |rayleighQuotient A x - hA.eigenvalues₀ i₀| ≤ D * overlapTangentSq u x := by
  set L := hA.eigenvalues₀ i₀ with hLdef
  set c := u ⬝ᵥ x with hcdef
  set w := x - c • u with hwdef
  have huu : u ⬝ᵥ u = 1 := by
    rw [← norm_toLp_sq_eq_dotProduct_self, hu1, one_pow]
  have huw : u ⬝ᵥ w = 0 := by
    simp only [hwdef, dotProduct_sub, dotProduct_smul, huu, smul_eq_mul, mul_one, ← hcdef, sub_self]
  set N := w ⬝ᵥ w with hNdef
  have hxw : x = c • u + w := by simp [hwdef]
  have hxx : x ⬝ᵥ x = c ^ 2 + N := by
    rw [hxw, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul, smul_dotProduct,
      dotProduct_smul, smul_dotProduct, huu, dotProduct_comm w u, huw]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hsymm : ∀ y z : n → ℝ, y ⬝ᵥ (A *ᵥ z) = (A *ᵥ y) ⬝ᵥ z := fun y z => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (Matrix.isHermitian_iff_isSymm.mp hA).eq]
  have hxAx : x ⬝ᵥ (A *ᵥ x) = L * c ^ 2 + w ⬝ᵥ (A *ᵥ w) := by
    have hAu : ∀ z : n → ℝ, u ⬝ᵥ (A *ᵥ z) = L * (u ⬝ᵥ z) := fun z => by
      rw [hsymm, hu, smul_dotProduct, smul_eq_mul]
    rw [hxw]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hAu]
    rw [hu, dotProduct_smul, dotProduct_comm w u, huw, huu]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  -- the orthogonal part in eigen-coordinates
  have hdiff : w ⬝ᵥ (A *ᵥ w) - L * N =
      ∑ i, (hA.eigenvalues i - L) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) ^ 2 := by
    have h := quadForm_eq_sum_eigenvalues hA w
    rw [quadForm_def, star_trivial] at h
    rw [h, hNdef, ← sum_sq_eigenvectorBasis_dotProduct hA w, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : |w ⬝ᵥ (A *ᵥ w) - L * N| ≤ D * N := by
    rw [hdiff, hNdef, ← sum_sq_eigenvectorBasis_dotProduct hA w, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w))]
    exact mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
  have hc1 : 0 < c ^ 2 := by positivity
  have hN : 0 ≤ N := dotProduct_self_nonneg w
  have hD0 : 0 ≤ D := by
    have := hD (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq, sub_self, abs_zero] at this
    exact this
  have hpos : 0 < x ⬝ᵥ x := by rw [hxx]; exact add_pos_of_pos_of_nonneg hc1 hN
  have hq : rayleighQuotient A x - L = (x ⬝ᵥ (A *ᵥ x) - L * (x ⬝ᵥ x)) / (x ⬝ᵥ x) := by
    rw [rayleighQuotient_def, RCLike.re_to_real, RCLike.re_to_real, quadForm_def, star_trivial,
      sub_div, mul_div_assoc, div_self hpos.ne', mul_one]
  rw [overlapTangentSq_of_norm_eq_one hu1, hq, hxAx, hxx, ← hcdef, abs_div,
    abs_of_pos (add_pos_of_pos_of_nonneg hc1 hN),
    show L * c ^ 2 + w ⬝ᵥ (A *ᵥ w) - L * (c ^ 2 + N) = w ⬝ᵥ (A *ᵥ w) - L * N by ring,
    show c ^ 2 + N - c ^ 2 = N by ring]
  calc _ ≤ D * N / (c ^ 2 + N) := div_le_div_of_nonneg_right hbound (by positivity)
    _ ≤ D * N / c ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hD0 hN) hc1 (by linarith)
    _ = D * (N / c ^ 2) := mul_div_assoc _ _ _

/-- **Power iteration, Rayleigh quotient.** For real symmetric `A`, a unit eigenvector `u` of
`λ₁ = λ_{i₀} ≠ 0`, `|λᵢ| ≤ ρ` at the other sorted positions, `|λᵢ − λ₁| ≤ D` for all `i`, and
`u ⬝ x₀ ≠ 0`: `|ρ(A^k x₀) − λ₁| ≤ D (ρ/|λ₁|)^{2k} tan² ∠(u, x₀)`, the squared rate of the
angle. Source: Trefethen–Bau (1997) [`tb97`], Thm 27.1; Golub–Van Loan (2013) [`gvl13`],
Thm 8.2.1. Deviation: explicit constant `D` (T&B: `O(|λ₂/λ₁|^{2k})`).
atlas: power-iteration -/
theorem abs_rayleighQuotient_powerIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) (hl : hA.eigenvalues₀ i₀ ≠ 0) {ρ D : ℝ}
    (hρ : ∀ i, i ≠ i₀ → |hA.eigenvalues₀ i| ≤ ρ)
    (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues₀ i₀| ≤ D) {x₀ : n → ℝ} (hx₀ : u ⬝ᵥ x₀ ≠ 0)
    (k : ℕ) :
    |rayleighQuotient A (powerIterate A x₀ k) - hA.eigenvalues₀ i₀| ≤
      D * ((ρ / |hA.eigenvalues₀ i₀|) ^ (2 * k) * overlapTangentSq u x₀) := by
  have hD0 : 0 ≤ D := by
    have := hD (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq, sub_self, abs_zero] at this
    exact this
  have hxk : u ⬝ᵥ powerIterate A x₀ k ≠ 0 := by
    have h := dotProduct_aeval_mulVec_of_mulVec_eq_smul hA hu (X ^ k) x₀
    rw [aeval_X_pow, eval_pow, eval_X] at h
    rw [powerIterate, h]
    exact mul_ne_zero (pow_ne_zero _ hl) hx₀
  exact (abs_rayleighQuotient_sub_le_mul_overlapTangentSq hA hu hu1 hD hxk).trans
    (mul_le_mul_of_nonneg_left (overlapTangentSq_powerIterate_le hA hu hu1 hρ x₀ k) hD0)

/-! ### Inverse iteration -/

/-- The `k`-th (unnormalised) inverse-iteration iterate with shift `μ`: power iteration on the
resolvent, `(A − μI)^{-k} x₀`. Junk (Mathlib's inverse `0`) when `μ` is an eigenvalue.
Source: Trefethen–Bau (1997) [`tb97`], Alg. 27.2; Golub–Van Loan (2013) [`gvl13`], §8.2.2.
Helper for `inverse-iteration`. -/
def inverseIterate (A : Matrix n n ℝ) (μ : ℝ) (x₀ : n → ℝ) (k : ℕ) : n → ℝ :=
  powerIterate (A - μ • (1 : Matrix n n ℝ))⁻¹ x₀ k

/-- The shifted matrix in eigen-coordinates: `uᵢ ⬝ ((A − μI) y) = (λᵢ − μ)(uᵢ ⬝ y)`. Helper for
`inverse-iteration`. -/
theorem eigenvectorBasis_dotProduct_sub_smul_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (μ : ℝ) (y : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((A - μ • (1 : Matrix n n ℝ)) *ᵥ y) =
      (hA.eigenvalues i - μ) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ y) := by
  have h := eigenvectorBasis_dotProduct_aeval_mulVec hA (X - C μ) y i
  simpa [Algebra.algebraMap_eq_smul_one] using h

/-- The resolvent shares the eigenvectors of `A`: if `μ` is not an eigenvalue,
`uᵢ ⬝ ((A − μI)⁻¹ v) = (λᵢ − μ)⁻¹ (uᵢ ⬝ v)`. Source: Trefethen–Bau (1997) [`tb97`], Lect. 27.
Helper for `inverse-iteration`. -/
theorem eigenvectorBasis_dotProduct_inv_sub_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : ∀ i, hA.eigenvalues i ≠ μ) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ ((A - μ • (1 : Matrix n n ℝ))⁻¹ *ᵥ v) =
      (hA.eigenvalues i - μ)⁻¹ * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  set B := A - μ • (1 : Matrix n n ℝ)
  have hker : ∀ y, B *ᵥ y = 0 → y = 0 := fun y hy => by
    have hc : ∀ j, (hA.eigenvectorBasis j : n → ℝ) ⬝ᵥ y = 0 := fun j => by
      have h := eigenvectorBasis_dotProduct_sub_smul_mulVec hA μ y j
      rw [show B *ᵥ y = 0 from hy, dotProduct_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (sub_ne_zero.2 (hμ j))
    have hyy := sum_sq_eigenvectorBasis_dotProduct hA y
    simp only [hc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at hyy
    exact dotProduct_self_eq_zero.1 hyy.symm
  have hinj : Function.Injective B.mulVec := fun y z h =>
    sub_eq_zero.1 (hker _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hB : IsUnit B := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hBB : B *ᵥ (B⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).1 hB),
      Matrix.one_mulVec]
  have h := eigenvectorBasis_dotProduct_sub_smul_mulVec hA μ (B⁻¹ *ᵥ v) i
  rw [hBB] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 (hμ i)), one_mul]

/-- **Inverse iteration, angle bound.** Let `A` be real symmetric, `μ` not an eigenvalue, `u` a
unit eigenvector for the eigenvalue `λ_{i₀}` at sorted position `i₀` (the one closest to `μ`),
and `d > 0` with `|λᵢ − μ| ≥ d` at every other sorted position (`d` the distance of the second
closest, T&B's `|μ − λ_K|`). Then the inverse-iteration iterates satisfy
`tan² ∠(u, (A − μI)^{-k} x₀) ≤ (|λ_{i₀} − μ|/d)^{2k} tan² ∠(u, x₀)`. Source:
Trefethen–Bau (1997) [`tb97`], Thm 27.2; Golub–Van Loan (2013) [`gvl13`], §8.2.2.
Deviations: squared tangents; unnormalised iterates (normalisation is bookkeeping,
`overlapTangentSq_smul`).
atlas: inverse-iteration -/
theorem overlapTangentSq_inverseIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (hμ : ∀ i, hA.eigenvalues i ≠ μ) {i₀ : Fin (Fintype.card n)} {u : n → ℝ}
    (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) {d : ℝ} (hd : 0 < d)
    (hdJ : ∀ i, i ≠ i₀ → d ≤ |hA.eigenvalues₀ i - μ|) (x₀ : n → ℝ) (k : ℕ) :
    overlapTangentSq u (inverseIterate A μ x₀ k) ≤
      (|hA.eigenvalues₀ i₀ - μ| / d) ^ (2 * k) * overlapTangentSq u x₀ := by
  have hf := eigenvectorBasis_dotProduct_pow_mulVec_eq hA (B := (A - μ • (1 : Matrix n n ℝ))⁻¹)
    (f := fun i => (hA.eigenvalues i - μ)⁻¹)
    (fun i y => eigenvectorBasis_dotProduct_inv_sub_mulVec hA hμ y i) k
  have hM : ∀ i, i ≠ i₀ → |(hA.eigenvalues₀ i - μ)⁻¹ ^ k| ≤ d⁻¹ ^ k := fun i hi => by
    rw [abs_pow, abs_inv]
    exact pow_le_pow_left₀ (inv_nonneg.2 (abs_nonneg _)) (inv_anti₀ hd (hdJ i hi)) k
  have h := overlapTangentSq_le_of_forall_eigenvectorBasis_dotProduct_eq hA hu hu1
    (g := fun x => (x - μ)⁻¹ ^ k) hM (fun i => hf x₀ i)
  refine h.trans (le_of_eq ?_)
  congr 1
  have hJ : hA.eigenvalues₀ i₀ - μ ≠ 0 := by
    have := hμ (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq] at this
    exact sub_ne_zero.2 this
  rw [← div_pow, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, div_pow, div_pow |_|, sq_abs]
  congr 1
  field_simp

/-- **Inverse iteration, Rayleigh quotient.** Under the hypotheses of
`overlapTangentSq_inverseIterate_le`, with `|λᵢ − λ_{i₀}| ≤ D` for all `i` and `u ⬝ x₀ ≠ 0`:
`|ρ(x_k) − λ_{i₀}| ≤ D (|λ_{i₀} − μ|/d)^{2k} tan² ∠(u, x₀)`. Source: Trefethen–Bau (1997)
[`tb97`], Thm 27.2 (second bound).
atlas: inverse-iteration -/
theorem abs_rayleighQuotient_inverseIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {μ : ℝ} (hμ : ∀ i, hA.eigenvalues i ≠ μ) {i₀ : Fin (Fintype.card n)} {u : n → ℝ}
    (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) {d D : ℝ} (hd : 0 < d)
    (hdJ : ∀ i, i ≠ i₀ → d ≤ |hA.eigenvalues₀ i - μ|)
    (hD : ∀ i, |hA.eigenvalues i - hA.eigenvalues₀ i₀| ≤ D) {x₀ : n → ℝ} (hx₀ : u ⬝ᵥ x₀ ≠ 0)
    (k : ℕ) :
    |rayleighQuotient A (inverseIterate A μ x₀ k) - hA.eigenvalues₀ i₀| ≤
      D * ((|hA.eigenvalues₀ i₀ - μ| / d) ^ (2 * k) * overlapTangentSq u x₀) := by
  have hD0 : 0 ≤ D := by
    have := hD (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq, sub_self, abs_zero] at this
    exact this
  have hxk : u ⬝ᵥ inverseIterate A μ x₀ k ≠ 0 := by
    have hf := eigenvectorBasis_dotProduct_pow_mulVec_eq hA
      (B := (A - μ • (1 : Matrix n n ℝ))⁻¹) (f := fun i => (hA.eigenvalues i - μ)⁻¹)
      (fun i y => eigenvectorBasis_dotProduct_inv_sub_mulVec hA hμ y i) k
    have h := dotProduct_eq_mul_dotProduct_of_forall_eigenvectorBasis_dotProduct_eq hA hu
      (g := fun x => (x - μ)⁻¹ ^ k) (fun i => hf x₀ i)
    rw [inverseIterate, powerIterate, h]
    have hJ : hA.eigenvalues₀ i₀ - μ ≠ 0 := by
      have := hμ (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
      rw [hA.eigenvalues_equivOfCardEq] at this
      exact sub_ne_zero.2 this
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hJ)) hx₀
  exact (abs_rayleighQuotient_sub_le_mul_overlapTangentSq hA hu hu1 hD hxk).trans
    (mul_le_mul_of_nonneg_left (overlapTangentSq_inverseIterate_le hA hμ hu hu1 hd hdJ x₀ k) hD0)

/-! ### Bridge to principal angles -/

omit [DecidableEq n] in
/-- The total one-column inverse-overlap norm squared is the vector's total
squared overlap tangent. Both algebraic expressions are zero when the overlap
vanishes. Source: Saad (2011), §5.2 and §6.6.1; matrix-toolkit derivations, §1.
atlas: principal-angles-def (partial) -/
theorem sq_overlapTangentNorm_replicateCol_eq_overlapTangentSq {u : n → ℝ}
    (hu : ‖WithLp.toLp 2 u‖ = 1) (x : n → ℝ) :
    overlapTangentNorm (Matrix.replicateCol Unit u) (Matrix.replicateCol Unit x) ^ 2 =
      overlapTangentSq u x := by
  have hu1 : u ⬝ᵥ u = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hu, one_pow]
  let a : ℝ := u ⬝ᵥ x
  have hG : (Matrix.replicateCol Unit u)ᵀ * Matrix.replicateCol Unit x =
      Matrix.diagonal (fun _ : Unit => a) := by
    ext i j
    cases i
    cases j
    simp [Matrix.mul_apply, dotProduct, a]
  have hR : projResidual (Matrix.replicateCol Unit u) (Matrix.replicateCol Unit x) *
      ((Matrix.replicateCol Unit u)ᵀ * Matrix.replicateCol Unit x)⁻¹ =
      Matrix.replicateCol Unit (a⁻¹ • (x - a • u)) := by
    rw [hG, Matrix.inv_subsingleton]
    ext i j
    cases j
    simp [projResidual, Matrix.mul_apply, dotProduct, a, Ring.inverse_eq_inv]
    ring
  have hr : (x - a • u) ⬝ᵥ (x - a • u) = x ⬝ᵥ x - a ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hu1, dotProduct_comm x u]
    change x ⬝ᵥ x - a * a - a * (a - a * 1) = x ⬝ᵥ x - a ^ 2
    ring
  rw [overlapTangentNorm, hR, specNorm_sq_replicateCol, norm_toLp_sq_eq_dotProduct_self]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hr, overlapTangentSq, hu1]
  change a⁻¹ * (a⁻¹ * (x ⬝ᵥ x - a ^ 2)) = (1 * (x ⬝ᵥ x) - a ^ 2) / a ^ 2
  simp only [div_eq_mul_inv]
  ring

end NLAlib

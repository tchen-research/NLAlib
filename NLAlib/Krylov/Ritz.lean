import NLAlib.Krylov.GaussQuadrature
import NLAlib.Polynomial.Approximation

/-!
# Ritz values: gap-free Lanczos eigenvalue bound

For a symmetric positive semidefinite `A` with top eigenvalue `λ₁` (eigenvector `u₁`) and a
starting vector `b` with `u₁ ⬝ b ≠ 0`, the Krylov space `K_q(A, b)` contains a vector `y = p(A) b`
whose Rayleigh quotient is within `ε λ₁ + λ₁ (2/(1 + √(2γ))^{q−1})² ‖b‖²/(u₁ ⬝ b)²` of `λ₁`,
`γ = ε/(1 − ε)`; `p` is the Chebyshev amplifier (`NLAlib.chebyshevAmplifier`). Consequently
the largest Ritz value (largest eigenvalue of `QᵀAQ` for an orthonormal `Q` whose range contains
`K_q`) obeys the same bound. No eigenvalue gap is assumed.

## Main results

* `NLAlib.exists_mem_krylovSpace_sub_rayleigh_le`: the Krylov vector.
* `NLAlib.dotProduct_mulVec_le_of_mem_range`: Rayleigh quotients over `range Q` are bounded by
  any upper bound on the Ritz values.
* `NLAlib.exists_eigenvalues_transpose_mul_mul_ge`: the gap-free Ritz-value bound.

Source: Musco–Musco (2015) [`mm15`], Lem. 4–5 and proof of Thm 1 (gap-free block Krylov);
Saad (2011), *Numerical Methods for Large Eigenvalue Problems*, §6.6 (Kaniel–Paige–Saad).
Atlas: `ritz-value-bounds` (new, gap-free form); uses `chebyshev-amplifier`,
`polynomial-spectral-bound`, `krylov-subspace`.
Deviation: the gap-dependent Kaniel–Paige–Saad form is not stated.
-/

noncomputable section

open scoped Matrix
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A Krylov vector with near-maximal Rayleigh quotient (gap-free).** Let `A` be symmetric
with eigenvalues in `[0, λ₁]`, `λ₁ = λ_{i₁}`, let `0 < ε < 1`, `q ≥ 1`, and `c₁ = u_{i₁} ⬝ b ≠ 0`.
Then there is a nonzero `y ∈ K_q(A, b)` with
`λ₁ ‖y‖² − yᵀAy ≤ (ε λ₁ + λ₁ (2/(1 + √(2γ))^{q−1})² ‖b‖²/c₁²) ‖y‖²`, `γ = ε/(1 − ε)`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4–5 and proof of Thm 1 (single-vector case).
Atlas: `ritz-value-bounds`; uses `chebyshev-amplifier`, `polynomial-spectral-bound`,
`krylov-subspace`. -/
theorem exists_mem_krylovSpace_sub_rayleigh_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i) {i₁ : n} (htop : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₁)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (b : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) :
    ∃ y ∈ krylovSpace A b q, y ≠ 0 ∧
      hA.eigenvalues i₁ * (y ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤
        (ε * hA.eigenvalues i₁ + hA.eigenvalues i₁ *
          (2 / (1 + √(2 * (ε / (1 - ε)))) ^ (q - 1)) ^ 2 * (b ⬝ᵥ b) /
            ((hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b) ^ 2) * (y ⬝ᵥ y) := by
  set L := hA.eigenvalues i₁
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ b with hcdef
  have hc1 : 0 < c i₁ ^ 2 := by positivity
  have hbb : b ⬝ᵥ b = ∑ i, c i ^ 2 := (sum_sq_eigenvectorBasis_dotProduct hA b).symm
  have hL : 0 ≤ L := hpsd i₁
  set M := 2 / (1 + √(2 * (ε / (1 - ε)))) ^ (q - 1)
  rcases hL.lt_or_eq with hLpos | hL0
  · -- the amplifier `p = T_{q-1}(x/α)/T_{q-1}(1+γ)`, `α = (1-ε)L`, `γ = ε/(1-ε)`
    set α := (1 - ε) * L
    set γ := ε / (1 - ε)
    have hα : 0 < α := mul_pos (by linarith) hLpos
    have hγ : 0 ≤ γ := div_nonneg hε0.le (by linarith)
    have h1ε : 1 - ε ≠ 0 := (by linarith : (0 : ℝ) < 1 - ε).ne'
    have hαγ : α * (1 + γ) = L := by
      simp only [α, γ]; field_simp; ring
    set p := chebyshevAmplifier α γ (q - 1)
    have hp1 : p.eval L = 1 := by rw [← hαγ]; exact eval_chebyshevAmplifier_self _ hα hγ
    set y := aeval A p *ᵥ b
    have hy : y ∈ krylovSpace A b q := (mem_krylovSpace_iff_degree A b q y).2
      ⟨p, (degree_chebyshevAmplifier_le α γ (q - 1)).trans_lt (by exact_mod_cast (by omega)),
        rfl⟩
    have hyy : y ⬝ᵥ y = ∑ i, p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2 :=
      dotProduct_aeval_mulVec_self_eq_sum hA p b
    have hyAy : y ⬝ᵥ (A *ᵥ y) = ∑ i, hA.eigenvalues i * p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2 :=
      quadForm_aeval_mulVec_eq_sum hA p b
    have hylow : c i₁ ^ 2 ≤ y ⬝ᵥ y := by
      rw [hyy]
      have := Finset.single_le_sum (f := fun i => p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ i₁)
      simpa [L, hp1] using this
    refine ⟨y, hy, fun h0 => ?_, ?_⟩
    · rw [h0, dotProduct_zero] at hylow; linarith
    -- termwise bound
    have hterm : ∀ i, (L - hA.eigenvalues i) * (p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2) ≤
        ε * L * (p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2) + L * M ^ 2 * c i ^ 2 := fun i => by
      have hl0 := hpsd i
      have hlL := htop i
      have hpc : 0 ≤ p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2 := by positivity
      rcases lt_or_ge α (hA.eigenvalues i) with hbig | hsmall
      · have : L - hA.eigenvalues i ≤ ε * L := by simp only [α] at hbig; linarith
        have h1 := mul_le_mul_of_nonneg_right this hpc
        have h2 : 0 ≤ L * M ^ 2 * c i ^ 2 := by positivity
        linarith
      · have hmem : hA.eigenvalues i ∈ Set.Icc (-α) α := ⟨by linarith, hsmall⟩
        have hpM := abs_eval_chebyshevAmplifier_le (q - 1) hα hγ hmem
        have hM0 : 0 ≤ M := by positivity
        have hsq : p.eval (hA.eigenvalues i) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpM 2
        have h1 : (L - hA.eigenvalues i) * (p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2) ≤
            L * (M ^ 2 * c i ^ 2) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) hpc hL
        have h2 : 0 ≤ ε * L * (p.eval (hA.eigenvalues i) ^ 2 * c i ^ 2) := by positivity
        nlinarith
    have hsum : L * (y ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) := by
      rw [hyy, hyAy, hbb, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hterm i
      linarith
    have hbound : L * M ^ 2 * (b ⬝ᵥ b) ≤ L * M ^ 2 * (b ⬝ᵥ b) / c i₁ ^ 2 * (y ⬝ᵥ y) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
      exact mul_le_mul_of_nonneg_left hylow
        (mul_nonneg (mul_nonneg hL (sq_nonneg M)) (dotProduct_self_nonneg b))
    calc L * (y ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) := hsum
      _ ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) / c i₁ ^ 2 * (y ⬝ᵥ y) := by linarith
      _ = (ε * L + L * M ^ 2 * (b ⬝ᵥ b) / c i₁ ^ 2) * (y ⬝ᵥ y) := by ring
  · -- `λ₁ = 0`: every eigenvalue vanishes; take `y = b`
    have hall : ∀ i, hA.eigenvalues i = 0 := fun i =>
      le_antisymm (hL0 ▸ htop i) (hpsd i)
    have hbAb : b ⬝ᵥ (A *ᵥ b) = 0 := by
      have := quadForm_eq_sum_eigenvalues hA b
      simp only [quadForm, hall, zero_mul, Finset.sum_const_zero] at this
      exact this
    refine ⟨b, ?_, fun h0 => ?_, ?_⟩
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact self_mem_krylovSpace_succ A b q'
    · exact hb (by rw [h0, dotProduct_zero])
    · rw [← hL0, hbAb]; simp

variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq n] in
/-- Rayleigh quotients over `range Q` are bounded by any upper bound `θ` on the eigenvalues of
`QᵀAQ` (the Ritz values), for `Q` with orthonormal columns: `yᵀAy ≤ θ ‖y‖²` for `y ∈ range Q`.
Source: Parlett (1998), Thm 11.4.1 (Rayleigh–Ritz). Atlas: `ritz-value-bounds` (helper). -/
theorem dotProduct_mulVec_le_of_mem_range {A : Matrix n n ℝ} {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hT : (Qᵀ * A * Q).IsHermitian) {θ : ℝ}
    (hθ : ∀ j, hT.eigenvalues j ≤ θ) {y : n → ℝ} (hy : y ∈ LinearMap.range Q.mulVecLin) :
    y ⬝ᵥ (A *ᵥ y) ≤ θ * (y ⬝ᵥ y) := by
  obtain ⟨z, rfl⟩ := hy
  simp only [Matrix.mulVecLin_apply]
  have h := dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues hT hθ z
  rw [mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ]
  calc (Q *ᵥ z) ⬝ᵥ (A *ᵥ (Q *ᵥ z)) = z ⬝ᵥ ((Qᵀ * A * Q) *ᵥ z) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Qᵀ,
          Matrix.vecMul_transpose]
    _ ≤ θ * (z ⬝ᵥ z) := h

/-- **Gap-free Ritz-value bound.** Let `A` be symmetric with eigenvalues in `[0, λ₁]`,
`λ₁ = λ_{i₁}`, `0 < ε < 1`, `q ≥ 1`, `u_{i₁} ⬝ b ≠ 0`, and `Q` with orthonormal columns and
`K_q(A, b) ⊆ range Q` (e.g. the Lanczos basis). Then some Ritz value `θ_j` (eigenvalue of
`QᵀAQ`) satisfies
`λ₁ − θ_j ≤ ε λ₁ + λ₁ (2/(1 + √(2γ))^{q−1})² ‖b‖²/(u_{i₁} ⬝ b)²`, `γ = ε/(1 − ε)`.
Source: Musco–Musco (2015) [`mm15`], Thm 1 (single-vector, gap-free); Kuczyński–Woźniakowski
(1992) [`kw92`] for the random-start analysis. Atlas: `ritz-value-bounds`; uses
`chebyshev-amplifier`, `polynomial-spectral-bound`, `krylov-subspace`. -/
theorem exists_eigenvalues_transpose_mul_mul_ge {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i) {i₁ : n} (htop : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₁)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (b : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin)
    (hT : (Qᵀ * A * Q).IsHermitian) :
    ∃ j, hA.eigenvalues i₁ - hT.eigenvalues j ≤
      ε * hA.eigenvalues i₁ + hA.eigenvalues i₁ *
        (2 / (1 + √(2 * (ε / (1 - ε)))) ^ (q - 1)) ^ 2 * (b ⬝ᵥ b) /
          ((hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b) ^ 2 := by
  obtain ⟨y, hyK, hy0, hy⟩ :=
    exists_mem_krylovSpace_sub_rayleigh_le hA hpsd htop hε0 hε1 b hq hb
  obtain ⟨z, hz⟩ := hK hyK
  have hk : Nonempty k := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hy0
    rw [← hz]
    ext r
    simp [Matrix.mulVec, dotProduct]
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ hT.eigenvalues Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hR := dotProduct_mulVec_le_of_mem_range hQ hT (θ := hT.eigenvalues j)
    (fun j' => hj j' (Finset.mem_univ _)) (hK hyK)
  have hpos : 0 < y ⬝ᵥ y := lt_of_le_of_ne (dotProduct_self_nonneg y)
    (Ne.symm fun h => hy0 (dotProduct_self_eq_zero.mp h))
  set B := ε * hA.eigenvalues i₁ + hA.eigenvalues i₁ *
    (2 / (1 + √(2 * (ε / (1 - ε)))) ^ (q - 1)) ^ 2 * (b ⬝ᵥ b) /
      ((hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b) ^ 2
  have : (hA.eigenvalues i₁ - hT.eigenvalues j) * (y ⬝ᵥ y) ≤ B * (y ⬝ᵥ y) := by nlinarith
  exact le_of_mul_le_mul_right this hpos

end NLAlib

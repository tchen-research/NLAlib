import NLAlib.Krylov.GaussQuadrature
import NLAlib.Polynomial.Approximation

/-!
# Ritz values: gap-free and gap-dependent Lanczos eigenvalue bounds

**Gap-free.** For a symmetric positive semidefinite `A` with top eigenvalue `λ₁` (eigenvector
`u₁`) and a starting vector `b` with `u₁ ⬝ b ≠ 0`, the Krylov space `K_q(A, b)` contains a vector
`y = p(A) b` whose Rayleigh quotient is within `ε λ₁ + λ₁ (2/(1 + √(2γ))^{q−1})² ‖b‖²/(u₁ ⬝ b)²`
of `λ₁`, `γ = ε/(1 − ε)`; `p` is the Chebyshev amplifier (`NLAlib.chebyshevAmplifier`).
Consequently the largest Ritz value (largest eigenvalue of `QᵀAQ` for an orthonormal `Q` whose
range contains `K_q`) obeys the same bound. No eigenvalue gap is assumed. This is Musco–Musco's
bound (MM15, Lem. 4 and Thm 1); it is not Saad's Thm 6.4.

**Gap-dependent (Kaniel–Paige–Saad).** If every eigenvalue other than `λ₁` lies in `[a, c]`,
`a < c < λ₁`, then `K_{q+1}(A, b)` contains `x` with
`tan² ∠(u₁, x) ≤ tan² ∠(u₁, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`, and the largest Ritz
value satisfies `0 ≤ λ₁ − θ₁ ≤ (λ₁ − a) tan² ∠(u₁, b) / T_q(1 + 2γ)²` (Saad 2011, Thm 6.4).
Both are corollaries of polynomial forms that take any `p` and a bound `M` on `|p(λᵢ)|`, `i ≠ i₁`.

## Main results

* `NLAlib.exists_mem_krylovSpace_sub_rayleigh_le`: the gap-free Krylov vector.
* `NLAlib.dotProduct_mulVec_le_of_mem_range`: Rayleigh quotients over `range Q` are bounded by
  any upper bound on the Ritz values.
* `NLAlib.exists_eigenvalues_transpose_mul_mul_ge`: the gap-free Ritz-value bound.
* `NLAlib.tanSqAngle`, `NLAlib.tanSqAngle_aeval_mulVec_le`: the squared tangent of an angle and
  the polynomial form of the eigenvector-angle bound.
* `NLAlib.exists_mem_krylovSpace_tanSqAngle_le` (and `…_two_div_pow`): the Chebyshev angle bound.
* `NLAlib.eigenvalues_transpose_mul_mul_le`,
  `NLAlib.eigenvalues_sub_eigenvalues_transpose_mul_mul_le` (and `…_of_poly`): the
  Kaniel–Paige–Saad bound for the largest Ritz value.

Source: Musco–Musco (2015) [`mm15`], Lem. 4–5 and proof of Thm 1 (gap-free block Krylov);
Saad (2011) [`saad11`], §6.6.1 and Thm 6.4 (Kaniel–Paige–Saad, case `i = 1`).
Atlas: `ritz-value-bounds` (gap-free form), `krylov-eigenvector-angle`, `kaniel-paige-saad`;
uses `chebyshev-amplifier`, `chebyshev-growth`, `polynomial-spectral-bound`, `krylov-subspace`.
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
`krylov-subspace`.
atlas: ritz-value-bounds -/
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
`chebyshev-amplifier`, `polynomial-spectral-bound`, `krylov-subspace`.
Label note: this is the gap-free bound (MM15); the gap-dependent bound of Saad (2011), Thm 6.4,
is `eigenvalues_sub_eigenvalues_transpose_mul_mul_le` (`kaniel-paige-saad`).
atlas: ritz-value-bounds -/
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

/-! ### Gap-dependent bounds: the eigenvector angle and Kaniel–Paige–Saad -/

omit [DecidableEq n] in
/-- The squared tangent of the angle between `u` and `x`,
`tan² ∠(u, x) = (‖u‖² ‖x‖² − ⟨u, x⟩²)/⟨u, x⟩²`. For a unit `u` this is
`‖(I − u uᵀ) x‖²/⟨u, x⟩²`. Junk value `0` when `⟨u, x⟩ = 0` (the angle is `π/2`).
Source: Saad (2011) [`saad11`], §6.6.1 (where `tan θ(u, x)` is used with `‖u‖ = 1`).
Helper for `krylov-eigenvector-angle` (belongs with principal angles in `NLAlib.Matrix`). -/
def tanSqAngle (u x : n → ℝ) : ℝ := ((u ⬝ᵥ u) * (x ⬝ᵥ x) - (u ⬝ᵥ x) ^ 2) / (u ⬝ᵥ x) ^ 2

/-- The eigenvector basis is orthonormal in dot-product form: `uᵢ ⬝ uⱼ = δᵢⱼ`.
Helper for `krylov-eigenvector-angle` (belongs in `NLAlib.Matrix.PolynomialCalculus`). -/
theorem eigenvectorBasis_dotProduct_eigenvectorBasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i j : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hA.eigenvectorBasis j : n → ℝ) =
      if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.1 hA.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

/-- Eigen-coordinates of `p(A) v`: `uᵢ ⬝ p(A) v = p(λᵢ) (uᵢ ⬝ v)` for real symmetric `A`.
Helper for `krylov-eigenvector-angle` (belongs in `NLAlib.Matrix.PolynomialCalculus`). -/
theorem eigenvectorBasis_dotProduct_aeval_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (p : ℝ[X]) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (aeval A p *ᵥ v) =
      p.eval (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  rw [aeval_mulVec_eq_sum hA p v, dotProduct_sum]
  simp [dotProduct_smul, eigenvectorBasis_dotProduct_eigenvectorBasis hA]

/-- The squared tangent to an eigenvector in eigen-coordinates:
`tan² ∠(u_{i₁}, v) = (∑_{i ≠ i₁} (uᵢ ⬝ v)²)/(u_{i₁} ⬝ v)²`.
Helper for `krylov-eigenvector-angle`. -/
theorem tanSqAngle_eigenvectorBasis_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n)
    (v : n → ℝ) :
    tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) v =
      (∑ i ∈ Finset.univ.erase i₁, ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) ^ 2) /
        ((hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ v) ^ 2 := by
  rw [tanSqAngle, eigenvectorBasis_dotProduct_self hA i₁, one_mul,
    ← sum_sq_eigenvectorBasis_dotProduct hA v,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁), add_sub_cancel_left]

/-- `tan² ∠(u_{i₁}, v) ≥ 0`. Helper for `krylov-eigenvector-angle`. -/
theorem tanSqAngle_eigenvectorBasis_nonneg {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n)
    (v : n → ℝ) : 0 ≤ tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) v := by
  rw [tanSqAngle_eigenvectorBasis_eq]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

/-- **The shifted Chebyshev amplifier.** For `a < c < L` and every `q` there is a polynomial
`p` of degree at most `q` with `p(L) = 1` and `|p| ≤ 1/T_q(1 + 2γ)` on `[a, c]`,
`γ = (L − c)/(c − a)`: namely `p(x) = T_q((2x − c − a)/(c − a))/T_q(1 + 2γ)`, the
`chebyshevAmplifier` with `α = (c − a)/2`, `γ' = 2γ`, shifted by `(c + a)/2`.
Source: Saad (2011) [`saad11`], §6.6.1. Helper for `krylov-eigenvector-angle` (belongs in
`NLAlib.Polynomial.Approximation` next to `chebyshev-amplifier`). -/
theorem exists_degree_le_eval_eq_one_abs_eval_le {a c L : ℝ} (hac : a < c) (hcL : c < L)
    (q : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval L = 1 ∧ ∀ x ∈ Set.Icc a c,
      |p.eval x| ≤ 1 / (Chebyshev.T ℝ q).eval (1 + 2 * ((L - c) / (c - a))) := by
  set α := (c - a) / 2 with hαdef
  set m := (c + a) / 2 with hmdef
  set γ := 2 * ((L - c) / (c - a)) with hγdef
  have hca : 0 < c - a := by linarith
  have hα : 0 < α := by positivity
  have hγ : 0 ≤ γ := by have : 0 < L - c := by linarith
                        positivity
  have hT1 : 1 ≤ (Chebyshev.T ℝ q).eval (1 + γ) :=
    Chebyshev.one_le_eval_T_real (q : ℤ) (by linarith)
  refine ⟨(chebyshevAmplifier α γ q).comp (X - C m), ?_, ?_, ?_⟩
  · refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    rw [natDegree_X_sub_C, mul_one]
    exact natDegree_le_iff_degree_le.2 (degree_chebyshevAmplifier_le α γ q)
  · rw [eval_comp, eval_sub, eval_X, eval_C,
      show L - m = α * (1 + γ) by simp only [hαdef, hmdef, hγdef]; field_simp; ring]
    exact eval_chebyshevAmplifier_self q hα hγ
  · intro x hx
    rw [eval_comp, eval_sub, eval_X, eval_C, eval_chebyshevAmplifier, abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < (Chebyshev.T ℝ q).eval (1 + γ))]
    refine div_le_div_of_nonneg_right (Chebyshev.abs_eval_T_real_le_one (q : ℤ) ?_)
      (by linarith)
    rw [abs_div, abs_of_pos hα, div_le_one hα, abs_le]
    constructor <;> simp only [hαdef, hmdef] <;> linarith [hx.1, hx.2]

/-- **Eigenvector angle, polynomial form.** For real symmetric `A`, an index `i₁`, and any
polynomial `p` with `|p(λᵢ)| ≤ M` for every `i ≠ i₁`,
`tan² ∠(u_{i₁}, p(A) b) ≤ (M/p(λ_{i₁}))² tan² ∠(u_{i₁}, b)`. With `deg p < q`, `p(A) b ∈ K_q(A, b)`.
No hypothesis on `b` or `p(λ_{i₁})` is needed (both sides use the junk value `0` for a right
angle). Source: Saad (2011) [`saad11`], §6.6.1, proof of the angle bound (`i = 1`).
atlas: krylov-eigenvector-angle (partial) -/
theorem tanSqAngle_aeval_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (i₁ : n)
    {p : ℝ[X]} {M : ℝ} (hM : ∀ i, i ≠ i₁ → |p.eval (hA.eigenvalues i)| ≤ M) (b : n → ℝ) :
    tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) (aeval A p *ᵥ b) ≤
      (M / p.eval (hA.eigenvalues i₁)) ^ 2 * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) b := by
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ b with hc
  set P := p.eval (hA.eigenvalues i₁)
  rw [tanSqAngle_eigenvectorBasis_eq, tanSqAngle_eigenvectorBasis_eq]
  simp only [eigenvectorBasis_dotProduct_aeval_mulVec hA]
  set N := ∑ i ∈ Finset.univ.erase i₁, c i ^ 2
  have hN : ∑ i ∈ Finset.univ.erase i₁, (p.eval (hA.eigenvalues i) * c i) ^ 2 ≤ M ^ 2 * N := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have h := hM i (Finset.ne_of_mem_erase hi)
    have hsq : p.eval (hA.eigenvalues i) ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (p.eval (hA.eigenvalues i))]) ((le_abs_self _).trans h)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  rw [show (M / P) ^ 2 * (N / c i₁ ^ 2) = M ^ 2 * N / (P * c i₁) ^ 2 by ring]
  exact div_le_div_of_nonneg_right hN (sq_nonneg _)

/-- **Angle between the top eigenvector and the Krylov space (Chebyshev bound).** Let `A` be
real symmetric, `λ₁ = λ_{i₁}`, and suppose every other eigenvalue lies in `[a, c]` with
`a < c < λ₁` (e.g. `a = λₙ`, `c = λ₂`). If `u₁ ⬝ b ≠ 0` then `K_{q+1}(A, b)` contains `x` with
`u₁ ⬝ x ≠ 0` and `tan² ∠(u₁, x) ≤ tan² ∠(u₁, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`.
The witness is `x = T_q((2A − (c + a)I)/(c − a)) b`, written through `chebyshevAmplifier`.
Source: Saad (2011) [`saad11`], §6.6.1 (case `i = 1`); Saad (2003), §6.11.
Deviation: squared tangents; Krylov dimension `q + 1` (Saad's `m`) so that the degree is `q`;
an arbitrary enclosure `[a, c]` of the other eigenvalues instead of `[λₙ, λ₂]`.
atlas: krylov-eigenvector-angle -/
theorem exists_mem_krylovSpace_tanSqAngle_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {i₁ : n}
    {a c : ℝ} (hac : a < c) (hc : c < hA.eigenvalues i₁)
    (hspec : ∀ i, i ≠ i₁ → hA.eigenvalues i ∈ Set.Icc a c) (b : n → ℝ)
    (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) (q : ℕ) :
    ∃ x ∈ krylovSpace A b (q + 1), (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ x ≠ 0 ∧
      tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x ≤
        tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) b /
          (Chebyshev.T ℝ q).eval (1 + 2 * ((hA.eigenvalues i₁ - c) / (c - a))) ^ 2 := by
  obtain ⟨p, hpdeg, hp1, hM⟩ := exists_degree_le_eval_eq_one_abs_eval_le hac hc q
  replace hM : ∀ i, i ≠ i₁ → |p.eval (hA.eigenvalues i)| ≤ _ := fun i hi => hM _ (hspec i hi)
  refine ⟨aeval A p *ᵥ b, (mem_krylovSpace_iff_degree A b (q + 1) _).2
    ⟨p, hpdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self q), rfl⟩, ?_, ?_⟩
  · rw [eigenvectorBasis_dotProduct_aeval_mulVec, hp1, one_mul]; exact hb
  · refine (tanSqAngle_aeval_mulVec_le hA i₁ hM b).trans (le_of_eq ?_)
    rw [hp1, div_one, div_pow, one_pow, one_div_mul_eq_div]

/-- The growth of `T_q` in gap form: for `γ ≥ 0`,
`(1 + 2γ + 2√(γ + γ²))^q / 2 ≤ T_q(1 + 2γ)`. Source: Saad (2011) [`saad11`], §6.6.1 (after
Thm 6.3). Helper for `krylov-eigenvector-angle`; an instance of `chebyshev-growth` (belongs in
`NLAlib.Polynomial.Chebyshev`). -/
theorem pow_div_two_le_eval_T_real_one_add_two_mul {γ : ℝ} (hγ : 0 ≤ γ) (q : ℕ) :
    (1 + 2 * γ + 2 * √(γ + γ ^ 2)) ^ q / 2 ≤ (Chebyshev.T ℝ q).eval (1 + 2 * γ) := by
  have h := pow_div_two_le_eval_T_real (by linarith : (1 : ℝ) ≤ 1 + 2 * γ) q
  have hs : √((1 + 2 * γ) ^ 2 - 1) = 2 * √(γ + γ ^ 2) := by
    rw [show (1 + 2 * γ) ^ 2 - 1 = 2 ^ 2 * (γ + γ ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rwa [hs] at h

/-- **Eigenvector angle, explicit rate.** Under the hypotheses of
`exists_mem_krylovSpace_tanSqAngle_le`, `K_{q+1}(A, b)` contains `x` with `u₁ ⬝ x ≠ 0` and
`tan² ∠(u₁, x) ≤ (2/(1 + 2γ + 2√(γ + γ²))^q)² tan² ∠(u₁, b)`, `γ = (λ₁ − c)/(c − a)`.
Source: Saad (2011) [`saad11`], §6.6.1.
atlas: krylov-eigenvector-angle -/
theorem exists_mem_krylovSpace_tanSqAngle_le_two_div_pow {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {i₁ : n} {a c : ℝ} (hac : a < c) (hc : c < hA.eigenvalues i₁)
    (hspec : ∀ i, i ≠ i₁ → hA.eigenvalues i ∈ Set.Icc a c) (b : n → ℝ)
    (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) (q : ℕ) :
    ∃ x ∈ krylovSpace A b (q + 1), (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ x ≠ 0 ∧
      tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x ≤
        (2 / (1 + 2 * ((hA.eigenvalues i₁ - c) / (c - a)) +
          2 * √((hA.eigenvalues i₁ - c) / (c - a) + ((hA.eigenvalues i₁ - c) / (c - a)) ^ 2))
            ^ q) ^ 2 * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) b := by
  obtain ⟨x, hxK, hx0, hx⟩ := exists_mem_krylovSpace_tanSqAngle_le hA hac hc hspec b hb q
  refine ⟨x, hxK, hx0, hx.trans ?_⟩
  set γ := (hA.eigenvalues i₁ - c) / (c - a)
  have hγ : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have hT := pow_div_two_le_eval_T_real_one_add_two_mul hγ q
  set ρ := (1 + 2 * γ + 2 * √(γ + γ ^ 2)) ^ q
  have hρ : 0 < ρ := by positivity
  have htan := tanSqAngle_eigenvectorBasis_nonneg hA i₁ b
  rw [div_eq_mul_inv, mul_comm, ← inv_pow]
  refine mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.2 (by linarith [div_pos hρ two_pos])) ?_ 2) htan
  have := inv_anti₀ (by positivity : 0 < ρ / 2) hT
  rwa [inv_div] at this

/-- The Ritz values are at most the top eigenvalue: `θⱼ ≤ λ_{i₁}` for every eigenvalue `θⱼ` of
`Qᵀ A Q`, `Q` with orthonormal columns. This is the lower half `0 ≤ λ₁ − θ₁` of the
Kaniel–Paige–Saad bound. Source: Saad (2011) [`saad11`], Thm 6.4 (left inequality; Cauchy
interlacing).
atlas: kaniel-paige-saad (partial) -/
theorem eigenvalues_transpose_mul_mul_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {i₁ : n}
    (htop : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₁) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hT : (Qᵀ * A * Q).IsHermitian) (j : k) :
    hT.eigenvalues j ≤ hA.eigenvalues i₁ := by
  have hlow : ∀ i, -∑ i', |hA.eigenvalues i'| ≤ hA.eigenvalues i := fun i => by
    have := Finset.single_le_sum (f := fun i' => |hA.eigenvalues i'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [neg_abs_le (hA.eigenvalues i)]
  exact (eigenvalues_transpose_mul_mul_mem_Icc hA hQ hT (fun i => ⟨hlow i, htop i⟩) j).2

/-- **Rayleigh–Ritz step of Kaniel–Paige–Saad.** Let `A` be real symmetric with every
eigenvalue `≥ a`, `Q` with orthonormal columns, `θ₁ = θ_{j₁}` the largest eigenvalue of `Qᵀ A Q`,
and `x ∈ range Q` with `u₁ ⬝ x ≠ 0` (`u₁ = u_{i₁}`). Then
`λ₁ − θ₁ ≤ (λ₁ − a) tan² ∠(u₁, x)` (from `λ₁ − xᵀAx/xᵀx ≤ (λ₁ − a) sin² ∠(u₁, x)`).
Source: Saad (2011) [`saad11`], proof of Thm 6.4. Helper for `kaniel-paige-saad`. -/
theorem eigenvalues_sub_eigenvalues_le_mul_tanSqAngle {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₁ : n} {a : ℝ}
    (ha : ∀ i, a ≤ hA.eigenvalues i) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hT : (Qᵀ * A * Q).IsHermitian) {j₁ : k} (hj₁ : ∀ j, hT.eigenvalues j ≤ hT.eigenvalues j₁)
    {x : n → ℝ} (hxQ : x ∈ LinearMap.range Q.mulVecLin)
    (hx : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ x ≠ 0) :
    hA.eigenvalues i₁ - hT.eigenvalues j₁ ≤
      (hA.eigenvalues i₁ - a) * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) x := by
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ x with hc
  set L := hA.eigenvalues i₁
  set θ := hT.eigenvalues j₁
  set N := ∑ i ∈ Finset.univ.erase i₁, c i ^ 2
  set S := ∑ i ∈ Finset.univ.erase i₁, hA.eigenvalues i * c i ^ 2
  have hR := dotProduct_mulVec_le_of_mem_range hQ hT hj₁ hxQ
  have hxx : x ⬝ᵥ x = c i₁ ^ 2 + N := by
    rw [← sum_sq_eigenvectorBasis_dotProduct hA x,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
  have hxAx : x ⬝ᵥ (A *ᵥ x) = L * c i₁ ^ 2 + S := by
    have h := quadForm_eq_sum_eigenvalues hA x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)] at h
    exact h
  have hS : a * N ≤ S := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1 : 0 < c i₁ ^ 2 := by positivity
  have haL : 0 ≤ L - a := by linarith [ha i₁]
  rw [tanSqAngle_eigenvectorBasis_eq, ← mul_div_assoc, le_div_iff₀ hc1]
  rw [hxx, hxAx] at hR
  have key : (L - θ) * (c i₁ ^ 2 + N) ≤ (L - a) * N := by nlinarith
  rcases le_or_gt (L - θ) 0 with hneg | hpos
  · nlinarith
  · nlinarith

/-- **Kaniel–Paige–Saad, polynomial form.** Let `A` be real symmetric with every eigenvalue
`≥ a`, `u₁ ⬝ b ≠ 0`, `Q` with orthonormal columns and `K_q(A, b) ⊆ range Q`, and `θ₁` the
largest eigenvalue of `Qᵀ A Q`. For every polynomial `p` with `deg p < q`, `p(λ₁) ≠ 0` and
`|p(λᵢ)| ≤ M` for `i ≠ i₁`: `λ₁ − θ₁ ≤ (λ₁ − a) (M/p(λ₁))² tan² ∠(u₁, b)`.
Source: Saad (2011) [`saad11`], proof of Thm 6.4 (`i = 1`).
atlas: kaniel-paige-saad (partial) -/
theorem eigenvalues_sub_eigenvalues_transpose_mul_mul_le_of_poly {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {i₁ : n} {a : ℝ}
    (ha : ∀ i, a ≤ hA.eigenvalues i) (b : n → ℝ)
    (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) {q : ℕ} {p : ℝ[X]} (hp : p.degree < q)
    (hp1 : p.eval (hA.eigenvalues i₁) ≠ 0) {M : ℝ}
    (hM : ∀ i, i ≠ i₁ → |p.eval (hA.eigenvalues i)| ≤ M) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin)
    (hT : (Qᵀ * A * Q).IsHermitian) {j₁ : k} (hj₁ : ∀ j, hT.eigenvalues j ≤ hT.eigenvalues j₁) :
    hA.eigenvalues i₁ - hT.eigenvalues j₁ ≤ (hA.eigenvalues i₁ - a) *
      ((M / p.eval (hA.eigenvalues i₁)) ^ 2 * tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) b) := by
  have hxK : aeval A p *ᵥ b ∈ krylovSpace A b q :=
    (mem_krylovSpace_iff_degree A b q _).2 ⟨p, hp, rfl⟩
  have hx0 : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ (aeval A p *ᵥ b) ≠ 0 := by
    rw [eigenvectorBasis_dotProduct_aeval_mulVec]; exact mul_ne_zero hp1 hb
  refine (eigenvalues_sub_eigenvalues_le_mul_tanSqAngle hA ha hQ hT hj₁ (hK hxK) hx0).trans ?_
  exact mul_le_mul_of_nonneg_left (tanSqAngle_aeval_mulVec_le hA i₁ hM b)
    (by linarith [ha i₁])

/-- **Kaniel–Paige–Saad bound for the largest Ritz value.** Let `A` be real symmetric,
`λ₁ = λ_{i₁}`, every other eigenvalue in `[a, c]` with `a < c < λ₁` (e.g. `a = λₙ`, `c = λ₂`),
`u₁ ⬝ b ≠ 0`, `Q` with orthonormal columns and `K_{q+1}(A, b) ⊆ range Q` (e.g. a Lanczos basis),
and `θ₁` the largest eigenvalue of `Qᵀ A Q`. Then
`λ₁ − θ₁ ≤ (λ₁ − a) tan² ∠(u₁, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`; the lower bound
`0 ≤ λ₁ − θ₁` is `eigenvalues_transpose_mul_mul_le`.
Source: Saad (2011) [`saad11`], Thm 6.4 (`i = 1`); Golub–Meurant (2010) [`gm10`], Ch. 4.
Deviation: Krylov dimension `q + 1` (Saad's `m`, so `T_{m−1} = T_q`); `[a, c]` any enclosure
of the other eigenvalues (Saad: `a = λₙ`, `c = λ₂`, factor `λ₁ − λₙ`); any orthonormal `Q`
whose range contains the Krylov space.
atlas: kaniel-paige-saad -/
theorem eigenvalues_sub_eigenvalues_transpose_mul_mul_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₁ : n} {a c : ℝ} (hac : a < c)
    (hc : c < hA.eigenvalues i₁) (hspec : ∀ i, i ≠ i₁ → hA.eigenvalues i ∈ Set.Icc a c)
    (b : n → ℝ) (hb : (hA.eigenvectorBasis i₁ : n → ℝ) ⬝ᵥ b ≠ 0) (q : ℕ) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hK : krylovSpace A b (q + 1) ≤ LinearMap.range Q.mulVecLin)
    (hT : (Qᵀ * A * Q).IsHermitian) {j₁ : k} (hj₁ : ∀ j, hT.eigenvalues j ≤ hT.eigenvalues j₁) :
    hA.eigenvalues i₁ - hT.eigenvalues j₁ ≤ (hA.eigenvalues i₁ - a) *
      (tanSqAngle (hA.eigenvectorBasis i₁ : n → ℝ) b /
        (Chebyshev.T ℝ q).eval (1 + 2 * ((hA.eigenvalues i₁ - c) / (c - a))) ^ 2) := by
  have ha : ∀ i, a ≤ hA.eigenvalues i := fun i => by
    by_cases hi : i = i₁
    · subst hi; linarith
    · exact (hspec i hi).1
  obtain ⟨x, hxK, hx0, hx⟩ := exists_mem_krylovSpace_tanSqAngle_le hA hac hc hspec b hb q
  exact (eigenvalues_sub_eigenvalues_le_mul_tanSqAngle hA ha hQ hT hj₁ (hK hxK) hx0).trans
    (mul_le_mul_of_nonneg_left hx (by linarith [ha i₁]))

end NLAlib

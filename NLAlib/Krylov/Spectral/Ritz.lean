import NLAlib.Krylov.Quadrature.GaussQuadrature
import NLAlib.Polynomial.FunctionApproximation.Approximation
/-!
# Ritz values: gap-free and gap-dependent Lanczos eigenvalue bounds

Statements take a unit eigenvector `u` for the eigenvalue at a sorted position
(`A *ᵥ u = hA.eigenvalues₀ i₀ • u`, `‖WithLp.toLp 2 u‖ = 1`); the top eigenvalue is
`hA.eigenvalues₀ 0`. "The other eigenvalues" are the other sorted positions, so repeated top
eigenvalues are handled correctly (an eigenvector of a repeated eigenvalue is bounded by its
copies).

**Gap-free.** For a positive semidefinite `A` with top eigenvalue `λ₁ = λ₀(A)` (unit eigenvector
`u`) and a starting vector `b` with `u ⬝ b ≠ 0`, the Krylov space `K_{q+1}(A, b)` (`q` matvecs)
contains a vector `y = p(A) b` whose Rayleigh quotient is within
`ε λ₁ + λ₁ (2/(1 + √(2γ)))^{2q} ‖b‖²/(u ⬝ b)²` of `λ₁`, `γ = ε/(1 − ε)`; `p` is the Chebyshev
amplifier (`NLAlib.chebyshevAmplifier`). Consequently the largest Ritz value (largest eigenvalue of
`QᵀAQ` for an orthonormal `Q` whose range contains `K_{q+1}`) obeys the same bound. No eigenvalue
gap is assumed. This is Musco–Musco's bound (MM15, Lem. 4 and Thm 1); it is not Saad's Thm 6.4.

**Gap-dependent (Kaniel–Paige–Saad).** If every eigenvalue other than `λ₁` (every sorted position
`≠ 0`) lies in `[a, c]`, `a < c < λ₁`, then `K_{q+1}(A, b)` contains `x` with
`tan² ∠(u, x) ≤ tan² ∠(u, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`, and the largest Ritz
value satisfies `0 ≤ λ₁ − θ₁ ≤ (λ₁ − a) tan² ∠(u, b) / T_q(1 + 2γ)²` (Saad 2011, Thm 6.4).
Both are corollaries of polynomial forms that take any `p` and a bound `M` on `|p(λᵢ)|` over
the other sorted positions.

## Main results

* `NLAlib.exists_mem_krylovSpace_sub_rayleigh_le`: the gap-free Krylov vector.
* `NLAlib.dotProduct_mulVec_le_of_mem_range`: Rayleigh quotients over `range Q` are bounded by
  any upper bound on the Ritz values.
* `NLAlib.exists_eigenvalues_transpose_mul_mul_ge`: the gap-free Ritz-value bound.
* `NLAlib.overlapTangentSq`, `NLAlib.overlapTangentSq_aeval_mulVec_le`: the squared tangent of an angle and
  the polynomial form of the eigenvector-angle bound (`overlapTangentSq_le_of_forall_eigenvectorBasis_dotProduct_eq`
  is the spectral-multiplier form shared with the power method).
* `NLAlib.exists_mem_krylovSpace_overlapTangentSq_le` (and `…_two_div_pow`): the Chebyshev angle bound.
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

/-! ### Vector-norm bridges and the eigenvector coordinates (helpers) -/

/-- A unit vector has `u ⬝ u = 1`. -/
private lemma dotProduct_self_eq_one {u : n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) : u ⬝ᵥ u = 1 := by
  rw [← norm_toLp_sq_eq_dotProduct_self, hu, one_pow]

omit [DecidableEq n] in
/-- Cauchy–Schwarz for the dot product: `(u ⬝ v)² ≤ (u ⬝ u)(v ⬝ v)`. -/
theorem sq_dotProduct_le_dotProduct_mul_dotProduct (u v : n → ℝ) :
    (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have h := real_inner_mul_inner_self_le (WithLp.toLp 2 u : EuclideanSpace ℝ n)
    (WithLp.toLp 2 v)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp] at h
  simpa only [sq, dotProduct_comm v u] using h

/-- The eigenvalue at sorted position `i₀` is the eigenvalue of the label
`Fintype.equivOfCardEq (Fintype.card_fin _) i₀` (the bridge between `eigenvalues₀` and
`eigenvalues`). Helper. -/
theorem _root_.Matrix.IsHermitian.eigenvalues_equivOfCardEq {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (i₀ : Fin (Fintype.card n)) :
    hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) i₀) = hA.eigenvalues₀ i₀ := by
  unfold Matrix.IsHermitian.eigenvalues
  rw [Equiv.symm_apply_apply]

/-- Every eigenvalue is at most the one at sorted position `0`. Helper. -/
theorem _root_.Matrix.IsHermitian.eigenvalues_le_eigenvalues₀_zero [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ hA.eigenvalues₀ 0 :=
  hA.eigenvalues₀_antitone (Fin.zero_le _)

section EigenvectorCoordinates

variable {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- Eigen-coordinates of an eigenvector: `(λᵢ − L)(uᵢ ⬝ u) = 0` when `A u = L u`. Helper for
`krylov-eigenvector-angle`. -/
theorem eigenvalues_sub_mul_eigenvectorBasis_dotProduct_eq_zero {u : n → ℝ} {L : ℝ}
    (hu : A *ᵥ u = L • u) (i : n) :
    (hA.eigenvalues i - L) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ u) = 0 := by
  have h := eigenvectorBasis_dotProduct_aeval_mulVec hA X u i
  rw [aeval_X, hu, dotProduct_smul, eval_X, smul_eq_mul] at h
  rw [sub_mul]; linarith

/-- Parseval for a pair: `v ⬝ w = ∑ᵢ (uᵢ ⬝ v)(uᵢ ⬝ w)`. Helper. -/
theorem dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul (v w : n → ℝ) :
    v ⬝ᵥ w = ∑ i, ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) *
      ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) := by
  have h1 := sum_sq_eigenvectorBasis_dotProduct hA (v + w)
  have h2 := sum_sq_eigenvectorBasis_dotProduct hA v
  have h3 := sum_sq_eigenvectorBasis_dotProduct hA w
  simp only [dotProduct_add, add_sq, Finset.sum_add_distrib, add_dotProduct] at h1
  rw [dotProduct_comm w v] at h1
  have h4 : ∑ i, 2 * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) *
      ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) = 2 * ∑ i, ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) *
      ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4] at h1
  linarith

/-- For an eigenvector `u` with `A u = L u`, `uᵢ ⬝ u` vanishes unless `λᵢ = L`, so any `g` acts
as `g(L)` on these coordinates: `(uᵢ ⬝ u) g(λᵢ) = (uᵢ ⬝ u) g(L)`. Helper. -/
theorem eigenvectorBasis_dotProduct_mul_eq {u : n → ℝ} {L : ℝ} (hu : A *ᵥ u = L • u)
    (g : ℝ → ℝ) (i : n) :
    ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ u) * g (hA.eigenvalues i) =
      ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ u) * g L := by
  rcases mul_eq_zero.1 (eigenvalues_sub_mul_eigenvectorBasis_dotProduct_eq_zero hA hu i) with
    h | h
  · rw [sub_eq_zero.1 h]
  · rw [h, zero_mul, zero_mul]

/-- **A spectral multiplier commutes with an eigenvector**: if `uᵢ ⬝ w = g(λᵢ)(uᵢ ⬝ v)` for
every `i` (e.g. `w = g(A) v`) and `A u = L u`, then `u ⬝ w = g(L)(u ⬝ v)`. Helper for
`krylov-eigenvector-angle`, `power-iteration`. -/
theorem dotProduct_eq_mul_dotProduct_of_forall_eigenvectorBasis_dotProduct_eq {u v w : n → ℝ}
    {L : ℝ} (hu : A *ᵥ u = L • u) {g : ℝ → ℝ}
    (hw : ∀ i, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w =
      g (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v)) :
    u ⬝ᵥ w = g L * (u ⬝ᵥ v) := by
  rw [dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul hA u w,
    dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul hA u v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw i, ← mul_assoc, eigenvectorBasis_dotProduct_mul_eq hA hu g i]
  ring

/-- **Angle contraction under a spectral multiplier, numerator form.** Let `u` be a unit
eigenvector for the eigenvalue at sorted position `i₀`, let `|g| ≤ M` at every other sorted
position, and let `uᵢ ⬝ w = g(λᵢ)(uᵢ ⬝ v)` for every `i`. Then the component of `w`
orthogonal to `u` is at most `M` times that of `v`: `‖w‖² − (u ⬝ w)² ≤ M² (‖v‖² − (u ⬝ v)²)`.
Source: Trefethen–Bau (1997) [`tb97`], proof of Thm 27.1; Saad (2011) [`saad11`], §6.6.1.
Helper for `krylov-eigenvector-angle`, `power-iteration`, `inverse-iteration`. -/
theorem sub_sq_dotProduct_le_of_forall_eigenvectorBasis_dotProduct_eq
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {g : ℝ → ℝ} {M : ℝ}
    (hM : ∀ i, i ≠ i₀ → |g (hA.eigenvalues₀ i)| ≤ M) {v w : n → ℝ}
    (hw : ∀ i, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w =
      g (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v)) :
    w ⬝ᵥ w - (u ⬝ᵥ w) ^ 2 ≤ M ^ 2 * (v ⬝ᵥ v - (u ⬝ᵥ v) ^ 2) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with he
  set L := hA.eigenvalues₀ i₀
  set a : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ u with ha
  set c : n → ℝ := fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v with hc
  set d : n → ℝ := fun i => c i - (u ⬝ᵥ v) * a i with hd
  have huu : u ⬝ᵥ u = 1 := dotProduct_self_eq_one hu1
  have haa : ∑ i, a i ^ 2 = 1 := by rw [sum_sq_eigenvectorBasis_dotProduct hA u, huu]
  have huv : u ⬝ᵥ v = ∑ i, a i * c i := dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul hA u v
  have huw : u ⬝ᵥ w = g L * (u ⬝ᵥ v) :=
    dotProduct_eq_mul_dotProduct_of_forall_eigenvectorBasis_dotProduct_eq hA hu hw
  have hag : ∀ i, a i * g (hA.eigenvalues i) = a i * g L := fun i =>
    eigenvectorBasis_dotProduct_mul_eq hA hu g i
  -- the orthogonal components in eigen-coordinates
  have hwd : ∀ i, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w - (u ⬝ᵥ w) * a i =
      g (hA.eigenvalues i) * d i := fun i => by
    rw [hw i, huw, hd]; dsimp only
    have := hag i
    linear_combination (u ⬝ᵥ v) * this
  have hsq_v : v ⬝ᵥ v - (u ⬝ᵥ v) ^ 2 = ∑ i, d i ^ 2 := by
    have h1 : ∑ i, d i ^ 2 = ∑ i, c i ^ 2 - 2 * (u ⬝ᵥ v) * ∑ i, a i * c i +
        (u ⬝ᵥ v) ^ 2 * ∑ i, a i ^ 2 := by
      simp only [hd, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, ← huv, haa, sum_sq_eigenvectorBasis_dotProduct hA v]; ring
  have hsq_w : w ⬝ᵥ w - (u ⬝ᵥ w) ^ 2 = ∑ i, (g (hA.eigenvalues i) * d i) ^ 2 := by
    have huw' : u ⬝ᵥ w = ∑ i, a i * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) :=
      dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul hA u w
    have h1 : ∑ i, (g (hA.eigenvalues i) * d i) ^ 2 =
        ∑ i, ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) ^ 2 -
          2 * (u ⬝ᵥ w) * ∑ i, a i * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w) +
            (u ⬝ᵥ w) ^ 2 * ∑ i, a i ^ 2 := by
      simp only [← hwd, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, ← huw', haa, sum_sq_eigenvectorBasis_dotProduct hA w]; ring
  rw [hsq_v, hsq_w, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_pow]
  by_cases hi : e.symm i = i₀
  · -- the position of `u`: either `L` is repeated (then `|g L| ≤ M`) or `d i = 0`
    have hLi : hA.eigenvalues i = L := by
      change hA.eigenvalues₀ (e.symm i) = L; rw [hi]
    by_cases hrep : ∃ j, j ≠ i₀ ∧ hA.eigenvalues₀ j = L
    · obtain ⟨j, hj, hjL⟩ := hrep
      have := hM j hj
      rw [hjL, ← hLi] at this
      exact mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2) (sq_nonneg _)
    · push Not at hrep
      -- `u` is a multiple of the `i`-th eigenvector
      have hzero : ∀ j, j ≠ i → a j = 0 := fun j hj => by
        have hne : hA.eigenvalues j ≠ L := fun hjL => by
          exact hrep (e.symm j)
            (fun h => hj (e.symm.injective (h.trans hi.symm))) hjL
        rcases mul_eq_zero.1 (eigenvalues_sub_mul_eigenvectorBasis_dotProduct_eq_zero hA hu j)
          with h | h
        · exact absurd (sub_eq_zero.1 h) hne
        · exact h
      have hai : a i ^ 2 = 1 := by
        rw [← haa, Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, sq, mul_zero])
          (fun h => absurd (Finset.mem_univ i) h)]
      have huv' : u ⬝ᵥ v = a i * c i := by
        rw [huv, Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, zero_mul])
          (fun h => absurd (Finset.mem_univ i) h)]
      have hdi : d i = 0 := by
        simp only [hd, huv']
        linear_combination (-(c i)) * hai
      rw [hdi]; simp
  · have := hM (e.symm i) hi
    change |g (hA.eigenvalues i)| ≤ M at this
    exact mul_le_mul_of_nonneg_right
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2) (sq_nonneg _)

end EigenvectorCoordinates

/-! ### The squared tangent and the spectral-multiplier bound -/

omit [DecidableEq n] in
/-- The totalized quadratic overlap ratio of `u` and `x`,
`tan² ∠(u, x) = (‖u‖² ‖x‖² − ⟨u, x⟩²)/⟨u, x⟩²`. For a unit `u` this is
`‖(I − u uᵀ) x‖²/⟨u, x⟩²`. The algebraic value is `0` when `⟨u, x⟩ = 0` (the angle is `π/2`).
Source: Saad (2011) [`saad11`], §6.6.1 (where `tan θ(u, x)` is used with `‖u‖ = 1`).
Helper for `krylov-eigenvector-angle` (the one-column case of `overlapTangentNorm`,
`sq_overlapTangentNorm_replicateCol_eq_overlapTangentSq`). -/
def overlapTangentSq (u x : n → ℝ) : ℝ := ((u ⬝ᵥ u) * (x ⬝ᵥ x) - (u ⬝ᵥ x) ^ 2) / (u ⬝ᵥ x) ^ 2

omit [DecidableEq n] in
/-- The squared tangent of the angle between two vectors with nonzero overlap.
Source: Saad (2011), §6.6.1. The overlap premise excludes the orthogonal and zero-vector cases. -/
def tanSqAngle (u x : n → ℝ) (_hux : u ⬝ᵥ x ≠ 0) : ℝ := overlapTangentSq u x

omit [DecidableEq n] in
/-- The geometric squared tangent agrees with its quadratic quotient on the valid domain. -/
theorem tanSqAngle_eq_overlapTangentSq (u x : n → ℝ) (hux : u ⬝ᵥ x ≠ 0) :
    tanSqAngle u x hux = overlapTangentSq u x := rfl

omit [DecidableEq n] in
/-- `tan² ∠(u, x) ≥ 0` (Cauchy–Schwarz). Helper for `krylov-eigenvector-angle`. -/
theorem overlapTangentSq_nonneg (u x : n → ℝ) : 0 ≤ overlapTangentSq u x :=
  div_nonneg (sub_nonneg.2 (sq_dotProduct_le_dotProduct_mul_dotProduct u x)) (sq_nonneg _)

omit [DecidableEq n] in
/-- The squared tangent on its nonzero-overlap domain is nonnegative. -/
theorem tanSqAngle_nonneg (u x : n → ℝ) (hux : u ⬝ᵥ x ≠ 0) :
    0 ≤ tanSqAngle u x hux := overlapTangentSq_nonneg u x

omit [DecidableEq n] in
/-- For a unit vector `u`, `tan² ∠(u, x) = (‖x‖² − (u ⬝ x)²)/(u ⬝ x)²`. Helper. -/
theorem overlapTangentSq_of_norm_eq_one {u : n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) (x : n → ℝ) :
    overlapTangentSq u x = (x ⬝ᵥ x - (u ⬝ᵥ x) ^ 2) / (u ⬝ᵥ x) ^ 2 := by
  classical
  rw [overlapTangentSq, dotProduct_self_eq_one hu, one_mul]

omit [DecidableEq n] in
/-- For a unit reference vector and nonzero overlap, the squared tangent is the orthogonal
energy divided by squared overlap. Source: Saad (2011), §6.6.1. -/
theorem tanSqAngle_of_norm_eq_one {u : n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (x : n → ℝ) (hux : u ⬝ᵥ x ≠ 0) :
    tanSqAngle u x hux = (x ⬝ᵥ x - (u ⬝ᵥ x) ^ 2) / (u ⬝ᵥ x) ^ 2 :=
  overlapTangentSq_of_norm_eq_one hu x

/-- **Angle contraction under a spectral multiplier.** Let `u` be a unit eigenvector for the
eigenvalue at sorted position `i₀`, `|g| ≤ M` at every other sorted position, and
`uᵢ ⬝ w = g(λᵢ)(uᵢ ⬝ v)` for every `i` (e.g. `w = p(A) v`, `w = (A − μI)⁻¹ v`). Then
`tan² ∠(u, w) ≤ (M/g(λ_{i₀}))² tan² ∠(u, v)`. Source: Trefethen–Bau (1997) [`tb97`], proof of
Thm 27.1. Helper for `krylov-eigenvector-angle`, `power-iteration`, `inverse-iteration`. -/
theorem overlapTangentSq_le_of_forall_eigenvectorBasis_dotProduct_eq {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {i₀ : Fin (Fintype.card n)} {u : n → ℝ}
    (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) {g : ℝ → ℝ} {M : ℝ}
    (hM : ∀ i, i ≠ i₀ → |g (hA.eigenvalues₀ i)| ≤ M) {v w : n → ℝ}
    (hw : ∀ i, (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ w =
      g (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v)) :
    overlapTangentSq u w ≤ (M / g (hA.eigenvalues₀ i₀)) ^ 2 * overlapTangentSq u v := by
  have huw : u ⬝ᵥ w = g (hA.eigenvalues₀ i₀) * (u ⬝ᵥ v) :=
    dotProduct_eq_mul_dotProduct_of_forall_eigenvectorBasis_dotProduct_eq hA hu hw
  have hnum := sub_sq_dotProduct_le_of_forall_eigenvectorBasis_dotProduct_eq hA hu hu1 hM hw
  rw [overlapTangentSq_of_norm_eq_one hu1, overlapTangentSq_of_norm_eq_one hu1, huw, mul_pow, div_pow,
    div_mul_div_comm]
  rw [huw, mul_pow] at hnum
  exact div_le_div_of_nonneg_right hnum (by positivity)

/-- **Eigenvector angle, polynomial form.** Let `u` be a unit eigenvector for the eigenvalue
`λ_{i₀}` at sorted position `i₀`, and `p` a polynomial with `|p(λᵢ)| ≤ M` at every other sorted
position. Then `tan² ∠(u, p(A) b) ≤ (M/p(λ_{i₀}))² tan² ∠(u, b)`. With `deg p < q`,
`p(A) b ∈ K_q(A, b)`. This algebraic quotient identity uses zero at vanishing overlap; its geometric form
`tanSqAngle_aeval_mulVec_le` requires nonzero starting overlap and nonzero `p(λ_{i₀})`. Source: Saad (2011) [`saad11`], §6.6.1, proof of the angle bound
(`i = 1`).
atlas: krylov-eigenvector-angle (partial) -/
theorem overlapTangentSq_aeval_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {p : ℝ[X]} {M : ℝ}
    (hM : ∀ i, i ≠ i₀ → |p.eval (hA.eigenvalues₀ i)| ≤ M) (b : n → ℝ) :
    overlapTangentSq u (aeval A p *ᵥ b) ≤
      (M / p.eval (hA.eigenvalues₀ i₀)) ^ 2 * overlapTangentSq u b :=
  overlapTangentSq_le_of_forall_eigenvectorBasis_dotProduct_eq hA hu hu1 (g := fun x => p.eval x) hM
    (fun i => eigenvectorBasis_dotProduct_aeval_mulVec hA p b i)

/-- An eigenvector pairs with `p(A) b` through `p(λ)`: `u ⬝ p(A) b = p(λ)(u ⬝ b)` when
`A u = λ u`. Helper for `krylov-eigenvector-angle`, `ritz-value-bounds`. -/
theorem dotProduct_aeval_mulVec_of_mulVec_eq_smul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {u : n → ℝ} {L : ℝ} (hu : A *ᵥ u = L • u) (p : ℝ[X]) (b : n → ℝ) :
    u ⬝ᵥ (aeval A p *ᵥ b) = p.eval L * (u ⬝ᵥ b) :=
  dotProduct_eq_mul_dotProduct_of_forall_eigenvectorBasis_dotProduct_eq hA hu
    (g := fun x => p.eval x) (fun i => eigenvectorBasis_dotProduct_aeval_mulVec hA p b i)

/-- A polynomial preserves nonzero eigenvector overlap when its value at the eigenvalue
is nonzero. Source: Saad (2011), §6.6.1. -/
theorem dotProduct_aeval_mulVec_ne_zero {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {u : n → ℝ} {L : ℝ} (hu : A *ᵥ u = L • u) (p : ℝ[X]) (b : n → ℝ)
    (hb : u ⬝ᵥ b ≠ 0) (hp : p.eval L ≠ 0) : u ⬝ᵥ (aeval A p *ᵥ b) ≠ 0 := by
  rw [dotProduct_aeval_mulVec_of_mulVec_eq_smul hA hu]
  exact mul_ne_zero hp hb

/-- Polynomial contraction of the geometric squared tangent on its nonzero-overlap domain.
Source: Saad (2011), §6.6.1. -/
theorem tanSqAngle_aeval_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {p : ℝ[X]} {M : ℝ}
    (hM : ∀ i, i ≠ i₀ → |p.eval (hA.eigenvalues₀ i)| ≤ M) (b : n → ℝ)
    (hb : u ⬝ᵥ b ≠ 0) (hp : p.eval (hA.eigenvalues₀ i₀) ≠ 0) :
    tanSqAngle u (aeval A p *ᵥ b) (dotProduct_aeval_mulVec_ne_zero hA hu p b hb hp) ≤
      (M / p.eval (hA.eigenvalues₀ i₀)) ^ 2 * tanSqAngle u b hb :=
  overlapTangentSq_aeval_mulVec_le hA hu hu1 hM b

/-! ### Gap-free bounds -/

/-- **A Krylov vector with near-maximal Rayleigh quotient (gap-free).** Let `A` be positive
semidefinite with top eigenvalue `λ₁ = λ₀(A)` and unit eigenvector `u`, let `0 < ε < 1`, and
`u ⬝ b ≠ 0`. Then there is a nonzero `y ∈ K_{q+1}(A, b)` (`q` matvecs) with
`λ₁ ‖y‖² − yᵀAy ≤ (ε λ₁ + λ₁ (2/(1 + √(2γ)))^{2q} ‖b‖²/(u ⬝ b)²) ‖y‖²`, `γ = ε/(1 − ε)`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4–5 and proof of Thm 1 (single-vector case).
Deviation: `K_{q+1}` and the exponent `q` (the source counts the Krylov dimension).
atlas: ritz-value-bounds -/
theorem exists_mem_krylovSpace_sub_rayleigh_le [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {u : n → ℝ} (hu : A *ᵥ u = hA.isHermitian.eigenvalues₀ 0 • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {b : n → ℝ}
    (hb : u ⬝ᵥ b ≠ 0) (q : ℕ) :
    ∃ y ∈ krylovSpace A b (q + 1), y ≠ 0 ∧
      hA.isHermitian.eigenvalues₀ 0 * ‖WithLp.toLp 2 y‖ ^ 2 - y ⬝ᵥ (A *ᵥ y) ≤
        (ε * hA.isHermitian.eigenvalues₀ 0 + hA.isHermitian.eigenvalues₀ 0 *
          (2 / (1 + √(2 * (ε / (1 - ε)))) ^ q) ^ 2 * ‖WithLp.toLp 2 b‖ ^ 2 / (u ⬝ᵥ b) ^ 2) *
            ‖WithLp.toLp 2 y‖ ^ 2 := by
  simp only [norm_toLp_sq_eq_dotProduct_self]
  have hH := hA.isHermitian
  set L := hH.eigenvalues₀ 0 with hLdef
  have htop : ∀ i, hH.eigenvalues i ≤ L := hH.eigenvalues_le_eigenvalues₀_zero
  have hpsd : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  set c : n → ℝ := fun i => (hH.eigenvectorBasis i : n → ℝ) ⬝ᵥ b with hcdef
  have hc1 : 0 < (u ⬝ᵥ b) ^ 2 := by positivity
  have hbb : b ⬝ᵥ b = ∑ i, c i ^ 2 := (sum_sq_eigenvectorBasis_dotProduct hH b).symm
  have huu : u ⬝ᵥ u = 1 := dotProduct_self_eq_one hu1
  have hL : 0 ≤ L := by
    obtain ⟨i⟩ := ‹Nonempty n›
    exact (hpsd i).trans (htop i)
  set M := 2 / (1 + √(2 * (ε / (1 - ε)))) ^ q
  rcases hL.lt_or_eq with hLpos | hL0
  · -- the amplifier `p = T_q(x/α)/T_q(1+γ)`, `α = (1-ε)L`, `γ = ε/(1-ε)`
    set α := (1 - ε) * L
    set γ := ε / (1 - ε)
    have hα : 0 < α := mul_pos (by linarith) hLpos
    have hγ : 0 ≤ γ := div_nonneg hε0.le (by linarith)
    have h1ε : 1 - ε ≠ 0 := (by linarith : (0 : ℝ) < 1 - ε).ne'
    have hαγ : α * (1 + γ) = L := by
      simp only [α, γ]; field_simp; ring
    set p := chebyshevAmplifier α γ q
    have hp1 : p.eval L = 1 := by rw [← hαγ]; exact eval_chebyshevAmplifier_self _ hα hγ
    set y := aeval A p *ᵥ b
    have hy : y ∈ krylovSpace A b (q + 1) := (mem_krylovSpace_iff A b (q + 1) y).2
      ⟨p, (degree_chebyshevAmplifier_le α γ q).trans_lt (by exact_mod_cast Nat.lt_succ_self q),
        rfl⟩
    have hyy : y ⬝ᵥ y = ∑ i, p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2 :=
      dotProduct_aeval_mulVec_self_eq_sum hH p b
    have hyAy : y ⬝ᵥ (A *ᵥ y) = ∑ i, hH.eigenvalues i * p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2 :=
      quadForm_aeval_mulVec_eq_sum hH p b
    have huy : u ⬝ᵥ y = u ⬝ᵥ b := by
      rw [dotProduct_aeval_mulVec_of_mulVec_eq_smul hH hu p b, hp1, one_mul]
    have hylow : (u ⬝ᵥ b) ^ 2 ≤ y ⬝ᵥ y := by
      have := sq_dotProduct_le_dotProduct_mul_dotProduct u y
      rwa [huy, huu, one_mul] at this
    refine ⟨y, hy, fun h0 => ?_, ?_⟩
    · rw [h0, dotProduct_zero] at hylow; linarith
    -- termwise bound
    have hterm : ∀ i, (L - hH.eigenvalues i) * (p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2) ≤
        ε * L * (p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2) + L * M ^ 2 * c i ^ 2 := fun i => by
      have hl0 := hpsd i
      have hlL := htop i
      have hpc : 0 ≤ p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2 := by positivity
      rcases lt_or_ge α (hH.eigenvalues i) with hbig | hsmall
      · have : L - hH.eigenvalues i ≤ ε * L := by simp only [α] at hbig; linarith
        have h1 := mul_le_mul_of_nonneg_right this hpc
        have h2 : 0 ≤ L * M ^ 2 * c i ^ 2 := by positivity
        linarith
      · have hmem : hH.eigenvalues i ∈ Set.Icc (-α) α := ⟨by linarith, hsmall⟩
        have hpM := abs_eval_chebyshevAmplifier_le q hα hγ hmem
        have hM0 : 0 ≤ M := by positivity
        have hsq : p.eval (hH.eigenvalues i) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpM 2
        have h1 : (L - hH.eigenvalues i) * (p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2) ≤
            L * (M ^ 2 * c i ^ 2) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) hpc hL
        have h2 : 0 ≤ ε * L * (p.eval (hH.eigenvalues i) ^ 2 * c i ^ 2) := by positivity
        nlinarith
    have hsum : L * (y ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) := by
      rw [hyy, hyAy, hbb, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hterm i
      linarith
    have hbound : L * M ^ 2 * (b ⬝ᵥ b) ≤ L * M ^ 2 * (b ⬝ᵥ b) / (u ⬝ᵥ b) ^ 2 * (y ⬝ᵥ y) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
      exact mul_le_mul_of_nonneg_left hylow
        (mul_nonneg (mul_nonneg hL (sq_nonneg M)) (dotProduct_self_nonneg b))
    calc L * (y ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) := hsum
      _ ≤ ε * L * (y ⬝ᵥ y) + L * M ^ 2 * (b ⬝ᵥ b) / (u ⬝ᵥ b) ^ 2 * (y ⬝ᵥ y) := by linarith
      _ = (ε * L + L * M ^ 2 * (b ⬝ᵥ b) / (u ⬝ᵥ b) ^ 2) * (y ⬝ᵥ y) := by ring
  · -- `λ₁ = 0`: every eigenvalue vanishes; take `y = b`
    have hall : ∀ i, hH.eigenvalues i = 0 := fun i =>
      le_antisymm (hL0 ▸ htop i) (hpsd i)
    have hbAb : b ⬝ᵥ (A *ᵥ b) = 0 := by
      have := quadForm_eq_sum_eigenvalues hH b
      simp only [quadForm_def, star_trivial, hall, zero_mul, Finset.sum_const_zero] at this
      exact this
    refine ⟨b, self_mem_krylovSpace_succ A b q, fun h0 => ?_, ?_⟩
    · exact hb (by rw [h0, dotProduct_zero])
    · rw [← hL0, hbAb]; simp

variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq n] in
/-- Rayleigh quotients over `range Q` are bounded by any upper bound `θ` on the eigenvalues of
`QᵀAQ` (the Ritz values), for `Q` with orthonormal columns: `yᵀAy ≤ θ ‖y‖²` for `y ∈ range Q`.
Source: Parlett (1998), Thm 11.4.1 (Rayleigh–Ritz). Atlas: `ritz-value-bounds` (helper). -/
theorem dotProduct_mulVec_le_of_mem_range {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) {θ : ℝ}
    (hθ : ∀ j, (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ≤ θ) {y : n → ℝ}
    (hy : y ∈ LinearMap.range Q.mulVecLin) :
    y ⬝ᵥ (A *ᵥ y) ≤ θ * (y ⬝ᵥ y) := by
  obtain ⟨z, rfl⟩ := hy
  simp only [Matrix.mulVecLin_apply]
  have h := dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues (Matrix.isHermitian_conjTranspose_mul_mul Q hA)
    hθ z
  have hQz := star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ z
  simp only [star_trivial] at hQz
  rw [hQz]
  calc (Q *ᵥ z) ⬝ᵥ (A *ᵥ (Q *ᵥ z)) = z ⬝ᵥ ((Qᵀ * A * Q) *ᵥ z) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Qᵀ,
          Matrix.vecMul_transpose]
    _ ≤ θ * (z ⬝ᵥ z) := h

/-- **Gap-free Ritz-value bound.** Let `A` be positive semidefinite with top eigenvalue
`λ₁ = λ₀(A)` and unit eigenvector `u`, `0 < ε < 1`, `u ⬝ b ≠ 0`, and `Q` with orthonormal
columns and `K_{q+1}(A, b) ⊆ range Q` (e.g. the Lanczos basis after `q` matvecs). Then some Ritz
value `θ_j` (eigenvalue of `QᵀAQ`) satisfies
`λ₁ − θ_j ≤ ε λ₁ + λ₁ (2/(1 + √(2γ)))^{2q} ‖b‖²/(u ⬝ b)²`, `γ = ε/(1 − ε)`.
Source: Musco–Musco (2015) [`mm15`], Thm 1 (single-vector, gap-free); Kuczyński–Woźniakowski
(1992) [`kw92`] for the random-start analysis. The gap-dependent bound of Saad (2011), Thm 6.4,
is `eigenvalues_sub_eigenvalues_transpose_mul_mul_le` (`kaniel-paige-saad`).
Deviation: `K_{q+1}` and the exponent `q` (the source counts the Krylov dimension).
atlas: ritz-value-bounds -/
theorem exists_eigenvalues_transpose_mul_mul_ge [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {u : n → ℝ} (hu : A *ᵥ u = hA.isHermitian.eigenvalues₀ 0 • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {b : n → ℝ}
    (hb : u ⬝ᵥ b ≠ 0) (q : ℕ) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hK : krylovSpace A b (q + 1) ≤ LinearMap.range Q.mulVecLin) :
    ∃ j, hA.isHermitian.eigenvalues₀ 0 -
        (Matrix.isHermitian_conjTranspose_mul_mul Q hA.isHermitian).eigenvalues j ≤
      ε * hA.isHermitian.eigenvalues₀ 0 + hA.isHermitian.eigenvalues₀ 0 *
        (2 / (1 + √(2 * (ε / (1 - ε)))) ^ q) ^ 2 * ‖WithLp.toLp 2 b‖ ^ 2 / (u ⬝ᵥ b) ^ 2 := by
  obtain ⟨y, hyK, hy0, hy⟩ := exists_mem_krylovSpace_sub_rayleigh_le hA hu hu1 hε0 hε1 hb q
  obtain ⟨z, hz⟩ := hK hyK
  have hk : Nonempty k := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hy0
    rw [← hz]
    ext r
    simp [Matrix.mulVec, dotProduct]
  set hT := (Matrix.isHermitian_conjTranspose_mul_mul Q hA.isHermitian)
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ hT.eigenvalues Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hR := dotProduct_mulVec_le_of_mem_range hA.isHermitian hQ (θ := hT.eigenvalues j)
    (fun j' => hj j' (Finset.mem_univ _)) (hK hyK)
  rw [norm_toLp_sq_eq_dotProduct_self] at hy
  have hpos : 0 < y ⬝ᵥ y := lt_of_le_of_ne (dotProduct_self_nonneg y)
    (Ne.symm fun h => hy0 (dotProduct_self_eq_zero.mp h))
  set B := ε * hA.isHermitian.eigenvalues₀ 0 + hA.isHermitian.eigenvalues₀ 0 *
    (2 / (1 + √(2 * (ε / (1 - ε)))) ^ q) ^ 2 * ‖WithLp.toLp 2 b‖ ^ 2 / (u ⬝ᵥ b) ^ 2
  have : (hA.isHermitian.eigenvalues₀ 0 - hT.eigenvalues j) * (y ⬝ᵥ y) ≤ B * (y ⬝ᵥ y) := by
    nlinarith
  exact le_of_mul_le_mul_right this hpos

/-! ### Gap-dependent bounds: the eigenvector angle and Kaniel–Paige–Saad -/

/-- **The shifted Chebyshev amplifier.** For `a < c < L` and every `q` there is a polynomial
`p` of degree at most `q` with `p(L) = 1` and `|p| ≤ 1/T_q(1 + 2γ)` on `[a, c]`,
`γ = (L − c)/(c − a)`: namely `p(x) = T_q((2x − c − a)/(c − a))/T_q(1 + 2γ)`, the
`chebyshevAmplifier` with `α = (c − a)/2`, `γ' = 2γ`, shifted by `(c + a)/2`.
Source: Saad (2011) [`saad11`], §6.6.1. Helper for `krylov-eigenvector-angle` (belongs in
`NLAlib.Polynomial.FunctionApproximation.Approximation` next to `chebyshev-amplifier`). -/
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

/-- **Angle between the top eigenvector and the Krylov space (Chebyshev bound).** Let `A` be
real symmetric with top eigenvalue `λ₁ = λ₀(A)` and unit eigenvector `u`, and suppose every other
eigenvalue (every sorted position `≠ 0`) lies in `[a, c]` with `a < c < λ₁` (e.g. `a = λₙ`,
`c = λ₂`). If `u ⬝ b ≠ 0` then `K_{q+1}(A, b)` contains `x` with `u ⬝ x ≠ 0` and
`tan² ∠(u, x) ≤ tan² ∠(u, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`.
The witness is `x = T_q((2A − (c + a)I)/(c − a)) b`, written through `chebyshevAmplifier`.
Source: Saad (2011) [`saad11`], §6.6.1 (case `i = 1`); Saad (2003), §6.11.
Deviation: squared tangents; Krylov dimension `q + 1` (Saad's `m`) so that the degree is `q`;
an arbitrary enclosure `[a, c]` of the other eigenvalues instead of `[λₙ, λ₂]`.
atlas: krylov-eigenvector-angle -/
theorem exists_mem_krylovSpace_overlapTangentSq_le [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ 0 • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {a c : ℝ} (hac : a < c) (hc : c < hA.eigenvalues₀ 0)
    (hspec : ∀ i, i ≠ 0 → hA.eigenvalues₀ i ∈ Set.Icc a c) {b : n → ℝ} (hb : u ⬝ᵥ b ≠ 0)
    (q : ℕ) :
    ∃ x ∈ krylovSpace A b (q + 1), u ⬝ᵥ x ≠ 0 ∧
      overlapTangentSq u x ≤ overlapTangentSq u b /
        (Chebyshev.T ℝ q).eval (1 + 2 * ((hA.eigenvalues₀ 0 - c) / (c - a))) ^ 2 := by
  obtain ⟨p, hpdeg, hp1, hM⟩ := exists_degree_le_eval_eq_one_abs_eval_le hac hc q
  replace hM : ∀ i, i ≠ 0 → |p.eval (hA.eigenvalues₀ i)| ≤ _ := fun i hi => hM _ (hspec i hi)
  refine ⟨aeval A p *ᵥ b, (mem_krylovSpace_iff A b (q + 1) _).2
    ⟨p, hpdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self q), rfl⟩, ?_, ?_⟩
  · rw [dotProduct_aeval_mulVec_of_mulVec_eq_smul hA hu, hp1, one_mul]; exact hb
  · refine (overlapTangentSq_aeval_mulVec_le hA hu hu1 hM b).trans (le_of_eq ?_)
    rw [hp1, div_one, div_pow, one_pow, one_div_mul_eq_div]

/-- The growth of `T_q` in gap form: for `γ ≥ 0`,
`(1 + 2γ + 2√(γ + γ²))^q / 2 ≤ T_q(1 + 2γ)`. Source: Saad (2011) [`saad11`], §6.6.1 (after
Thm 6.3). Helper for `krylov-eigenvector-angle`; an instance of `chebyshev-growth` (belongs in
`NLAlib.Polynomial.Chebyshev.Growth`). -/
theorem pow_div_two_le_eval_T_real_one_add_two_mul {γ : ℝ} (hγ : 0 ≤ γ) (q : ℕ) :
    (1 + 2 * γ + 2 * √(γ + γ ^ 2)) ^ q / 2 ≤ (Chebyshev.T ℝ q).eval (1 + 2 * γ) := by
  have h := pow_div_two_le_eval_T_real (by linarith : (1 : ℝ) ≤ 1 + 2 * γ) q
  have hs : √((1 + 2 * γ) ^ 2 - 1) = 2 * √(γ + γ ^ 2) := by
    rw [show (1 + 2 * γ) ^ 2 - 1 = 2 ^ 2 * (γ + γ ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rwa [hs] at h

/-- **Eigenvector angle, explicit rate.** Under the hypotheses of
`exists_mem_krylovSpace_overlapTangentSq_le`, `K_{q+1}(A, b)` contains `x` with `u ⬝ x ≠ 0` and
`tan² ∠(u, x) ≤ (2/(1 + 2γ + 2√(γ + γ²))^q)² tan² ∠(u, b)`, `γ = (λ₁ − c)/(c − a)`.
Source: Saad (2011) [`saad11`], §6.6.1.
atlas: krylov-eigenvector-angle -/
theorem exists_mem_krylovSpace_overlapTangentSq_le_two_div_pow [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ 0 • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {a c : ℝ} (hac : a < c) (hc : c < hA.eigenvalues₀ 0)
    (hspec : ∀ i, i ≠ 0 → hA.eigenvalues₀ i ∈ Set.Icc a c) {b : n → ℝ} (hb : u ⬝ᵥ b ≠ 0)
    (q : ℕ) :
    ∃ x ∈ krylovSpace A b (q + 1), u ⬝ᵥ x ≠ 0 ∧
      overlapTangentSq u x ≤
        (2 / (1 + 2 * ((hA.eigenvalues₀ 0 - c) / (c - a)) +
          2 * √((hA.eigenvalues₀ 0 - c) / (c - a) + ((hA.eigenvalues₀ 0 - c) / (c - a)) ^ 2))
            ^ q) ^ 2 * overlapTangentSq u b := by
  obtain ⟨x, hxK, hx0, hx⟩ := exists_mem_krylovSpace_overlapTangentSq_le hA hu hu1 hac hc hspec hb q
  refine ⟨x, hxK, hx0, hx.trans ?_⟩
  set γ := (hA.eigenvalues₀ 0 - c) / (c - a)
  have hγ : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have hT := pow_div_two_le_eval_T_real_one_add_two_mul hγ q
  set ρ := (1 + 2 * γ + 2 * √(γ + γ ^ 2)) ^ q
  have hρ : 0 < ρ := by positivity
  have htan := overlapTangentSq_nonneg u b
  rw [div_eq_mul_inv, mul_comm, ← inv_pow]
  refine mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (inv_nonneg.2 (by linarith [div_pos hρ two_pos])) ?_ 2) htan
  have := inv_anti₀ (by positivity : 0 < ρ / 2) hT
  rwa [inv_div] at this

/-- The Ritz values are at most the top eigenvalue: `θⱼ ≤ λ₀(A)` for every eigenvalue `θⱼ` of
`Qᵀ A Q`, `Q` with orthonormal columns. This is the lower half `0 ≤ λ₁ − θ₁` of the
Kaniel–Paige–Saad bound. Source: Saad (2011) [`saad11`], Thm 6.4 (left inequality; Cauchy
interlacing).
atlas: kaniel-paige-saad (partial) -/
theorem eigenvalues_transpose_mul_mul_le [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (j : k) :
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ≤ hA.eigenvalues₀ 0 := by
  have hlow : ∀ i, -∑ i', |hA.eigenvalues i'| ≤ hA.eigenvalues i := fun i => by
    have := Finset.single_le_sum (f := fun i' => |hA.eigenvalues i'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [neg_abs_le (hA.eigenvalues i)]
  exact (eigenvalues_transpose_mul_mul_mem_Icc hA hQ
    (fun i => ⟨hlow i, hA.eigenvalues_le_eigenvalues₀_zero i⟩) j).2

/-- **Rayleigh–Ritz step of Kaniel–Paige–Saad.** Let `A` be real symmetric with every
eigenvalue `≥ a`, `u` a unit eigenvector for the eigenvalue `λ` at sorted position `i₀`, `Q`
with orthonormal columns, `θ₁ = θ_{j₁}` the largest eigenvalue of `Qᵀ A Q`, and `x ∈ range Q`
with `u ⬝ x ≠ 0`. Then `λ − θ₁ ≤ (λ − a) tan² ∠(u, x)` (from
`λ − xᵀAx/xᵀx ≤ (λ − a) sin² ∠(u, x)`). Source: Saad (2011) [`saad11`], proof of Thm 6.4.
Helper for `kaniel-paige-saad`. -/
theorem eigenvalues_sub_eigenvalues_le_mul_overlapTangentSq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i₀ : Fin (Fintype.card n)} {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {a : ℝ} (ha : ∀ i, a ≤ hA.eigenvalues i)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) {j₁ : k}
    (hj₁ : ∀ j, (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ≤
      (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁)
    {x : n → ℝ} (hxQ : x ∈ LinearMap.range Q.mulVecLin) (hx : u ⬝ᵥ x ≠ 0) :
    hA.eigenvalues₀ i₀ - (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁ ≤
      (hA.eigenvalues₀ i₀ - a) * overlapTangentSq u x := by
  set L := hA.eigenvalues₀ i₀ with hLdef
  set θ := (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁
  set c := u ⬝ᵥ x with hcdef
  set w := x - c • u with hwdef
  have huu : u ⬝ᵥ u = 1 := dotProduct_self_eq_one hu1
  have hR := dotProduct_mulVec_le_of_mem_range hA hQ hj₁ hxQ
  have huw : u ⬝ᵥ w = 0 := by
    simp only [hwdef, dotProduct_sub, dotProduct_smul, huu, smul_eq_mul, mul_one, ← hcdef, sub_self]
  set N := w ⬝ᵥ w with hNdef
  have hxx : x ⬝ᵥ x = c ^ 2 + N := by
    have : x = c • u + w := by simp [hwdef]
    rw [this, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_smul, smul_dotProduct,
      dotProduct_smul, smul_dotProduct, huu, dotProduct_comm w u, huw]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hsymm : ∀ y z : n → ℝ, y ⬝ᵥ (A *ᵥ z) = (A *ᵥ y) ⬝ᵥ z := fun y z => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      (Matrix.isHermitian_iff_isSymm.mp hA).eq]
  have hAu : ∀ z : n → ℝ, u ⬝ᵥ (A *ᵥ z) = L * (u ⬝ᵥ z) := fun z => by
    rw [hsymm, hu, smul_dotProduct, smul_eq_mul]
  have hxAx : x ⬝ᵥ (A *ᵥ x) = L * c ^ 2 + w ⬝ᵥ (A *ᵥ w) := by
    have : x = c • u + w := by simp [hwdef]
    rw [this]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hAu]
    rw [hu, dotProduct_smul, dotProduct_comm w u, huw, huu]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hS : a * N ≤ w ⬝ᵥ (A *ᵥ w) := mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues hA ha w
  have hN : 0 ≤ N := dotProduct_self_nonneg w
  have hc1 : 0 < c ^ 2 := by positivity
  have haL : 0 ≤ L - a := by
    have := ha (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq] at this
    linarith
  rw [overlapTangentSq_of_norm_eq_one hu1, hxx, ← hcdef, show c ^ 2 + N - c ^ 2 = N by ring,
    ← mul_div_assoc, le_div_iff₀ hc1]
  rw [hxx, hxAx] at hR
  have key : (L - θ) * (c ^ 2 + N) ≤ (L - a) * N := by nlinarith
  rcases le_or_gt (L - θ) 0 with hneg | hpos
  · nlinarith
  · nlinarith

/-- **Kaniel–Paige–Saad, polynomial form.** Let `A` be real symmetric with every eigenvalue
`≥ a`, `u` a unit eigenvector for the eigenvalue `λ` at sorted position `i₀`, `u ⬝ b ≠ 0`, `Q`
with orthonormal columns and `K_q(A, b) ⊆ range Q`, and `θ₁` the largest eigenvalue of `Qᵀ A Q`.
For every polynomial `p` with `deg p < q`, `p(λ) ≠ 0` and `|p| ≤ M` at every other sorted
position: `λ − θ₁ ≤ (λ − a) (M/p(λ))² tan² ∠(u, b)`.
Source: Saad (2011) [`saad11`], proof of Thm 6.4 (`i = 1`).
atlas: kaniel-paige-saad (partial) -/
theorem eigenvalues_sub_eigenvalues_transpose_mul_mul_le_of_poly {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {i₀ : Fin (Fintype.card n)} {u : n → ℝ}
    (hu : A *ᵥ u = hA.eigenvalues₀ i₀ • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) {a : ℝ}
    (ha : ∀ i, a ≤ hA.eigenvalues i) {b : n → ℝ} (hb : u ⬝ᵥ b ≠ 0) {q : ℕ} {p : ℝ[X]}
    (hp : p.degree < q) (hp1 : p.eval (hA.eigenvalues₀ i₀) ≠ 0) {M : ℝ}
    (hM : ∀ i, i ≠ i₀ → |p.eval (hA.eigenvalues₀ i)| ≤ M) {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hK : krylovSpace A b q ≤ LinearMap.range Q.mulVecLin)
    {j₁ : k} (hj₁ : ∀ j, (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ≤
      (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁) :
    hA.eigenvalues₀ i₀ - (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁ ≤
      (hA.eigenvalues₀ i₀ - a) *
        ((M / p.eval (hA.eigenvalues₀ i₀)) ^ 2 * overlapTangentSq u b) := by
  have hxK : aeval A p *ᵥ b ∈ krylovSpace A b q :=
    (mem_krylovSpace_iff A b q _).2 ⟨p, hp, rfl⟩
  have hx0 : u ⬝ᵥ (aeval A p *ᵥ b) ≠ 0 := by
    rw [dotProduct_aeval_mulVec_of_mulVec_eq_smul hA hu]; exact mul_ne_zero hp1 hb
  have haL : 0 ≤ hA.eigenvalues₀ i₀ - a := by
    have := ha (Fintype.equivOfCardEq (Fintype.card_fin _) i₀)
    rw [hA.eigenvalues_equivOfCardEq] at this
    linarith
  refine (eigenvalues_sub_eigenvalues_le_mul_overlapTangentSq hA hu hu1 ha hQ hj₁ (hK hxK)
    hx0).trans ?_
  exact mul_le_mul_of_nonneg_left (overlapTangentSq_aeval_mulVec_le hA hu hu1 hM b) haL

/-- **Kaniel–Paige–Saad bound for the largest Ritz value.** Let `A` be real symmetric with top
eigenvalue `λ₁ = λ₀(A)` and unit eigenvector `u`, every other eigenvalue (sorted position `≠ 0`)
in `[a, c]` with `a < c < λ₁` (e.g. `a = λₙ`, `c = λ₂`), `u ⬝ b ≠ 0`, `Q` with orthonormal
columns and `K_{q+1}(A, b) ⊆ range Q` (e.g. a Lanczos basis after `q` matvecs), and `θ₁` the
largest eigenvalue of `Qᵀ A Q`. Then
`λ₁ − θ₁ ≤ (λ₁ − a) tan² ∠(u, b) / T_q(1 + 2γ)²`, `γ = (λ₁ − c)/(c − a)`; the lower bound
`0 ≤ λ₁ − θ₁` is `eigenvalues_transpose_mul_mul_le`.
Source: Saad (2011) [`saad11`], Thm 6.4 (`i = 1`); Golub–Meurant (2010) [`gm10`], Ch. 4.
Deviation: Krylov dimension `q + 1` (Saad's `m`, so `T_{m−1} = T_q`); `[a, c]` any enclosure
of the other eigenvalues (Saad: `a = λₙ`, `c = λ₂`, factor `λ₁ − λₙ`); any orthonormal `Q`
whose range contains the Krylov space.
atlas: kaniel-paige-saad -/
theorem eigenvalues_sub_eigenvalues_transpose_mul_mul_le [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {u : n → ℝ} (hu : A *ᵥ u = hA.eigenvalues₀ 0 • u)
    (hu1 : ‖WithLp.toLp 2 u‖ = 1) {a c : ℝ} (hac : a < c) (hc : c < hA.eigenvalues₀ 0)
    (hspec : ∀ i, i ≠ 0 → hA.eigenvalues₀ i ∈ Set.Icc a c) {b : n → ℝ} (hb : u ⬝ᵥ b ≠ 0)
    (q : ℕ) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hK : krylovSpace A b (q + 1) ≤ LinearMap.range Q.mulVecLin) {j₁ : k}
    (hj₁ : ∀ j, (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ≤
      (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁) :
    hA.eigenvalues₀ 0 - (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j₁ ≤
      (hA.eigenvalues₀ 0 - a) * (overlapTangentSq u b /
        (Chebyshev.T ℝ q).eval (1 + 2 * ((hA.eigenvalues₀ 0 - c) / (c - a))) ^ 2) := by
  have ha : ∀ i, a ≤ hA.eigenvalues i := fun i => by
    set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
    have hi : hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := rfl
    rw [hi]
    by_cases h0 : e.symm i = 0
    · rw [h0]; linarith
    · exact (hspec _ h0).1
  obtain ⟨x, hxK, hx0, hx⟩ := exists_mem_krylovSpace_overlapTangentSq_le hA hu hu1 hac hc hspec hb q
  exact (eigenvalues_sub_eigenvalues_le_mul_overlapTangentSq hA hu hu1 ha hQ hj₁ (hK hxK) hx0).trans
    (mul_le_mul_of_nonneg_left hx (by
      have htop := ha (Fintype.equivOfCardEq (Fintype.card_fin _) 0)
      rw [hA.eigenvalues_equivOfCardEq] at htop
      linarith))

end NLAlib

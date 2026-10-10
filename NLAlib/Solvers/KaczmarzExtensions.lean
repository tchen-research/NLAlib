import NLAlib.Solvers.Kaczmarz
import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.Spectral
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Randomized Kaczmarz: inconsistent and rank-deficient systems

Extensions of Strohmer–Vershynin's bound (`NLAlib.Kaczmarz.expErr_le`), in the same
finite-sum model of the expectation (`NLAlib.Kaczmarz.expErr`).

* **Inconsistent systems** (Needell 2010; Zouzias–Freris 2013): for any reference point `xh`
  (for example a least-squares solution) and `e = b − A xh`,
  `E‖x_k − xh‖² ≤ ρ^k ‖x₀ − xh‖² + (∑_{j<k} ρ^j) ‖e‖²/‖A‖_F²`, `ρ = 1 − σ²/‖A‖_F²`
  (`NLAlib.Kaczmarz.expErr_le_add`), hence `≤ ρ^k ‖x₀ − xh‖² + ‖e‖²/σ²` for `σ > 0`
  (`NLAlib.Kaczmarz.expErr_le_add_div_sq`).
* **Rank-deficient consistent systems**: the lower bound `σ²‖v‖² ≤ ‖Av‖²` is needed only on the
  row space, provided the initial error lies there (`NLAlib.Kaczmarz.expErr_le_of_sub_mem_range`);
  with `σ = ‖A⁺‖⁻¹` and `x₀ = 0` the iterates converge to the least-norm solution `A⁺b`
  (`NLAlib.Kaczmarz.expErr_zero_le_moorePenroseInverse`).

Source: Needell (2010) [`needell10`], Thm 2.1; Zouzias–Freris (2013) [`zf13`], Thm 2 / eq. (5);
Strohmer–Vershynin (2009) [`sv09`], Thm 2. Atlas: `randomized-kaczmarz` (extensions);
`kaczmarz-inconsistent`, `kaczmarz-rank-deficient` (new).
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

namespace Kaczmarz

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- One Kaczmarz step from an arbitrary reference point `xh` (no consistency assumed): with
`e = b − A xh`,
`‖step A b x i − xh‖² = ‖x − xh‖² − (Aᵢ ⬝ (x − xh))²/‖Aᵢ‖² + eᵢ²/‖Aᵢ‖²`.
Source: Needell (2010) [`needell10`], proof of Thm 2.1. Atlas: `kaczmarz-inconsistent`. -/
theorem sqErr_step_eq_add (A : Matrix m n ℝ) (b : m → ℝ) (xh x : n → ℝ) (i : m) :
    (step A b x i - xh) ⬝ᵥ (step A b x i - xh) =
      (x - xh) ⬝ᵥ (x - xh) - (A i ⬝ᵥ (x - xh)) ^ 2 / (A i ⬝ᵥ A i) +
        (b i - A i ⬝ᵥ xh) ^ 2 / (A i ⬝ᵥ A i) := by
  set d := x - xh
  set a := A i
  have hstep : step A b x i - xh = d + ((b i - a ⬝ᵥ xh - a ⬝ᵥ d) / (a ⬝ᵥ a)) • a := by
    simp only [step, d, a, dotProduct_sub]
    abel_nf
  rw [hstep]
  have hda : d ⬝ᵥ a = a ⬝ᵥ d := dotProduct_comm _ _
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hda]
  by_cases ha : a ⬝ᵥ a = 0
  · have : a = 0 := dotProduct_self_eq_zero.mp ha
    simp [this]
  · field_simp
    ring

/-- One-step bound for inconsistent systems: if `σ²‖v‖² ≤ ‖Av‖²` for all `v`, then for any `xh`
`∑ᵢ pᵢ ‖step A b x i − xh‖² ≤ (1 − σ²/‖A‖_F²) ‖x − xh‖² + ‖b − A xh‖²/‖A‖_F²`.
Source: Needell (2010) [`needell10`], proof of Thm 2.1. Atlas: `kaczmarz-inconsistent`. -/
theorem expected_sqErr_step_le_add (A : Matrix m n ℝ) (b : m → ℝ) (xh x : n → ℝ) (σ : ℝ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) :
    ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) ≤
      (1 - σ ^ 2 / frobSq A) * ((x - xh) ⬝ᵥ (x - xh)) +
        (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A := by
  by_cases hA : A = 0
  · subst hA
    simp only [prob, frobSq_zero, div_zero, zero_mul, Finset.sum_const_zero, sub_zero, one_mul,
      add_zero]
    exact dotProduct_self_nonneg _
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hterm : ∀ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) ≤
      prob A i * ((x - xh) ⬝ᵥ (x - xh)) - (A i ⬝ᵥ (x - xh)) ^ 2 / frobSq A +
        (b - A *ᵥ xh) i ^ 2 / frobSq A := fun i => by
    rw [sqErr_step_eq_add A b xh x i]
    have hei : (b - A *ᵥ xh) i = b i - A i ⬝ᵥ xh := rfl
    rw [hei]
    by_cases ha : A i ⬝ᵥ A i = 0
    · have h0 : A i = 0 := dotProduct_self_eq_zero.mp ha
      have hp : prob A i = 0 := by simp [prob, h0]
      rw [hp, h0]
      simp only [zero_mul, zero_dotProduct, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, zero_add]
      exact div_nonneg (sq_nonneg _) (frobSq_nonneg A)
    · rw [prob]
      apply le_of_eq
      field_simp
  set d := x - xh
  set e := b - A *ᵥ xh
  calc ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh))
      ≤ ∑ i, (prob A i * (d ⬝ᵥ d) - (A i ⬝ᵥ d) ^ 2 / frobSq A + e i ^ 2 / frobSq A) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = d ⬝ᵥ d - (A *ᵥ d) ⬝ᵥ (A *ᵥ d) / frobSq A + e ⬝ᵥ e / frobSq A := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_prob A hA,
          one_mul, ← Finset.sum_div, ← Finset.sum_div, mulVec_dotProduct_mulVec_eq_sum_sq]
        simp only [dotProduct, sq]
    _ ≤ (1 - σ ^ 2 / frobSq A) * (d ⬝ᵥ d) + e ⬝ᵥ e / frobSq A := by
        have h := div_le_div_of_nonneg_right (hσ d) hF.le
        rw [sub_mul, one_mul, div_mul_eq_mul_div]
        linarith

/-- **Randomized Kaczmarz on inconsistent systems.** If `σ²‖v‖² ≤ ‖Av‖²` for all `v`, then for
any reference point `xh` and `e = b − A xh`, with `ρ = 1 − σ²/‖A‖_F²`,
`E‖x_k − xh‖² ≤ ρ^k ‖x₀ − xh‖² + (∑_{j<k} ρ^j) ‖e‖²/‖A‖_F²`.
Source: Needell (2010) [`needell10`], Thm 2.1 (stated for norms, with `xh` the least-squares
solution); Zouzias–Freris (2013) [`zf13`], eq. (5) (squared form).
Atlas: `kaczmarz-inconsistent`; uses `randomized-kaczmarz`.
Deviation: any reference point `xh` (no least-squares or consistency assumption); the geometric
sum is kept exact. -/
theorem expErr_le_add (A : Matrix m n ℝ) (b : m → ℝ) (xh : n → ℝ) (σ : ℝ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) (x : n → ℝ) (k : ℕ) :
    expErr A b xh x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
      (∑ j ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ j) *
        ((b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A) := by
  classical
  set ρ := 1 - σ ^ 2 / frobSq A
  set c := (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / frobSq A
  have hc : 0 ≤ c := div_nonneg (dotProduct_self_nonneg _) (frobSq_nonneg A)
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ v : n → ℝ, v ⬝ᵥ v = 0 := fun v => by simp [dotProduct]
    have : ∀ k (x : n → ℝ), expErr A b xh x k = 0 := by
      intro k
      induction k with
      | zero => intro x; exact h0 _
      | succ k ih => intro x; simp [expErr_succ, ih]
    rw [this, h0, mul_zero, zero_add]
    have hρ : ρ = 1 := by
      have hF : frobSq A = 0 := by
        rw [frobSq_eq_zero_iff]; ext i j; exact (IsEmpty.false j).elim
      simp [ρ, hF]
    rw [hρ]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact mul_nonneg (Nat.cast_nonneg k) hc
  have hρ : 0 ≤ ρ := rate_nonneg A σ hσ
  have hsum : ∀ i, 0 ≤ prob A i := prob_nonneg A
  have hsum1 : ∑ i, prob A i ≤ 1 := by
    by_cases hA : A = 0
    · subst hA; simp [prob]
    · rw [sum_prob A hA]
  induction k generalizing x with
  | zero => simp [expErr_zero]
  | succ k ih =>
    rw [expErr_succ, Finset.sum_range_succ]
    have hS : 0 ≤ ∑ j ∈ Finset.range k, ρ ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hρ j
    generalize ∑ j ∈ Finset.range k, ρ ^ j = S at ih hS ⊢
    calc ∑ i, prob A i * expErr A b xh (step A b x i) k
        ≤ ∑ i, prob A i * (ρ ^ k * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) + S * c) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih _) (hsum i)
      _ = ρ ^ k * ∑ i, prob A i * ((step A b x i - xh) ⬝ᵥ (step A b x i - xh)) +
            (∑ i, prob A i) * (S * c) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ρ ^ k * (ρ * ((x - xh) ⬝ᵥ (x - xh)) + c) + 1 * (S * c) := by
          gcongr
          exact expected_sqErr_step_le_add A b xh x σ hσ
      _ = ρ ^ (k + 1) * ((x - xh) ⬝ᵥ (x - xh)) + (S + ρ ^ k) * c := by ring

/-- **Randomized Kaczmarz on inconsistent systems, horizon form.** If `σ > 0` and
`σ²‖v‖² ≤ ‖Av‖²` for all `v`, then for any `xh`,
`E‖x_k − xh‖² ≤ (1 − σ²/‖A‖_F²)^k ‖x₀ − xh‖² + ‖b − A xh‖²/σ²`.
Source: Needell (2010) [`needell10`], Thm 2.1 (squared form, `R = ‖A‖_F²/σ²`);
Zouzias–Freris (2013) [`zf13`], Thm 2. Atlas: `kaczmarz-inconsistent`. -/
theorem expErr_le_add_div_sq (A : Matrix m n ℝ) (b : m → ℝ) (xh : n → ℝ) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ v : n → ℝ, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)) (x : n → ℝ) (k : ℕ) :
    expErr A b xh x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xh) ⬝ᵥ (x - xh)) +
      (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh) / σ ^ 2 := by
  classical
  refine (expErr_le_add A b xh σ hσ x k).trans (add_le_add le_rfl ?_)
  set c := (b - A *ᵥ xh) ⬝ᵥ (b - A *ᵥ xh)
  have hc : 0 ≤ c := dotProduct_self_nonneg _
  rcases isEmpty_or_nonempty n with hn | hn
  · -- no columns: `frobSq A = 0`, so the noise term is `0`
    have hF : frobSq A = 0 := by
      rw [frobSq_eq_zero_iff]; ext i j; exact (IsEmpty.false j).elim
    simp only [hF, div_zero, mul_zero]
    positivity
  have j : n := hn.some
  have hA : A ≠ 0 := by
    intro h0
    have := hσ (Pi.single j 1)
    have h1 : (Pi.single j (1 : ℝ) : n → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by simp
    rw [h1, mul_one, h0, Matrix.zero_mulVec, dotProduct_zero] at this
    nlinarith [sq_pos_of_pos hσ0]
  have hF : 0 < frobSq A :=
    lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hρ0 : 0 ≤ 1 - σ ^ 2 / frobSq A := rate_nonneg A σ hσ
  have hρ1 : 1 - σ ^ 2 / frobSq A < 1 := by
    have : 0 < σ ^ 2 / frobSq A := div_pos (by positivity) hF
    linarith
  have hgeom : ∑ i ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ i ≤ frobSq A / σ ^ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hρ0 hρ1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  calc (∑ i ∈ Finset.range k, (1 - σ ^ 2 / frobSq A) ^ i) * (c / frobSq A)
      ≤ frobSq A / σ ^ 2 * (c / frobSq A) :=
        mul_le_mul_of_nonneg_right hgeom (div_nonneg hc hF.le)
    _ = c / σ ^ 2 := by field_simp

/-! ### Rank-deficient consistent systems -/

/-- Kaczmarz steps keep the error in the row space: if `A xs = b` and `x − xs ∈ range Aᵀ`, then
`step A b x i − xs ∈ range Aᵀ`. Atlas: `kaczmarz-rank-deficient` (helper). -/
theorem step_sub_mem_range [DecidableEq m] (A : Matrix m n ℝ) (b : m → ℝ) (xs x : n → ℝ)
    (hxs : A *ᵥ xs = b) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (i : m) :
    step A b x i - xs ∈ LinearMap.range Aᵀ.mulVecLin := by
  rw [step_sub_solution A b xs x hxs i]
  refine Submodule.sub_mem _ hx (Submodule.smul_mem _ _ ⟨Pi.single i 1, ?_⟩)
  ext j
  simp

/-- **Randomized Kaczmarz on rank-deficient consistent systems.** If `A xs = b`, the initial
error `x − xs` lies in the row space `range Aᵀ`, and `σ²‖v‖² ≤ ‖Av‖²` for every `v` in the row
space, then `E‖x_k − xs‖² ≤ (1 − σ²/‖A‖_F²)^k ‖x − xs‖²`.
Source: Strohmer–Vershynin (2009) [`sv09`], Thm 2 in the form of Zouzias–Freris (2013) [`zf13`],
Thm 2 (`σ = σ_min⁺(A)`, the smallest nonzero singular value).
Atlas: `kaczmarz-rank-deficient`; uses `randomized-kaczmarz`. -/
theorem expErr_le_of_sub_mem_range [DecidableEq m] (A : Matrix m n ℝ) (b : m → ℝ)
    (xs : n → ℝ) (hxs : A *ᵥ xs = b) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    expErr A b xs x k ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  -- the rate is nonnegative
  have hρ : 0 ≤ 1 - σ ^ 2 / frobSq A := by
    by_cases hA : A = 0
    · subst hA; simp
    have hF : 0 < frobSq A :=
      lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
    obtain ⟨i, hi⟩ : ∃ i, A i ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (Matrix.ext fun i j => by simp [h i])
    have hmem : A i ∈ LinearMap.range Aᵀ.mulVecLin := ⟨Pi.single i 1, by
      ext j; simp⟩
    have h1 := hσ _ hmem
    have h2 := mulVec_dotProduct_mulVec_le_frobSq_mul A (A i)
    have hpos : 0 < A i ⬝ᵥ A i := lt_of_le_of_ne (dotProduct_self_nonneg _)
      (Ne.symm (fun h => hi (dotProduct_self_eq_zero.mp h)))
    have : σ ^ 2 ≤ frobSq A := le_of_mul_le_mul_right (h1.trans h2) hpos
    rw [sub_nonneg, div_le_one hF]
    exact this
  induction k generalizing x with
  | zero => simp [expErr_zero]
  | succ k ih =>
    rw [expErr_succ]
    have hstep : ∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) ≤
        (1 - σ ^ 2 / frobSq A) * ((x - xs) ⬝ᵥ (x - xs)) := by
      by_cases hA : A = 0
      · subst hA
        simp only [prob, frobSq_zero, div_zero, zero_mul, Finset.sum_const_zero, sub_zero,
          one_mul]
        exact dotProduct_self_nonneg _
      rw [expected_sqErr_step_eq A b xs x hxs hA]
      have hF : 0 < frobSq A :=
        lt_of_le_of_ne (frobSq_nonneg A) (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
      have h := div_le_div_of_nonneg_right (hσ _ hx) hF.le
      rw [sub_mul, one_mul, div_mul_eq_mul_div]
      linarith
    calc ∑ i, prob A i * expErr A b xs (step A b x i) k
        ≤ ∑ i, prob A i * ((1 - σ ^ 2 / frobSq A) ^ k *
            ((step A b x i - xs) ⬝ᵥ (step A b x i - xs))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (ih _ (step_sub_mem_range A b xs x hxs hx i)) (prob_nonneg A i)
      _ = (1 - σ ^ 2 / frobSq A) ^ k *
            ∑ i, prob A i * ((step A b x i - xs) ⬝ᵥ (step A b x i - xs)) := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ (1 - σ ^ 2 / frobSq A) ^ k * ((1 - σ ^ 2 / frobSq A) * ((x - xs) ⬝ᵥ (x - xs))) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hρ k)
      _ = (1 - σ ^ 2 / frobSq A) ^ (k + 1) * ((x - xs) ⬝ᵥ (x - xs)) := by ring

/-- The Moore–Penrose lower bound on the row space: for `v ∈ range Aᵀ`,
`‖A⁺‖⁻² ‖v‖² ≤ ‖Av‖²`. Source: Zouzias–Freris (2013) [`zf13`], §2 (`σ_min⁺ = ‖A⁺‖⁻¹`).
Atlas: `kaczmarz-rank-deficient` (helper). -/
theorem inv_specNorm_moorePenroseInverse_sq_mul_le [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) {v : n → ℝ} (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) :
    (specNorm (moorePenroseInverse A))⁻¹ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  set B := moorePenroseInverse A
  by_cases hB : specNorm B = 0
  · simp only [hB, _root_.inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    exact dotProduct_self_nonneg _
  obtain ⟨w, rfl⟩ := hv
  simp only [Matrix.mulVecLin_apply]
  have hfix : B *ᵥ (A *ᵥ (Aᵀ *ᵥ w)) = Aᵀ *ᵥ w := by
    have hsym : (B * A)ᵀ = B * A := moorePenroseInverse_mul_isSymm A
    have h : B * A * Aᵀ = Aᵀ := by
      calc B * A * Aᵀ = (B * A)ᵀ * Aᵀ := by rw [hsym]
        _ = (A * (B * A))ᵀ := (Matrix.transpose_mul _ _).symm
        _ = Aᵀ := by rw [← Matrix.mul_assoc, mul_moorePenroseInverse_mul]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  have hBound := sum_sq_mulVec_le_specNorm_sq B (A *ᵥ (Aᵀ *ᵥ w))
  rw [hfix] at hBound
  have hScale := mul_le_mul_of_nonneg_left hBound (sq_nonneg (specNorm B)⁻¹)
  have hCancel : (specNorm B)⁻¹ ^ 2 * specNorm B ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hB, one_pow]
  rw [← mul_assoc, hCancel, one_mul] at hScale
  simpa only [dotProduct, pow_two] using hScale

/-- **Randomized Kaczmarz converges to the least-norm solution.** For a consistent system
(`b ∈ range A`) started at `x₀ = 0`,
`E‖x_k − A⁺b‖² ≤ (1 − ‖A⁺‖⁻²/‖A‖_F²)^k ‖A⁺b‖²`, with no rank assumption.
Source: Zouzias–Freris (2013) [`zf13`], Thm 2 (`b ∈ range A`, `x₀ = 0`);
Needell–Tropp (2014), §1. Atlas: `kaczmarz-rank-deficient`; uses `pseudoinverse`. -/
theorem expErr_zero_le_moorePenroseInverse [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ)
    (b : m → ℝ) (hb : ∃ y, A *ᵥ y = b) (k : ℕ) :
    expErr A b (moorePenroseInverse A *ᵥ b) 0 k ≤
      (1 - (specNorm (moorePenroseInverse A))⁻¹ ^ 2 / frobSq A) ^ k *
        ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) := by
  set B := moorePenroseInverse A
  obtain ⟨y, rfl⟩ := hb
  have hxs : A *ᵥ (B *ᵥ (A *ᵥ y)) = A *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_moorePenroseInverse_mul]
  have hmem : (0 : n → ℝ) - B *ᵥ (A *ᵥ y) ∈ LinearMap.range Aᵀ.mulVecLin := by
    -- `B = B A B = (B A)ᵀ B = Aᵀ Bᵀ B`
    have hBeq : B = Aᵀ * (Bᵀ * B) := by
      have hsym : (B * A)ᵀ = B * A := moorePenroseInverse_mul_isSymm A
      calc B = B * A * B := (moorePenroseInverse_mul_moorePenroseInverse A).symm
        _ = (B * A)ᵀ * B := by rw [hsym]
        _ = Aᵀ * (Bᵀ * B) := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
    have hB' : B *ᵥ (A *ᵥ y) = Aᵀ *ᵥ ((Bᵀ * B) *ᵥ (A *ᵥ y)) := by
      conv_lhs => rw [hBeq]
      rw [← Matrix.mulVec_mulVec]
    refine ⟨-((Bᵀ * B) *ᵥ (A *ᵥ y)), ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg, zero_sub, hB']
  have h := expErr_le_of_sub_mem_range A (A *ᵥ y) (B *ᵥ (A *ᵥ y)) hxs
    (specNorm B)⁻¹ (fun v hv => inv_specNorm_moorePenroseInverse_sq_mul_le A hv) 0 hmem k
  simpa using h

end Kaczmarz

end NLAlib

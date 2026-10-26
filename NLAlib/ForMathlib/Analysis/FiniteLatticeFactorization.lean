import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Common power factors for finite lattice intersections

Finitely many positive power factorizations of the same vector can share
one Euclidean left factor. The new right factor is pointwise below every
old right factor, and the square of the left factor is the sum of the old
left squares. Thus any coordinatewise monotone endpoint norms are preserved
simultaneously. For three normalized profile norms the Euclidean loss is
only `sqrt 3`.

This is an explicit finite-dimensional substitute for the lattice
intersection step in Latała--van Handel--Youssef, arXiv:1711.00807v2, §2.3.
-/

noncomputable section

namespace NLAlib

/-- A finite collection of nonnegative factorizations
`a = u_l^(1-θ) v_l^θ` admits one common left factor whose square is exactly
the sum of the left squares, and one common right factor below every `v_l`.
Consequently all monotone right-endpoint lattice norms are controlled at
once, while Euclidean left-endpoint norms add in squares. Zero coordinates
and empty coordinate spaces are included. -/
theorem exists_common_power_factors_with_right_eq
    {ι κ : Type*} [Fintype ι] [Nonempty ι]
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (a : κ → ℝ) (u v : ι → κ → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hu : ∀ l x, 0 ≤ u l x) (hv : ∀ l x, 0 ≤ v l x)
    (hfactor : ∀ l x, a x = u l x ^ (1 - θ) * v l x ^ θ) :
    ∃ U V : κ → ℝ,
      (∀ x, 0 ≤ U x) ∧ (∀ x, 0 ≤ V x) ∧
      (∀ x, a x = U x ^ (1 - θ) * V x ^ θ) ∧
      (∀ x, U x ^ 2 = ∑ l, u l x ^ 2) ∧
      (∀ l x, V x ≤ v l x) ∧
      (∀ x, V x = (a x / U x ^ (1 - θ)) ^ θ⁻¹) := by
  classical
  let U : κ → ℝ := fun x => Real.sqrt (∑ l, u l x ^ 2)
  let V : κ → ℝ := fun x => (a x / U x ^ (1 - θ)) ^ θ⁻¹
  have hU : ∀ x, 0 ≤ U x := fun _ => Real.sqrt_nonneg _
  have hUsq (x : κ) : U x ^ 2 = ∑ l, u l x ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg (u l x))
  have hule (l : ι) (x : κ) : u l x ≤ U x := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ (Finset.univ : Finset ι)) =>
      sq_nonneg (u l x)) (Finset.mem_univ l)
    nlinarith [hUsq x, hU x, hu l x]
  have hVpow (x : κ) : V x ^ θ = a x / U x ^ (1 - θ) := by
    dsimp [V]
    exact Real.rpow_inv_rpow (div_nonneg (ha x) (Real.rpow_nonneg (hU x) _)) hθ.1.ne'
  refine ⟨U, V, hU, fun x => Real.rpow_nonneg
    (div_nonneg (ha x) (Real.rpow_nonneg (hU x) _)) _, ?_, hUsq, ?_, fun _ => rfl⟩
  · intro x
    rw [hVpow]
    by_cases hzero : U x = 0
    · have hueq : ∀ l, u l x = 0 := fun l => le_antisymm (by simpa [hzero] using hule l x) (hu l x)
      have hazero : a x = 0 := by
        rw [hfactor (Classical.arbitrary ι) x, hueq,
          Real.zero_rpow (by linarith [hθ.2] : 1 - θ ≠ 0), zero_mul]
      simp [hazero]
    · have hpowne : U x ^ (1 - θ) ≠ 0 :=
        (Real.rpow_pos_of_pos (lt_of_le_of_ne (hU x) (Ne.symm hzero)) _).ne'
      rw [mul_div_cancel₀ _ hpowne]
  · intro l x
    have hbound : a x ≤ U x ^ (1 - θ) * v l x ^ θ := by
      rw [hfactor l x]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hu l x) (hule l x) (by linarith [hθ.2]))
        (Real.rpow_nonneg (hv l x) _)
    have hdiv : a x / U x ^ (1 - θ) ≤ v l x ^ θ := by
      by_cases hzero : U x = 0
      · simp [hzero, Real.zero_rpow (by linarith [hθ.2] : 1 - θ ≠ 0),
          Real.rpow_nonneg (hv l x) θ]
      · apply (div_le_iff₀ (Real.rpow_pos_of_pos (lt_of_le_of_ne (hU x) (Ne.symm hzero)) _)).mpr
        simpa only [mul_comm] using hbound
    have hh := Real.rpow_le_rpow
      (div_nonneg (ha x) (Real.rpow_nonneg (hU x) _)) hdiv (inv_nonneg.mpr hθ.1.le)
    rwa [Real.rpow_rpow_inv (hv l x) hθ.1.ne'] at hh

/-- Common power factors for a finite family of lattice factorizations.
The left Euclidean power sums add in squares and every monotone right
endpoint norm is preserved. The strengthened variant
`exists_common_power_factors_with_right_eq` also gives the explicit right
factor formula, which preserves any symmetry of the input and left factor. -/
theorem exists_common_power_factors_of_power_factorizations
    {ι κ : Type*} [Fintype ι] [Nonempty ι]
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (a : κ → ℝ) (u v : ι → κ → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hu : ∀ l x, 0 ≤ u l x) (hv : ∀ l x, 0 ≤ v l x)
    (hfactor : ∀ l x, a x = u l x ^ (1 - θ) * v l x ^ θ) :
    ∃ U V : κ → ℝ,
      (∀ x, 0 ≤ U x) ∧ (∀ x, 0 ≤ V x) ∧
      (∀ x, a x = U x ^ (1 - θ) * V x ^ θ) ∧
      (∀ x, U x ^ 2 = ∑ l, u l x ^ 2) ∧
      (∀ l x, V x ≤ v l x) := by
  obtain ⟨U, V, hU, hV, hf, hsq, hle, _⟩ :=
    exists_common_power_factors_with_right_eq hθ a u v ha hu hv hfactor
  exact ⟨U, V, hU, hV, hf, hsq, hle⟩

private theorem sum_sq_mul_rpow_eq
    {κ : Type*} [Fintype κ] (a : κ → ℝ) {s t : ℝ} (hs : 0 ≤ s)
    (hsum : ∑ j, a j ^ 2 = s ^ 2) (ht : 0 < 2 + 2 * t) :
    ∑ j, (a j * s ^ t) ^ 2 = s ^ (2 + 2 * t) := by
  simp_rw [mul_pow, ← Finset.sum_mul, hsum]
  by_cases hs0 : s = 0
  · simp [hs0, Real.zero_rpow ht.ne']
  · have hspos := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [← Real.rpow_natCast s 2, ← Real.rpow_natCast (s ^ t) 2,
      ← Real.rpow_mul hs, ← Real.rpow_add hspos]
    congr 1
    norm_num
    ring

/-- Explicit simultaneous `ℓ₂`/`ℓ_q(ℓ₂)` power factors for a nonnegative
finite matrix at a target exponent `p ≥ 2`. The input `s i` is the Euclidean
norm of row `i`. Both endpoint power sums equal exactly `∑ i, s i ^ p`,
so applying the same construction to the transpose supplies the column
factorization required for Gaussian profile interpolation. Zero rows are
included, even when the right scaling has a negative exponent. -/
theorem exists_row_power_factors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p q θ : ℝ} (hp : 2 ≤ p) (hq : 0 < q) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hexp : 1 / p = (1 - θ) / 2 + θ / q)
    (a : ι → κ → ℝ) (s : ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hs : ∀ i, 0 ≤ s i)
    (hsum : ∀ i, ∑ j, a i j ^ 2 = s i ^ 2) :
    ∃ u v : ι → κ → ℝ,
      (∀ i j, 0 ≤ u i j) ∧ (∀ i j, 0 ≤ v i j) ∧
      (∀ i j, a i j = u i j ^ (1 - θ) * v i j ^ θ) ∧
      (∑ i, ∑ j, u i j ^ 2) = ∑ i, s i ^ p ∧
      (∑ i, (∑ j, v i j ^ 2) ^ (q / 2)) = ∑ i, s i ^ p := by
  classical
  have hp0 : 0 < p := by linarith
  let u : ι → κ → ℝ := fun i j => a i j * s i ^ (p / 2 - 1)
  let v : ι → κ → ℝ := fun i j => a i j * s i ^ (p / q - 1)
  have he : (p / 2 - 1) * (1 - θ) + (p / q - 1) * θ = 0 := by
    calc
      _ = p * ((1 - θ) / 2 + θ / q) - 1 := by ring
      _ = 0 := by rw [← hexp]; field_simp; ring
  refine ⟨u, v, fun i j => mul_nonneg (ha i j) (Real.rpow_nonneg (hs i) _),
    fun i j => mul_nonneg (ha i j) (Real.rpow_nonneg (hs i) _), ?_, ?_, ?_⟩
  · intro i j
    by_cases hs0 : s i = 0
    · have hj : a i j = 0 := by
        have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset κ)) =>
          sq_nonneg (a i j)) (Finset.mem_univ j)
        rw [hsum i, hs0] at hh
        nlinarith [ha i j]
      simp [u, v, hj, Real.zero_rpow hθ.1.ne',
        Real.zero_rpow (by linarith [hθ.2] : 1 - θ ≠ 0)]
    · have hspos := lt_of_le_of_ne (hs i) (Ne.symm hs0)
      symm
      dsimp [u, v]
      rw [Real.mul_rpow (ha i j) (Real.rpow_nonneg (hs i) _),
        Real.mul_rpow (ha i j) (Real.rpow_nonneg (hs i) _),
        ← Real.rpow_mul (hs i), ← Real.rpow_mul (hs i)]
      calc
        _ = (a i j ^ (1 - θ) * a i j ^ θ) *
          (s i ^ ((p / 2 - 1) * (1 - θ)) * s i ^ ((p / q - 1) * θ)) := by ring
        _ = a i j := by
          rw [← Real.rpow_add_of_nonneg (ha i j) (by linarith [hθ.2]) hθ.1.le,
            ← Real.rpow_add hspos, he]
          simp
  · apply Finset.sum_congr rfl
    intro i _
    have hh := sum_sq_mul_rpow_eq (a i) (hs i) (hsum i)
      (t := p / 2 - 1) (by linarith)
    convert hh using 1
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i _
    have hh := sum_sq_mul_rpow_eq (a i) (hs i) (hsum i)
      (t := p / q - 1) (by have := div_pos hp0 hq; linarith)
    change (∑ j, (a i j * s i ^ (p / q - 1)) ^ 2) ^ (q / 2) = _
    rw [hh, ← Real.rpow_mul (hs i)]
    congr 1
    field_simp
    ring

/-- Explicit power factors for an entrywise finite `ℓ_p` norm. Their left
Euclidean power sum and right `ℓ_q` power sum both equal the original
`p`th power sum. This supplies the entry endpoint alongside the row and
column factorizations. -/
theorem exists_scalar_power_factors
    {κ : Type*} [Fintype κ] {p q θ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hexp : 1 / p = (1 - θ) / 2 + θ / q)
    (a : κ → ℝ) (ha : ∀ x, 0 ≤ a x) :
    ∃ u v : κ → ℝ,
      (∀ x, 0 ≤ u x) ∧ (∀ x, 0 ≤ v x) ∧
      (∀ x, a x = u x ^ (1 - θ) * v x ^ θ) ∧
      (∑ x, u x ^ 2) = ∑ x, a x ^ p ∧
      (∑ x, v x ^ q) = ∑ x, a x ^ p := by
  refine ⟨fun x => a x ^ (p / 2), fun x => a x ^ (p / q),
    fun x => Real.rpow_nonneg (ha x) _, fun x => Real.rpow_nonneg (ha x) _, ?_, ?_, ?_⟩
  · intro x
    rw [← Real.rpow_mul (ha x), ← Real.rpow_mul (ha x)]
    by_cases hx : a x = 0
    · have he₀ : p / 2 * (1 - θ) ≠ 0 :=
        (mul_pos (div_pos hp (by norm_num : (0 : ℝ) < 2)) (by linarith [hθ.2])).ne'
      have he₁ : p / q * θ ≠ 0 := (mul_pos (div_pos hp hq) hθ.1).ne'
      simp [hx, Real.zero_rpow he₀, Real.zero_rpow he₁]
    · rw [← Real.rpow_add (lt_of_le_of_ne (ha x) (Ne.symm hx))]
      have he : p / 2 * (1 - θ) + p / q * θ = 1 := by
        calc
          _ = p * ((1 - θ) / 2 + θ / q) := by ring
          _ = 1 := by rw [← hexp]; field_simp
      rw [he, Real.rpow_one]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Real.rpow_natCast (a x ^ (p / 2)) 2, ← Real.rpow_mul (ha x)]
    congr 1
    norm_num
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Real.rpow_mul (ha x)]
    congr 1
    exact div_mul_cancel₀ p hq.ne'

/-- A weighted entry endpoint can share the same original coefficient
factorization: weighting its right `ℓ_q` norm by `c` weights both endpoint
power sums by `c^(θ p)`. This is the exact `sqrt(q)` entry factor used for
Gaussian profile interpolation. -/
theorem exists_weighted_scalar_power_factors
    {κ : Type*} [Fintype κ] {p q θ c : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c)
    (hexp : 1 / p = (1 - θ) / 2 + θ / q)
    (a : κ → ℝ) (ha : ∀ x, 0 ≤ a x) :
    ∃ u v : κ → ℝ,
      (∀ x, 0 ≤ u x) ∧ (∀ x, 0 ≤ v x) ∧
      (∀ x, a x = u x ^ (1 - θ) * v x ^ θ) ∧
      (∑ x, u x ^ 2) = c ^ (θ * p) * ∑ x, a x ^ p ∧
      c ^ q * (∑ x, v x ^ q) = c ^ (θ * p) * ∑ x, a x ^ p := by
  obtain ⟨u, v, hu, hv, hfactor, hleft, hright⟩ :=
    exists_scalar_power_factors hp hq hθ hexp (fun x => c ^ θ * a x)
      (fun x => mul_nonneg (Real.rpow_nonneg hc.le _) (ha x))
  have hsum : (∑ x, (c ^ θ * a x) ^ p) = c ^ (θ * p) * ∑ x, a x ^ p := by
    simp_rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) (ha _),
      ← Real.rpow_mul hc.le, ← Finset.mul_sum]
  refine ⟨u, fun x => v x / c, hu, fun x => div_nonneg (hv x) hc.le, ?_,
    hleft.trans hsum, ?_⟩
  · intro x
    rw [Real.div_rpow (hv x) hc.le, ← mul_div_assoc, ← hfactor x]
    exact (mul_div_cancel_left₀ (a x) (Real.rpow_pos_of_pos hc θ).ne').symm
  · simp_rw [Real.div_rpow (hv _) hc.le, ← Finset.sum_div]
    rw [mul_div_cancel₀ _ (Real.rpow_pos_of_pos hc q).ne']
    exact hright.trans hsum

/-- The entire interpolation coefficient associated with two nonnegative
power factors. A missing factor gives the identically zero function, so
zero coordinates cause no logarithmic singularity. -/
def powerInterpolationCoefficient (u v : ℝ) (z : ℂ) : ℂ :=
  if 0 < u ∧ 0 < v then
    Complex.exp ((1 - z) * (Real.log u : ℂ) + z * (Real.log v : ℂ))
  else 0

/-- Every fixed pair of power factors gives an entire coefficient. -/
@[fun_prop] theorem differentiable_powerInterpolationCoefficient (u v : ℝ) :
    Differentiable ℂ (powerInterpolationCoefficient u v) := by
  unfold powerInterpolationCoefficient
  split_ifs <;> fun_prop

/-- The coefficient modulus at each point is its ordinary geometric power
interpolation when the two factors are positive. -/
theorem norm_powerInterpolationCoefficient_of_pos
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (z : ℂ) :
    ‖powerInterpolationCoefficient u v z‖ = u ^ (1 - z.re) * v ^ z.re := by
  rw [powerInterpolationCoefficient, if_pos ⟨hu, hv⟩, Complex.norm_exp,
    Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hv, ← Real.exp_add]
  congr 1
  simp
  ring

/-- The two boundary coefficient moduli are bounded by the supplied power
factors, including zero factor directions. -/
theorem norm_powerInterpolationCoefficient_boundaries
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (t : ℝ) :
    ‖powerInterpolationCoefficient u v ((t : ℂ) * Complex.I)‖ ≤ u ∧
    ‖powerInterpolationCoefficient u v (1 + (t : ℂ) * Complex.I)‖ ≤ v := by
  by_cases hh : 0 < u ∧ 0 < v
  · simp [norm_powerInterpolationCoefficient_of_pos hh.1 hh.2]
  · simp [powerInterpolationCoefficient, hh, hu, hv]

/-- At a real interpolation point, the coefficient is exactly the given
nonnegative power factorization, also when either factor vanishes. -/
theorem powerInterpolationCoefficient_real
    {u v θ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    powerInterpolationCoefficient u v (θ : ℂ) = ((u ^ (1 - θ) * v ^ θ : ℝ) : ℂ) := by
  by_cases hh : 0 < u ∧ 0 < v
  · rw [powerInterpolationCoefficient, if_pos hh, Real.rpow_def_of_pos hh.1,
      Real.rpow_def_of_pos hh.2, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · have hz : u = 0 ∨ v = 0 := by
      push Not at hh
      by_cases hu0 : u = 0
      · exact Or.inl hu0
      · exact Or.inr (le_antisymm (hh (lt_of_le_of_ne hu (Ne.symm hu0))) hv)
    rcases hz with rfl | rfl <;>
      simp [powerInterpolationCoefficient, Real.zero_rpow hθ.1.ne',
        Real.zero_rpow (by linarith [hθ.2] : 1 - θ ≠ 0)]

/-- The entire coefficient family is uniformly bounded on the closed
interpolation strip. This supplies actual boundedness for three-lines. -/
theorem norm_powerInterpolationCoefficient_le_max
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖powerInterpolationCoefficient u v z‖ ≤ max u v := by
  by_cases hh : 0 < u ∧ 0 < v
  · rw [norm_powerInterpolationCoefficient_of_pos hh.1 hh.2]
    calc
      _ ≤ max u v ^ (1 - z.re) * max u v ^ z.re :=
        mul_le_mul (Real.rpow_le_rpow hu (le_max_left _ _) (sub_nonneg.mpr hz.2))
          (Real.rpow_le_rpow hv (le_max_right _ _) hz.1)
          (Real.rpow_nonneg hv _) (Real.rpow_nonneg (hu.trans (le_max_left _ _)) _)
      _ = max u v := by
        rw [← Real.rpow_add (hh.1.trans_le (le_max_left _ _))]
        simp
  · simp [powerInterpolationCoefficient, hh, hu.trans (le_max_left u v)]

end NLAlib

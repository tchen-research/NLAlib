import NLAlib.Matrix.Inequalities.Majorization
/-!
# Maximal residual subsets and positive separation

A nonzero zero-sum residual has a positive maximum; normalized vectors on its
maximum coordinates and on their complement have strictly positive weighted
separation. Source: Schur–Horn variational rederivation, steps (3)–(6), supporting
the atlas result `schur-horn`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A nonzero zero-sum finite residual has a nonempty set of coordinates at a
strictly positive maximum. Schur–Horn variational rederivation, step (3). -/
theorem exists_pos_max_residual (r : n → ℝ) (hsum : ∑ i, r i = 0)
    (hne : ∃ i, r i ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset n, S.Nonempty ∧
      (∀ i, i ∈ S ↔ r i = ρ) ∧ (∀ i, r i ≤ ρ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  let _ : Nonempty n := ⟨i₀⟩
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_max_image r Finset.univ_nonempty
  have hmax : ∀ i, r i ≤ r j := fun i => hj i (Finset.mem_univ i)
  have hpos : 0 < r j := by
    by_contra hnot
    have hnonpos : ∀ i ∈ (Finset.univ : Finset n), r i ≤ 0 :=
      fun i _ => (hmax i).trans (le_of_not_gt hnot)
    exact hi₀ ((Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum i₀ (Finset.mem_univ i₀))
  refine ⟨r j, hpos, Finset.univ.filter (fun i => r i = r j), ?_, ?_, hmax⟩
  · exact ⟨j, by simp⟩
  · intro i
    simp

/-- A unit vector supported where a residual equals its maximum has weighted
squared residual average exactly that maximum. Schur–Horn variational
rederivation, equation (6). -/
theorem sum_mul_sq_eq_of_support (r u : n → ℝ) (ρ : ℝ) (S : Finset n)
    (hS : ∀ i ∈ S, r i = ρ) (hu : u ⬝ᵥ u = 1)
    (hsupport : ∀ i ∉ S, u i = 0) :
    (∑ i, r i * u i ^ 2) = ρ := by
  have heq : ∀ i, r i * u i ^ 2 = ρ * u i ^ 2 := by
    intro i
    by_cases hi : i ∈ S
    · rw [hS i hi]
    · simp [hsupport i hi]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have hu' : ∑ i, u i ^ 2 = 1 := by simpa only [dotProduct, pow_two] using hu
  rw [hu', mul_one]

omit [DecidableEq n] in
/-- A unit vector supported away from the maximal residual coordinates has
strictly smaller weighted squared average. Schur–Horn variational rederivation,
equation (6), with no positivity condition on the individual residuals. -/
theorem sum_mul_sq_lt_of_support_compl (r v : n → ℝ) (ρ : ℝ) (S : Finset n)
    (hmax : ∀ i, r i ≤ ρ) (hstrict : ∀ i ∉ S, r i < ρ)
    (hv : v ⬝ᵥ v = 1) (hsupport : ∀ i ∈ S, v i = 0) :
    (∑ i, r i * v i ^ 2) < ρ := by
  have hv' : ∑ i, v i ^ 2 = 1 := by simpa only [dotProduct, pow_two] using hv
  have hnonzero : ∃ i, v i ≠ 0 := by
    by_contra hnot
    have hzero : ∀ i, v i = 0 := by simpa only [not_exists, not_not] using hnot
    simp [hzero] at hv'
  obtain ⟨j, hj⟩ := hnonzero
  have hjS : j ∉ S := fun hjS => hj (hsupport j hjS)
  have hpos : 0 < ∑ i, (ρ - r i) * v i ^ 2 := by
    apply Finset.sum_pos_iff_of_nonneg
      (fun i _ => mul_nonneg (sub_nonneg.mpr (hmax i)) (sq_nonneg _)) |>.mpr
    exact ⟨j, Finset.mem_univ j, mul_pos (sub_pos.mpr (hstrict j hjS)) (sq_pos_of_ne_zero hj)⟩
  have heq : (∑ i, (ρ - r i) * v i ^ 2) = ρ - ∑ i, r i * v i ^ 2 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv', mul_one]
  rw [heq] at hpos
  linarith

/-- Disjoint unit vectors on the maximal residual subset and its complement
have positive residual-weighted squared separation. Schur–Horn variational
rederivation, equation (6). -/
theorem sum_mul_sub_sq_pos_of_max_support (r u v : n → ℝ) (ρ : ℝ) (S : Finset n)
    (hS : ∀ i, i ∈ S ↔ r i = ρ) (hmax : ∀ i, r i ≤ ρ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (hsu : ∀ i ∉ S, u i = 0) (hsv : ∀ i ∈ S, v i = 0) :
    0 < ∑ i, r i * (u i ^ 2 - v i ^ 2) := by
  have hstrict : ∀ i ∉ S, r i < ρ := by
    intro i hi
    exact lt_of_le_of_ne (hmax i) (fun heq => hi ((hS i).mpr heq))
  have huavg := sum_mul_sq_eq_of_support r u ρ S
    (fun i hi => (hS i).mp hi) hu hsu
  have hvavg := sum_mul_sq_lt_of_support_compl r v ρ S hmax hstrict hv hsv
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, huavg]
  exact sub_pos.mpr hvavg

end NLAlib

import NLAlib.Polynomial.JacksonPolynomial

/-!
# Sharp algebraic Jackson approximation on real intervals

Affine transplantation of the proved fixed Jackson polynomial preserves the degree
and gives the original interval constant `πL(c-a)/(4(n+1))`.
-/

noncomputable section

open Polynomial Real Set

namespace NLAlib

/-- Every Lipschitz function on a nondegenerate interval has an actual degree-`n` real
polynomial with the sharp error `πL(c-a)/(4(n+1))`, for every `n ≥ 0`.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:jackson-theorem`.
The sawtooth interpolation, sharp norm, periodic error, cosine-polynomial representation,
and affine rescaling are all proved without an approximation certificate.
atlas: jackson-lipschitz -/
theorem exists_degree_le_abs_sub_eval_le_jackson_interval {f : ℝ → ℝ} {a c : ℝ}
    {L : NNReal} (hac : a < c) (hf : LipschitzOnWith L f (Icc a c)) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc a c,
      |f x - p.eval x| ≤ Real.pi * (L : ℝ) * (c - a) / (4 * (n + 1)) := by
  have hca : 0 < c - a := sub_pos.mpr hac
  let ℓ : NNReal := ⟨(c - a) / 2, by positivity⟩
  let m : ℝ → ℝ := fun t => ((c - a) * t + c + a) / 2
  have hmap : ∀ t ∈ Icc (-1 : ℝ) 1, m t ∈ Icc a c := by
    intro t ht
    dsimp [m]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hca.le,
      mul_le_mul_of_nonneg_left ht.2 hca.le]
  have hLip : LipschitzOnWith (L * ℓ) (fun t => f (m t)) (Icc (-1 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdist : dist (m x) (m y) = (c - a) / 2 * dist x y := by
      rw [Real.dist_eq, Real.dist_eq]
      have heq : m x - m y = ((c - a) / 2) * (x - y) := by dsimp [m]; ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (c - a) / 2)]
    have h := hf.dist_le_mul (m x) (hmap x hx) (m y) (hmap y hy)
    rw [hdist] at h
    change dist (f (m x)) (f (m y)) ≤ ((L : ℝ) * ((c - a) / 2)) * dist x y
    simpa only [mul_assoc] using h
  obtain ⟨p, hp, hE⟩ := exists_degree_le_abs_sub_eval_le_jackson_unit hLip n
  let s : ℝ[X] := C (2 / (c - a)) * X - C ((c + a) / (c - a))
  refine ⟨p.comp s, ?_, ?_⟩
  · apply degree_le_of_natDegree_le
    refine natDegree_comp_le.trans ?_
    have hpN := natDegree_le_of_degree_le hp
    have hs : s.natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
      · simp
    nlinarith
  · intro x hx
    let t := 2 / (c - a) * x - (c + a) / (c - a)
    have ht : t ∈ Icc (-1 : ℝ) 1 := by
      have htform : t = (2 * x - c - a) / (c - a) := by dsimp [t]; ring
      rw [htform]
      constructor
      · rw [le_div_iff₀ hca]
        nlinarith [hx.1]
      · rw [div_le_iff₀ hca]
        nlinarith [hx.2]
    have heq : m t = x := by
      dsimp [m, t]
      field_simp [ne_of_gt hca]
      ring
    have h := hE t ht
    rw [heq] at h
    have hrate : Real.pi * ((L * ℓ : NNReal) : ℝ) / (2 * (n + 1)) =
        Real.pi * (L : ℝ) * (c - a) / (4 * (n + 1)) := by
      change Real.pi * ((L : ℝ) * ((c - a) / 2)) / (2 * (n + 1)) = _
      field_simp
      norm_num
    rw [hrate] at h
    simpa only [eval_comp, s, eval_sub, eval_mul, eval_C, eval_X, t] using h

end NLAlib

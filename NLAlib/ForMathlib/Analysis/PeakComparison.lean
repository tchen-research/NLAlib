import NLAlib.ForMathlib.Analysis.ProperInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Positive normals and global peak comparison

The proper peak-difference inverse and the scalar mean value theorem express the
equal-peak value as a convex combination of the peaks at every point. This is the
global analytic step in `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Filter Function Finset

namespace NLAlib

/-- The equal-peak value lies in the convex hull of every peak vector.
Source: focused reroutes, Lemma `lem:radial`; the scalar mean value theorem replaces
the final integral identity, after the proper global inverse has been proved.
Helper for `lebesgue-constant-lower-bound`.
The strict derivative hypothesis is on the actual vector of peak differences. -/
theorem exists_equal_peaks_with_convex_combination {n : ℕ}
    {U : Set (Fin n → ℝ)} [Nonempty U] [PreconnectedSpace U] (hU : IsOpen U)
    {M : Fin (n + 1) → (Fin n → ℝ) → ℝ}
    {L : Fin (n + 1) → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {D : (Fin n → ℝ) → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)}
    {W : (Fin n → ℝ) → Fin (n + 1) → ℝ}
    (hM : ∀ i x, x ∈ U → HasFDerivAt (M i) (L i x) x)
    (hΓ : ∀ x ∈ U, HasStrictFDerivAt (fun y j => M j.succ y - M 0 y)
      (D x : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x)
    (hproper : IsProperMap (fun x : U => fun j : Fin n => M j.succ x - M 0 x))
    (hWnonneg : ∀ x ∈ U, ∀ i, 0 ≤ W x i)
    (hWsum : ∀ x ∈ U, ∑ i, W x i = 1)
    (hnormal : ∀ x ∈ U, ∀ v, ∑ i, W x i * L i x v = 0) :
    ∃ x ∈ U, (∀ i, M i x = M 0 x) ∧ ∀ u ∈ U,
      ∃ w : Fin (n + 1) → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        M 0 x = ∑ i, w i * M i u := by
  let Γ : (Fin n → ℝ) → Fin n → ℝ := fun x j => M j.succ x - M 0 x
  obtain ⟨g, _, hgU, hright, hleft, hginv⟩ :=
    exists_inverse_of_isProperMap_of_hasStrictFDerivAt hU hΓ hproper
  refine ⟨g 0, hgU 0, ?_, ?_⟩
  · intro i
    refine Fin.cases rfl (fun j => ?_) i
    have h := congrFun (hright 0) j
    dsimp at h
    linarith
  · intro u hu
    let a : Fin (n + 1) → ℝ := fun i => M i u
    let z : ℝ → Fin n → ℝ := fun s => g (s • Γ u)
    let b : ℝ → Fin (n + 1) → ℝ := fun s i => L i (z s) ((D (z s)).symm (Γ u))
    have hzU (s : ℝ) : z s ∈ U := hgU _
    have hdifference (s : ℝ) (j : Fin n) : b s j.succ - b s 0 = a j.succ - a 0 := by
      have hd := (hasFDerivAt_apply j (Γ (z s))).comp (z s) (hΓ (z s) (hzU s)).hasFDerivAt
      have hm := (hM j.succ (z s) (hzU s)).sub (hM 0 (z s) (hzU s))
      have heq := hd.unique hm
      have hv := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A ((D (z s)).symm (Γ u))) heq
      change (D (z s) ((D (z s)).symm (Γ u))) j =
        L j.succ (z s) ((D (z s)).symm (Γ u)) - L 0 (z s) ((D (z s)).symm (Γ u)) at hv
      rw [ContinuousLinearEquiv.apply_symm_apply] at hv
      exact hv.symm
    have hb (s : ℝ) (i : Fin (n + 1)) : b s i = b s 0 + a i - a 0 := by
      refine Fin.cases (by ring) (fun j => ?_) i
      linarith [hdifference s j]
    have hscalar (s : ℝ) : b s 0 - a 0 = -∑ i, W (z s) i * a i := by
      have hN := hnormal (z s) (hzU s) ((D (z s)).symm (Γ u))
      change ∑ i, W (z s) i * b s i = 0 at hN
      have hsum : (∑ i, W (z s) i * b s i) =
          b s 0 + (∑ i, W (z s) i * a i) - a 0 := by
        calc
          _ = ∑ i, W (z s) i * (b s 0 + a i - a 0) :=
            sum_congr rfl (fun i _ => congrArg (fun t => W (z s) i * t) (hb s i))
          _ = _ := by
            simp_rw [mul_sub, mul_add]
            rw [sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul,
              hWsum (z s) (hzU s), one_mul, one_mul]
      rw [hsum] at hN
      linarith
    let c : ℝ → ℝ := fun s => M 0 (z s) - s * a 0
    have hcder (s : ℝ) : HasDerivAt c (b s 0 - a 0) s := by
      have hline := (hasDerivAt_id s).smul_const (Γ u)
      simp only [one_smul] at hline
      have hg := (hginv (s • Γ u)).hasFDerivAt.comp_hasDerivAt s hline
      have hm := (hM 0 (z s) (hzU s)).comp_hasDerivAt s hg
      convert! hm.sub ((hasDerivAt_id s).mul_const (a 0)) using 1
      simp only [b, z, one_mul, ContinuousLinearEquiv.coe_coe]
    obtain ⟨s, _, hs⟩ := exists_hasDerivAt_eq_slope c (fun s => b s 0 - a 0)
      (by norm_num : (0 : ℝ) < 1) (fun t _ => (hcder t).continuousAt.continuousWithinAt)
      (fun t _ => hcder t)
    have hc0 : c 0 = M 0 (g 0) := by simp [c, z]
    have hc1 : c 1 = 0 := by
      have hl : g (Γ u) = u := hleft u hu
      simp only [c, z, one_smul, one_mul, hl, a, sub_self]
    rw [hc0, hc1] at hs
    simp only [sub_zero, div_one, zero_sub] at hs
    refine ⟨W (z s), hWnonneg (z s) (hzU s), hWsum (z s) (hzU s), ?_⟩
    linarith [hscalar s]

/-- A finite convex combination lies between any common lower and upper bounds.
Source: positivity of finite sums; helper for `lebesgue-constant-lower-bound`. -/
theorem sum_mul_mem_Icc_of_nonneg_sum_one {ι : Type*} [Fintype ι]
    {w a : ι → ℝ} {A B : ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ i, a i ∈ Icc A B) : (∑ i, w i * a i) ∈ Icc A B := by
  constructor
  · calc
      A = ∑ i, w i * A := by rw [← sum_mul, hs, one_mul]
      _ ≤ ∑ i, w i * a i := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i).1 (hw i))
  · calc
      _ ≤ ∑ i, w i * B := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i).2 (hw i))
      _ = B := by rw [← sum_mul, hs, one_mul]

end NLAlib

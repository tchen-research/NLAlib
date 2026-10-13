import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Ordered zeros between sign-alternating samples

The intermediate value theorem supplies one strictly ordered interior zero between each
pair of successive samples with opposite signs.
-/

noncomputable section

namespace NLAlib

/-- Perturbations smaller in absolute value preserve the opposite signs of two real values.
Source: the elementary sign step in the polynomial and rational de la Vallée Poussin proofs. -/
theorem mul_sub_mul_sub_neg_of_abs_lt {a b c d : ℝ} (hab : a * b < 0)
    (hc : |c| < |a|) (hd : |d| < |b|) : (a - c) * (b - d) < 0 := by
  rcases mul_neg_iff.mp hab with h | h
  · rw [abs_of_pos h.1] at hc
    rw [abs_of_neg h.2] at hd
    have hc' := (abs_lt.mp hc).2
    have hd' := (abs_lt.mp hd).1
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · rw [abs_of_neg h.1] at hc
    rw [abs_of_pos h.2] at hd
    have hc' := (abs_lt.mp hc).1
    have hd' := (abs_lt.mp hd).2
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- Every nondegenerate real interval contains any prescribed finite number of strictly
ordered interior points. The equally spaced construction includes the empty index type. -/
theorem exists_strictMono_mem_Ioo {a b : ℝ} (hab : a < b) (k : ℕ) :
    ∃ v : Fin k → Set.Ioo a b, StrictMono (fun i => (v i : ℝ)) := by
  have hden : (0 : ℝ) < k + 1 := by positivity
  let v : Fin k → Set.Ioo a b := fun i =>
    ⟨a + (b - a) * ((i : ℕ) + 1) / (k + 1), by
      have hnum : (0 : ℝ) < (i : ℕ) + 1 := by positivity
      have hi : ((i : ℕ) + 1 : ℝ) < k + 1 := by exact_mod_cast (show (i : ℕ) + 1 < k + 1 by omega)
      constructor
      · exact lt_add_of_pos_right a (div_pos (mul_pos (sub_pos.mpr hab) hnum) hden)
      · have hpart : (b - a) * ((i : ℕ) + 1) / (k + 1) < b - a :=
          (div_lt_iff₀ hden).mpr (mul_lt_mul_of_pos_left hi (sub_pos.mpr hab))
        linarith⟩
  refine ⟨v, fun i j hij => ?_⟩
  have hijR : ((i : ℕ) + 1 : ℝ) < (j : ℕ) + 1 := by exact_mod_cast (show (i : ℕ) + 1 < (j : ℕ) + 1 by omega)
  have hdiv := div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left hijR (sub_pos.mpr hab)) hden
  dsimp [v]; linarith

/-- Equal nonzero magnitudes and opposite adjacent signs determine a signed alternating
power sequence. Source: the scalar sign normalization in the alternation theorem. -/
theorem exists_sign_of_alternating_abs_eq {k : ℕ} {E : ℝ} (hE : 0 < E)
    (u : Fin (k + 2) → ℝ) (habs : ∀ i, |u i| = E)
    (hsign : ∀ i : Fin (k + 1), u i.castSucc * u i.succ < 0) :
    ∃ σ : ℝ, |σ| = 1 ∧ ∀ i, u i = σ * (-1) ^ (i : ℕ) * E := by
  let σ := u 0 / E
  refine ⟨σ, ?_, ?_⟩
  · dsimp [σ]; rw [abs_div, habs 0, abs_of_pos hE]; exact div_self hE.ne'
  · intro i
    refine Fin.induction ?_ (fun j hj => ?_) i
    · simp only [Fin.val_zero, pow_zero, mul_one]
      exact (div_mul_cancel₀ (u 0) hE.ne').symm
    · have hnext : u j.succ = -u j.castSucc := by
        rcases abs_eq_abs.mp ((habs j.succ).trans (habs j.castSucc).symm) with h | h
        · have hs := hsign j
          rw [h] at hs
          exact (not_lt_of_ge (mul_self_nonneg _) hs).elim
        · exact h
      rw [hnext, hj]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring

/-- A nonvanishing continuous real function has the same strict sign at any two points
of a real interval. Source: the intermediate value theorem. -/
theorem mul_pos_of_continuousOn_ne_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hzero : ∀ x ∈ Set.Icc a b, f x ≠ 0)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) : 0 < f x * f y := by
  by_contra hnot
  have hneg : f x * f y < 0 := lt_of_le_of_ne (le_of_not_gt hnot)
    (mul_ne_zero (hzero x hx) (hzero y hy))
  rcases mul_neg_iff.mp hneg with h | h
  · obtain ⟨z, hz, heq⟩ := isPreconnected_Icc.intermediate_value hy hx hf
      ⟨h.2.le, h.1.le⟩
    exact hzero z hz heq
  · obtain ⟨z, hz, heq⟩ := isPreconnected_Icc.intermediate_value hx hy hf
      ⟨h.1.le, h.2.le⟩
    exact hzero z hz heq

/-- A continuous real function has ordered interior zeros between ordered samples whose
successive products are negative. Source: the intermediate value argument in Cheney (1966),
Chapter 3, the de la Vallée Poussin and alternation theorems. -/
theorem exists_strictMono_eq_zero_of_mul_neg {n : ℕ} {f : ℝ → ℝ}
    {v : Fin (n + 2) → ℝ} (hv : StrictMono v)
    (hf : ContinuousOn f (Set.Icc (v 0) (v (Fin.last _))))
    (hsign : ∀ i : Fin (n + 1), f (v i.castSucc) * f (v i.succ) < 0) :
    ∃ c : Fin (n + 1) → ℝ, StrictMono c ∧
      ∀ i, c i ∈ Set.Ioo (v i.castSucc) (v i.succ) ∧ f (c i) = 0 := by
  have hzero : ∀ i : Fin (n + 1),
      ∃ c ∈ Set.Ioo (v i.castSucc) (v i.succ), f c = 0 := by
    intro i
    have hi : v i.castSucc < v i.succ := hv Fin.castSucc_lt_succ
    have hcont : ContinuousOn f (Set.Icc (v i.castSucc) (v i.succ)) :=
      hf.mono (Set.Icc_subset_Icc
      (hv.monotone (Fin.zero_le _)) (hv.monotone (Fin.le_last _)))
    rcases mul_neg_iff.mp (hsign i) with h | h
    · exact intermediate_value_Ioo' hi.le hcont ⟨h.2, h.1⟩
    · exact intermediate_value_Ioo hi.le hcont ⟨h.1, h.2⟩
  choose c hc hczero using hzero
  refine ⟨c, fun i j hij => ?_, fun i => ⟨hc i, hczero i⟩⟩
  calc
    c i < v i.succ := (hc i).2
    _ ≤ v j.castSucc := hv.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    _ < c j := (hc j).1

end NLAlib

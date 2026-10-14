import NLAlib.Polynomial.BestApproximation.MinimaxError
import NLAlib.Polynomial.BestApproximation.ExtremalSigns
import NLAlib.Polynomial.BestApproximation.AlternatingInterpolant
import NLAlib.ForMathlib.Analysis.Normed.UniformApproximation
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Weighted polynomial minimax approximation

Finite-dimensional attainment and alternating extrema for a continuous positive
weight. Source: the weighted Chebyshev alternation theorem, as used in reciprocal
exponential certificate (RC10).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Set
namespace NLAlib

/-- A weighted polynomial minimizer exists on every compact real set, even for
a weight that vanishes. Source: finite-dimensional minimax attainment, RC10. -/
theorem exists_degree_le_weighted_norm_sub_minimal {s : Set ℝ} [CompactSpace s]
    (n : ℕ) (f w : C(s, ℝ)) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ q : ℝ[X], q.degree ≤ n →
      ‖w * (f - p.toContinuousMapOn s)‖ ≤ ‖w * (f - q.toContinuousMapOn s)‖ := by
  let L : C(s, ℝ) →ₗ[ℝ] C(s, ℝ) :=
    { toFun := fun g => w * g
      map_add' := by intro g h; ext x; simp [mul_add]
      map_smul' := by intro a g; ext x; simp }
  let S := (polynomialApproximationSpace s n).map L
  have : FiniteDimensional ℝ S := by dsimp [S]; infer_instance
  obtain ⟨g, hg, hbest⟩ := exists_norm_sub_eq_infDist_of_finiteDimensional S (w*f)
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hg
  obtain ⟨p, hp, rfl⟩ := mem_polynomialApproximationSpace_iff.mp hh
  have heq (q : ℝ[X]) : w*f - L (q.toContinuousMapOn s) =
      w * (f - q.toContinuousMapOn s) := by ext x; simp [L, mul_sub]
  refine ⟨p, hp, fun q hq => ?_⟩
  rw [← heq p, hbest, ← heq q]
  simpa only [dist_eq_norm] using (Metric.infDist_le_dist_of_mem (x := w*f)
    (show L (q.toContinuousMapOn s) ∈ S from
      Submodule.mem_map.mpr ⟨q.toContinuousMapOn s,
        mem_polynomialApproximationSpace_iff.mpr ⟨q, hq, rfl⟩, rfl⟩))

/-- A positive-error weighted minimizer has `n+2` alternating extrema. The
unweighted error has the same alternating signs because the weight is positive.
Source: weighted Chebyshev alternation, reciprocal exponential certificate (RC10). -/
theorem exists_alternating_extrema_of_weighted_norm_sub_minimal {n : ℕ} {a b : ℝ}
    (hab : a < b) (f w : C(Icc a b, ℝ)) (hw : ∀ x, 0 < w x)
    {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : ∀ q : ℝ[X], q.degree ≤ n →
      ‖w * (f - p.toContinuousMapOn (Icc a b))‖ ≤
        ‖w * (f - q.toContinuousMapOn (Icc a b))‖)
    (hE : 0 < ‖w * (f - p.toContinuousMapOn (Icc a b))‖) :
    ∃ v : Fin (n+2) → Icc a b, StrictMono (fun i => (v i : ℝ)) ∧
      (∀ i, |w (v i) * (f (v i) - p.eval (v i : ℝ))| =
        ‖w * (f - p.toContinuousMapOn (Icc a b))‖) ∧
      ∀ i : Fin (n+1), (f (v i.castSucc) - p.eval (v i.castSucc : ℝ)) *
        (f (v i.succ) - p.eval (v i.succ : ℝ)) < 0 := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let g := w * (f - p.toContinuousMapOn (Icc a b))
  let e : C(ℝ, ℝ) := ContinuousMap.IccExtendCM g
  let E := ‖g‖
  have heval : ∀ x (hx : x ∈ Icc a b), e x = g ⟨x, hx⟩ :=
    fun x hx => ContinuousMap.IccExtendCM_of_mem hx
  let K := Icc a b ∩ (fun x => |e x|) ⁻¹' {E}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_singleton.preimage e.continuous.abs)
  have hKne : K.Nonempty := by
    by_contra hnone
    have hlt : ‖g‖ < E := (ContinuousMap.norm_lt_iff g hE).mpr (by
      intro x
      have hne : |g x| ≠ E := by
        intro hx
        exact hnone ⟨x, x.property, by change |e x| = E; rw [heval _ x.property]; exact hx⟩
      exact lt_of_le_of_ne (g.norm_coe_le_norm x) hne)
    exact lt_irrefl E hlt
  obtain ⟨c, hc⟩ := hK.exists_isLeast hKne
  have hcab : c ∈ Icc a b := hc.1.1
  have hcE : |e c| = E := hc.1.2
  rcases exists_polynomial_extremal_sign_or_alternation n e E c b
      e.continuous hE hcab.2 hcE with ⟨q, hq, hqsign, _⟩ | ⟨v, hv, hvext, hvsign⟩
  · let h : C(Icc a b, ℝ) := w * q.toContinuousMapOn (Icc a b)
    have hsign : ∀ x : Icc a b, |g x| = ‖g‖ → 0 < g x * h x := by
      intro x hx
      have hex : |e x| = E := by rw [heval _ x.property]; exact hx
      have hcx : c ≤ x := hc.2 ⟨x.property, hex⟩
      have hpos := hqsign x ⟨hcx, x.property.2⟩ hex
      rw [heval _ x.property] at hpos
      change 0 < g x * (w x * q.eval (x : ℝ))
      simpa only [mul_left_comm] using mul_pos (hw x) hpos
    obtain ⟨t, _, himprove⟩ := exists_pos_norm_sub_smul_lt_of_extremal_sign g h hE hsign
    have hnew : (p + t • q).degree ≤ n :=
      mem_degreeLE.mp ((degreeLE ℝ n).add_mem (mem_degreeLE.mpr hp)
        ((degreeLE ℝ n).smul_mem t (mem_degreeLE.mpr hq)))
    have heq : w * (f - (p + t • q).toContinuousMapOn (Icc a b)) = g - t • h := by
      ext x
      simp [g, h, eval_smul]
      ring
    have hb := hbest (p+t•q) hnew
    rw [heq] at hb
    exact (not_lt_of_ge hb himprove).elim
  · let v' : Fin (n+2) → Icc a b := fun i =>
      ⟨v i, hcab.1.trans (hvext i).1.1, (hvext i).1.2⟩
    refine ⟨v', hv, ?_, ?_⟩
    · intro i
      have hext := (hvext i).2
      rw [heval _ (v' i).property] at hext
      exact hext
    · intro i
      have hs := hvsign i
      rw [heval _ (v' i.castSucc).property, heval _ (v' i.succ).property] at hs
      change (w (v' i.castSucc) * (f (v' i.castSucc) - p.eval (v' i.castSucc : ℝ))) *
        (w (v' i.succ) * (f (v' i.succ) - p.eval (v' i.succ : ℝ))) < 0 at hs
      by_contra hnone
      have hn := le_of_not_gt hnone
      have hm := mul_nonneg (mul_pos (hw (v' i.castSucc)) (hw (v' i.succ))).le hn
      have heq : (w (v' i.castSucc) * w (v' i.succ)) *
          ((f (v' i.castSucc) - p.eval (v' i.castSucc : ℝ)) *
            (f (v' i.succ) - p.eval (v' i.succ : ℝ))) =
          (w (v' i.castSucc) * (f (v' i.castSucc) - p.eval (v' i.castSucc : ℝ))) *
            (w (v' i.succ) * (f (v' i.succ) - p.eval (v' i.succ : ℝ))) := by ring
      rw [heq] at hm
      exact not_lt_of_ge hm hs

/-- A polynomial minimizing a positive weighted uniform error interpolates the
target at `n+1` ordered interior nodes, including the zero-error case.
Source: weighted Chebyshev alternation, reciprocal exponential certificate (RC10). -/
theorem exists_interpolate_eq_of_weighted_norm_sub_minimal {n : ℕ} {a b : ℝ}
    (hab : a < b) (f w : C(Icc a b, ℝ)) (hw : ∀ x, 0 < w x)
    {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : ∀ q : ℝ[X], q.degree ≤ n →
      ‖w * (f - p.toContinuousMapOn (Icc a b))‖ ≤
        ‖w * (f - q.toContinuousMapOn (Icc a b))‖) :
    ∃ c : Fin (n+1) → Ioo a b, StrictMono (fun i => (c i : ℝ)) ∧
      (∀ i, f ⟨c i, Ioo_subset_Icc_self (c i).property⟩ = p.eval (c i : ℝ)) ∧
      Lagrange.interpolate Finset.univ (fun i => (c i : ℝ))
        (fun i => f ⟨c i, Ioo_subset_Icc_self (c i).property⟩) = p := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  by_cases hE : ‖w * (f - p.toContinuousMapOn (Icc a b))‖ = 0
  · have hden : (0 : ℝ) < n+2 := by positivity
    let c : Fin (n+1) → Ioo a b := fun i =>
      ⟨a + (b-a) * ((i : ℕ)+1) / (n+2), by
        have hinum : (0 : ℝ) < (i : ℕ)+1 := by positivity
        have hi : ((i : ℕ)+1 : ℝ) < n+2 := by exact_mod_cast (show (i:ℕ)+1<n+2 by omega)
        constructor
        · exact lt_add_of_pos_right a (div_pos (mul_pos (sub_pos.mpr hab) hinum) hden)
        · have hpart : (b-a) * ((i:ℕ)+1) / (n+2) < b-a :=
            (div_lt_iff₀ hden).mpr (mul_lt_mul_of_pos_left hi (sub_pos.mpr hab))
          linarith⟩
    have hval : ∀ i, f ⟨c i, Ioo_subset_Icc_self (c i).property⟩ = p.eval (c i : ℝ) := by
      intro i
      have hzero := norm_eq_zero.mp hE
      let x : Icc a b := ⟨c i, Ioo_subset_Icc_self (c i).property⟩
      have hi := congrArg (fun g : C(Icc a b, ℝ) => g x) hzero
      change w x * (f x - p.eval (x : ℝ)) = 0 at hi
      exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (hw x).ne')
    have hc : StrictMono (fun i => (c i : ℝ)) := by
      intro i j hij
      have hijR : ((i:ℕ)+1 : ℝ) < (j:ℕ)+1 := by exact_mod_cast (show (i:ℕ)+1<(j:ℕ)+1 by omega)
      have hdiv := div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left hijR (sub_pos.mpr hab)) hden
      dsimp [c]
      linarith
    refine ⟨c, hc, hval, ?_⟩
    apply (Lagrange.eq_interpolate_of_eval_eq _ hc.injective.injOn ?_ ?_).symm
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
    · intro i _
      exact (hval i).symm
  · have hEpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    obtain ⟨v, hv, _, hsign⟩ :=
      exists_alternating_extrema_of_weighted_norm_sub_minimal hab f w hw hp hbest hEpos
    let g : C(ℝ, ℝ) := ContinuousMap.IccExtendCM f
    have hgv : ∀ i, g (v i) = f (v i) := fun i =>
      ContinuousMap.IccExtendCM_of_mem (v i).property
    obtain ⟨c, hc, hcI, hcval, hcinterp⟩ := exists_interpolate_eq_of_alternation g
      g.continuous.continuousOn hp hv (fun i => (v i).property)
      (by simpa only [hgv] using hsign)
    let c' : Fin (n+1) → Ioo a b := fun i => ⟨c i, hcI i⟩
    have hgval : ∀ i, g (c i) = f ⟨c' i, Ioo_subset_Icc_self (c' i).property⟩ :=
      fun i => ContinuousMap.IccExtendCM_of_mem (Ioo_subset_Icc_self (hcI i))
    refine ⟨c', hc, ?_, ?_⟩
    · intro i
      rw [← hgval]
      exact hcval i
    · simpa only [Function.comp_def, hgval] using hcinterp

end NLAlib

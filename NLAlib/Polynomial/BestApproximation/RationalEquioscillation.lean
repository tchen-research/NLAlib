import NLAlib.Polynomial.BestApproximation.RationalExistence
import NLAlib.Polynomial.BestApproximation.RationalDirections
import NLAlib.Polynomial.BestApproximation.RationalPerturbation
import NLAlib.Polynomial.BestApproximation.RationalLowerBound
import NLAlib.Polynomial.BestApproximation.ExtremalSigns
import NLAlib.ForMathlib.Topology.Order.IntermediateValue

/-!
# Rational equioscillation

The exact defect-adjusted extremal count is obtained from the polynomial numerator map.
Zero uses the reduced `0/1` representation and degree parameter `m`.
Source: Trefethen, ATAP, Theorem 24.1; focused rederivations, Section 1.
Atlas: `rational-equioscillation`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- Every polynomial numerator within the exact rational tangent degree has a direction
within the original type budgets. The zero function has degree parameter `m`.
Source: focused rederivations, Lemma `lem:rank`. -/
theorem exists_rational_direction {s : Set ℝ} {m n : ℕ} (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation s m n r) {H : ℝ[X]}
    (hH : H.degree ≤ rationalAlternationDegree m n r) :
    ∃ P Q : ℝ[X], P.degree ≤ m ∧ Q.degree ≤ n ∧ P * r.denom - r.num * Q = H := by
  by_cases hr0 : r = 0
  · subst r
    exact ⟨H, 0, by simpa [rationalAlternationDegree] using hH, by simp, by simp⟩
  · apply exists_degree_le_mul_sub_mul_eq_of_isCoprime (RatFunc.num_ne_zero hr0)
      (RatFunc.denom_ne_zero r) (RatFunc.isCoprime_num_denom r) hr.1 hr.2.1
    simpa [rationalAlternationDegree, hr0] using hH

/-- A best rational approximant with positive error has the full defect-adjusted number
of alternating extrema. Source: ATAP, Theorem 24.1; focused rederivations, Lemmas
`lem:rank`, `lem:signs`, and `lem:descent`. -/
theorem exists_alternating_extrema_of_norm_sub_eq_rationalMinimaxError {a b : ℝ}
    (hab : a < b) {m n : ℕ} (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    (hbest : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f)
    (hE : 0 < ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖) :
    ∃ v : Fin (rationalAlternationDegree m n r + 2) → Icc a b,
      StrictMono (fun i => (v i : ℝ)) ∧
      (∀ i, |f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i)| =
        ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖) ∧
      ∀ i : Fin (rationalAlternationDegree m n r + 1),
        (f (v i.castSucc) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.castSucc)) *
          (f (v i.succ) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.succ)) < 0 := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let g := f - rationalContinuousMap (Icc a b) r hr.2.2
  let e : C(ℝ, ℝ) := ContinuousMap.IccExtendCM g
  let E := ‖g‖
  let N := rationalAlternationDegree m n r
  have heval : ∀ x (hx : x ∈ Icc a b), e x = g ⟨x, hx⟩ :=
    fun x hx => ContinuousMap.IccExtendCM_of_mem hx
  let K := Icc a b ∩ (fun x => |e x|) ⁻¹' {E}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_singleton.preimage (e.continuous.abs))
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
  rcases exists_polynomial_extremal_sign_or_alternation N e E c b
      e.continuous hE hcab.2 hcE with ⟨H, hH, hHsign, _⟩ | ⟨v, hv, hvext, hvsign⟩
  · obtain ⟨P, Q, hP, hQ, hnum⟩ := exists_rational_direction r hr hH
    have hsign : ∀ x : Icc a b,
        |f x - r.num.eval (x : ℝ) / r.denom.eval (x : ℝ)| = E →
        0 < (f x - r.num.eval (x : ℝ) / r.denom.eval (x : ℝ)) *
          (P * r.denom - r.num * Q).eval (x : ℝ) := by
      intro x hx
      have hex : |e x| = E := by rw [heval _ x.property]; exact hx
      have hcx : c ≤ x := hc.2 ⟨x.property, hex⟩
      have hpos := hHsign x ⟨hcx, x.property.2⟩ hex
      rw [hnum]
      simpa [heval _ x.property, g, rationalContinuousMap] using hpos
    obtain ⟨t, ht, hstep⟩ := exists_pos_rational_perturbation_error_lt f r.num r.denom P Q
      (fun x => hr.2.2 x x.property) hE (fun x => g.norm_coe_le_norm x) hsign
    have hPnew : (r.num + t • P).degree ≤ m := mem_degreeLE.mp
      ((degreeLE ℝ m).add_mem (mem_degreeLE.mpr hr.1)
        ((degreeLE ℝ m).smul_mem t (mem_degreeLE.mpr hP)))
    have hQnew : (r.denom + t • Q).degree ≤ n := mem_degreeLE.mp
      ((degreeLE ℝ n).add_mem (mem_degreeLE.mpr hr.2.1)
        ((degreeLE ℝ n).smul_mem t (mem_degreeLE.mpr hQ)))
    have hQ0 : r.denom + t • Q ≠ 0 := by
      intro hzero
      have ha := (hstep ⟨a, le_rfl, hab.le⟩).1
      simp [hzero] at ha
    let s := algebraMap ℝ[X] (RatFunc ℝ) (r.num + t • P) /
      algebraMap ℝ[X] (RatFunc ℝ) (r.denom + t • Q)
    let hs := isPoleFreeRationalApproximation_div _ _ hPnew hQnew hQ0
      (fun x hx => (hstep ⟨x, hx⟩).1)
    have hnorm : ‖f - rationalContinuousMap (Icc a b) s hs.2.2‖ < E := by
      apply (ContinuousMap.norm_lt_iff _ hE).mpr
      intro x
      have heq := rationalContinuousMap_div_apply_eq _ _ hPnew hQnew hQ0
        (fun x hx => (hstep ⟨x, hx⟩).1) x
      change |f x - rationalContinuousMap (Icc a b) s hs.2.2 x| < E
      rw [heq]
      exact (hstep x).2
    have hbound := rationalMinimaxError_le_norm_sub m n f ⟨s, hs, rfl⟩
    rw [← hbest] at hbound
    exact (not_lt_of_ge hbound hnorm).elim
  · let w : Fin (N + 2) → Icc a b := fun i =>
      ⟨v i, hcab.1.trans (hvext i).1.1, (hvext i).1.2⟩
    refine ⟨w, hv, ?_, ?_⟩
    · intro i
      have hext := (hvext i).2
      rw [heval _ (w i).property] at hext
      exact hext
    · intro i
      have hsig := hvsign i
      rw [heval _ (w i.castSucc).property, heval _ (w i.succ).property] at hsig
      exact hsig

/-- Every best real rational approximant has the exact defect-adjusted equioscillation
certificate, including the zero function and zero error. Source: ATAP, Theorem 24.1;
focused rederivations, Theorem `thm:rational`.
atlas: rational-equioscillation (partial) -/
theorem exists_equioscillation_of_norm_sub_eq_rationalMinimaxError {a b : ℝ}
    (hab : a < b) {m n : ℕ} (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    (hbest : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f) :
    ∃ (v : Fin (rationalAlternationDegree m n r + 2) → Icc a b) (σ : ℝ),
      StrictMono (fun i => (v i : ℝ)) ∧ |σ| = 1 ∧
      ∀ i, f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i) =
        σ * (-1) ^ (i : ℕ) * ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ := by
  let g := f - rationalContinuousMap (Icc a b) r hr.2.2
  by_cases hE : ‖g‖ = 0
  · obtain ⟨v, hv⟩ := exists_strictMono_mem_Ioo hab (rationalAlternationDegree m n r + 2)
    let w : Fin (rationalAlternationDegree m n r + 2) → Icc a b :=
      fun i => ⟨v i, Ioo_subset_Icc_self (v i).property⟩
    refine ⟨w, 1, hv, by norm_num, fun i => ?_⟩
    have hzero := norm_eq_zero.mp hE
    have hval : g (w i) = 0 := congrArg (fun e : C(Icc a b, ℝ) => e (w i)) hzero
    change g (w i) = 1 * (-1) ^ (i : ℕ) * ‖g‖
    rw [hE, mul_zero]
    exact hval
  · have hEpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    obtain ⟨v, hv, habs, hsign⟩ :=
      exists_alternating_extrema_of_norm_sub_eq_rationalMinimaxError hab f r hr hbest hEpos
    obtain ⟨σ, hσ, hosc⟩ := exists_sign_of_alternating_abs_eq hEpos
      (fun i => f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i)) habs hsign
    exact ⟨v, σ, hv, hσ, hosc⟩

/-- An exact defect-adjusted rational equioscillation certificate implies optimality.
Source: ATAP, Theorem 24.1; focused rederivations, Theorem `thm:rational`.
atlas: rational-equioscillation (partial) -/
theorem norm_sub_eq_rationalMinimaxError_of_equioscillation {a b : ℝ}
    (hab : a < b) {m n : ℕ} (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    {v : Fin (rationalAlternationDegree m n r + 2) → Icc a b}
    (hv : StrictMono (fun i => (v i : ℝ))) {σ : ℝ} (hσ : |σ| = 1)
    (hosc : ∀ i, f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i) =
      σ * (-1) ^ (i : ℕ) * ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖) :
    ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f := by
  apply le_antisymm ?_ (rationalMinimaxError_le_norm_sub m n f ⟨r, hr, rfl⟩)
  by_cases hE : ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = 0
  · rw [hE]; exact rationalMinimaxError_nonneg m n f
  · have hEpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    have habs : ∀ i, |f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i)| =
        ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ := by
      intro i
      rw [hosc, abs_mul, abs_mul, abs_pow, hσ]
      simp [abs_of_nonneg (norm_nonneg _)]
    apply le_rationalMinimaxError_of_alternation hab f r hr hv ?_ (fun i => (habs i).ge)
    intro i
    have hnext : f (v i.succ) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.succ) =
        -(f (v i.castSucc) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.castSucc)) := by
      rw [hosc, hosc]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring
    have hne : f (v i.castSucc) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.castSucc) ≠ 0 := by
      intro hzero
      have := habs i.castSucc
      rw [hzero, abs_zero] at this
      linarith
    rw [hnext]
    nlinarith [sq_pos_of_ne_zero hne]

/-- A pole-free real rational function is best exactly when it equioscillates at the
defect-adjusted number of ordered points. The zero function has `m+2` points.
Source: ATAP, Theorem 24.1; focused rederivations, Theorem `thm:rational`.
atlas: rational-equioscillation -/
theorem norm_sub_eq_rationalMinimaxError_iff_equioscillation {a b : ℝ}
    (hab : a < b) {m n : ℕ} (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r) :
    ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ = rationalMinimaxError m n f ↔
      ∃ (v : Fin (rationalAlternationDegree m n r + 2) → Icc a b) (σ : ℝ),
        StrictMono (fun i => (v i : ℝ)) ∧ |σ| = 1 ∧
        ∀ i, f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i) =
          σ * (-1) ^ (i : ℕ) * ‖f - rationalContinuousMap (Icc a b) r hr.2.2‖ := by
  constructor
  · exact exists_equioscillation_of_norm_sub_eq_rationalMinimaxError hab f r hr
  · rintro ⟨v, σ, hv, hσ, hosc⟩
    exact norm_sub_eq_rationalMinimaxError_of_equioscillation hab f r hr hv hσ hosc

end NLAlib

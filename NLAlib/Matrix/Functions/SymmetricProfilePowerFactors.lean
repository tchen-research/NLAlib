import NLAlib.ForMathlib.Analysis.FiniteLatticeFactorization
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetric common power factors for Gaussian profiles

Pairing each row and entry factorization with its transpose preserves
symmetry. The four left Euclidean power sums give the uniform bound four;
the shared right factor simultaneously controls row energies and the
weighted entry norm. The construction includes all zero coordinates.

Source: the lattice-intersection step in Latała--van Handel--Youssef,
arXiv:1711.00807v2, §2.3, proved here by explicit power factors.
-/

noncomputable section
namespace NLAlib

/-- A normalized symmetric nonnegative profile has symmetric common power
factors with left Euclidean norm at most two, right row-profile norm at
most one, and weighted right entry norm at most one. The two input bounds
are exactly the target row power sum and the interpolated weighted entry
power sum. No abstract lattice-intersection theorem is assumed. -/
theorem exists_symmetric_profile_power_factors
    {n : Type*} [Fintype n] [DecidableEq n]
    {p q θ c : ℝ} (hp : 2 ≤ p) (hq : 0 < q) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hc : 0 < c) (hexp : 1 / p = (1 - θ) / 2 + θ / q)
    (a : Matrix n n ℝ) (ha : a.IsSymm) (ha0 : ∀ i j, 0 ≤ a i j)
    (hrow : (∑ i, (∑ j, a i j ^ 2) ^ (p / 2)) ≤ 1)
    (hentry : c ^ (θ * p) * (∑ i, ∑ j, a i j ^ p) ≤ 1) :
    ∃ U V : Matrix n n ℝ,
      (∀ i j, 0 ≤ U i j) ∧ (∀ i j, 0 ≤ V i j) ∧ U.IsSymm ∧ V.IsSymm ∧
      (∀ i j, a i j = U i j ^ (1 - θ) * V i j ^ θ) ∧
      (∑ i, ∑ j, U i j ^ 2) ≤ 4 ∧
      (∑ i, (∑ j, V i j ^ 2) ^ (q / 2)) ≤ 1 ∧
      c ^ q * (∑ i, ∑ j, V i j ^ q) ≤ 1 := by
  classical
  let s : n → ℝ := fun i => Real.sqrt (∑ j, a i j ^ 2)
  have hs : ∀ i, 0 ≤ s i := fun _ => Real.sqrt_nonneg _
  have hsq (i : n) : ∑ j, a i j ^ 2 = s i ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  have hsp : (∑ i, s i ^ p) = ∑ i, (∑ j, a i j ^ 2) ^ (p / 2) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    congr 1
    ring
  obtain ⟨ur, vr, hur, hvr, hfr, hlr, hrr⟩ :=
    exists_row_power_factors hp hq hθ hexp a s ha0 hs hsq
  obtain ⟨ue, ve, hue, hve, hfe, hle, hre⟩ :=
    exists_weighted_scalar_power_factors (by linarith : 0 < p) hq hθ hc hexp
      (fun ij : n × n => a ij.1 ij.2) (fun ij => ha0 ij.1 ij.2)
  have hlr' : (∑ i, ∑ j, ur i j ^ 2) ≤ 1 := hlr.trans_le (hsp.trans_le hrow)
  have hle' : (∑ ij, ue ij ^ 2) ≤ 1 := by
    rw [hle, Fintype.sum_prod_type]
    exact hentry
  let us : Bool × Bool → n × n → ℝ := fun l ij =>
    if l.1 then (if l.2 then ue (ij.2, ij.1) else ue ij)
    else (if l.2 then ur ij.2 ij.1 else ur ij.1 ij.2)
  let vs : Bool × Bool → n × n → ℝ := fun l ij =>
    if l.1 then (if l.2 then ve (ij.2, ij.1) else ve ij)
    else (if l.2 then vr ij.2 ij.1 else vr ij.1 ij.2)
  have hus (l : Bool × Bool) (ij : n × n) : 0 ≤ us l ij := by
    rcases l with ⟨l, r⟩
    cases l <;> cases r <;> dsimp [us] <;> first | exact hur _ _ | exact hue _
  have hvs (l : Bool × Bool) (ij : n × n) : 0 ≤ vs l ij := by
    rcases l with ⟨l, r⟩
    cases l <;> cases r <;> dsimp [vs] <;> first | exact hvr _ _ | exact hve _
  have hfs (l : Bool × Bool) (ij : n × n) :
      a ij.1 ij.2 = us l ij ^ (1 - θ) * vs l ij ^ θ := by
    rcases l with ⟨l, r⟩
    cases l <;> cases r
    · exact hfr _ _
    · change a ij.1 ij.2 = ur ij.2 ij.1 ^ (1 - θ) * vr ij.2 ij.1 ^ θ
      exact (ha.apply ij.2 ij.1).trans (hfr ij.2 ij.1)
    · exact hfe _
    · change a ij.1 ij.2 = ue (ij.2, ij.1) ^ (1 - θ) * ve (ij.2, ij.1) ^ θ
      exact (ha.apply ij.2 ij.1).trans (hfe (ij.2, ij.1))
  obtain ⟨U, V, hU, hV, hfactor, hUsq, hVle, hVeq⟩ :=
    exists_common_power_factors_with_right_eq hθ (fun ij : n × n => a ij.1 ij.2) us vs
      (fun ij => ha0 ij.1 ij.2) hus hvs hfs
  have hUsq' (i j : n) : U (i, j) ^ 2 = ur i j ^ 2 + ur j i ^ 2 +
      ue (i, j) ^ 2 + ue (j, i) ^ 2 := by
    rw [hUsq]
    simp [us, Fintype.sum_prod_type]
    ring
  have hUsym (i j : n) : U (j, i) = U (i, j) := by
    nlinarith [hUsq' i j, hUsq' j i, hU (i, j), hU (j, i)]
  have hVsym (i j : n) : V (j, i) = V (i, j) := by
    rw [hVeq, hVeq, hUsym, ha.apply j i]
  have hVrow (i j : n) : V (i, j) ≤ vr i j := hVle (false, false) (i, j)
  have hVentry (i j : n) : V (i, j) ≤ ve (i, j) := hVle (true, false) (i, j)
  refine ⟨fun i j => U (i, j), fun i j => V (i, j), fun i j => hU (i, j),
    fun i j => hV (i, j), ?_, ?_, fun i j => hfactor (i, j), ?_, ?_, ?_⟩
  · ext i j
    exact hUsym i j
  · ext i j
    exact hVsym i j
  · have hsum : (∑ i, ∑ j, U (i, j) ^ 2) =
        2 * (∑ i, ∑ j, ur i j ^ 2) + 2 * (∑ ij, ue ij ^ 2) := by
      simp_rw [hUsq', Finset.sum_add_distrib]
      rw [show (∑ i, ∑ j, ur j i ^ 2) = ∑ i, ∑ j, ur i j ^ 2 from Finset.sum_comm,
        show (∑ i, ∑ j, ue (j, i) ^ 2) = ∑ i, ∑ j, ue (i, j) ^ 2 from Finset.sum_comm,
        Fintype.sum_prod_type]
      ring
    rw [hsum]
    linarith
  · calc
      _ ≤ ∑ i, (∑ j, vr i j ^ 2) ^ (q / 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => sq_nonneg _) _ (by positivity)
        exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (hV (i, j)) (hVrow i j) 2
      _ = ∑ i, s i ^ p := hrr
      _ ≤ 1 := hsp.trans_le hrow
  · calc
      _ ≤ c ^ q * (∑ ij, ve ij ^ q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc.le _)
        rw [Fintype.sum_prod_type]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Real.rpow_le_rpow (hV (i, j)) (hVentry i j) hq.le
      _ = c ^ (θ * p) * ∑ ij : n × n, a ij.1 ij.2 ^ p := hre
      _ ≤ 1 := by simpa only [Fintype.sum_prod_type] using hentry

end NLAlib

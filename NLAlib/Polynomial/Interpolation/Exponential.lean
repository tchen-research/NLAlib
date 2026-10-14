import NLAlib.Polynomial.Interpolation.Lagrange
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Right-hand extrapolation of exponential interpolants

A polynomial interpolating a positive growing exponential at ordered real
nodes remains positive and increasing to the right of the last node, and stays
below the exponential there. The positivity proof uses finite interlacing Rolle
samples, avoiding a separate divided-difference or Newton-basis interface.
Source: the retained reciprocal lower-bound appendix in the focused re-derivations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Set
namespace NLAlib

private theorem exists_strictMono_deriv_zeros_between {n : ℕ} {f : ℝ → ℝ}
    {v : Fin (n+2) → ℝ} (hv : StrictMono v) (hf : Continuous f) (hz : ∀ i, f (v i) = 0) :
    ∃ c : Fin (n+1) → ℝ, StrictMono c ∧
      ∀ i, c i ∈ Ioo (v i.castSucc) (v i.succ) ∧ deriv f (c i) = 0 := by
  have h (i : Fin (n+1)) : ∃ c ∈ Ioo (v i.castSucc) (v i.succ), deriv f c = 0 := by
    exact exists_deriv_eq_zero (hv Fin.castSucc_lt_succ) hf.continuousOn (by rw [hz, hz])
  choose c hc hz using h
  refine ⟨c, fun i j hij => ?_, fun i => ⟨hc i, hz i⟩⟩
  exact (hc i).2.trans_le (hv.monotone (Fin.succ_le_castSucc_iff.mpr hij)) |>.trans (hc j).1

private theorem hasDerivAt_scaled_exp (A B x : ℝ) :
    HasDerivAt (fun t : ℝ => A * Real.exp (B*t)) (A*B*Real.exp (B*x)) x := by
  convert! (((hasDerivAt_id x).const_mul B).exp).const_mul A using 1
  simp [mul_comm, mul_assoc]

/-- A degree-`n` polynomial interpolating a positive growing exponential at
`n+1` ordered nodes is positive and has nonnegative derivative to the right
of the last node. Source: the retained reciprocal lower-bound appendix,
finite Rolle proof of positive divided differences. -/
theorem eval_pos_and_derivative_nonneg_of_exp_interpolation (n : ℕ) :
    ∀ (p : ℝ[X]) (_hp : p.degree ≤ n) (v : Fin (n+1) → ℝ), StrictMono v →
      ∀ (A B : ℝ), 0 < A → 0 < B →
        (∀ i, p.eval (v i) = A * Real.exp (B*v i)) →
        ∀ x : ℝ, v (Fin.last n) ≤ x → 0 < p.eval x ∧ 0 ≤ p.derivative.eval x := by
  induction n with
  | zero =>
    intro p hp v _ A B hA _ hval x _
    have hc := p.eq_C_of_degree_le_zero hp
    have h := hval (Fin.last 0)
    rw [hc, eval_C] at h
    rw [hc, eval_C, derivative_C, eval_zero]
    exact ⟨h ▸ mul_pos hA (Real.exp_pos _), le_rfl⟩
  | succ n ih =>
    intro p hp v hv A B hA hB hval x hx
    let f : ℝ → ℝ := fun t => A * Real.exp (B*t) - p.eval t
    have hf : Continuous f := by dsimp [f]; fun_prop
    obtain ⟨c, hc, hcz⟩ := exists_strictMono_deriv_zeros_between hv hf
      (fun i => by dsimp [f]; rw [hval]; ring)
    have hderval (i : Fin (n+1)) : p.derivative.eval (c i) =
        (A*B) * Real.exp (B*c i) := by
      have hd := (hasDerivAt_scaled_exp A B (c i)).sub (p.hasDerivAt (c i))
      have hd' : HasDerivAt (fun t : ℝ => A * Real.exp (B*t) - p.eval t)
          (A*B*Real.exp (B*c i) - p.derivative.eval (c i)) (c i) := by
        convert! hd using 1
      have hz := (hcz i).2
      change deriv (fun t => A * Real.exp (B*t) - p.eval t) (c i) = 0 at hz
      rw [hd'.deriv] at hz
      linarith
    have hpder : p.derivative.degree ≤ n := degree_le_of_natDegree_le
      ((natDegree_derivative_le p).trans (by have h := natDegree_le_of_degree_le hp; omega))
    have hlast : c (Fin.last n) < v (Fin.last (n+1)) := by
      simpa only [Fin.succ_last] using (hcz (Fin.last n)).1.2
    have hdpos (t : ℝ) (ht : v (Fin.last (n+1)) ≤ t) : 0 < p.derivative.eval t :=
      (ih p.derivative hpder c hc (A*B) B (mul_pos hA hB) hB hderval t
        (hlast.le.trans ht)).1
    have hmono : MonotoneOn p.eval (Ici (v (Fin.last (n+1)))) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) p.continuous.continuousOn
        (fun t _ => (p.hasDerivAt t).hasDerivWithinAt)
      intro t ht
      exact (hdpos t (interior_subset ht)).le
    have hnodepos : 0 < p.eval (v (Fin.last (n+1))) := by
      rw [hval]
      exact mul_pos hA (Real.exp_pos _)
    exact ⟨hnodepos.trans_le (hmono self_mem_Ici hx hx), (hdpos x hx).le⟩

/-- To the right of all interpolation nodes, an exponential interpolant is
positive, increasing, and bounded above by the target exponential.
Source: the retained reciprocal lower-bound appendix, interpolation remainder.
atlas: exp-rational-halfline (partial) -/
theorem eval_pos_le_exp_and_derivative_nonneg_of_interpolation {n : ℕ}
    {p : ℝ[X]} (hp : p.degree ≤ n) {v : Fin (n+1) → ℝ} (hv : StrictMono v)
    {a x B : ℝ} (hB : 0 < B) (hva : ∀ i, v i ∈ Ioo 0 a)
    (hval : ∀ i, p.eval (v i) = Real.exp (B*v i)) (hx : a ≤ x) :
    0 < p.eval x ∧ p.eval x ≤ Real.exp (B*x) ∧ 0 ≤ p.derivative.eval x := by
  have hxa : v (Fin.last n) ≤ x := (hva _).2.le.trans hx
  have hpos := eval_pos_and_derivative_nonneg_of_exp_interpolation n p hp v hv 1 B
    zero_lt_one hB (by simpa only [one_mul] using hval) x hxa
  have hax : 0 < x := (hva 0).1.trans_le ((hva 0).2.le.trans hx)
  have hinterp : Lagrange.interpolate Finset.univ v (fun i => Real.exp (B*v i)) = p := by
    apply (Lagrange.eq_interpolate_of_eval_eq _ hv.injective.injOn ?_ ?_).symm
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
    · intro i _
      exact hval i
  obtain ⟨ξ, _, hrem⟩ := exists_sub_eval_interpolate_eq (f := fun t => Real.exp (B*t))
    hax hv.injective (fun i => ⟨(hva i).1.le, (hva i).2.le.trans hx⟩)
    ⟨le_rfl.trans hax.le, le_rfl⟩ (by fun_prop) (by
      intro k _
      rw [iteratedDeriv_exp_const_mul]
      fun_prop)
  rw [show ((fun t => Real.exp (B*t)) ∘ v) = (fun i => Real.exp (B*v i)) by rfl,
    hinterp, iteratedDeriv_exp_const_mul] at hrem
  have hnodal : 0 ≤ (Lagrange.nodal Finset.univ v).eval x := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr ((hva i).2.le.trans hx)
  have hremNonneg : 0 ≤ Real.exp (B*x) - p.eval x := by
    rw [hrem]
    exact mul_nonneg (div_nonneg (mul_pos (pow_pos hB _) (Real.exp_pos _)).le
      (Nat.cast_nonneg _)) hnodal
  exact ⟨hpos.1, sub_nonneg.mp hremNonneg, hpos.2⟩

end NLAlib

import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Complex.Basic

/-! # Complex polynomial approximation on a real interval

Real Weierstrass approximation of the two components yields ordinary complex
polynomial approximation on a compact real interval.
-/

noncomputable section
open Polynomial Set
namespace Polynomial

/-- Every continuous complex function on a compact real interval is uniformly
approximated by a complex polynomial on the real argument. -/
theorem exists_complex_polynomial_near_of_continuousOn {a b : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ x ∈ Icc a b, ‖f x - p.eval (x : ℂ)‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (f x).re)
    (Complex.continuous_re.comp_continuousOn hf) (ε/2) (by linarith)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (f x).im)
    (Complex.continuous_im.comp_continuousOn hf) (ε/2) (by linarith)
  refine ⟨p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom, ?_⟩
  intro x hx
  have hp' := hp x hx
  have hq' := hq x hx
  have h := Complex.norm_le_abs_re_add_abs_im
    (f x - (p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom).eval (x : ℂ))
  have he : (p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom).eval (x : ℂ) =
      (p.eval x : ℝ) + Complex.I * (q.eval x : ℝ) := by
    change _ = (Complex.ofRealHom (p.eval x)) + Complex.I * Complex.ofRealHom (q.eval x)
    rw [eval_add, eval_mul, eval_C]
    rw [show (x : ℂ) = Complex.ofRealHom x by rfl, eval_map_apply, eval_map_apply]
  rw [he] at h
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, Complex.I_im, one_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add] at h
  rw [abs_sub_comm (p.eval x) _] at hp'
  rw [abs_sub_comm (q.eval x) _] at hq'
  rw [he]
  exact h.trans_lt (by linarith)

end Polynomial

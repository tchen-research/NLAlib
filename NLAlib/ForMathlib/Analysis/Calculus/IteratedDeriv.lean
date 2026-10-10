import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Iterated derivatives of `f − p` for a polynomial `p`

`iteratedDeriv_sub_eval_eqOn`: on an open set where `f, f', …, f^{(n−1)}` are differentiable,
the `k`-th derivative (`k ≤ n`) of `f − p` is `f^{(k)} − p^{(k)}`. A general calculus fact, not
about NLAlib's objects; candidate for upstreaming to `Mathlib/Analysis/Calculus/IteratedDeriv/`.
Used by `NLAlib.Polynomial.Interpolation` (atlas `interpolation-remainder`).
-/

namespace NLAlib

open Polynomial Set

/-- On an open set `U` where `f, f', …, f^{(n−1)}` are differentiable, the `k`-th derivative
(`k ≤ n`) of `f − p` for a polynomial `p` is `f^{(k)} − p^{(k)}`. -/
theorem iteratedDeriv_sub_eval_eqOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (p : ℝ[X])
    {n : ℕ} (hf : ∀ k < n, DifferentiableOn ℝ (iteratedDeriv k f) U) :
    ∀ k ≤ n, EqOn (iteratedDeriv k (fun t => f t - p.eval t))
      (fun t => iteratedDeriv k f t - (derivative^[k] p).eval t) U := by
  intro k hk
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    have hev : iteratedDeriv k (fun t => f t - p.eval t) =ᶠ[nhds t]
        (fun t => iteratedDeriv k f t - (derivative^[k] p).eval t) :=
      (ih (by omega)).eventuallyEq_of_mem (hU.mem_nhds ht)
    rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ, Function.iterate_succ_apply']
    exact (deriv_fun_sub ((hf k (by omega)).differentiableAt (hU.mem_nhds ht))
      (Polynomial.differentiableAt _)).trans (by rw [Polynomial.deriv])

end NLAlib

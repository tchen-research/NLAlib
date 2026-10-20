import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact derivatives of native resolvent powers

Differentiating the genuine resolvent in a possibly noncommutative Banach
algebra gives every power derivative and the exact iterated derivative,
including the zeroth derivative. Only actual resolvent-set membership is
required; no invertibility or derivative formula is supplied separately.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace spectrum
variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A]
  [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- The derivative of an actual resolvent power is its next power times the negative exponent. -/
theorem hasDerivAt_resolvent_pow (a : A) {z : 𝕜}
    (hz : z∈resolventSet 𝕜 a) (n : ℕ) :
    HasDerivAt (fun w : 𝕜 => resolvent a w^n)
      (-(n : 𝕜)•resolvent a z^(n+1)) z := by
  have hd := (hasDerivAt_resolvent_const_left hz).fun_pow' n
  have he : (∑ i∈Finset.range n,
      resolvent a z^(n.pred-i)*(-resolvent a z^2)*resolvent a z^i)=
      -(n : 𝕜)•resolvent a z^(n+1) := by
    calc
      _ = ∑ _i∈Finset.range n, -resolvent a z^(n+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_neg,neg_mul,← pow_add,← pow_add]
        have hi' : i<n := Finset.mem_range.mp hi
        have hex : n.pred-i+2+i=n+1 := by
          rw [Nat.pred_eq_sub_one]
          omega
        rw [hex]
      _ = _ := by simp [← Nat.cast_smul_eq_nsmul 𝕜]
  exact he ▸ hd

/-- The exact nth derivative of the native resolvent is the signed factorial times its next power. -/
theorem iteratedDeriv_resolvent (a : A) (n : ℕ) {z : 𝕜}
    (hz : z∈resolventSet 𝕜 a) :
    iteratedDeriv n (resolvent a) z=
      ((-1 : 𝕜)^n*(n.factorial : 𝕜))•resolvent a z^(n+1) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (resolvent a)=ᶠ[𝓝 z]
        (fun w : 𝕜 => ((-1 : 𝕜)^n*(n.factorial : 𝕜))•resolvent a w^(n+1)) := by
      filter_upwards [(isOpen_resolventSet a).mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedDeriv_succ,he.deriv_eq]
    have hder : deriv (fun w : 𝕜 => ((-1 : 𝕜)^n*(n.factorial : 𝕜))•resolvent a w^(n+1)) z=
        ((-1 : 𝕜)^n*(n.factorial : 𝕜))•(-(n+1 : 𝕜)•resolvent a z^(n+1+1)) := by
      simpa only [Nat.cast_add,Nat.cast_one,Pi.smul_def] using
        ((hasDerivAt_resolvent_pow a hz (n+1)).const_smul
          ((-1 : 𝕜)^n*(n.factorial : 𝕜))).deriv
    rw [hder]
    simp only [smul_smul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    congr 1
    ring

end spectrum

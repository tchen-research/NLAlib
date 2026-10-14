import NLAlib.ForMathlib.Algebra.BoundedPartialFractions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-! # The exact fixed-denominator rational space

Clearing the denominator identifies bounded numerator degree with a unique
polynomial part and all repeated-pole principal parts. This is the direct sum
used by rational Gauss quadrature. Linear factors are written monically as
`X-v`; the source's `1+ζX` factors differ by nonzero scalar factors.
Source: Gautschi (2004), rational Gauss rules; operator derivations AQ37.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

/-- The bounded numerator space is exactly the direct sum of its polynomial
part and the repeated-pole principal parts, with unique coefficients. At pole
degree `d` the polynomial part is zero, and at pole degree zero it is ordinary
polynomial approximation. Source: Gautschi (2004), rational space AQ37.
atlas: rational-gauss-quadrature (partial) -/
theorem existsUnique_fixed_denominator_partial_fractions
    (v : ι → 𝕜) (hv : Function.Injective v) (s : ι → ℕ)
    {d : ℕ} (hmd : (∑ i, s i) ≤ d) {p : 𝕜[X]} (hp : p.degree < d) :
    ∃! qc : 𝕜[X] × ((i : ι) → Fin (s i) → 𝕜),
      qc.1.degree < (d - ∑ i, s i : ℕ) ∧
      p = qc.1 * linearPoleProduct v s + linearPoleRemainder v s qc.2 := by
  obtain ⟨qc, hqc, huniq⟩ := existsUnique_eq_mul_linearPoleProduct_add_linearPoleRemainder v hv s p
  have hd := (degree_mul_linearPoleProduct_add_linearPoleRemainder_lt_iff v s hmd qc.1 qc.2).mp
    (hqc ▸ hp)
  exact ⟨qc, ⟨hd, hqc⟩, fun qc' h => huniq qc' h.2⟩

/-- Conversely, every polynomial plus the prescribed principal parts has
bounded numerator degree exactly when its polynomial part has the advertised
degree bound. This includes a zero polynomial part when the pole degree is
the full degree budget. Source: rational space AQ37.
atlas: rational-gauss-quadrature (partial) -/
theorem degree_fixed_denominator_partial_fractions_lt_iff
    (v : ι → 𝕜) (s : ι → ℕ) {d : ℕ} (hmd : (∑ i, s i) ≤ d)
    (q : 𝕜[X]) (c : (i : ι) → Fin (s i) → 𝕜) :
    (q*linearPoleProduct v s+linearPoleRemainder v s c).degree < d ↔
      q.degree < (d-∑ i, s i : ℕ) :=
  degree_mul_linearPoleProduct_add_linearPoleRemainder_lt_iff v s hmd q c

/-- Evaluating the cleared principal-part expansion recovers the actual
rational functions at every pole-free point. Source: rational space AQ37.
atlas: rational-gauss-quadrature (partial) -/
theorem eval_div_linearPoleProduct_eq_partial_fractions
    (v : ι → 𝕜) (s : ι → ℕ) (q : 𝕜[X])
    (c : (i : ι) → Fin (s i) → 𝕜) {t : 𝕜} (ht : ∀ i, t ≠ v i) :
    (q * linearPoleProduct v s + linearPoleRemainder v s c).eval t /
        (linearPoleProduct v s).eval t =
      q.eval t + ∑ i, ∑ j : Fin (s i), c i j / (t-v i)^(s i-j.val) := by
  have hprod : (∏ i, (t-v i)^(s i)) ≠ 0 := prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (sub_ne_zero.mpr (ht i)))
  have hden : (linearPoleProduct v s).eval t = ∏ i, (t-v i)^(s i) := by
    simp only [linearPoleProduct, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  rw [eval_add, eval_mul, add_div, mul_div_cancel_right₀ _ (hden ▸ hprod),
    linearPoleRemainder, eval_finsetSum, Finset.sum_div]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [eval_finsetSum, Finset.sum_div]
  apply sum_congr rfl
  intro j _
  simp only [eval_mul, eval_C, eval_prod, eval_pow, eval_sub, eval_X]
  have herase : (∏ k ∈ univ.erase i, (t-v k)^(s k)) ≠ 0 := prod_ne_zero_iff.mpr
    (fun k _ => pow_ne_zero _ (sub_ne_zero.mpr (ht k)))
  have hsplit : (∏ k, (t-v k)^(s k)) = (t-v i)^(s i) *
      (∏ k ∈ univ.erase i, (t-v k)^(s k)) := (mul_prod_erase _ _ (mem_univ i)).symm
  have hpow : (t-v i)^(s i) = (t-v i)^j.val * (t-v i)^(s i-j.val) := by
    rw [← pow_add, Nat.add_sub_of_le j.isLt.le]
  rw [hden, hsplit, hpow]
  field_simp [herase, sub_ne_zero.mpr (ht i)]

/-- A source factor `1+ζX` differs from its monic pole factor by the nonzero
scalar `ζ`. This identifies the pole-space convention with AQ37. -/
theorem one_add_C_mul_X_eq_C_mul_pole {ζ : 𝕜} (hζ : ζ ≠ 0) :
    1 + C ζ*X = C ζ*(X-C (-ζ⁻¹)) := by
  rw [mul_sub, ← map_mul, mul_neg, mul_inv_cancel₀ hζ, map_neg, C_1]
  ring

omit [DecidableEq ι] in
/-- The prescribed repeated `1+ζX` denominator is a nonzero scalar times the
monic linear-pole denominator. All pole multiplicities, including zero, are
retained. Source: rational Gauss space AQ37.
atlas: rational-gauss-quadrature (partial) -/
theorem prod_one_add_C_mul_X_pow_eq_C_mul_linearPoleProduct
    (ζ : ι → 𝕜) (hζ : ∀ i, ζ i ≠ 0) (s : ι → ℕ) :
    (∏ i, (1+C (ζ i)*X)^(s i)) =
      C (∏ i, (ζ i)^(s i)) * linearPoleProduct (fun i => -(ζ i)⁻¹) s := by
  simp_rw [one_add_C_mul_X_eq_C_mul_pole (hζ _), mul_pow]
  rw [prod_mul_distrib]
  simp only [← map_pow, ← map_prod, linearPoleProduct]

/-- Each monic pole power is exactly the prescribed source rational basis
function times its explicit nonzero scalar. Source: rational Gauss space AQ37.
atlas: rational-gauss-quadrature (partial) -/
theorem div_pole_pow_eq_mul_div_one_add_mul_pow {ζ t c : 𝕜}
    (hζ : ζ ≠ 0) (s : ℕ) :
    c/(t-(-ζ⁻¹))^s = (c*ζ^s)/(1+ζ*t)^s := by
  have hbase : 1+ζ*t = ζ*(t-(-ζ⁻¹)) := by rw [sub_neg_eq_add, mul_add, mul_inv_cancel₀ hζ]; ring
  rw [hbase, mul_pow]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ hζ)).symm.trans (by ring)

end NLAlib

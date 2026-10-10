import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Finset.Sort
import NLAlib.Polynomial.Basic
import NLAlib.ForMathlib.Algebra.Polynomial
import NLAlib.ForMathlib.Analysis.Calculus.IteratedDeriv

/-!
# Polynomial interpolation: Rolle, the remainder formula, Chebyshev nodes

Layer 0 (no matrices). The error of polynomial interpolation for a sufficiently differentiable
real function, and its specialisation to the zeros of a Chebyshev polynomial.

* `exists_iteratedDeriv_eq_zero_of_strictMono`, `exists_iteratedDeriv_eq_zero_of_card`:
  generalised Rolle — a function with `q + 2` zeros in `[a, b]` has a `(q + 1)`-st derivative
  vanishing somewhere in `(a, b)`.
* `exists_sub_eval_interpolate_eq`: the Lagrange (Cauchy) remainder formula
  `f x − p(x) = f^{(q+1)}(ξ)/(q+1)! · ω(x)` for interpolation at `q + 1` distinct nodes, with
  `ω = Lagrange.nodal` the nodal polynomial.
* `nodal_chebyshevZero` (with `chebyshevZero q k = cos((2k + 1)π/(2q))` from `Basic`):
  the nodal polynomial of the Chebyshev zeros is `T_q / 2^(q−1)`; hence
  `abs_eval_nodal_chebyshevZero_le`: `|ω(x)| ≤ 1/2^(q−1)` on `[−1, 1]`.
* `abs_sub_eval_interpolate_chebyshevZero_le`: interpolation at the `q + 1` zeros of `T_{q+1}`
  has error at most `M / (2^q (q + 1)!)` on `[−1, 1]` when `|f^{(q+1)}| ≤ M`.

Derivatives are Mathlib's global `iteratedDeriv`. Differentiability is assumed only on the open
interval (`DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)` for `k ≤ q`) together with
continuity of `f` on the closed interval, the classical hypothesis "`f ∈ C[a, b]` and `f^{(q+1)}`
exists on `(a, b)`".

Atlas: `interpolation-remainder`, `chebyshev-interpolation-error`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- One application of Rolle between consecutive zeros: zeros `v 0 < ⋯ < v (n+1)` of `f`
give zeros `c 0 < ⋯ < c n` of `deriv f` with `c i ∈ (v i, v (i+1))`. -/
private lemma exists_strictMono_deriv_eq_zero {n : ℕ} {f : ℝ → ℝ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (hf : ContinuousOn f (Icc (v 0) (v (Fin.last _))))
    (hz : ∀ i, f (v i) = 0) :
    ∃ c : Fin (n + 1) → ℝ, StrictMono c ∧
      ∀ i, c i ∈ Ioo (v i.castSucc) (v i.succ) ∧ deriv f (c i) = 0 := by
  have key : ∀ i : Fin (n + 1), ∃ c ∈ Ioo (v i.castSucc) (v i.succ), deriv f c = 0 := by
    intro i
    refine exists_deriv_eq_zero (hv Fin.castSucc_lt_succ) (hf.mono ?_) (by rw [hz, hz])
    exact Icc_subset_Icc (hv.monotone (Fin.zero_le _)) (hv.monotone (Fin.le_last _))
  choose c hc hc0 using key
  refine ⟨c, fun i j hij => ?_, fun i => ⟨hc i, hc0 i⟩⟩
  calc c i < v i.succ := (hc i).2
    _ ≤ v j.castSucc := hv.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    _ < c j := (hc j).1

/-- Generalised Rolle on the interval spanned by the nodes (induction on `q`). -/
private lemma exists_iteratedDeriv_eq_zero_aux (q : ℕ) :
    ∀ (f : ℝ → ℝ) (v : Fin (q + 2) → ℝ), StrictMono v →
      ContinuousOn f (Icc (v 0) (v (Fin.last _))) →
      (∀ k < q, ContinuousOn (iteratedDeriv (k + 1) f) (Ioo (v 0) (v (Fin.last _)))) →
      (∀ i, f (v i) = 0) → ∃ ξ ∈ Ioo (v 0) (v (Fin.last _)), iteratedDeriv (q + 1) f ξ = 0 := by
  induction q with
  | zero =>
    intro f v hv hf _ hz
    obtain ⟨c, -, hc⟩ := exists_strictMono_deriv_eq_zero hv hf hz
    exact ⟨c 0, (hc 0).1, by simpa using (hc 0).2⟩
  | succ q ih =>
    intro f v hv hf hf' hz
    obtain ⟨c, hcm, hc⟩ := exists_strictMono_deriv_eq_zero hv hf hz
    have hsub : Icc (c 0) (c (Fin.last _)) ⊆ Ioo (v 0) (v (Fin.last _)) := by
      intro t ht
      have h0 := (hc 0).1.1
      have h1 := (hc (Fin.last _)).1.2
      simp only [Fin.castSucc_zero, Fin.succ_last] at h0 h1
      exact ⟨h0.trans_le ht.1, ht.2.trans_lt h1⟩
    have hd0 : ContinuousOn (deriv f) (Icc (c 0) (c (Fin.last _))) := by
      have h := hf' 0 (Nat.succ_pos _)
      rw [zero_add, iteratedDeriv_one] at h
      exact h.mono hsub
    have hdk : ∀ k < q, ContinuousOn (iteratedDeriv (k + 1) (deriv f))
        (Ioo (c 0) (c (Fin.last _))) := by
      intro k hk
      have h := hf' (k + 1) (by omega)
      rw [iteratedDeriv_succ'] at h
      exact h.mono (Ioo_subset_Icc_self.trans hsub)
    obtain ⟨ξ, hξ, hξ0⟩ := ih (deriv f) c hcm hd0 hdk (fun i => (hc i).2)
    refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ), ?_⟩
    simpa only [iteratedDeriv_succ'] using hξ0

/-- **Generalised Rolle theorem.** If `f` vanishes at `q + 2` points `v 0 < ⋯ < v (q+1)` of
`[a, b]`, `f` is continuous on `[a, b]` and the derivatives `f', …, f^{(q)}` are continuous on
`(a, b)`, then `f^{(q+1)}(ξ) = 0` for some `ξ ∈ (a, b)`.
Source: Süli–Mayers, *An Introduction to Numerical Analysis*, proof of Thm 6.2; Atkinson,
*An Introduction to Numerical Analysis* (2nd ed.), proof of Thm 3.2.
Atlas: `interpolation-remainder` (lemma).
Deviation: stated with `q + 2` zeros and the `(q + 1)`-st derivative (so the conclusion is in the
open interval without a side condition); only continuity of `f^{(k)}`, `1 ≤ k ≤ q`, on `(a, b)`
is assumed — no differentiability, because `iteratedDeriv` is Mathlib's global derivative and
Rolle (`exists_deriv_eq_zero`) needs only continuity.
atlas: interpolation-remainder -/
theorem exists_iteratedDeriv_eq_zero_of_strictMono {f : ℝ → ℝ} {a b : ℝ} {q : ℕ}
    {v : Fin (q + 2) → ℝ} (hv : StrictMono v) (hva : ∀ i, v i ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < q, ContinuousOn (iteratedDeriv (k + 1) f) (Ioo a b))
    (hz : ∀ i, f (v i) = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 := by
  have hsub : Icc (v 0) (v (Fin.last _)) ⊆ Icc a b := Icc_subset_Icc (hva 0).1 (hva _).2
  have hsub' : Ioo (v 0) (v (Fin.last _)) ⊆ Ioo a b := Ioo_subset_Ioo (hva 0).1 (hva _).2
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_aux q f v hv (hf.mono hsub)
    (fun k hk => (hf' k hk).mono hsub') hz
  exact ⟨ξ, hsub' hξ, hξ0⟩

/-- **Generalised Rolle theorem**, finset form: if `f` vanishes on a set of `q + 2` points of
`[a, b]` (hypotheses as in `exists_iteratedDeriv_eq_zero_of_strictMono`), then `f^{(q+1)}`
vanishes somewhere in `(a, b)`.
Source: Süli–Mayers, proof of Thm 6.2. Atlas: `interpolation-remainder` (lemma).
atlas: interpolation-remainder -/
theorem exists_iteratedDeriv_eq_zero_of_card {f : ℝ → ℝ} {a b : ℝ} {q : ℕ} {s : Finset ℝ}
    (hs : s.card = q + 2) (hsab : ∀ x ∈ s, x ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < q, ContinuousOn (iteratedDeriv (k + 1) f) (Ioo a b))
    (hz : ∀ x ∈ s, f x = 0) :
    ∃ ξ ∈ Ioo a b, iteratedDeriv (q + 1) f ξ = 0 :=
  exists_iteratedDeriv_eq_zero_of_strictMono (s.orderEmbOfFin hs).strictMono
    (fun i => hsab _ (s.orderEmbOfFin_mem hs i)) hf hf' (fun i => hz _ (s.orderEmbOfFin_mem hs i))

/-- **Interpolation remainder formula.** Let `v : Fin (q + 1) → ℝ` be distinct nodes in
`[a, b]`, `f` continuous on `[a, b]` with `f, f', …, f^{(q)}` differentiable on `(a, b)`, and
`x ∈ [a, b]`. Then for the interpolating polynomial `L = Lagrange.interpolate univ v (f ∘ v)`
and the nodal polynomial `ω = ∏ (X − v i)` there is `ξ ∈ (a, b)` with
`f x − L(x) = f^{(q+1)}(ξ) / (q + 1)! · ω(x)`.
Source: Süli–Mayers, *An Introduction to Numerical Analysis*, Thm 6.2; Atkinson (2nd ed.),
Thm 3.2; Cheney, *Introduction to Approximation Theory*, Ch. 3. Atlas:
`interpolation-remainder`.
Deviation: `ξ` is in the open interval `(a, b)` (stronger than `[a, b]`), at the cost of the
hypothesis `a < b` (used only when `x` is a node).
atlas: interpolation-remainder -/
theorem exists_sub_eval_interpolate_eq {f : ℝ → ℝ} {a b x : ℝ} {q : ℕ} {v : Fin (q + 1) → ℝ}
    (hab : a < b) (hv : Function.Injective v) (hva : ∀ i, v i ∈ Icc a b) (hx : x ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k ≤ q, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b, f x - (Lagrange.interpolate Finset.univ v (f ∘ v)).eval x =
      iteratedDeriv (q + 1) f ξ / (q + 1).factorial * (Lagrange.nodal Finset.univ v).eval x := by
  classical
  set L := Lagrange.interpolate Finset.univ v (f ∘ v) with hL
  set ω := Lagrange.nodal Finset.univ v with hω_def
  have hLnode : ∀ i, L.eval (v i) = f (v i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ i)
  have hωnode : ∀ i, ω.eval (v i) = 0 := fun i => Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  by_cases hnode : ∃ i, x = v i
  · obtain ⟨i, rfl⟩ := hnode
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hLnode, hωnode]
    simp
  simp only [not_exists] at hnode
  have hω : ω.eval x ≠ 0 := by
    rw [hω_def, Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hnode i)
  set K := (f x - L.eval x) / ω.eval x with hK
  set h : ℝ[X] := L + C K * ω with hh
  have hs : (insert x (Finset.univ.image v)).card = q + 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hv, Finset.card_univ,
      Fintype.card_fin]
    simpa [eq_comm] using hnode
  have hEq := iteratedDeriv_sub_eval_eqOn isOpen_Ioo h (n := q + 1)
    (fun k hk => hf' k (by omega))
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_of_card (f := fun t => f t - h.eval t) hs
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact hva i)
    (hf.sub (Polynomial.continuous _).continuousOn)
    (fun k hk => ((hf' (k + 1) (by omega)).continuousOn.sub
      (Polynomial.continuous _).continuousOn).congr (hEq (k + 1) (by omega)))
    (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simp only [hh, eval_add, eval_mul, eval_C, hK]
        field_simp
        ring
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        simp [hh, hLnode, hωnode])
  refine ⟨ξ, hξ, ?_⟩
  have hD : (derivative^[q + 1] h).eval ξ = K * (q + 1).factorial := by
    have hLdeg : L.degree < ↑(q + 1) := by
      have := Lagrange.degree_interpolate_lt (s := Finset.univ) (f ∘ v) hv.injOn
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have hωdeg : ω.natDegree = q + 1 := by simp [hω_def, Lagrange.natDegree_nodal]
    have hωmon : ω.leadingCoeff = 1 := Lagrange.nodal_monic
    rw [hh, iterate_map_add, iterate_derivative_eq_zero_of_degree_lt hLdeg, zero_add,
      iterate_derivative_C_mul, eval_mul, eval_C, ← hωdeg, eval_iterate_derivative_natDegree,
      hωmon, mul_one]
  have h1 : iteratedDeriv (q + 1) (fun t => f t - h.eval t) ξ =
      iteratedDeriv (q + 1) f ξ - (derivative^[q + 1] h).eval ξ := hEq (q + 1) le_rfl hξ
  rw [hξ0, hD] at h1
  have hfac : ((q + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [show iteratedDeriv (q + 1) f ξ = K * (q + 1).factorial by linarith, hK]
  field_simp

/-- The nodal polynomial of the `q` Chebyshev zeros is the monic Chebyshev polynomial:
`∏ₖ (X − cos((2k + 1)π/(2q))) = T_q / 2^(q−1)` (both sides are `1` when `q = 0`).
Source: Trefethen, *Approximation Theory and Approximation Practice*, Ch. 2–3; Rivlin,
*Chebyshev Polynomials*, §1.2.
Atlas: `chebyshev-interpolation-error` (lemma).
Deviation: no `0 < q` hypothesis is needed (`q − 1` is truncated subtraction).
atlas: chebyshev-interpolation-error -/
theorem nodal_chebyshevZero (q : ℕ) :
    Lagrange.nodal Finset.univ (chebyshevZero q) = C (1 / 2 ^ (q - 1)) * Chebyshev.T ℝ q := by
  classical
  have hroots := Chebyshev.roots_T_real q
  rw [Finset.image_val, Finset.range_val, (Chebyshev.roots_T_real_nodup q).dedup] at hroots
  have hcard : (Chebyshev.T ℝ q).roots.card = (Chebyshev.T ℝ q).natDegree := by
    rw [hroots]
    simp
  have hT := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hroots, Multiset.map_map] at hT
  conv_rhs => rw [← hT]
  rw [Chebyshev.leadingCoeff_T, Lagrange.nodal_eq, ← mul_assoc, ← C_mul]
  have hc : (1 / 2 ^ (q - 1) : ℝ) * 2 ^ ((q : ℤ).natAbs - 1) = 1 := by
    rw [Int.natAbs_natCast]
    field_simp
  rw [hc, C_1, one_mul]
  have := Finset.prod_map_val (Finset.range q)
    ((fun a => X - C a) ∘ fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * q)))
  rw [Finset.range_val] at this
  rw [this, ← Fin.prod_univ_eq_prod_range]
  rfl

/-- The Chebyshev zeros are roots of `T_q`.
Atlas: `chebyshev-interpolation-error` (API).
atlas: chebyshev-interpolation-error -/
theorem eval_T_real_chebyshevZero (q : ℕ) (k : Fin q) :
    (Chebyshev.T ℝ q).eval (chebyshevZero q k) = 0 := by
  classical
  have h := Lagrange.eval_nodal_at_node (s := Finset.univ) (v := chebyshevZero q)
    (Finset.mem_univ k)
  rw [nodal_chebyshevZero, eval_mul, eval_C] at h
  exact (mul_eq_zero.mp h).resolve_left (by positivity)

/-- On `[−1, 1]` the nodal polynomial of the `q` Chebyshev zeros is at most `1/2^(q−1)` in
modulus. Source: Trefethen, ATAP, Ch. 3; Cheney, Ch. 3. Atlas: `chebyshev-interpolation-error`
(lemma). Deviation: no `0 < q` hypothesis.
atlas: chebyshev-interpolation-error -/
theorem abs_eval_nodal_chebyshevZero_le (q : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Lagrange.nodal Finset.univ (chebyshevZero q)).eval x| ≤ 1 / 2 ^ (q - 1) := by
  rw [nodal_chebyshevZero, eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity)
    (Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx))

/-- **Chebyshev interpolation error.** Let `f` be continuous on `[−1, 1]` with
`f, f', …, f^{(q)}` differentiable on `(−1, 1)` and `|f^{(q+1)}| ≤ M` on `(−1, 1)`. The polynomial
interpolating `f` at the `q + 1` zeros of `T_{q+1}` satisfies
`|f x − L(x)| ≤ M / (2^q (q + 1)!)` for every `x ∈ [−1, 1]`.
Source: Süli–Mayers, Ch. 8 (Chebyshev nodes); Trefethen, *Approximation Theory and
Approximation Practice*, Ch. 11; Cheney, Ch. 3.
Atlas: `chebyshev-interpolation-error`; uses `interpolation-remainder`.
Deviation: the derivative bound is assumed only on the open interval `(−1, 1)` (weaker than
on `[−1, 1]`).
atlas: chebyshev-interpolation-error -/
theorem abs_sub_eval_interpolate_chebyshevZero_le {f : ℝ → ℝ} {q : ℕ} {M : ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hf' : ∀ k ≤ q, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo (-1) 1))
    (hM : ∀ ξ ∈ Ioo (-1 : ℝ) 1, |iteratedDeriv (q + 1) f ξ| ≤ M) :
    ∀ x ∈ Icc (-1 : ℝ) 1,
      |f x - (Lagrange.interpolate Finset.univ (chebyshevZero (q + 1))
        (f ∘ chebyshevZero (q + 1))).eval x| ≤ M / (2 ^ q * (q + 1).factorial) := by
  intro x hx
  obtain ⟨ξ, hξ, heq⟩ := exists_sub_eval_interpolate_eq (by norm_num)
    (chebyshevZero_injective _) (chebyshevZero_mem_Icc _) hx hf hf'
  have hω := abs_eval_nodal_chebyshevZero_le (q + 1) hx
  rw [Nat.add_sub_cancel] at hω
  rw [heq, abs_mul, abs_div, Nat.abs_cast]
  calc |iteratedDeriv (q + 1) f ξ| / (q + 1).factorial *
        |(Lagrange.nodal Finset.univ (chebyshevZero (q + 1))).eval x|
      ≤ M / (q + 1).factorial * (1 / 2 ^ q) := by
        have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ξ hξ)
        exact mul_le_mul (div_le_div_of_nonneg_right (hM ξ hξ) (by positivity)) hω
          (abs_nonneg _) (by positivity)
    _ = M / (2 ^ q * (q + 1).factorial) := by
        field_simp

end NLAlib

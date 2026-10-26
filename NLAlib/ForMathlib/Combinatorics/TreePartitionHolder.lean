import NLAlib.ForMathlib.Combinatorics.StationaryTree
import NLAlib.ForMathlib.Analysis.FiniteWeightedHolder

/-!
# Hölder estimates for stationary tree partition functions

The exact stationary tree density converts a weighted tree partition into a
product of degree factors and vertex potentials under a probability law with
known marginals. Generalized Hölder then gives a bound using only scalar
moments under the degree distribution. No independence of the vertex labels
is asserted or needed.
-/

noncomputable section

open scoped BigOperators

namespace NLAlib.LeafTree

variable {α : Type*} [Fintype α]

/-- A tree partition with extra nonnegative vertex potentials is controlled
by the degree-distribution moments of the degree and potential functions.
There are `n` degree-excess factors and `c` additional potential factors.
The moment exponent is exactly `n + c`, with no dimension enlargement. -/
theorem sum_edgeWeight_mul_prod_pow_le
    (w : α → α → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsymm : ∀ i j, w i j = w j i)
    (hD : 0 < ∑ i, ∑ j, w i j)
    {n : ℕ} (t : LeafTree n) (s : α → ℝ) (hs : ∀ i, 0 ≤ s i)
    (q : Fin (n + 2) → ℕ) (c : ℕ) (hq : ∑ v, q v = c)
    (hN : 0 < n + c) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hdmoment :
      (∑ i, ((∑ j, w i j) / (∑ i, ∑ j, w i j)) * (∑ j, w i j) ^ (n + c)) ≤
        A ^ (n + c))
    (hsmoment :
      (∑ i, ((∑ j, w i j) / (∑ i, ∑ j, w i j)) * s i ^ (n + c)) ≤
        B ^ (n + c)) :
    (∑ x : Fin (n + 2) → α, t.edgeWeight w x * ∏ v, s (x v) ^ q v) ≤
      (∑ i, ∑ j, w i j) * A ^ n * B ^ c := by
  classical
  obtain ⟨P, hP, _hPsum, hmarginal, hdensity⟩ :=
    t.exists_stationary_edgeWeight_factorization w hw hsymm hD
  let e : Sum (Fin (n + 2)) (Fin (n + 2)) → ℕ :=
    Sum.elim t.degreeExcess q
  let f : Sum (Fin (n + 2)) (Fin (n + 2)) → (Fin (n + 2) → α) → ℝ :=
    Sum.elim (fun v x => ∑ j, w (x v) j) (fun v x => s (x v))
  let C : Sum (Fin (n + 2)) (Fin (n + 2)) → ℝ :=
    Sum.elim (fun _ => A) (fun _ => B)
  have hf (i) (x : Fin (n + 2) → α) : 0 ≤ f i x := by
    cases i with
    | inl v => exact Finset.sum_nonneg fun j _ => hw _ j
    | inr v => exact hs _
  have he : ∑ i, e i = n + c := by
    simp only [e, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      t.sum_degreeExcess, hq]
  have hC (i) : 0 < C i := by
    cases i <;> assumption
  have hmoment (i) : (∑ x, P x * f i x ^ (n + c)) ≤ C i ^ (n + c) := by
    cases i with
    | inl v =>
      exact (hmarginal v (fun i => (∑ j, w i j) ^ (n + c))).trans_le hdmoment
    | inr v =>
      exact (hmarginal v (fun i => s i ^ (n + c))).trans_le hsmoment
  have hholder := Real.sum_mul_prod_pow_le_prod_pow P hP f hf e (n + c) hN he C hC hmoment
  have hprod (x : Fin (n + 2) → α) :
      (∏ i, f i x ^ e i) =
        t.excessWeight (fun i => ∑ j, w i j) x * ∏ v, s (x v) ^ q v := by
    simp only [f, e, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, excessWeight]
  have hcap : (∏ i, C i ^ e i) = A ^ n * B ^ c := by
    simp only [C, e, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_pow_eq_pow_sum, t.sum_degreeExcess, hq]
  rw [hcap] at hholder
  calc
    (∑ x : Fin (n + 2) → α, t.edgeWeight w x * ∏ v, s (x v) ^ q v) =
        (∑ i, ∑ j, w i j) * ∑ x, P x * ∏ i, f i x ^ e i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hdensity, hprod]
      ring
    _ ≤ (∑ i, ∑ j, w i j) * (A ^ n * B ^ c) :=
      mul_le_mul_of_nonneg_left hholder hD.le
    _ = _ := by ring

private theorem sum_mul_pow_le_of_power_sums
    (d s : α → ℝ) (hd : ∀ i, 0 ≤ d i) (hs : ∀ i, 0 ≤ s i)
    (N : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hda : (∑ i, d i ^ (N + 1)) ≤ a ^ (N + 1))
    (hsb : (∑ i, s i ^ (N + 1)) ≤ b ^ (N + 1)) :
    (∑ i, d i * s i ^ N) ≤ a * b ^ N := by
  classical
  have h := Real.sum_mul_prod_pow_le_prod_pow (fun _ : α => (1 : ℝ)) (fun _ => by norm_num)
    (Fin.cons d (Fin.cons s Fin.elim0)) (by intro i; fin_cases i <;> assumption)
    ![1, N] (N + 1) (Nat.succ_pos _) (by simp; omega)
    ![a, b] (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> simpa using (by assumption))
  simpa [Fin.prod_univ_succ] using h

/-- The degree and vertex-potential power sums control a tree partition with
constant one. The exponent is `p = n + c + 1`: a tree with `n + 2` vertices
contributes `a ^ (n + 1)` and the `c` additional factors contribute `b ^ c`.
This is the profile-sensitive tree inequality used after selecting a spanning
tree in the weighted graph estimate for Gaussian Schatten moments. -/
theorem sum_edgeWeight_mul_prod_pow_le_of_power_sums
    (w : α → α → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsymm : ∀ i j, w i j = w j i)
    (hD : 0 < ∑ i, ∑ j, w i j)
    {n : ℕ} (t : LeafTree n) (s : α → ℝ) (hs : ∀ i, 0 ≤ s i)
    (q : Fin (n + 2) → ℕ) (c : ℕ) (hq : ∑ v, q v = c)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hda : (∑ i, (∑ j, w i j) ^ (n + c + 1)) ≤ a ^ (n + c + 1))
    (hsb : (∑ i, s i ^ (n + c + 1)) ≤ b ^ (n + c + 1)) :
    (∑ x : Fin (n + 2) → α, t.edgeWeight w x * ∏ v, s (x v) ^ q v) ≤
      a ^ (n + 1) * b ^ c := by
  classical
  by_cases hN : 0 < n + c
  case neg =>
    have hn : n = 0 := by omega
    have hc : c = 0 := by omega
    subst n c
    have hq0 (v) : q v = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hq v (by simp)
    cases t
    simp only [hq0, pow_zero, Finset.prod_const_one, mul_one]
    change (∑ x : Fin 2 → α, edge.edgeWeight w x) ≤ a ^ 1
    rw [sum_edgeWeight_edge, pow_one]
    simpa only [zero_add, pow_one] using hda
  let N := n + c
  let D : ℝ := ∑ i, ∑ j, w i j
  have hDne : D ≠ 0 := ne_of_gt hD
  have hNne : N ≠ 0 := Nat.ne_of_gt hN
  have hd (i : α) : 0 ≤ ∑ j, w i j := Finset.sum_nonneg fun j _ => hw i j
  have hmix := sum_mul_pow_le_of_power_sums (fun i => ∑ j, w i j) s hd hs N a b ha hb hda hsb
  let A : ℝ := (a ^ (N + 1) / D) ^ ((N : ℝ)⁻¹)
  let B : ℝ := (a * b ^ N / D) ^ ((N : ℝ)⁻¹)
  have hAbase : 0 < a ^ (N + 1) / D := div_pos (pow_pos ha _) hD
  have hBbase : 0 < a * b ^ N / D := div_pos (mul_pos ha (pow_pos hb _)) hD
  have hA : 0 < A := Real.rpow_pos_of_pos hAbase _
  have hB : 0 < B := Real.rpow_pos_of_pos hBbase _
  have hApow : A ^ N = a ^ (N + 1) / D := Real.rpow_inv_natCast_pow hAbase.le hNne
  have hBpow : B ^ N = a * b ^ N / D := Real.rpow_inv_natCast_pow hBbase.le hNne
  have hdmoment :
      (∑ i, ((∑ j, w i j) / D) * (∑ j, w i j) ^ N) ≤ A ^ N := by
    rw [hApow]
    calc
      (∑ i, ((∑ j, w i j) / D) * (∑ j, w i j) ^ N) =
          (∑ i, (∑ j, w i j) ^ (N + 1)) / D := by
        simp only [div_mul_eq_mul_div, ← pow_succ', ← Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right hda hD.le
  have hsmoment : (∑ i, ((∑ j, w i j) / D) * s i ^ N) ≤ B ^ N := by
    rw [hBpow]
    calc
      (∑ i, ((∑ j, w i j) / D) * s i ^ N) = (∑ i, (∑ j, w i j) * s i ^ N) / D := by
        simp only [div_mul_eq_mul_div, ← Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right hmix hD.le
  have hbound := t.sum_edgeWeight_mul_prod_pow_le w hw hsymm hD s hs q c hq hN A B hA hB
    hdmoment hsmoment
  have hexponent : (a ^ (N + 1)) ^ n * a ^ c = (a ^ (n + 1)) ^ N := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    dsimp [N]
    ring
  have hpower : (D * A ^ n * B ^ c) ^ N = (a ^ (n + 1) * b ^ c) ^ N := by
    calc
      (D * A ^ n * B ^ c) ^ N = D ^ N * (A ^ N) ^ n * (B ^ N) ^ c := by
        simp only [mul_pow, pow_right_comm A n N, pow_right_comm B c N]
      _ = D ^ N * (a ^ (N + 1) / D) ^ n * (a * b ^ N / D) ^ c := by rw [hApow, hBpow]
      _ = (a ^ (N + 1)) ^ n * a ^ c * (b ^ N) ^ c := by
        rw [div_pow, div_pow, mul_pow, show D ^ N = D ^ n * D ^ c from pow_add D n c]
        field_simp
      _ = (a ^ (n + 1) * b ^ c) ^ N := by
        rw [hexponent, pow_right_comm b N c, mul_pow]
  have hnonneg :
      0 ≤ ∑ x : Fin (n + 2) → α, t.edgeWeight w x * ∏ v, s (x v) ^ q v :=
    Finset.sum_nonneg fun x _ => mul_nonneg (t.edgeWeight_nonneg w hw x)
      (Finset.prod_nonneg fun v _ => pow_nonneg (hs _) _)
  apply le_of_pow_le_pow_left₀ hNne (by positivity : 0 ≤ a ^ (n + 1) * b ^ c)
  exact (pow_le_pow_left₀ hnonneg hbound N).trans_eq hpower

end NLAlib.LeafTree

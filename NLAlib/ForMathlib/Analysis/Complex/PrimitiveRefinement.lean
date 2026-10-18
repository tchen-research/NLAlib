import NLAlib.ForMathlib.Analysis.Complex.PrimitiveTransport
import NLAlib.ForMathlib.Algebra.FiniteBlockSum

/-! # Refinement of uniform local primitive transports

A uniform subdivision may be refined by any positive integer factor without
changing the local primitive transport. The proof uses actual containment of
each fine cell in its coarse cell, primitive-chart independence, and finite
block telescoping. This is a continuous-path theorem, with no smoothness or
assumed contour evaluation formula.
-/

noncomputable section
open Set Finset
namespace Complex

private theorem uniformSubdivision_refinement_cell_subset
    {n m i j : ℕ} (hn : 0 < n) (hm : 0 < m) (hj : j < m) :
    Icc (((i * m + j : ℕ) : ℝ) / (n * m : ℕ))
      (((i * m + j + 1 : ℕ) : ℝ) / (n * m : ℕ)) ⊆
      Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnm' : 0 < ((n * m : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hn hm
  have hleft : (i : ℝ) / n ≤ ((i * m + j : ℕ) : ℝ) / (n * m : ℕ) := by
    rw [div_le_div_iff₀ hn' hnm']
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hn'.le]
  have hright : ((i * m + j + 1 : ℕ) : ℝ) / (n * m : ℕ) ≤ (i + 1 : ℝ) / n := by
    rw [div_le_div_iff₀ hnm' hn']
    push_cast
    have hj' : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hj
    nlinarith [mul_le_mul_of_nonneg_right hj' hn'.le]
  exact fun _ ht => ⟨hleft.trans ht.1, ht.2.trans hright⟩

private theorem mul_add_lt_mul {n m i j : ℕ} (hi : i < n) (hj : j < m) :
    i * m + j < n * m := by
  calc
    i * m + j < i * m + m := Nat.add_lt_add_left hj _
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hi)

/-- A positive-factor uniform refinement preserves the actual local primitive
transport. The coarse and fine charts may differ, with their respective
primitive and path-containment hypotheses proved independently. -/
theorem primitiveSubdivisionTransport_uniform_refinement
    {γ : ℝ → ℂ} (hγ : Continuous γ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {G H : ℕ → ℂ → ℂ} {U V : ℕ → Set ℂ} {g : ℂ → ℂ}
    (hU : ∀ i < n, IsOpen (U i)) (hV : ∀ k < n * m, IsOpen (V k))
    (hG : ∀ i < n, ∀ z ∈ U i, HasDerivAt (G i) (g z) z)
    (hH : ∀ k < n * m, ∀ z ∈ V k, HasDerivAt (H k) (g z) z)
    (hγU : ∀ i < n, ∀ t ∈ Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n), γ t ∈ U i)
    (hγV : ∀ k < n * m, ∀ t ∈ Icc ((k : ℝ) / (n * m : ℕ))
      ((k + 1 : ℝ) / (n * m : ℕ)), γ t ∈ V k) :
    primitiveSubdivisionTransport γ (fun i => (i : ℝ) / n) G n =
      primitiveSubdivisionTransport γ (fun k => (k : ℝ) / (n * m : ℕ)) H (n * m) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnm : 0 < ((n * m : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hn hm
  have hblock (i : ℕ) (hi : i < n) :
      (∑ j ∈ range m, (H (i * m + j) (γ (((i * m + j + 1 : ℕ) : ℝ) / (n * m : ℕ))) -
        H (i * m + j) (γ (((i * m + j : ℕ) : ℝ) / (n * m : ℕ))))) =
        G i (γ ((i + 1 : ℝ) / n)) - G i (γ ((i : ℝ) / n)) := by
    let p : ℕ → ℝ := fun j => ((i * m + j : ℕ) : ℝ) / (n * m : ℕ)
    have hp (j : ℕ) (_hj : j < m) : p j ≤ p (j + 1) := by
      dsimp [p]
      apply div_le_div_of_nonneg_right _ hnm.le
      exact_mod_cast Nat.add_le_add_left (Nat.le_succ j) (i * m)
    have hinner := primitiveSubdivisionTransport_eq_sub_of_hasDerivAt hγ hp
      (hU i hi) (fun j hj => hV (i * m + j) (mul_add_lt_mul hi hj))
      (hG i hi) (fun j hj => hH (i * m + j) (mul_add_lt_mul hi hj))
      (fun j hj t ht => hγU i hi t
        (uniformSubdivision_refinement_cell_subset hn hm hj
          (by simpa only [p, Nat.add_assoc] using ht)))
      (fun j hj t ht => hγV (i * m + j) (mul_add_lt_mul hi hj) t
        (by simpa only [p, Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using ht))
    have hp0 : p 0 = (i : ℝ) / n := by
      dsimp [p]
      push_cast
      field_simp
    have hpm : p m = (i + 1 : ℝ) / n := by
      dsimp [p]
      push_cast
      field_simp
    simpa only [primitiveSubdivisionTransport, p, hp0, hpm, Nat.add_assoc] using hinner
  unfold primitiveSubdivisionTransport
  rw [sum_range_mul_blocks]
  apply sum_congr rfl
  intro i hi
  simpa only [Nat.cast_add, Nat.cast_one] using (hblock i (mem_range.mp hi)).symm

/-- Two independently chosen uniform subdivisions give the same transport
for a continuous path. A common-multiple refinement is constructed from the
first chart family, and genuine refinement invariance compares both sums. -/
theorem primitiveSubdivisionTransport_uniform_eq
    {γ : ℝ → ℂ} (hγ : Continuous γ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {G H : ℕ → ℂ → ℂ} {U V : ℕ → Set ℂ} {g : ℂ → ℂ}
    (hU : ∀ i < n, IsOpen (U i)) (hV : ∀ i < m, IsOpen (V i))
    (hG : ∀ i < n, ∀ z ∈ U i, HasDerivAt (G i) (g z) z)
    (hH : ∀ i < m, ∀ z ∈ V i, HasDerivAt (H i) (g z) z)
    (hγU : ∀ i < n, ∀ t ∈ Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n), γ t ∈ U i)
    (hγV : ∀ i < m, ∀ t ∈ Icc ((i : ℝ) / m) ((i + 1 : ℝ) / m), γ t ∈ V i) :
    primitiveSubdivisionTransport γ (fun i => (i : ℝ) / n) G n =
      primitiveSubdivisionTransport γ (fun i => (i : ℝ) / m) H m := by
  let P : ℕ → ℂ → ℂ := fun k => G (k / m)
  let W : ℕ → Set ℂ := fun k => U (k / m)
  have hindex (k : ℕ) (hk : k < n * m) : k / m < n :=
    (Nat.div_lt_iff_lt_mul hm).mpr hk
  have hW : ∀ k < n * m, IsOpen (W k) := fun k hk => hU _ (hindex k hk)
  have hP : ∀ k < n * m, ∀ z ∈ W k, HasDerivAt (P k) (g z) z :=
    fun k hk => hG _ (hindex k hk)
  have hγW : ∀ k < n * m, ∀ t ∈ Icc ((k : ℝ) / (n * m : ℕ))
      ((k + 1 : ℝ) / (n * m : ℕ)), γ t ∈ W k := by
    intro k hk t ht
    apply hγU _ (hindex k hk) t
    have hidx : k / m * m + k % m = k := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod k m
    apply uniformSubdivision_refinement_cell_subset hn hm (Nat.mod_lt k hm)
    simpa only [hidx, Nat.cast_add, Nat.cast_one] using ht
  have h₁ := primitiveSubdivisionTransport_uniform_refinement hγ hn hm hU hW hG hP hγU hγW
  have h₂ := primitiveSubdivisionTransport_uniform_refinement hγ hm hn hV
    (by simpa only [Nat.mul_comm] using hW)
    hH (by simpa only [Nat.mul_comm] using hP)
    hγV (by simpa only [Nat.mul_comm] using hγW)
  rw [Nat.mul_comm m n] at h₂
  exact h₁.trans h₂.symm

end Complex

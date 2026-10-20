import NLAlib.Matrix.Functions.ResolventSeries
import NLAlib.ForMathlib.Analysis.FiniteGeometricSeries
import NLAlib.ForMathlib.LinearAlgebra.Matrix.TraceWordProfiles
import NLAlib.Matrix.Functions.AggregateResolventTraceWords
import NLAlib.Matrix.Functions.ResolventMomentDerivatives

/-!
# Actual aggregate Neumann profile trace bounds

A profile is the literal ordered product from the native resolvent series.
Computed structural arcs and coefficient labels are shared across every
summand; all original and additional Hermitian insertions retain their exact
slotwise aggregate square bounds. No independence from the common matrix is
assumed. The actual shifted word is recovered from a jointly absolutely
convergent ordered Neumann expansion; the finite geometric profile sum
bounds its correction factor by three.

Source: the common-resolvent multilinear mechanism supporting
Brailovskaya--van Handel, arXiv:2201.05142v3, Proposition 5.1 and Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

private abbrev HistoryBlock (κ : Type*) := Bool × Option κ
private def historyMarkedCount {κ : Type*} {N : ℕ} (w : Fin N → HistoryBlock κ) : ℕ :=
  ∑ j, if (w j).2.isSome then 1 else 0

private def taggedWordInsert {κ : Type*} {N : ℕ} (w : Fin N → HistoryBlock κ)
    (i : Fin N) (tag : κ) : Fin (N + 1) → HistoryBlock κ :=
  Fin.insertNth i.castSucc ((w i).1, some tag) w

private theorem historyMarkedCount_taggedWordInsert {κ : Type*} {N : ℕ}
    (w : Fin N → HistoryBlock κ) (i : Fin N) (tag : κ) :
    historyMarkedCount (taggedWordInsert w i tag) = historyMarkedCount w + 1 := by
  unfold historyMarkedCount
  rw [Fin.sum_univ_succAbove _ i.castSucc]
  simp only [taggedWordInsert, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Option.isSome_some, ↓reduceIte]
  exact Nat.add_comm _ _

private def initialTaggedWord (κ : Type*) (p : ℕ) : Fin (p + p) → HistoryBlock κ :=
  Fin.append (fun _ : Fin p => (false, none)) (fun _ : Fin p => (true, none))

private theorem historyMarkedCount_initialTaggedWord (κ : Type*) (p : ℕ) :
    historyMarkedCount (initialTaggedWord κ p) = 0 := by
  have hnone (j : Fin (p + p)) : (initialTaggedWord κ p j).2 = none := by
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
    · simp only [initialTaggedWord, Fin.append_left]
    · simp only [initialTaggedWord, Fin.append_right]
  simp [historyMarkedCount, hnone]

private def thirdTaggedWord (p : ℕ) (i : Fin (p + p))
    (j : Fin (p + p + 1)) (k : Fin (p + p + 1 + 1)) :
    Fin (p + p + 1 + 1 + 1) → HistoryBlock (Fin 3) :=
  taggedWordInsert (taggedWordInsert
    (taggedWordInsert (initialTaggedWord (Fin 3) p) i 2) j 1) k 0

private theorem historyMarkedCount_thirdTaggedWord (p : ℕ) (i : Fin (p + p))
    (j : Fin (p + p + 1)) (k : Fin (p + p + 1 + 1)) :
    historyMarkedCount (thirdTaggedWord p i j k) = 3 := by
  simp only [thirdTaggedWord, historyMarkedCount_taggedWordInsert, historyMarkedCount_initialTaggedWord]

private def evaluateTaggedWord {n κ : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    (z : ℂ) (C : κ → Matrix n n ℂ) (w : Fin N → HistoryBlock κ) :
    Fin N → ℂ × Matrix n n ℂ :=
  fun j => ((if (w j).1 then star z else z), (w j).2.elim 1 C)

/-- Structural insertion is exactly the actual native derivative insertion,
for every coefficient interpretation simultaneously. -/
private theorem evaluateTaggedWord_insert {n κ : Type*} [Fintype n] [DecidableEq n] {N : ℕ}
    (z : ℂ) (C : κ → Matrix n n ℂ) (w : Fin N → HistoryBlock κ)
    (i : Fin N) (tag : κ) :
    evaluateTaggedWord z C (taggedWordInsert w i tag) =
      resolventWordInsert (evaluateTaggedWord z C w) i (C tag) := by
  funext j
  refine Fin.succAboveCases i.castSucc ?_ (fun l => ?_) j
  · simp [evaluateTaggedWord, taggedWordInsert, resolventWordInsert]
  · simp [evaluateTaggedWord, taggedWordInsert, resolventWordInsert]

private theorem evaluateTaggedWord_initial {n κ : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (C : κ → Matrix n n ℂ) (p : ℕ) :
    evaluateTaggedWord z C (initialTaggedWord κ p) = mixedResolventWord z p := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · simp only [evaluateTaggedWord, initialTaggedWord, mixedResolventWord, Fin.append_left]
    rfl
  · simp only [evaluateTaggedWord, initialTaggedWord, mixedResolventWord, Fin.append_right]
    rfl

private theorem evaluateTaggedWord_third {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (C : Fin 3 → Matrix n n ℂ) (p : ℕ) (i : Fin (p + p))
    (j : Fin (p + p + 1)) (k : Fin (p + p + 1 + 1)) :
    evaluateTaggedWord z C (thirdTaggedWord p i j k) =
      resolventWordInsert (resolventWordInsert
        (resolventWordInsert (mixedResolventWord z p) i (C 2)) j (C 1)) k (C 0) := by
  rw [thirdTaggedWord, evaluateTaggedWord_insert, evaluateTaggedWord_insert,
    evaluateTaggedWord_insert, evaluateTaggedWord_initial]

open scoped Matrix.Norms.L2Operator in
/-- A literal common-resolvent Neumann profile with three original marked
Hermitian directions and ell additional Hermitian insertions obeys the exact
aggregate bound with k=3+ell and L=2p+3+ell. The same computed arcs and labels
serve all family indices; no numerical coefficient test or supplied word
norm estimate is used. Empty dimensions and radius zero are included. -/
theorem norm_sum_normalizedTrace_resolvent_neumann_profile_le
    {ι n κ : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {N : ℕ} (w : Fin N → Bool × Option κ)
    (hMarked : ((List.ofFn w).filter (fun b => b.2.isSome)).length = 3)
    (m : Fin N → ℕ) (C : ι → κ → Matrix n n ℂ) (H : ι → Fin N → Matrix n n ℂ)
    (hHermC : ∀ i t, (C i t).IsHermitian) (hHermH : ∀ i j, (H i j).IsHermitian)
    {r M : ℝ} (hr : 0 ≤ r)
    (hC : ∀ i t, specNorm (C i t) ≤ r) (hH : ∀ i j, specNorm (H i j) ≤ r)
    (hMassC : ∀ t, specNorm (∑ i, C i t ^ 2) ≤ M)
    (hMassH : ∀ j, specNorm (∑ i, H i j ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (hN : N = 2 * p + 3) :
    ‖∑ i, normalizedTrace ((List.ofFn (fun j =>
      (resolvent A (if (w j).1 then star z else z) * H i j) ^ m j *
        resolvent A (if (w j).1 then star z else z) * (w j).2.elim 1 (C i))).prod)‖ ≤
      r ^ (1 + ∑ j, m j) * M * (|z.im|⁻¹) ^ (4 + ∑ j, m j) *
        resolventEvenMoment A z p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  have hMarkedPos : 0 < ((List.ofFn w).filter (fun b => b.2.isSome)).length := by omega
  let S := List.cyclicProfileArcs w m
  obtain ⟨hLen, hDegree, hArc⟩ := List.cyclicProfileArcs_spec w m hMarkedPos
  have hLen' : S.length = 3 + ∑ j, m j := by simpa only [hMarked] using hLen
  let a : Fin S.length → ℕ := fun j => (S.get j).2.1
  let b : Fin S.length → ℕ := fun j => (S.get j).2.2
  let Z : ι → Fin S.length → Matrix n n ℂ :=
    fun i j => Sum.elim (C i) (H i) (S.get j).1
  have hHerm (i : ι) (j : Fin S.length) : (Z i j).IsHermitian := by
    dsimp only [Z]
    cases (S.get j).1 with
    | inl t => exact hHermC i t
    | inr t => exact hHermH i t
  have hBound (i : ι) (j : Fin S.length) : specNorm (Z i j) ≤ r := by
    dsimp only [Z]
    cases (S.get j).1 with
    | inl t => exact hC i t
    | inr t => exact hH i t
  have hMass (j : Fin S.length) : specNorm (∑ i, Z i j ^ 2) ≤ M := by
    dsimp only [Z]
    cases (S.get j).1 with
    | inl t => exact hMassC t
    | inr t => exact hMassH t
  have hPos (j : Fin S.length) : 0 < a j + b j := hArc _ (List.get_mem S j)
  have hSum : ∑ j, (a j + b j) = N + ∑ j, m j := by
    rw [← Fin.sum_ofFn]
    have ht := congrArg (List.map (fun t : (κ ⊕ Fin N) × (ℕ × ℕ) => t.2.1 + t.2.2))
      (List.ofFn_get S)
    rw [List.map_ofFn] at ht
    have ht' : List.ofFn (fun j => a j + b j) = S.map (fun t => t.2.1 + t.2.2) := ht
    rw [ht']
    exact hDegree
  have hWord (i : ι) :
      normalizedTrace ((List.ofFn (fun j =>
        (resolvent A (if (w j).1 then star z else z) * H i j) ^ m j *
          resolvent A (if (w j).1 then star z else z) * (w j).2.elim 1 (C i))).prod) =
        normalizedTrace ((List.ofFn (fun j => Z i j *
          (resolvent A z ^ a j * resolvent A (star z) ^ b j))).prod) := by
    have ht := Matrix.trace_profile_word_eq_cyclicProfileArcs
      (commute_resolvent A z (star z)) w m hMarkedPos (C i) (H i)
    have hMode (mode : Bool) : (if mode then resolvent A (star z) else resolvent A z) =
        resolvent A (if mode then star z else z) := by cases mode <;> rfl
    simp_rw [hMode] at ht
    have hList := congrArg (List.map (fun t : (κ ⊕ Fin N) × (ℕ × ℕ) =>
      Sum.elim (C i) (H i) t.1 * (resolvent A z ^ t.2.1 * resolvent A (star z) ^ t.2.2)))
      (List.ofFn_get S)
    rw [List.map_ofFn] at hList
    change List.ofFn (fun j => Z i j *
      (resolvent A z ^ a j * resolvent A (star z) ^ b j)) = _ at hList
    rw [hList]
    unfold normalizedTrace
    exact congrArg (fun t : ℂ => (Fintype.card n : ℂ)⁻¹ * t) ht
  have hNorm := norm_sum_normalizedTrace_resolvent_mixed_word_le_resolventEvenMoment
    (by omega : 2 ≤ S.length) Z hHerm hr hBound hMass hA hz a b hp hSum (by omega) hPos
  have hk : S.length - 2 = 1 + ∑ j, m j := by omega
  have hL : N + ∑ j, m j - (2 * p - 1) = 4 + ∑ j, m j := by omega
  have hSumWord := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hWord i)
  rw [hSumWord]
  simpa only [hk, hL] using hNorm

private theorem historyMarkedCount_eq_length_filter {κ : Type*} {N : ℕ}
    (w : Fin N → HistoryBlock κ) :
    historyMarkedCount w = ((List.ofFn w).filter (fun b => b.2.isSome)).length := by
  have hlist (t : List (HistoryBlock κ)) :
      (t.filter (fun b => b.2.isSome)).length =
        (t.map (fun b => if b.2.isSome then 1 else 0)).sum := by
    induction t with
    | nil => rfl
    | cons b t ih =>
      obtain ⟨mode, c⟩ := b
      cases c with
      | none => simp [ih]
      | some tag =>
        simp [ih]
        omega
  rw [hlist, List.map_ofFn, Fin.sum_ofFn]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The literal three nested native derivative insertions have the same sharp
profile bound. Their original coefficients are retained by insertion history,
even if any interpreted direction equals zero or identity. The perturbation
may depend on the family index and on the common matrix without independence. -/
theorem norm_sum_normalizedTrace_third_resolventWord_neumann_profile_le
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {p : ℕ} (hp : 0 < p) (i₀ : Fin (p + p))
    (i₁ : Fin (p + p + 1)) (i₂ : Fin (p + p + 1 + 1))
    (m : Fin (p + p + 1 + 1 + 1) → ℕ)
    (C : ι → Fin 3 → Matrix n n ℂ) (H : ι → Matrix n n ℂ)
    (hHermC : ∀ i t, (C i t).IsHermitian) (hHermH : ∀ i, (H i).IsHermitian)
    {r M : ℝ} (hr : 0 ≤ r)
    (hC : ∀ i t, specNorm (C i t) ≤ r) (hH : ∀ i, specNorm (H i) ≤ r)
    (hMassC : ∀ t, specNorm (∑ i, C i t ^ 2) ≤ M)
    (hMassH : specNorm (∑ i, H i ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖∑ i, normalizedTrace (let w := resolventWordInsert (resolventWordInsert
        (resolventWordInsert (mixedResolventWord z p) i₀ (C i 2)) i₁ (C i 1)) i₂ (C i 0)
      (List.ofFn (fun j => (resolvent A (w j).1 * H i) ^ m j *
        resolvent A (w j).1 * (w j).2)).prod)‖ ≤
      r ^ (1 + ∑ j, m j) * M * (|z.im|⁻¹) ^ (4 + ∑ j, m j) *
        resolventEvenMoment A z p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  have hMarked : ((List.ofFn (thirdTaggedWord p i₀ i₁ i₂)).filter
      (fun b => b.2.isSome)).length = 3 := by
    rw [← historyMarkedCount_eq_length_filter, historyMarkedCount_thirdTaggedWord]
  have ht := norm_sum_normalizedTrace_resolvent_neumann_profile_le
    (thirdTaggedWord p i₀ i₁ i₂) hMarked m C (fun i _ => H i)
    hHermC (fun i _ => hHermH i) hr hC (fun i _ => hH i)
    hMassC (fun _ => hMassH) hA hz hp (by omega)
  change ‖∑ i, normalizedTrace ((List.ofFn (fun j =>
    (resolvent A ((evaluateTaggedWord z (C i) (thirdTaggedWord p i₀ i₁ i₂)) j).1 * H i) ^ m j *
      resolvent A ((evaluateTaggedWord z (C i) (thirdTaggedWord p i₀ i₁ i₂)) j).1 *
        ((evaluateTaggedWord z (C i) (thirdTaggedWord p i₀ i₁ i₂)) j).2)).prod)‖ ≤ _ at ht
  simpa only [evaluateTaggedWord_third] using ht

private theorem abs_im_insertNth {β : Type*} {N : ℕ} (w : Fin N → ℂ × β)
    {η : ℝ} (hw : ∀ j, |(w j).1.im| = η) (i : Fin N) (C : β) :
    ∀ j, |((Fin.insertNth (α := fun _ => ℂ × β) i.castSucc ((w i).1, C) w) j).1.im| = η := by
  intro j
  refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
  · simpa only [Fin.insertNth_apply_same] using hw i
  · simpa only [Fin.insertNth_apply_succAbove] using hw k

private theorem abs_im_mixedResolventWord {n : Type*} [DecidableEq n]
    (z : ℂ) (p : ℕ) :
    ∀ j, |((mixedResolventWord (n := n) z p) j).1.im| = |z.im| := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [mixedResolventWord, Fin.append_left]
  · simp only [mixedResolventWord, Fin.append_right, Complex.star_def, Complex.conj_im, abs_neg]

open scoped Matrix.Norms.L2Operator in
/-- The genuine shifted three-insertion trace word obeys the aggregate
common-resolvent bound after summing its actual Neumann series. The height
condition is 8*p*r≤|Im z|; M is the realized aggregate square-mass bound and
its nonnegativity is derived from an actual direction slot. Empty dimensions,
empty summand families, radius zero and arbitrary dependence on A are included. -/
theorem norm_sum_normalizedTrace_third_resolventWord_add_le
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {p : ℕ} (hp : 0 < p) (i₀ : Fin (p + p))
    (i₁ : Fin (p + p + 1)) (i₂ : Fin (p + p + 1 + 1))
    (C : ι → Fin 3 → Matrix n n ℂ) (H : ι → Matrix n n ℂ)
    (hHermC : ∀ i t, (C i t).IsHermitian) (hHermH : ∀ i, (H i).IsHermitian)
    {r M : ℝ} (hr : 0 ≤ r)
    (hC : ∀ i t, specNorm (C i t) ≤ r) (hH : ∀ i, specNorm (H i) ≤ r)
    (hMassC : ∀ t, specNorm (∑ i, C i t ^ 2) ≤ M)
    (hMassH : specNorm (∑ i, H i ^ 2) ≤ M)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (hsmall : 8 * (p : ℝ) * r ≤ |z.im|) :
    ‖∑ i, normalizedTrace (let w := resolventWordInsert (resolventWordInsert
        (resolventWordInsert (mixedResolventWord z p) i₀ (C i 2)) i₁ (C i 1)) i₂ (C i 0)
      (List.ofFn (fun j => resolvent (A + H i) (w j).1 * (w j).2)).prod)‖ ≤
      3 * r * M * (|z.im|⁻¹) ^ 4 *
        resolventEvenMoment A z p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  let N := p + p + 1 + 1 + 1
  let W (i : ι) : Fin N → ℂ × Matrix n n ℂ :=
    resolventWordInsert (resolventWordInsert
      (resolventWordInsert (mixedResolventWord z p) i₀ (C i 2)) i₁ (C i 1)) i₂ (C i 0)
  let η : ℝ := |z.im|
  let ρ : ℝ := r / η
  let E : ℝ := resolventEvenMoment A z p ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ))
  let B : ℝ := r * M * (η⁻¹) ^ 4 * E
  have hη : 0 < η := abs_pos.mpr hz
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpr : r ≤ (p : ℝ) * r := by nlinarith
  have hrη : r < η := by dsimp only [η]; nlinarith
  have hρ0 : 0 ≤ ρ := div_nonneg hr hη.le
  have hρ1 : ρ < 1 := (div_lt_one hη).mpr hrη
  have hNreal : (N : ℝ) = 2 * (p : ℝ) + 3 := by dsimp only [N]; push_cast; ring
  have hNle : (N : ℝ) ≤ 5 * (p : ℝ) := by rw [hNreal]; nlinarith
  have htotal : (N : ℝ) * ρ ≤ 2 / 3 := by
    dsimp only [ρ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hη).mpr
    have hNr := mul_le_mul_of_nonneg_right hNle hr
    change 8 * (p : ℝ) * r ≤ η at hsmall
    nlinarith
  have hM : 0 ≤ M := (specNorm_nonneg (∑ i, C i 0 ^ 2)).trans (hMassC 0)
  have hE : 0 ≤ E := Real.rpow_nonneg (resolventEvenMoment_nonneg A z hp) _
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (mul_nonneg hr hM) (pow_nonneg (inv_nonneg.mpr hη.le) _)) hE
  have hheight (i : ι) : ∀ j, |((W i) j).1.im| = η := by
    dsimp only [W, resolventWordInsert]
    apply abs_im_insertNth
    apply abs_im_insertNth
    apply abs_im_insertNth
    exact abs_im_mixedResolventWord z p
  have hshift (i : ι) (j : Fin N) : ((W i) j).1.im ≠ 0 :=
    abs_pos.mp (by rw [hheight]; exact hη)
  let T : Matrix n n ℂ →L[ℂ] ℂ :=
    (normalizedTraceLinearMap : Matrix n n ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hSeries (i : ι) :
      HasSum (fun m : Fin N → ℕ => normalizedTrace ((List.ofFn (fun j =>
        (resolvent A ((W i) j).1 * H i) ^ m j * resolvent A ((W i) j).1 * ((W i) j).2)).prod))
        (normalizedTrace ((List.ofFn (fun j => resolvent (A + H i) ((W i) j).1 * ((W i) j).2)).prod)) := by
    have hHsmall (j : Fin N) : specNorm (H i) < |((W i) j).1.im| := by
      rw [hheight]
      exact (hH i).trans_lt hrη
    have hs := (hA.summable_norm_and_hasSum_resolventWord_add (W i) (hshift i) hHsmall).2
    have ht := T.hasSum hs
    simpa only [T, LinearMap.coe_toContinuousLinearMap', normalizedTraceLinearMap_apply] using ht
  have hAll :
      HasSum (fun m : Fin N → ℕ => ∑ i, normalizedTrace ((List.ofFn (fun j =>
        (resolvent A ((W i) j).1 * H i) ^ m j * resolvent A ((W i) j).1 * ((W i) j).2)).prod))
        (∑ i, normalizedTrace ((List.ofFn (fun j => resolvent (A + H i) ((W i) j).1 * ((W i) j).2)).prod)) :=
    hasSum_sum (fun i _ => hSeries i)
  have hProfile (m : Fin N → ℕ) :
      ‖∑ i, normalizedTrace ((List.ofFn (fun j =>
        (resolvent A ((W i) j).1 * H i) ^ m j * resolvent A ((W i) j).1 * ((W i) j).2)).prod)‖ ≤
        B * ρ ^ (∑ j, m j) := by
    have ht := norm_sum_normalizedTrace_third_resolventWord_neumann_profile_le
      hp i₀ i₁ i₂ m C H hHermC hHermH hr hC hH hMassC hMassH hA hz
    calc
      _ ≤ r ^ (1 + ∑ j, m j) * M * (|z.im|⁻¹) ^ (4 + ∑ j, m j) * E := ht
      _ = B * ρ ^ (∑ j, m j) := by
        dsimp only [B, E, ρ, η]
        simp only [pow_add, pow_one, div_eq_mul_inv, inv_pow]
        ring
  have hg := (Real.hasSum_pow_sum_fin hρ0 hρ1 N).mul_left B
  have hBound := hAll.norm_le_of_bounded hg hProfile
  have hCorrection := Real.inv_one_sub_pow_le_three hρ0 N htotal
  change ‖∑ i, normalizedTrace ((List.ofFn (fun j =>
    resolvent (A + H i) ((W i) j).1 * ((W i) j).2)).prod)‖ ≤ _
  calc
    _ ≤ B * ((1 - ρ)⁻¹ ^ N) := hBound
    _ ≤ B * 3 := mul_le_mul_of_nonneg_left hCorrection hB
    _ = _ := by dsimp only [B, E, η]; ring

end NLAlib

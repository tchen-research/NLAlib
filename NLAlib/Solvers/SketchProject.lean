import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.Norms

/-!
# Sketch-and-project for consistent linear systems

Gower–Richtárik's sketch-and-project method with the Euclidean metric (`B = I`): given a sketch
`S : Matrix m s ℝ`, one step projects the iterate onto the sketched solution set
`{y | Sᵀ A y = Sᵀ b}`,
`step A b S x = x − (SᵀA)⁺ Sᵀ (A x − b)`.
With sketches `S j` drawn with probabilities `p j` from a finite family, the expected squared
error (`NLAlib.SketchProject.expErr`, defined by first-step recursion as for randomized
Kaczmarz) contracts by `1 − λ`, where `λ ‖v‖² ≤ vᵀ W v` and `W = ∑ⱼ pⱼ (SⱼᵀA)⁺(SⱼᵀA)` is the
expected projector (`NLAlib.SketchProject.expErr_le`).

Randomized Kaczmarz is the case `S j = e_j`, `p j = ‖A_j‖²/‖A‖_F²`, with `W = AᵀA/‖A‖_F²`
(not formalised here; see `NLAlib.Kaczmarz.expErr_le`).

Source: Gower–Richtárik (2015) [`gr15`], Thm 4.6 (case `B = I`, Euclidean norm);
Strohmer–Vershynin (2009) [`sv09`] for the Kaczmarz special case.
Atlas: `sketch-and-project`; uses `pseudoinverse`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

namespace SketchProject

variable {m n s J : Type*} [Fintype m] [Fintype n] [Fintype s] [Fintype J]

/-- One sketch-and-project step with sketch `S`: the Euclidean projection of `x` onto
`{y | Sᵀ A y = Sᵀ b}`, written `x − (SᵀA)⁺ Sᵀ (A x − b)`. Source: Gower–Richtárik (2015)
[`gr15`], eq. (2.2)–(2.3) with `B = I`. Atlas: `sketch-and-project`.
atlas: sketch-and-project -/
def step (A : Matrix m n ℝ) (b : m → ℝ) (S : Matrix m s ℝ) (x : n → ℝ) : n → ℝ :=
  x - moorePenroseInverse (Sᵀ * A) *ᵥ (Sᵀ *ᵥ (A *ᵥ x - b))

/-- Expected squared error after `k` sketch-and-project steps from `x`, sketches `S j` drawn
i.i.d. with probabilities `p j`, by first-step recursion:
`expErr 0 x = ‖x − xs‖²`, `expErr (k+1) x = ∑ⱼ pⱼ expErr k (step A b (S j) x)`.
Atlas: `sketch-and-project`.
atlas: sketch-and-project -/
def expErr (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ) (S : J → Matrix m s ℝ) (xs : n → ℝ) :
    (n → ℝ) → ℕ → ℝ
  | x, 0 => (x - xs) ⬝ᵥ (x - xs)
  | x, k + 1 => ∑ j, p j * expErr A b p S xs (step A b (S j) x) k

/-- The expected projector `W = ∑ⱼ pⱼ (SⱼᵀA)⁺(SⱼᵀA)`. Source: Gower–Richtárik (2015) [`gr15`],
eq. (4.1) (`E[Z]` with `B = I`). Atlas: `sketch-and-project`.
atlas: sketch-and-project -/
def expectedProjector (A : Matrix m n ℝ) (p : J → ℝ) (S : J → Matrix m s ℝ) : Matrix n n ℝ :=
  ∑ j, p j • (moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A))

/-- Error recursion: if `A xs = b` then `step A b S x − xs = (I − Z)(x − xs)` with the
projector `Z = (SᵀA)⁺(SᵀA)`. Source: Gower–Richtárik (2015) [`gr15`], eq. (4.3).
Atlas: `sketch-and-project`. -/
theorem step_sub_solution (A : Matrix m n ℝ) (b : m → ℝ) (S : Matrix m s ℝ) {xs : n → ℝ}
    (hxs : A *ᵥ xs = b) (x : n → ℝ) :
    step A b S x - xs =
      (x - xs) - (moorePenroseInverse (Sᵀ * A) * (Sᵀ * A)) *ᵥ (x - xs) := by
  have h : Sᵀ *ᵥ (A *ᵥ x - b) = (Sᵀ * A) *ᵥ (x - xs) := by
    rw [← hxs, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rw [step, h, Matrix.mulVec_mulVec]
  abel

/-- The Moore–Penrose row projector `Z = M⁺M` satisfies `(d − Zd)ᵀ(d − Zd) = dᵀd − dᵀZd`.
Atlas: `sketch-and-project` (helper). -/
theorem sub_mulVec_dotProduct_sub_mulVec {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p q ℝ) (d : q → ℝ) :
    (d - (moorePenroseInverse M * M) *ᵥ d) ⬝ᵥ (d - (moorePenroseInverse M * M) *ᵥ d) =
      d ⬝ᵥ d - d ⬝ᵥ ((moorePenroseInverse M * M) *ᵥ d) := by
  set Z := moorePenroseInverse M * M
  have hsym : Zᵀ = Z := moorePenroseInverse_mul_isSymm M
  have hidem : Z * Z = Z := (moorePenroseInverse_mul_isIdempotentElem M).eq
  have hZZ : (Z *ᵥ d) ⬝ᵥ (Z *ᵥ d) = d ⬝ᵥ (Z *ᵥ d) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, Matrix.mulVec_mulVec,
      hidem, dotProduct_comm]
  have hdZ : (Z *ᵥ d) ⬝ᵥ d = d ⬝ᵥ (Z *ᵥ d) := dotProduct_comm _ _
  simp only [sub_dotProduct, dotProduct_sub, hZZ, hdZ]
  ring

/-- The projector is a contraction in the quadratic-form sense: `dᵀ (M⁺M) d ≤ dᵀd`.
Atlas: `sketch-and-project` (helper). -/
theorem dotProduct_mulVec_le_dotProduct_self {p q : Type*} [Fintype p] [Fintype q]
    (M : Matrix p q ℝ) (d : q → ℝ) :
    d ⬝ᵥ ((moorePenroseInverse M * M) *ᵥ d) ≤ d ⬝ᵥ d := by
  have h := sub_mulVec_dotProduct_sub_mulVec M d
  have h0 := dotProduct_self_nonneg (d - (moorePenroseInverse M * M) *ᵥ d)
  linarith

/-- One-step expected error identity: for `A xs = b` and `∑ pⱼ = 1`,
`∑ⱼ pⱼ ‖step A b (S j) x − xs‖² = ‖x − xs‖² − (x − xs)ᵀ W (x − xs)`.
Source: Gower–Richtárik (2015) [`gr15`], proof of Thm 4.6. Atlas: `sketch-and-project`. -/
theorem expected_sqErr_step_eq (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ)
    (hp1 : ∑ j, p j = 1) (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b)
    (x : n → ℝ) :
    ∑ j, p j * ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs)) =
      (x - xs) ⬝ᵥ (x - xs) - (x - xs) ⬝ᵥ (expectedProjector A p S *ᵥ (x - xs)) := by
  simp_rw [step_sub_solution A b _ hxs x, sub_mulVec_dotProduct_sub_mulVec, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, expectedProjector,
    Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- A convex combination of sketch row-space projectors is a contraction in
the quadratic-form sense: `vᵀ W v ≤ ‖v‖²`. Gower–Richtárik 2015, equation (4.1);
atlas `sketch-and-project` (expected-projector helper). -/
theorem dotProduct_expectedProjector_mulVec_le (A : Matrix m n ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) (v : n → ℝ) :
    v ⬝ᵥ (expectedProjector A p S *ᵥ v) ≤ v ⬝ᵥ v := by
  simp only [expectedProjector, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  calc ∑ j, p j * (v ⬝ᵥ ((moorePenroseInverse ((S j)ᵀ * A) * ((S j)ᵀ * A)) *ᵥ v))
      ≤ ∑ j, p j * (v ⬝ᵥ v) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (dotProduct_mulVec_le_dotProduct_self _ v) (hp j)
    _ = v ⬝ᵥ v := by rw [← Finset.sum_mul, hp1, one_mul]

/-- **Sketch-and-project converges linearly in expectation.** Let `A xs = b`, `pⱼ ≥ 0`,
`∑ pⱼ = 1`, and `λ ‖v‖² ≤ vᵀ W v` for all `v`, with `W = ∑ⱼ pⱼ (SⱼᵀA)⁺(SⱼᵀA)`. Then after `k`
steps with i.i.d. sketches, `E‖x_k − xs‖² ≤ (1 − λ)^k ‖x₀ − xs‖²`.
Source: Gower–Richtárik (2015) [`gr15`], Thm 4.6 (`B = I`; the sharp `λ` is
`λ_min⁺(W)`). Atlas: `sketch-and-project`; uses `pseudoinverse`. Deviation: finite sketch
distribution; expectation modelled by first-step recursion.
atlas: sketch-and-project -/
theorem expErr_le (A : Matrix m n ℝ) (b : m → ℝ) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v : n → ℝ, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (expectedProjector A p S *ᵥ v)) (x : n → ℝ)
    (k : ℕ) :
    expErr A b p S xs x k ≤ (1 - lam) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  classical
  have hW := dotProduct_expectedProjector_mulVec_le A p hp hp1 S
  have hstep : ∀ x : n → ℝ, ∑ j, p j * ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs)) ≤
      (1 - lam) * ((x - xs) ⬝ᵥ (x - xs)) := fun x => by
    rw [expected_sqErr_step_eq A b p hp1 S hxs x]
    have := hlam (x - xs)
    linarith
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ v : n → ℝ, v ⬝ᵥ v = 0 := fun v => by simp [dotProduct]
    have : ∀ k (x : n → ℝ), expErr A b p S xs x k = 0 := by
      intro k
      induction k with
      | zero => intro x; exact h0 _
      | succ k ih => intro x; simp [expErr, ih]
    rw [this, h0, mul_zero]
  have hρ : 0 ≤ 1 - lam := by
    obtain ⟨i⟩ := hn
    have h1 := hlam (Pi.single i 1)
    have h2 := hW (Pi.single i 1)
    have he : (Pi.single i (1 : ℝ) : n → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by simp
    rw [he, mul_one] at h1
    rw [he] at h2
    linarith
  induction k generalizing x with
  | zero => simp [expErr]
  | succ k ih =>
    show ∑ j, p j * expErr A b p S xs (step A b (S j) x) k ≤ _
    calc ∑ j, p j * expErr A b p S xs (step A b (S j) x) k
        ≤ ∑ j, p j * ((1 - lam) ^ k * ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _) (hp j)
      _ = (1 - lam) ^ k * ∑ j, p j * ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (1 - lam) ^ k * ((1 - lam) * ((x - xs) ⬝ᵥ (x - xs))) :=
          mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg hρ k)
      _ = (1 - lam) ^ (k + 1) * ((x - xs) ⬝ᵥ (x - xs)) := by ring

/-- A sketch-and-project update preserves membership of the error in `range Aᵀ`,
even for an arbitrary reference point and an inconsistent right-hand side.
The correction belongs to the row space because the Moore–Penrose inverse of `SᵀA`
has range contained in `range Aᵀ`. Gower–Richtárik 2015, eq. (2.3);
atlas `sketch-and-project` (invariant-space helper). -/
theorem step_sub_mem_range (A : Matrix m n ℝ) (b : m → ℝ) (S : Matrix m s ℝ)
    (xs x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) :
    step A b S x - xs ∈ LinearMap.range Aᵀ.mulVecLin := by
  let B := moorePenroseInverse (Sᵀ * A)
  have hB : B = Aᵀ * (S * (Bᵀ * B)) := by
    have hsym : (B * (Sᵀ * A))ᵀ = B * (Sᵀ * A) :=
      moorePenroseInverse_mul_isSymm (Sᵀ * A)
    calc B = B * (Sᵀ * A) * B :=
          (moorePenroseInverse_mul_moorePenroseInverse (Sᵀ * A)).symm
      _ = (B * (Sᵀ * A))ᵀ * B := by rw [hsym]
      _ = Aᵀ * (S * (Bᵀ * B)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
          simp only [Matrix.mul_assoc]
  have hstep : step A b S x - xs = (x - xs) - B *ᵥ (Sᵀ *ᵥ (A *ᵥ x - b)) := by
    dsimp [step, B]
    abel
  rw [hstep]
  refine Submodule.sub_mem _ hx ⟨(S * (Bᵀ * B)) *ᵥ (Sᵀ *ᵥ (A *ᵥ x - b)), ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hB]

/-- **Sketch-and-project contraction on the row space.** For a consistent system,
an initial error in `range Aᵀ`, and a lower bound `λ‖v‖² ≤ vᵀ W v` only on that
row space, the finite iid sketch distribution satisfies
`E‖x_k-xs‖² ≤ (1-λ)^k ‖x₀-xs‖²`. No full-column-rank assumption is required.
Gower–Richtárik 2015, Theorem 4.6, Euclidean case `B = I`;
atlas `sketch-and-project`. Deviation: a finite sketch distribution, with expectation
given by the exact first-step recursion. The initial-error membership is essential.
atlas: sketch-and-project -/
theorem expErr_le_of_sub_mem_range (A : Matrix m n ℝ) (b : m → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (S : J → Matrix m s ℝ) {xs : n → ℝ} (hxs : A *ᵥ xs = b) {lam : ℝ}
    (hlam : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (expectedProjector A p S *ᵥ v))
    (x : n → ℝ) (hx : x - xs ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    expErr A b p S xs x k ≤ (1 - lam) ^ k * ((x - xs) ⬝ᵥ (x - xs)) := by
  classical
  have hW := dotProduct_expectedProjector_mulVec_le A p hp hp1 S
  have hsol : ∀ k, expErr A b p S xs xs k = 0 := by
    intro k
    induction k with
    | zero => simp [expErr]
    | succ k ih => simp [expErr, step, hxs, ih]
  induction k generalizing x with
  | zero => simp [expErr]
  | succ k ih =>
    by_cases hx0 : x = xs
    · subst x
      simp [hsol]
    have hpos : 0 < (x - xs) ⬝ᵥ (x - xs) :=
      lt_of_le_of_ne (dotProduct_self_nonneg _) (Ne.symm fun h =>
        hx0 (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h)))
    have hlam1 : lam ≤ 1 :=
      le_of_mul_le_mul_right (by simpa only [one_mul] using (hlam _ hx).trans (hW _)) hpos
    have hρ : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hstep : ∑ j, p j * ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs)) ≤
        (1 - lam) * ((x - xs) ⬝ᵥ (x - xs)) := by
      rw [expected_sqErr_step_eq A b p hp1 S hxs x]
      have := hlam _ hx
      linarith
    show ∑ j, p j * expErr A b p S xs (step A b (S j) x) k ≤ _
    calc ∑ j, p j * expErr A b p S xs (step A b (S j) x) k
        ≤ ∑ j, p j * ((1 - lam) ^ k *
            ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (ih _ (step_sub_mem_range A b (S j) xs x hx)) (hp j)
      _ = (1 - lam) ^ k * ∑ j, p j *
          ((step A b (S j) x - xs) ⬝ᵥ (step A b (S j) x - xs)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (1 - lam) ^ k * ((1 - lam) * ((x - xs) ⬝ᵥ (x - xs))) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hρ k)
      _ = (1 - lam) ^ (k + 1) * ((x - xs) ⬝ᵥ (x - xs)) := by ring

end SketchProject

end NLAlib

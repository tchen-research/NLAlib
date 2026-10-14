import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Convergence from finite degree-transfer inequalities

An approximation error sequence whose scaled values can be transferred from
arbitrarily large even degrees has a limit, without a normal-family argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace NLAlib

/-- Finite degree-transfer inequalities with vanishing target-degree remainder
force the even subsequence to converge to its actual liminf.
Source: focused Bernstein reroute, scalar closure of the finite inequality. -/
theorem tendsto_even_sequence_of_degree_transfer
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a (2*n)) {M : ℝ} (hM : ∀ n, a (2*n) ≤ M)
    (htransfer : ∀ α : ℝ, 0 < α → α < 1 →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
        ∀ N : ℕ, 1 ≤ N → ∀ᶠ m : ℕ in atTop, a N ≤ a (2*m)/α+r N) :
    Tendsto (fun n => a (2*n)) atTop (𝓝 (liminf (fun n => a (2*n)) atTop)) := by
  let u : ℕ → ℝ := fun n => a (2*n)
  let b : ℝ := liminf u atTop
  have hbelow : IsBoundedUnder (· ≥ ·) atTop u :=
    ⟨0, eventually_map.mpr (Eventually.of_forall ha)⟩
  have habove : IsBoundedUnder (· ≤ ·) atTop u :=
    ⟨M, eventually_map.mpr (Eventually.of_forall hM)⟩
  have hco : IsCoboundedUnder (· ≥ ·) atTop u := habove.isCoboundedUnder_ge
  obtain ⟨σ, hσu, hσ⟩ := exists_seq_tendsto_liminf hco hbelow
  have hα (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : limsup u atTop ≤ b/α := by
    obtain ⟨r, hr, htr⟩ := htransfer α hα0 hα1
    have hpoint (N : ℕ) (hN : 1 ≤ N) : a N ≤ b/α+r N := by
      have h := hσ.eventually (htr N hN)
      exact le_of_tendsto_of_tendsto tendsto_const_nhds
        ((hσu.div_const α).add_const (r N)) h
    apply le_of_forall_pos_le_add
    intro ε hε
    apply limsup_le_of_le hbelow.isCoboundedUnder_le
    have hrε : ∀ᶠ n : ℕ in atTop, r (2*n) < ε := by
      exact (hr.comp (tendsto_atTop_mono (fun n : ℕ => by dsimp; omega) tendsto_id)).eventually
        (gt_mem_nhds hε)
    filter_upwards [eventually_ge_atTop 1, hrε] with n hn hnr
    exact (hpoint (2*n) (by omega)).trans (by linarith)
  have hsup : limsup u atTop ≤ b := by
    let α : ℕ → ℝ := fun n => 1-1/(n+2:ℝ)
    have hαt : Tendsto α atTop (𝓝 1) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp
        (tendsto_add_atTop_nat 2)
      have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, α, sub_zero] using hc.sub h
    have hden : ∀ n : ℕ, (0:ℝ) < n+2 := by intro n; positivity
    have hα0 (n : ℕ) : 0 < α n := by
      dsimp [α]
      have hn : (1:ℝ) < n+2 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have h := (div_lt_one (hden n)).mpr hn
      linarith
    have hα1 (n : ℕ) : α n < 1 := by
      dsimp [α]
      have := div_pos (zero_lt_one : (0:ℝ)<1) (hden n)
      linarith
    have hlim : Tendsto (fun n => b/α n) atTop (𝓝 b) := by
      have hc : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
      simpa only [div_one] using! hc.div hαt (one_ne_zero : (1:ℝ)≠0)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall (fun n => hα (α n) (hα0 n) (hα1 n)))
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hsup habove hbelow

/-- Convergence of the even and odd subsequences gives convergence of the whole
natural-index sequence. -/
theorem tendsto_nat_of_even_odd {a : ℕ → ℝ} {b : ℝ}
    (he : Tendsto (fun n => a (2*n)) atTop (𝓝 b))
    (ho : Tendsto (fun n => a (2*n+1)) atTop (𝓝 b)) :
    Tendsto a atTop (𝓝 b) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually hs)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ho.eventually hs)
  apply eventually_atTop.mpr
  refine ⟨2*max N M, ?_⟩
  intro n hn
  have hdivN : N ≤ n/2 := by omega
  have hdivM : M ≤ n/2 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hneven : n=2*(n/2) := by omega
    rw [hneven]
    exact hN _ hdivN
  · have hnodd : n=2*(n/2)+1 := by omega
    rw [hnodd]
    exact hM _ hdivM

/-- For an antitone approximation-error sequence, convergence of the scaled
even degrees implies convergence at every degree by the two neighboring even
degrees. No parity identity for minimizing polynomials is required. -/
theorem tendsto_nat_mul_of_even_tendsto {e : ℕ → ℝ} (he : Antitone e) {b : ℝ}
    (h : Tendsto (fun n => (2*n:ℕ)*e (2*n)) atTop (𝓝 b)) :
    Tendsto (fun n : ℕ => (n:ℝ)*e n) atTop (𝓝 b) := by
  apply tendsto_nat_of_even_odd h
  let L : ℕ → ℝ := fun n =>
    ((2*n+1:ℕ):ℝ)/((2*n+2:ℕ):ℝ) * (((2*(n+1):ℕ):ℝ)*e (2*(n+1)))
  let U : ℕ → ℝ := fun n =>
    ((2*n+1:ℕ):ℝ)/((2*n:ℕ):ℝ) * (((2*n:ℕ):ℝ)*e (2*n))
  have hratioL : Tendsto (fun n : ℕ => ((2*n+1:ℕ):ℝ)/((2*n+2:ℕ):ℝ))
      atTop (𝓝 1) := by
    convert! tendsto_add_mul_div_add_mul_atTop_nhds (1:ℝ) 2 2
      (d := 2) (by norm_num) using 1
    · funext n
      push_cast
      ring
    · norm_num
  have hratioU : Tendsto (fun n : ℕ => ((2*n+1:ℕ):ℝ)/((2*n:ℕ):ℝ))
      atTop (𝓝 1) := by
    convert! tendsto_add_mul_div_add_mul_atTop_nhds (1:ℝ) 0 2
      (d := 2) (by norm_num) using 1
    · funext n
      push_cast
      ring
    · norm_num
  have hL : Tendsto L atTop (𝓝 b) := by
    simpa only [L, Function.comp_apply, one_mul] using
      hratioL.mul (h.comp (tendsto_add_atTop_nat 1))
  have hU : Tendsto U atTop (𝓝 b) := by
    simpa only [U, one_mul] using hratioU.mul h
  have hlo : ∀ᶠ n : ℕ in atTop, L n ≤ ((2*n+1:ℕ):ℝ)*e (2*n+1) := by
    filter_upwards [] with n
    have hden : ((2*n+2:ℕ):ℝ) ≠ 0 := by positivity
    have heq : L n = ((2*n+1:ℕ):ℝ)*e (2*n+2) := by
      dsimp [L]
      rw [show 2*(n+1)=2*n+2 by omega]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left (he (by omega : 2*n+1 ≤ 2*n+2)) (by positivity)
  have hhi : ∀ᶠ n : ℕ in atTop, ((2*n+1:ℕ):ℝ)*e (2*n+1) ≤ U n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hden : ((2*n:ℕ):ℝ) ≠ 0 := by positivity
    have heq : U n = ((2*n+1:ℕ):ℝ)*e (2*n) := by
      dsimp [U]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left (he (by omega : 2*n ≤ 2*n+1)) (by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU hlo hhi

end NLAlib

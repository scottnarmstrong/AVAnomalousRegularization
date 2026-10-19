-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Definitions.Iteration.CascadeStatement
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

section
open Filter Topology
namespace AVRegularity.Providers

/-! Proof of `cascade_wait`.

For `j ≥ 1`, `τ_j ≤ τ''_j ≤ 2^{-25}ε_{j-1}^κ` with `κ = 2 - β + 2δ > 0`, so the tail
`∑_{j > m₀}(3τ_j + 4τ''_j)` is at most `7·2^{-25}ε_{m₀}^κ/(1 - Λ^{-κ})` by the forward geometric
tail of the wavelengths, which tends to zero. -/

/-- `τ_j ≤ τ''_j`: the block count `L_j ≥ 1`. -/
theorem ocTau_le_ocTauPP {α q : ℝ} {Λ j : ℕ} (hΛ : 1 ≤ Λ) :
    ocTau α q Λ j ≤ ocTauPP α q Λ j := by
  have hτ := (AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := j) hΛ).le
  have hL : (1 : ℝ) ≤ (ocL α q Λ j : ℝ) ^ 2 := by
    have : 1 ≤ ocL α q Λ j := by unfold ocL; omega
    have h1 : (1 : ℝ) ≤ (ocL α q Λ j : ℝ) := by exact_mod_cast this
    nlinarith
  unfold ocTau
  exact div_le_self hτ hL

/-- One term of the wait sum: `3τ_j + 4τ''_j ≤ 7·ε_{j-1}^κ`. -/
theorem wait_term_le {α s q : ℝ} {Λ j : ℕ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    3 * ocTau α q Λ j + 4 * ocTauPP α q Λ j ≤
      7 * ocEpsilon q Λ (j - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) := by
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hE := AVRegularity.Scales.epsilon_basic (m := j - 1) hq.1 hΛ
  have hκ : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q := by linarith
  have hup := (AVRegularity.CycleReference.ocTauPP_power_bounds (α := α) (m := j)
    hE.1 hE.2.1 hκ).2
  have hle := ocTau_le_ocTauPP (α := α) (q := q) (j := j) (by omega : 1 ≤ Λ)
  have h25 : (2 : ℝ) ^ (-25 : ℤ) ≤ 1 := by norm_num
  have hp : 0 ≤ ocEpsilon q Λ (j - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) :=
    Real.rpow_nonneg hE.1.le _
  have : ocTauPP α q Λ j ≤ ocEpsilon q Λ (j - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) :=
    hup.trans (by nlinarith)
  linarith

/-- **The cascade wait**. -/
theorem cascade_wait (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ t₀ : ℝ, 0 < t₀ → ∃ m₁ : ℕ, ∀ m₀ : ℕ, m₁ ≤ m₀ →
      ∀ n : ℕ, ∑ j ∈ Finset.Ioc m₀ n, (3 * ocTau α q Λ j + 4 * ocTauPP α q Λ j) < t₀ := by
  refine ⟨128, le_rfl, fun Λ hΛ t₀ ht₀ => ?_⟩
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  set κ := 2 - (1 + α) + 2 * ocDelta α q with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  set ρ : ℝ := 1 - (Λ : ℝ) ^ (-κ) with hρ
  have hΛ1 : (1 : ℝ) < Λ := by exact_mod_cast (show 1 < Λ by omega)
  have hρpos : 0 < ρ := by
    rw [hρ, sub_pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hΛ1 (by linarith)
  have hlim : Tendsto (fun k : ℕ => ocEpsilon q Λ (1 + k) ^ κ) atTop (𝓝 0) :=
    (AVRegularity.Scales.epsilon_forward_tail (q := q) (Λ := Λ) (m := 1) (p := κ) hq.1 hΛ
      le_rfl hκ).1.tendsto_atTop_zero
  have hev : ∀ᶠ k : ℕ in atTop, ocEpsilon q Λ (1 + k) ^ κ < t₀ * ρ / 7 :=
    hlim (gt_mem_nhds (by positivity))
  obtain ⟨m₂, hm₂⟩ := eventually_atTop.1 hev
  refine ⟨m₂ + 1, fun m₀ hm₀ n => ?_⟩
  have hsmall : ocEpsilon q Λ m₀ ^ κ < t₀ * ρ / 7 := by
    have := hm₂ (m₀ - 1) (by omega)
    rwa [show 1 + (m₀ - 1) = m₀ by omega] at this
  have hm₀1 : 1 ≤ m₀ := by omega
  obtain ⟨hsum, htail⟩ := AVRegularity.Scales.epsilon_forward_tail (q := q) (Λ := Λ)
    (m := m₀) (p := κ) hq.1 hΛ hm₀1 hκ
  have hnn : ∀ k : ℕ, 0 ≤ ocEpsilon q Λ (m₀ + k) ^ κ := fun k =>
    Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := m₀ + k) hq.1 hΛ).1.le κ
  -- reindex `j ∈ (m₀, n]` as `j = m₀ + 1 + k`, `k < n - m₀`
  have hre : ∑ j ∈ Finset.Ioc m₀ n, ocEpsilon q Λ (j - 1) ^ κ =
      ∑ k ∈ Finset.range (n - m₀), ocEpsilon q Λ (m₀ + k) ^ κ := by
    have hI : Finset.Ioc m₀ n = Finset.Ico (m₀ + 1) (n + 1) := by
      ext j; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun k _ => ?_
    congr 2
    omega
  calc ∑ j ∈ Finset.Ioc m₀ n, (3 * ocTau α q Λ j + 4 * ocTauPP α q Λ j)
      ≤ ∑ j ∈ Finset.Ioc m₀ n, 7 * ocEpsilon q Λ (j - 1) ^ κ :=
        Finset.sum_le_sum fun j _ => wait_term_le hα₀ hα₁ hs₀ hs₁ hq hΛ
    _ = 7 * ∑ k ∈ Finset.range (n - m₀), ocEpsilon q Λ (m₀ + k) ^ κ := by
        rw [← Finset.mul_sum, hre]
    _ ≤ 7 * ∑' k : ℕ, ocEpsilon q Λ (m₀ + k) ^ κ := by
        gcongr
        exact hsum.sum_le_tsum _ fun k _ => hnn k
    _ ≤ 7 * (ocEpsilon q Λ m₀ ^ κ / ρ) := by gcongr
    _ < 7 * (t₀ * ρ / 7 / ρ) := by gcongr
    _ = t₀ := by field_simp

end AVRegularity.Providers
end

section
namespace AVRegularity.Providers

/-! Proof of `cascade_schedule_exists` (the schedule block).

The choices follow the statement's docstring: `Q = 2(P + qZ_K + 5)`; the menus `H, N, p, A_cl` (each a
strict lower bound against a positive exponent); then `D_*`, the widths `σ = m/6`, `a = σ/2`,
`σ₀ = 3σ/2` with `m` the width bound of `IsCascadeWidths`; then `J` (the history exponent
`θ₂ = δ - σ₀D_* - η₀ ≥ 3δ/4 > 0`); then the moments `L_c, L_f, L_pr, L`, the kernel order `n_k`,
and the reserves `N_aux = K_res`, `N_out = N_aux + 4p`. `N_aux` contains the summand
`succReconFloor r₀ D₀ H J N p A_cl L_c` (the order floor of the physical reconstruction; every
condition on `N_aux` is a lower bound, and the menus are chosen before it). -/

/-- A natural number with `a * n > B` for `a > 0`. -/
private theorem exists_nat_mul_gt' {a : ℝ} (ha : 0 < a) (B : ℝ) : ∃ n : ℕ, a * n > B := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / a)
  exact ⟨n, by rw [div_lt_iff₀ ha] at hn; linarith⟩

/-- `Σ_H ≥ H + 1` (each term `q₀^l ≥ 1`). -/
theorem succSigmaH_ge {q : ℝ} (hq : 1 ≤ q) (H : ℕ) : (H : ℝ) + 1 ≤ succSigmaH q H := by
  unfold succSigmaH
  have : ∑ l ∈ Finset.range (H + 1), (1 : ℝ) ≤ ∑ l ∈ Finset.range (H + 1), ((1 + q) / 2) ^ l :=
    Finset.sum_le_sum fun l _ => one_le_pow₀ (by linarith)
  simpa using this

/-- **Order choice for the cascade** (the schedule (12.5) of the paper). -/
theorem cascade_schedule_exists (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    ∀ (K : ℕ) (Pacc : ℝ) (r₀ D₀ : ℕ) (lamE σE : ℝ), 3 ≤ K → 0 < Pacc → 0 < lamE → 0 < σE →
    ∃ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a
        σ ∧
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux := by
  intro K Pacc r₀ D₀ lamE σE _hK hP hlam hσE
  obtain ⟨hγ, hδ, hmu, -, -, -⟩ :=
    AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hq1 := hq.1
  have hq0 : 0 < q := by linarith
  have hmuS : 0 < ocMuS α q s := hmu
  have hc : 0 < ocC α q := by unfold ocC; positivity
  set δ := ocDelta α q with hδdef
  set η := succEta0 α q s with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηδ : η ≤ δ / 8 := min_le_left _ _
  have hZ : 0 < iterZ α q s K := by unfold iterZ; positivity
  -- `Q`
  set Q : ℝ := 2 * (Pacc + q * iterZ α q s K + 5) with hQdef
  have hQ : 0 < Q := by positivity
  set R : ℝ := Q + q * ocGamma α q + 4 with hR
  -- menus
  obtain ⟨H', hH'⟩ := exists_nat_mul_gt' (show 0 < η / 8 by positivity) R
  obtain ⟨N', hN'⟩ := exists_nat_mul_gt' (show 0 < 3 * δ by positivity) R
  obtain ⟨p', hp'⟩ := exists_nat_mul_gt' hδ R
  obtain ⟨Acl, hAcl⟩ := exists_nat_mul_gt' (show 0 < q * ocGamma α q + 3 * δ by positivity)
    (2 - (1 + α) + 8 * δ)
  set H := H' + 1 with hH
  set N := N' + 2 with hN
  set p := p' + 1 with hp
  set Dst : ℕ := succDstar D₀ N p H with hDst
  -- widths
  set m : ℝ := min lamE (min ((1 / 2) * min lamE ((q - 1) * (1 + ocC α q)))
    (δ / (8 * (1 + (Dst : ℝ))))) with hm
  have hm0 : 0 < m := by
    have : 0 < (q - 1) * (1 + ocC α q) := mul_pos (by linarith) (by linarith)
    refine lt_min hlam (lt_min ?_ (by positivity))
    exact mul_pos (by norm_num) (lt_min hlam this)
  set σ : ℝ := m / 6 with hσ
  set a : ℝ := σ / 2 with ha
  set σ₀ : ℝ := a + σ with hσ₀
  have hσpos : 0 < σ := by positivity
  have hapos : 0 < a := by positivity
  have hσ₀pos : 0 < σ₀ := by positivity
  have h3σ : 3 * σ < m := by rw [hσ]; linarith
  have hmlam : m ≤ lamE := min_le_left _ _
  have hmD : m ≤ δ / (8 * (1 + (Dst : ℝ))) := (min_le_right _ _).trans (min_le_right _ _)
  have hDst0 : (0 : ℝ) ≤ Dst := Nat.cast_nonneg _
  have hσ₀D : σ₀ * Dst ≤ δ / 8 := by
    have h1 : 3 * σ * (1 + (Dst : ℝ)) < δ / 8 := by
      have h2 : 3 * σ < δ / (8 * (1 + (Dst : ℝ))) := h3σ.trans_le hmD
      rw [lt_div_iff₀ (by positivity)] at h2
      linarith
    have : σ₀ = 3 * σ / 2 := by rw [hσ₀, ha]; ring
    rw [this]
    nlinarith
  -- the history exponent and `J`
  have hθ₂ : 0 < succTheta2 α q s σ₀ Dst := by
    unfold succTheta2; rw [← hδdef, ← hηdef]; linarith
  obtain ⟨J, hJ⟩ := exists_nat_mul_gt' hθ₂ (R - succTheta1 α q s σ₀ Dst)
  -- moments
  set σf : ℝ := min σE (δ + σ₀) with hσf
  have hσf0 : 0 < σf := lt_min hσE (by positivity)
  obtain ⟨Lc, hLc⟩ := exists_nat_mul_gt' hσ₀pos R
  obtain ⟨Lf, hLf⟩ := exists_nat_mul_gt' (show 0 < q * σf by positivity) (Q + 4)
  obtain ⟨Lpr, hLpr⟩ := exists_nat_mul_gt' (show 0 < q * σf by positivity) (Q + 3)
  obtain ⟨L, hL⟩ := exists_nat_mul_gt' hσ₀pos
    (Pacc + max (iterZ α q s K) (q * (1 + s)) + 4)
  set nk : ℕ := max Lpr (max Lc Lf) + L + 1 with hnk
  set X₁ : ℕ := 4 * (N + succSchedD D₀ N p (H + 1)) + 2 * Acl + 16 + succSchedD D₀ N p (H + 1) +
    Lc + 6 * p with hX₁
  set X₂ : ℕ := Dst + Lf + N + 2 * p + 1 with hX₂
  set Naux : ℕ := X₁ + X₂ + (2 * (K + 2) + N + 2 * p + L) +
    succReconFloor r₀ D₀ H J N p Acl Lc with hNaux
  have hHc : (H' : ℝ) + 2 = (H : ℝ) + 1 := by rw [hH]; push_cast; ring
  have hNc : (N' : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  have hpc : (p' : ℝ) ≤ p := by rw [hp]; push_cast; linarith
  have hSig := succSigmaH_ge hq1.le H
  have hHgoal : η / 8 * succSigmaH q H > R := by
    have h1 : η / 8 * ((H : ℝ) + 1) ≤ η / 8 * succSigmaH q H :=
      mul_le_mul_of_nonneg_left hSig (by positivity)
    have h2 : η / 8 * (H' : ℝ) ≤ η / 8 * ((H' : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hHc] at h2
    linarith only [h1, h2, hH']
  have hNgoal : 3 * δ * N > R :=
    lt_of_lt_of_le hN' (mul_le_mul_of_nonneg_left hNc (by positivity))
  have hpgoal : δ * p > R := lt_of_lt_of_le hp' (mul_le_mul_of_nonneg_left hpc hδ.le)
  have hJgoal : succTheta1 α q s σ₀ Dst + J * succTheta2 α q s σ₀ Dst > R := by
    linarith only [hJ]
  have hσ₀lam : σ₀ < lamE := by
    have : σ₀ = 3 * σ / 2 := by rw [hσ₀, ha]; ring
    linarith only [this, h3σ, hmlam, hσpos]
  have haσ : a < σ := by rw [ha]; linarith only [hσpos]
  have hQ2 : Pacc + q * iterZ α q s K + 4 < Q / 2 := by rw [hQdef]; linarith only
  have hmax : max X₁ X₂ ≤ Naux := max_le (by omega) (by omega)
  refine ⟨Q, H, J, N, p, nk, Lc, Lf, Lpr, Acl, Naux, Naux + 4 * p, Naux, L, σ₀, a, σ,
    ⟨hQ, hQ2, ?_, le_rfl, by omega, ⟨by omega, hL, by omega⟩, ⟨hapos, haσ, h3σ⟩⟩, by omega⟩
  exact ⟨hHgoal, hJgoal, hNgoal, hpgoal, hAcl.le, hσ₀, hapos, haσ.le, hσ₀lam, hσ₀D, hLc,
    hLf, hLpr, by omega, hmax, le_rfl, by omega, by omega, by omega, by omega⟩

end AVRegularity.Providers
end

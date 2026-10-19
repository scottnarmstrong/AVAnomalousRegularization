-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Passage.Profiles.RetainedCovFresh
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Finite.TerminalLift.PositiveInput
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
import AVRegularity.Finite.Lift.PositivePhysicalIdentity
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
section
/-! **The kernel bound at all orders `2 ≤ i ≤ K + 2p`, with one constant**

`retCov_kernel_orders`: from `passage_kernel_sup` at `(m', l') = (i, min K i)`: for an admissible
kernel `S` of order `nk` and positive width `r`, and a periodic `C^K` field `W`,
`∑_{|α|=i} ‖∂^α S W‖_∞ ≤ C_k r^{ℓ-i} ∑_{|β|=ℓ} ‖∂^β W‖_∞`, `ℓ = min K i`, for every
`2 ≤ i ≤ K + 2p`, with `C_k` depending only on `(φ₀, Γ, L, nk, K, p)`.

Special cases: `K + 2p < 2` (no order, vacuous). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

theorem retCov_kernel_orders (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (Γ : ℝ) (L : ℕ) (nk : ℕ+)
    (K p : ℕ) (hK : 1 ≤ K) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ (S : KernelSpec), S.order = nk → S.IsAdmissible Γ L → 0 < S.width →
    ∀ (t : ℝ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
      (Wf : Vec 2 → H), ContDiff ℝ K Wf → IsZ2Periodic Wf →
    ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α (S.applyClassical φ₀ t Wf)) ≤
        ENNReal.ofReal (Ck * S.width ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf) := by
  have key : ∀ i : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ i → ∀ (S : KernelSpec), S.order = nk →
      S.IsAdmissible Γ L → 0 < S.width → ∀ (t : ℝ) {H : Type} [NormedAddCommGroup H]
      [NormedSpace ℝ H] [CompleteSpace H] (V : Vec 2 → H),
      ContDiff ℝ (min K i : ℕ) V → IsZ2Periodic V →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α (S.applyClassical φ₀ t V)) ≤
        ENNReal.ofReal (C * S.width ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β V)) := by
    intro i
    by_cases hi : 2 ≤ i
    · obtain ⟨C, hC, h⟩ := Providers.passage_kernel_sup φ₀ hφ₀ hφs hφsupp Γ L nk i (min K i)
        (by omega) (by omega)
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose Cf hCf hCf2 using key
  refine ⟨∑ i ∈ Finset.range (K + 2 * p + 1), Cf i + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range (K + 2 * p + 1), Cf i :=
      Finset.sum_nonneg fun i _ => (hCf i).le
    linarith
  intro S hSo hSa hSw t H _ _ _ Wf hW hWp i hi2 hiM
  refine (hCf2 i hi2 S hSo hSa hSw t Wf (hW.of_le (by exact_mod_cast Nat.min_le_left _ _)) hWp).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hSw.le _)
  have : Cf i ≤ ∑ i ∈ Finset.range (K + 2 * p + 1), Cf i :=
    Finset.single_le_sum (f := Cf) (fun j _ => (hCf j).le) (Finset.mem_range.mpr (by omega))
  linarith

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The scales of the discarded profiles**.

`discScales : DiscScalesStatement α q ζ`: `ρ = rhoEnh = freshLength` (`m ≥ 1`); the renewal radius
`ρ ≍ E^{1+c}` (`bandChain_renewal_radius`) gives `ρ ≥ C⁻¹E^{1+c}`, and `ρ ≤ C E`; `1 + c ≤ q`
(`c = γ/2 + δ`) gives `ρ ≥ C⁻¹E^q`; `e = ε_m ≥ E^q/2` (`ocEpsilon_succ_ge`); `ε_n → 0`.

Special cases: `m = 2`; `cr = 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.IterationPassage.Passage

theorem discScales_eps_le {q : ℝ} {Λ n : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hn : 1 ≤ n) :
    ocEpsilon q Λ n ≤ (1 / 2 : ℝ) ^ n := by
  have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 1 ≤ Λ)
  have hΛ2 : (2 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 2 ≤ Λ)
  set y := (Λ : ℝ) ^ (q ^ n / (q - 1)) with hy
  have hq1 : 0 < q - 1 := by linarith
  have hexp : (n : ℝ) ≤ q ^ n / (q - 1) := by
    rw [le_div_iff₀ hq1]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ q - 1 by linarith) n
    have h2 : (1 + (q - 1)) ^ n = q ^ n := by ring_nf
    nlinarith
  have hyn : (Λ : ℝ) ^ n ≤ y := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hΛ1 hexp
  have h2n : (2 : ℝ) ^ n ≤ (Λ : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hΛ2 n
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) (h2n.trans hyn)
  have heq : ocEpsilon q Λ n = ((⌈y⌉₊ : ℕ) : ℝ)⁻¹ := by simp [ocEpsilon, Nat.ne_of_gt hn, hy]
  rw [heq]
  calc ((⌈y⌉₊ : ℕ) : ℝ)⁻¹ ≤ y⁻¹ := inv_anti₀ hypos (Nat.le_ceil y)
    _ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) (h2n.trans hyn)
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]

theorem discScales_eps_tendsto {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {c : ℝ} (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ocEpsilon q Λ n ≤ c := by
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have h2 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  exact (discScales_eps_le hq hΛ h1).trans
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) h2).trans hn₀.le)

/-- `1 + c ≤ q` for `c = ocC α q = γ/2 + δ`. -/
theorem discScales_c_le {α q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hq : 1 < q) :
    1 + ocC α q ≤ q := by
  unfold ocC ocGamma ocDelta
  have hq1 : 0 < q - 1 := by linarith
  have h1 : (q - 1) * (1 + α) / (q + 1) ≤ 2 * (q - 1) / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h2 : (2 * q + 1) * (1 + α) / (2 * q + 2) ≥ 0 := by positivity
  have h3 : (q - 1) / 4 * (1 - (2 * q + 1) * (1 + α) / (2 * q + 2)) ≤ (q - 1) / 4 := by
    nlinarith
  linarith

theorem discScales (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : DiscScalesStatement α q ζ := by
  obtain ⟨C', hC', Λr, hΛr, hren⟩ := CycleReference.bandChain_renewal_radius hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λr, hΛr, fun Λ hΛ => ⟨(ocC_pos_of_admissible hα₀ hq).le, ?_, ?_⟩⟩
  · intro c hc
    obtain ⟨n₀, hn⟩ := discScales_eps_tendsto hq.1 (hΛr.trans hΛ) hc
    refine ⟨n₀ + 1, fun D hDα hDq hDΛ hDζ m hm => ?_⟩
    unfold OCData.eps
    rw [hDq, hDΛ]
    exact hn _ (by omega)
  · intro cr hcr hcr1
    have hC'0 : 0 < C' := by linarith
    refine ⟨max 2 (C' / cr), le_trans (by norm_num) (le_max_left _ _), ?_⟩
    intro D hDα hDq hDΛ hDζ M hband hterm m hm2 hmM
    have hΛ1 : 1 ≤ Λ := by have := hΛr.trans hΛ; omega
    have hr := hren Λ hΛ M (by omega) D.κ hband m hm2 hmM
    have heps : D.eps (m - 1) = ocEpsilon q Λ (m - 1) := by
      unfold OCData.eps; rw [hDq, hDΛ]
    have hρeq : rhoEnh D cr m = cr * ocRh α q Λ m (D.κ (m - 1)) := by
      unfold rhoEnh ocRh; rw [hDα, hDq, hDΛ]
    set Cc := max 2 (C' / cr) with hCc
    have hCc2 : 2 ≤ Cc := le_max_left _ _
    have hCc0 : 0 < Cc := by linarith
    have hCcC' : C' ≤ Cc := by
      have h1 : C' / cr ≤ Cc := le_max_right _ _
      have h2 : C' ≤ C' / cr := by
        rw [le_div_iff₀ hcr]; nlinarith
      linarith
    have hEpos : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
    have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 := ocEpsilon_le_one hΛ1 _
    have hy1 : ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) ≤ ocEpsilon q Λ (m - 1) := by
      have := Real.rpow_le_rpow_of_exponent_ge hEpos hE1 (show (1 : ℝ) ≤ 1 + ocC α q by
        linarith [ocC_pos_of_admissible hα₀ hq])
      simpa using this
    have hyq : ocEpsilon q Λ (m - 1) ^ q ≤ ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) :=
      Real.rpow_le_rpow_of_exponent_ge hEpos hE1 (discScales_c_le hα₀ hα₁ hq.1)
    have hylow : Cc⁻¹ * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) ≤ rhoEnh D cr m := by
      rw [hρeq]
      have h1 := hr.1
      have h2 : Cc⁻¹ ≤ cr * C'⁻¹ := by
        rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hCc0 hC'0]
        have : C' ≤ Cc * cr := by
          have : C' / cr ≤ Cc := le_max_right _ _
          rw [div_le_iff₀ hcr] at this; linarith
        linarith
      calc _ ≤ cr * C'⁻¹ * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = cr * (C'⁻¹ * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hcr.le
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold rhoEnh freshLength
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    · intro hE
      rw [heps] at hE
      rw [hρeq]
      have hup := hr.2
      calc cr * ocRh α q Λ m (D.κ (m - 1)) ≤ 1 * (C' * ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) :=
            mul_le_mul hcr1 hup (by unfold ocRh; exact Real.sqrt_nonneg _) zero_le_one
        _ ≤ C' * ocEpsilon q Λ (m - 1) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hy1 hC'0.le
        _ ≤ Cc * ocEpsilon q Λ (m - 1) := mul_le_mul_of_nonneg_right hCcC' hEpos.le
        _ ≤ Cc * Cc⁻¹ := mul_le_mul_of_nonneg_left hE hCc0.le
        _ = 1 := mul_inv_cancel₀ hCc0.ne'
    · rw [heps]; exact hylow
    · rw [heps]
      exact le_trans (mul_le_mul_of_nonneg_left hyq (by positivity)) hylow
    · rw [heps]
      have h := Applications.ocEpsilon_succ_ge (q := q) (Λ := Λ) (m := m - 1) hq.1 (hΛr.trans hΛ) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
      have hD : D.eps m = ocEpsilon q Λ m := by unfold OCData.eps; rw [hDq, hDΛ]
      rw [hD]
      refine le_trans ?_ h
      have : Cc⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hCc2
      calc Cc⁻¹ * ocEpsilon q Λ (m - 1) ^ q ≤ 1 / 2 * ocEpsilon q Λ (m - 1) ^ q :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The positive part of the passage lift in normalized coordinates**.

For the slot lifts of a cascade stage `G` (level `m`, masses `π`), the actual lift coefficients
`CcT` of the passage (`IsPassageLift`) and a field `a t` of class `C^{P₀+N}`, periodic:

* `passageLift_positive_difference`: `T a - a` is the glued lift of the positive coefficients
  (`pulse_positive_difference_time`, `obs_cutoff_sum_one`);
* `passageLift_positive_eq_native`: on the active pulses the positive coefficients are those of
  the slot lifts (`nativeStageLiftFamily_coefficients_unique`);
* `passageLift_positive_word_bound`: for a spatial word `β` of order `r ≤ P₀`,
  `e^r |∂^β F[(T - I)a](x)| ≤ price · cost · (d_*/ρ_L) ∑_{1≤|γ|≤P₀+N} ρ_L^{|γ|} |∂^γ F[a](x)|`,
  `F = compField π`, by the componentwise bound `nativeStageLiftFamily_positive_glued_word_bound`,
  the Schur budget of the native matrix (`nativeSlotLift_uniform_matrix_schur_budget`) and the
  weighted word bound (`weakPositive_weighted_word_bound`,
  `weakPositive_weighted_input_density_le`);
* `passageLift_positive_partial_bound`: the same for the partial derivatives `∂^β`,
  `|β| ≤ P₀`, with one constant.

The chart jets at the lift radius are hypotheses here (they come from
`uniform_native_physical_flow_jets`). Special cases: `a t` constant (both sides vanish); no active
pulse; `r = 0` (the bound of the value of `(T - I)a` by the positive jets of `a`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison.Lift
  AVRegularity.Finite AVRegularity.Finite.WeakLift

namespace AVRegularity.IterationPassage.Passage

/-- The numeric price of a positive word of order `r`: chart transport and jet conversion. -/
def liftPositivePrice (C : ℝ) (P₀ N r : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r) *
    ((2 : ℝ) ^ (P₀ + N) * (((P₀ + N : ℕ) : ℝ) + 1) ^ 2)

/-- The path cost of the native matrix: scalar budget times the heights of the Schur budget. -/
def liftPositiveCost (P₀ Q Dm H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S : ℝ) : ℝ :=
  nativeLiftScalarBudget P₀ Q Dm H N CG Cw Cj * ∑ hh ∈ Finset.range (H + 1), S ^ hh

theorem liftPositivePrice_nonneg {C : ℝ} (hC : 1 ≤ C) (P₀ N r : ℕ) :
    0 ≤ liftPositivePrice C P₀ N r :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => nativeChartTransportConstant_nonneg hC _ _ _)
    (mul_nonneg (by positivity) (sq_nonneg _))

theorem liftPositiveCost_nonneg (P₀ Q Dm H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) {S : ℝ}
    (hS : 0 ≤ S) : 0 ≤ liftPositiveCost P₀ Q Dm H N CG Cw Cj S :=
  mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
    (Finset.sum_nonneg fun _ _ => pow_nonneg hS _)

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- A time with a nonzero cutoff lies in the cell window of the slot. -/
theorem passageLift_active_time (hc : 0 < D.cellScaleSq G.level)
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (t : ℝ) (j : ℤ)
    (hj : ocCutoff D.α D.q D.Λ G.level j t ≠ 0) :
    (D.cellScaleSq G.level)⁻¹ * t ∈
      Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩

/-- The passage lift minus its input is the glued lift of the positive coefficients. -/
theorem passageLift_positive_difference (hc : 0 < D.cellScaleSq G.level)
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hρ : liftLength D G.level ≠ 0) (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ) (x : Vec 2)
    (v : CompIn G.comps) :
    passageLift D G.level N H CcT a t x v - a t x v =
      passageLift D G.level N H (positiveLiftCoefficients CcT) a t x v := by
  classical
  have hdiff : passageLift D G.level N H CcT a t x v -
      passageLift D G.level N H (positiveLiftCoefficients CcT) a t x v = a t x v := by
    simp only [passageLift, gluedLift, Finset.sum_apply, Pi.smul_apply]
    rw [← Finset.sum_sub_distrib]
    trans ∑ j ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level j t • a t x v
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hw : ocCutoff D.α D.q D.Λ G.level j t = 0
      · simp only [hw, zero_smul, sub_self]
      · have hodd : Odd j := (Finset.mem_filter.mp hj).2.1
        rw [← smul_sub]
        apply congrArg (fun y : ℝ => ocCutoff D.α D.q D.Λ G.level j t • y)
        exact pulse_positive_difference_time _ sX sZ _ _ N H CcT j (hCcT j hodd)
          _ _ _ _ t hc.ne' hρ (passageLift_active_time hc hτ t j hw) _ _ a x
          (weak_chart_inverse D (G.level - 1) t (D.slotAnchor G.level j) x) v
    · rw [← Finset.sum_smul, obs_cutoff_sum_one _ _ _ _ _ hτ, one_smul]
  linarith only [hdiff]

/-- On the active pulses the positive coefficients are those of the native slot lifts. -/
theorem passageLift_positive_eq_native
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hc : 0 < D.cellScaleSq G.level) (hτ : 0 < ocTau D.α D.q D.Λ G.level) (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ) (x : Vec 2) :
    passageLift D G.level N H (positiveLiftCoefficients CcT) a t x = gluedLift
      (ocObsPulses D.α D.q D.Λ G.level t t) (fun j => ocCutoff D.α D.q D.Λ G.level j)
      (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level)
      (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
      N H (positiveLiftCoefficients (nativeStageLiftFamily slotLifts))
      (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
      (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') a t x := by
  classical
  apply gluedLift_coeff_congr
  intro j hj hcut hh hhh n _hn m α X z v' u
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  by_cases hn0 : n = 0
  · simp only [positiveLiftCoefficients, hn0, ite_true]
  · simp only [positiveLiftCoefficients, hn0, ite_false]
    exact nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hCcT
      j hjodd hh hhh n m α _ (passageLift_active_time hc hτ t j hcut) X z v' u

/-- **The positive word bound of the passage lift**, normalized coordinates. -/
theorem passageLift_positive_word_bound
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hterm : G.level ≤ D.term)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r ≤ P₀) (hrQ : r ≤ max k (L + 2))
    {C : ℝ} (hC : 1 ≤ C) (t : ℝ)
    (hJ : ∀ j : ℤ, Odd j → ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (P₀ + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (P₀ + N) C (liftLength D G.level))
    (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) (hp : IsZ2Periodic (a t))
    (β : DerivativeWord2 r) (x : Vec 2) :
    D.eps G.level ^ r * ‖orderedDerivative β (compField π
        (fun y => passageLift D G.level N H CcT a t y - a t y)) x‖ ≤
      (liftPositivePrice C P₀ N r * liftPositiveCost P₀ (max k (L + 2)) Dm H N CG Cw Cj S) *
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level) *
        ∑ γ ∈ multiIndicesBetween 1 (P₀ + N), liftLength D G.level ^ (γ 0 + γ 1) *
          ‖partialDerivative γ (compField π (a t)) x‖ := by
  classical
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have he : 0 < D.eps G.level := (slotLifts ⟨1, by decide⟩).setting.e_pos
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hπ : ∀ v, 0 < π v := (slotLifts ⟨1, by decide⟩).setting.mass_pos
  have hkap : D.kap G.level = D.κ G.level := by
    simp only [OCData.kap, Nat.min_eq_left hterm]
  have hprev : D.kap (G.level - 1) = D.κ (G.level - 1) := by
    simp only [OCData.kap, Nat.min_eq_left ((Nat.sub_le G.level 1).trans hterm)]
  have hε1 : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1 := by
    simpa only [hkap, hprev] using (slotLifts ⟨1, by decide⟩).setting.εc_le
  have hε : 0 ≤ ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level := div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) hρ.le
  have heρ : D.eps G.level ≤ liftLength D G.level :=
    cell_scale_le_lift_radius he.le (slotLifts ⟨1, by decide⟩).setting.ν_pos
      ((div_le_one (slotLifts ⟨1, by decide⟩).setting.B_pos).mp
        ((slotLifts ⟨1, by decide⟩).setting.η_eq.symm ▸ (slotLifts ⟨1, by decide⟩).setting.η_le)) hρ
      (by simpa only [ocDStar, OCData.eps] using (slotLifts ⟨1, by decide⟩).setting.εc_le)
  have hodd : ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t, Odd j :=
    fun j hj => (Finset.mem_filter.mp hj).2.1
  have hreg : ContDiff ℝ (r : ℕ∞)
      (fun y => passageLift D G.level N H CcT a t y - a t y) :=
    (regularLift_contDiff_periodic slotLifts hi hΛ hζ hband htorus P₀ hreserve r hrP hrQ sX sZ CcT
      hCcT a t ha hp).1.sub (ha.of_le (by exact_mod_cast hrP.trans (Nat.le_add_right P₀ N)))
  unfold liftPositivePrice liftPositiveCost
  set ε := ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level
    with hεdef
  set ct := ∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) r with hctdef
  set budget := nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj with hbudget
  set Yin := ∑ γ ∈ multiIndicesBetween 1 (P₀ + N), liftLength D G.level ^ (γ 0 + γ 1) *
    ‖partialDerivative γ (compField π (a t)) x‖ with hYin
  have hct : 0 ≤ ct := Finset.sum_nonneg fun n _ => nativeChartTransportConstant_nonneg hC _ _ _
  have hcost : 0 ≤ budget * ∑ hh ∈ Finset.range (H + 1), S ^ hh :=
    mul_nonneg (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
      (Finset.sum_nonneg fun _ _ => pow_nonneg hS _)
  have hb (v : CompIn G.comps) : D.eps G.level ^ r * ‖orderedDerivative β
      (fun X => (passageLift D G.level N H CcT a t X - a t X) v) x‖ ≤
      (ε * ct) * ∑ u, (∑ hh ∈ Finset.range (H + 1), budget *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) *
        (∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
          liftLength D G.level ^ j * ‖iteratedFDeriv ℝ j (fun X => a t X u) x‖) := by
    have hfun : (fun X => (passageLift D G.level N H CcT a t X - a t X) v) = fun Y => gluedLift
        (ocObsPulses D.α D.q D.Λ G.level t t) (fun j => ocCutoff D.α D.q D.Λ G.level j)
        (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level) ε
        N H (positiveLiftCoefficients (nativeStageLiftFamily slotLifts))
        (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
        (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') a t Y v := by
      funext X
      rw [Pi.sub_apply, passageLift_positive_difference hc hτ hρ.ne' sX sZ CcT hCcT a t X v,
        passageLift_positive_eq_native slotLifts hc hτ sX sZ CcT hCcT a t X]
    rw [hfun]
    exact nativeStageLiftFamily_positive_glued_word_bound slotLifts P₀ hreserve r hrP hrQ
      (ocObsPulses D.α D.q D.Λ G.level t t) hodd (fun j => ocCutoff D.α D.q D.Λ G.level j)
      (D.cellScaleSq G.level) ε t hc.ne' hε hε1 a ha
      (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
      (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') hC
      (fun j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
        (D.slotAnchor G.level j)).of_le (by simp))
      (fun j hj hw => (hJ j (hodd j hj) hw).1) he le_rfl heρ
      (fun j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level j) t).of_le (by simp))
      (fun j hj hw n hn hnr X => (hJ j (hodd j hj) hw).2 n hn
        (hnr.trans (hrP.trans (Nat.le_add_right P₀ N))) X)
      (fun j _ => Providers.CascadeInvariants.ocCutoff_nonneg j t)
      (le_of_eq (obs_cutoff_sum_one _ _ _ _ _ hτ)) β x
      (fun j _ _ => weak_chart_inverse D (G.level - 1) t (D.slotAnchor G.level j) x)
      (fun j _ hw => passageLift_active_time hc hτ t j hw) v
  have hpath : HasRealSchurBudget (massConjugatedMatrix π (fun v u =>
      ∑ hh ∈ Finset.range (H + 1), budget *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u))
      (budget * ∑ hh ∈ Finset.range (H + 1), S ^ hh) := by
    have hsum := finite_sum_real_schur_budget (Finset.range (H + 1))
      (fun hh => massConjugatedMatrix π (fun v u => budget *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u))
      (fun hh => budget * S ^ hh)
      (fun hh _ => nativeSlotLift_uniform_matrix_schur_budget
        (slotLifts ⟨1, by decide⟩) hS P₀ hh)
    have heq : (fun v u => ∑ hh ∈ Finset.range (H + 1), massConjugatedMatrix π (fun v u =>
        budget * finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam))
          hh v u) v u) =
        massConjugatedMatrix π (fun v u => ∑ hh ∈ Finset.range (H + 1), budget *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u) := by
      funext v u
      simp only [massConjugatedMatrix, Finset.mul_sum]
    rw [heq] at hsum
    simpa only [Finset.mul_sum] using hsum
  have hout := weakPositive_weighted_word_bound β π hπ
    (fun y => passageLift D G.level N H CcT a t y - a t y) hreg x he.le (mul_nonneg hε hct)
    hcost _ hpath _ hb
  have hin : Real.sqrt (∑ u, (π u)⁻¹ *
      (∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
        liftLength D G.level ^ j * ‖iteratedFDeriv ℝ j (fun X => a t X u) x‖) ^ 2) ≤
      ((2 : ℝ) ^ (P₀ + N) * (((P₀ + N : ℕ) : ℝ) + 1) ^ 2) * Yin :=
    weakPositive_weighted_input_density_le hρ.le π hπ (a t) ha x
  calc D.eps G.level ^ r * ‖orderedDerivative β (compField π
        (fun y => passageLift D G.level N H CcT a t y - a t y)) x‖
      ≤ (ε * ct) * (budget * ∑ hh ∈ Finset.range (H + 1), S ^ hh) *
        Real.sqrt (∑ u, (π u)⁻¹ *
          (∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else
            liftLength D G.level ^ j * ‖iteratedFDeriv ℝ j (fun X => a t X u) x‖) ^ 2) := hout
    _ ≤ (ε * ct) * (budget * ∑ hh ∈ Finset.range (H + 1), S ^ hh) *
        (((2 : ℝ) ^ (P₀ + N) * (((P₀ + N : ℕ) : ℝ) + 1) ^ 2) * Yin) :=
      mul_le_mul_of_nonneg_left hin (mul_nonneg (mul_nonneg hε hct) hcost)
    _ = _ := by ring

/-- **The positive bound of the passage lift for partial derivatives**, with one constant for
all orders `|β| ≤ P₀`. -/
theorem passageLift_positive_partial_bound
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hterm : G.level ≤ D.term)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hPQ : P₀ ≤ max k (L + 2))
    {C : ℝ} (hC : 1 ≤ C) (t : ℝ)
    (hJ : ∀ j : ℤ, Odd j → ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (P₀ + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (P₀ + N) C (liftLength D G.level))
    (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) (hp : IsZ2Periodic (a t))
    (β : Fin 2 → ℕ) (hβ : β 0 + β 1 ≤ P₀) (x : Vec 2) :
    D.eps G.level ^ (β 0 + β 1) * ‖partialDerivative β (compField π
        (fun y => passageLift D G.level N H CcT a t y - a t y)) x‖ ≤
      ((∑ r ∈ Finset.range (P₀ + 1), liftPositivePrice C P₀ N r) *
          liftPositiveCost P₀ (max k (L + 2)) Dm H N CG Cw Cj S) *
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level) *
        ∑ γ ∈ multiIndicesBetween 1 (P₀ + N), liftLength D G.level ^ (γ 0 + γ 1) *
          ‖partialDerivative γ (compField π (a t)) x‖ := by
  have he : 0 < D.eps G.level := (slotLifts ⟨1, by decide⟩).setting.e_pos
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hε : 0 ≤ ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level := div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) hρ.le
  have hY : 0 ≤ ∑ γ ∈ multiIndicesBetween 1 (P₀ + N), liftLength D G.level ^ (γ 0 + γ 1) *
      ‖partialDerivative γ (compField π (a t)) x‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hρ.le _) (norm_nonneg _)
  have heq : ![β 0, β 1] = β := by ext i; fin_cases i <;> rfl
  have hw := passageLift_positive_word_bound slotLifts hS hi hΛ hζ hband hterm htorus P₀ hreserve
    (β 0 + β 1) hβ (hβ.trans hPQ) hC t hJ sX sZ CcT hCcT a ha hp
    (Fin.append (fun _ : Fin (β 0) => (0 : Fin 2)) (fun _ : Fin (β 1) => (1 : Fin 2))) x
  rw [weakPositive_sorted_word_eq_partial, heq] at hw
  have hprice : liftPositivePrice C P₀ N (β 0 + β 1) ≤
      ∑ r ∈ Finset.range (P₀ + 1), liftPositivePrice C P₀ N r :=
    Finset.single_le_sum (fun r _ => liftPositivePrice_nonneg hC P₀ N r)
      (Finset.mem_range.mpr (by omega))
  exact hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hprice (liftPositiveCost_nonneg _ _ _ _ _ _ _ _ hS)) hε) hY)

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **Jets of the covariance polynomial against sup norms of order-`i` partials**

Abstract analysis on `Vec 2`-valued fields, no solution objects:

* `retCov_jet_le`: `‖D^n g(x)‖ ≤ 2^n ∑_{|α|=n} ‖∂^α g‖_∞` in `ℝ≥0∞`;
* `retCov_word_le`: for a word `β` of order `j`,
  `|∂^β (𝒫_p - I)(R ∘ g)(x)| ≤ ∑_{l=1}^p (4B)^l ‖R‖ ‖D^{j+2l} g(x)‖` when the entries of the
  covariance matrix are at most `B`; with `retCov_jet_le` the sup norm of `∂^a (𝒫_p - I)(R ∘ g)`,
  `|a| = j`, is at most `∑_{l=1}^p (4B)^l ‖R‖ 2^{j+2l} ∑_{|α|=j+2l} ‖∂^α g‖_∞`.

Special cases: `p = 0` (empty sum, `𝒫_0 = I`); `g` of degree `< 2` polynomial (vanishing
second jets) gives `0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.Finite.TerminalLift AVRegularity.Finite.WeakLift
  AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem retCov_mem_between_self {n : ℕ} (a b : ℕ) (hab : a + b = n) :
    (![a, b] : Fin 2 → ℕ) ∈ multiIndicesBetween n n := by
  simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, by omega, by omega⟩
  intro i
  fin_cases i <;> simp <;> omega

/-- The full derivative of order `n` at a point is controlled by the sup norms of the order-`n`
partial derivatives. -/
theorem retCov_jet_le {g : Vec 2 → V} {n : ℕ} (hg : ContDiff ℝ (n : ℕ∞) g) (x : Vec 2) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ n g x‖ ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∑ α ∈ multiIndicesBetween n n, supNorm (partialDerivative α g) := by
  have h1 := CycleWords.Assembly.norm_iteratedFDeriv_le_sum_thetaPartial hg x
  have h2 : ∀ a ∈ Finset.range (n + 1), ‖thetaPartial a (n - a) g x‖ =
      ‖partialDerivative ![a, n - a] g x‖ := by
    intro a ha
    have han : a + (n - a) = n := by have := Finset.mem_range.mp ha; omega
    rw [weakPositive_thetaPartial_eq_partial a (n - a) g (by rw [han]; exact hg)]
  have h3 : ∀ a ∈ Finset.range (n + 1), ENNReal.ofReal ‖partialDerivative ![a, n - a] g x‖ ≤
      supNorm (partialDerivative ![a, n - a] g) := by
    intro a _
    refine (ofReal_norm _).le.trans ?_
    exact le_iSup (fun y => (‖partialDerivative ![a, n - a] g y‖₊ : ℝ≥0∞)) x
  have hinj : Set.InjOn (fun a : ℕ => (![a, n - a] : Fin 2 → ℕ)) (Finset.range (n + 1) : Set ℕ) := by
    intro a ha b hb hab
    have := congrFun hab 0
    simpa using this
  calc ENNReal.ofReal ‖iteratedFDeriv ℝ n g x‖
      ≤ ENNReal.ofReal ((2 : ℝ) ^ n * ∑ a ∈ Finset.range (n + 1), ‖thetaPartial a (n - a) g x‖) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) *
          ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal ‖partialDerivative ![a, n - a] g x‖ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
          (fun _ _ => norm_nonneg _)]
        congr 1
        exact Finset.sum_congr rfl fun a ha => by rw [h2 a ha]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) *
          ∑ a ∈ Finset.range (n + 1), supNorm (partialDerivative ![a, n - a] g) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum h3)
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) *
          ∑ α ∈ (Finset.range (n + 1)).image (fun a : ℕ => (![a, n - a] : Fin 2 → ℕ)),
            supNorm (partialDerivative α g) := by
        rw [Finset.sum_image hinj]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset ?_)
        intro α hα
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hα
        exact retCov_mem_between_self a (n - a) (by have := Finset.mem_range.mp ha; omega)

/-- Pointwise word bound for `(𝒫_p - I)(R ∘ g)` against full jets of `g`. -/
theorem retCov_word_le (A : Matrix (Fin 2) (Fin 2) ℝ) (B Cn : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (p j : ℕ) {g : Vec 2 → V}
    (hg : ContDiff ℝ ((j + 2 * p : ℕ) : ℕ∞) g) (β : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedDerivative β (covPolyP A p (fun y => R (g y)) - fun y => R (g y)) x‖ ≤
      ∑ n ∈ Finset.range p, (4 * B) ^ (n + 1) * (Cn * ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) g x‖) := by
  let F : Vec 2 → W := fun y => R (g y)
  have hcoef1 (n : ℕ) : ((n + 1).factorial : ℝ)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    exact (div_le_one (by exact_mod_cast Nat.factorial_pos (n + 1))).mpr
      (by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (n + 1)))
  have hcoef (n : ℕ) : 0 ≤ ((n + 1).factorial : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hreg (n : ℕ) (hn : n ∈ Finset.range p) :
      ContDiff ℝ (j : ℕ∞) ((covOperator A)^[n + 1] F) := by
    apply covOperator_iterate_contDiff A (n + 1) j F
    exact (R.contDiff.comp hg).of_le (by exact_mod_cast
      (by have := Finset.mem_range.mp hn; omega : j + 2 * (n + 1) ≤ j + 2 * p))
  have he : orderedDerivative β (covPolyP A p F - F) = fun y => ∑ n ∈ Finset.range p,
      ((n + 1).factorial : ℝ)⁻¹ • orderedDerivative β ((covOperator A)^[n + 1] F) y := by
    rw [terminal_covariance_positive_expansion]
    simpa only [one_smul] using CoarseFluxDiff.orderedDerivative_sum_smul β
      (Finset.range p) 1 (fun n => ((n + 1).factorial : ℝ)⁻¹) hreg
  change ‖orderedDerivative β (covPolyP A p F - F) x‖ ≤ _
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hj : j + 2 * (n + 1) ≤ j + 2 * p := by have := Finset.mem_range.mp hn; omega
  have hi := terminal_covariance_iterate_word_bound A 1 B one_pos hB
    (by intro i k; simpa using hA i k) (n + 1) j F
    ((R.contDiff.comp hg).of_le (by exact_mod_cast hj)) β x
  have hnorm := R.norm_iteratedFDeriv_comp_left (n := j + 2 * (n + 1))
    (hg.contDiffAt (x := x)) (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoef n)]
  simp only [one_pow, one_mul] at hi
  calc ((n + 1).factorial : ℝ)⁻¹ * ‖orderedDerivative β ((covOperator A)^[n + 1] F) x‖
      ≤ 1 * ‖orderedDerivative β ((covOperator A)^[n + 1] F) x‖ :=
        mul_le_mul_of_nonneg_right (hcoef1 n) (norm_nonneg _)
    _ ≤ (4 * B) ^ (n + 1) * ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) F x‖ := by
        rw [one_mul]; exact hi
    _ ≤ (4 * B) ^ (n + 1) * (Cn * ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) g x‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
        exact hnorm.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The abstract profile bound of the retained covariance profile**.

`retCov_profile_bound`: let `g` be a field whose order-`i` partials obey a kernel bound
`∑_{|α|=i} ‖∂^α g‖_∞ ≤ C_k r^{ℓ-i} ∑_{|β|=ℓ} ‖∂^β W‖_∞` with `ℓ = min K i` (the output of
`passage_kernel_sup` for `g = S_r W`), let `R` be a bounded linear map and `A` a covariance matrix
with entries `≤ ε r²`, `r ≤ c₂ E`. Then the raw jet bound
`E^{|a|-s} ‖∂^a (𝒫_p - I)(R g)‖_∞ ≤ c ε [W]_{E,K;s}` holds for `|a| ≤ K`, with `c` explicit.
`retCov_profile_norm`: the same for `profileNorm`, by the existing jet packing.

Special cases: `p = 0` gives `0 ≤ …`; `ε = 0` gives `A = 0`, so both sides vanish. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.Finite.TerminalLift AVRegularity.Finite.WeakLift
  AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- Real algebra of one term: the powers of `r` and `E`. -/
theorem retCov_alg {E r ε Cc Cn Ck c₂ s : ℝ} {j a l M K : ℕ} (hE : 0 < E) (hr : 0 < r)
    (hrE : r ≤ c₂ * E) (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn)
    (hCk : 0 ≤ Ck) (hl : 1 ≤ l) (haK : a ≤ K) (hM : j + 2 * l ≤ M) :
    E ^ ((j : ℝ) - s) * ((4 * (ε * r ^ 2)) ^ l * Cn * 2 ^ (j + 2 * l) *
        (Ck * r ^ (((j + a : ℕ) : ℝ) - ((j + 2 * l : ℕ) : ℝ)))) ≤
      ε * (4 ^ l * Cc ^ (l - 1) * Cn * 2 ^ M * Ck * c₂ ^ K) * E ^ (((j + a : ℕ) : ℝ) - s) := by
  have hCc : 0 ≤ Cc := hε.trans hεC
  have hexp : (((j + a : ℕ) : ℝ) - ((j + 2 * l : ℕ) : ℝ)) = (a : ℝ) - ((2 * l : ℕ) : ℝ) := by
    push_cast; ring
  have hrpow : r ^ (((j + a : ℕ) : ℝ) - ((j + 2 * l : ℕ) : ℝ)) = r ^ a / r ^ (2 * l) := by
    rw [hexp, Real.rpow_sub hr, Real.rpow_natCast, Real.rpow_natCast]
  have hEa : E ^ ((j : ℝ) - s) * r ^ a ≤ c₂ ^ K * E ^ (((j + a : ℕ) : ℝ) - s) := by
    have h1 : r ^ a ≤ (c₂ * E) ^ a := pow_le_pow_left₀ hr.le hrE a
    have h2 : E ^ (((j + a : ℕ) : ℝ) - s) = E ^ ((j : ℝ) - s) * E ^ a := by
      have : (((j + a : ℕ) : ℝ) - s) = ((j : ℝ) - s) + (a : ℝ) := by push_cast; ring
      rw [this, Real.rpow_add_natCast hE.ne']
    have h3 : c₂ ^ a ≤ c₂ ^ K := pow_le_pow_right₀ hc₂ haK
    have hEp : 0 ≤ E ^ ((j : ℝ) - s) := Real.rpow_nonneg hE.le _
    calc E ^ ((j : ℝ) - s) * r ^ a ≤ E ^ ((j : ℝ) - s) * (c₂ * E) ^ a :=
          mul_le_mul_of_nonneg_left h1 hEp
      _ = c₂ ^ a * (E ^ ((j : ℝ) - s) * E ^ a) := by rw [mul_pow]; ring
      _ ≤ c₂ ^ K * (E ^ ((j : ℝ) - s) * E ^ a) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hEp (pow_nonneg hE.le _))
      _ = _ := by rw [h2]
  have hεl : ε ^ l ≤ ε * Cc ^ (l - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rw [pow_succ', Nat.add_sub_cancel]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε hεC k) hε
  have h2M : (2 : ℝ) ^ (j + 2 * l) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have hr2 : r ^ (2 * l) ≠ 0 := (pow_pos hr _).ne'
  have hmain : (4 * (ε * r ^ 2)) ^ l * (r ^ a / r ^ (2 * l)) = 4 ^ l * ε ^ l * r ^ a := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 l]
    field_simp
  rw [hrpow]
  have hcomb : (4 * (ε * r ^ 2)) ^ l * Cn * 2 ^ (j + 2 * l) * (Ck * (r ^ a / r ^ (2 * l))) =
      (4 ^ l * ε ^ l * Cn * 2 ^ (j + 2 * l) * Ck) * r ^ a := by
    calc _ = ((4 * (ε * r ^ 2)) ^ l * (r ^ a / r ^ (2 * l))) * Cn * 2 ^ (j + 2 * l) * Ck := by ring
      _ = _ := by rw [hmain]; ring
  rw [hcomb]
  have hEp : 0 ≤ E ^ ((j : ℝ) - s) := Real.rpow_nonneg hE.le _
  calc E ^ ((j : ℝ) - s) * ((4 ^ l * ε ^ l * Cn * 2 ^ (j + 2 * l) * Ck) * r ^ a)
      = (4 ^ l * ε ^ l * Cn * 2 ^ (j + 2 * l) * Ck) * (E ^ ((j : ℝ) - s) * r ^ a) := by ring
    _ ≤ (4 ^ l * ε ^ l * Cn * 2 ^ (j + 2 * l) * Ck) * (c₂ ^ K * E ^ (((j + a : ℕ) : ℝ) - s)) :=
        mul_le_mul_of_nonneg_left hEa (by positivity)
    _ ≤ (4 ^ l * (ε * Cc ^ (l - 1)) * Cn * 2 ^ M * Ck) * (c₂ ^ K * E ^ (((j + a : ℕ) : ℝ) - s)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        gcongr
    _ = _ := by ring

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The abstract profile bound of the retained covariance profile**.

`retCov_raw_bound`: let `g` be a field whose order-`i` partials obey a kernel bound
`∑_{|α|=i} ‖∂^α g‖_∞ ≤ C_k r^{ℓ-i} ∑_{|β|=ℓ} ‖∂^β W‖_∞` with `ℓ = min K i` (the output of
`passage_kernel_sup` for `g = S_r W`), let `R` be a bounded linear map and `A` a covariance matrix
with entries `≤ ε r²`, `r ≤ c₂ E`. Then the raw jet bound
`E^{|a|-s} ‖∂^a (𝒫_p - I)(R g)‖_∞ ≤ c ε [W]_{E,K;s}` holds for `|a| ≤ K` (`RawProfileJetBound`).
`retCov_profile_norm`: the same for `profileNorm`, by the existing jet packing.

Special cases: `p = 0` gives `0 ≤ …`; `ε = 0` gives `A = 0`, so both sides vanish. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.Finite AVRegularity.Finite.TerminalLift AVRegularity.Finite.WeakLift
  AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- The constant of the retained covariance profile bound. -/
def retCovConst (Cn Cc Ck c₂ : ℝ) (K p : ℕ) : ℝ :=
  (∑ n ∈ Finset.range p, 4 ^ (n + 1) * Cc ^ n) * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K * (K.factorial : ℝ)

theorem retCov_mem_between_one {K ℓ : ℕ} (h1 : 1 ≤ ℓ) (hK : ℓ ≤ K) {β : Fin 2 → ℕ}
    (hβ : β ∈ multiIndicesBetween ℓ ℓ) : β ∈ multiIndicesBetween 1 K := by
  simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hβ ⊢
  exact ⟨fun i => (hβ.1 i).trans_le (by omega), by omega, by omega⟩

/-- A fixed-order block of sup norms is controlled by the profile seminorm. -/
theorem retCov_block_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {E s : ℝ} (hE : 0 < E)
    {K ℓ : ℕ} (h1 : 1 ≤ ℓ) (hK : ℓ ≤ K) (W : Vec 2 → V) :
    ENNReal.ofReal (E ^ ((ℓ : ℝ) - s)) * ∑ β ∈ multiIndicesBetween ℓ ℓ, supNorm (partialDerivative β W) ≤
      ENNReal.ofReal (K.factorial : ℝ) * profileSeminorm E K s W := by
  rw [Finset.mul_sum, profileSeminorm, Finset.mul_sum]
  calc ∑ β ∈ multiIndicesBetween ℓ ℓ, ENNReal.ofReal (E ^ ((ℓ : ℝ) - s)) * supNorm (partialDerivative β W)
      ≤ ∑ β ∈ multiIndicesBetween ℓ ℓ, ENNReal.ofReal (K.factorial : ℝ) *
          (ENNReal.ofReal (E ^ (((β 0 + β 1 : ℕ) : ℝ) - s) / multiIndexFactorial β) *
            supNorm (partialDerivative β W)) := by
        refine Finset.sum_le_sum fun β hβ => ?_
        have hs : β 0 + β 1 = ℓ := by
          simp only [multiIndicesBetween, Finset.mem_filter] at hβ; omega
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hs]
        have hf : 0 < multiIndexFactorial β := by
          simp only [multiIndexFactorial, Fin.prod_univ_two]; positivity
        have hfa : multiIndexFactorial β ≤ (K.factorial : ℝ) := by
          simp only [multiIndexFactorial, Fin.prod_univ_two]
          have : (β 0).factorial * (β 1).factorial ∣ (β 0 + β 1).factorial :=
            Nat.factorial_mul_factorial_dvd_factorial_add _ _
          have h2 : (β 0).factorial * (β 1).factorial ≤ K.factorial :=
            (Nat.le_of_dvd (Nat.factorial_pos _) this).trans (Nat.factorial_le (by omega))
          exact_mod_cast h2
        have hEp : 0 ≤ E ^ ((ℓ : ℝ) - s) := Real.rpow_nonneg hE.le _
        rw [mul_div_assoc', le_div_iff₀ hf]
        exact mul_le_mul_of_nonneg_left hfa hEp |>.trans_eq (by ring)
    _ ≤ ∑ β ∈ multiIndicesBetween 1 K, ENNReal.ofReal (K.factorial : ℝ) *
          (ENNReal.ofReal (E ^ (((β 0 + β 1 : ℕ) : ℝ) - s) / multiIndexFactorial β) *
            supNorm (partialDerivative β W)) :=
        Finset.sum_le_sum_of_subset fun β hβ => retCov_mem_between_one h1 hK hβ

/-- The sup of a pointwise bound. -/
theorem retCov_sup_le {V : Type*} [NormedAddCommGroup V] (F : Vec 2 → V) (c : ℝ≥0∞) (Y : ℝ≥0∞)
    (h : ∀ x, c * ENNReal.ofReal ‖F x‖ ≤ Y) : c * supNorm F ≤ Y := by
  unfold supNorm
  rw [ENNReal.mul_iSup]
  refine iSup_le fun x => ?_
  have := h x
  rwa [ofReal_norm] at this

theorem retCov_ofReal_comb (a b c d : ℝ) (S : ℝ≥0∞) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * (ENNReal.ofReal d * S))) =
      ENNReal.ofReal (a * (b * c * d)) * S := by
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul (mul_nonneg hb hc), ENNReal.ofReal_mul hb]
  ring

section Main

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- One term of the word bound, in `ℝ≥0∞`. -/
theorem retCov_term_le {E r ε Cc Cn Ck c₂ s : ℝ} {K p : ℕ} (hE : 0 < E) (hr : 0 < r)
    (hrE : r ≤ c₂ * E) (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck)
    (hK : 1 ≤ K) {j n : ℕ} (hj : j ≤ K) (hn : n < p) (g Wf : Vec 2 → V) (x : Vec 2)
    (hg : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf)) :
    ENNReal.ofReal (E ^ ((j : ℝ) - s)) *
        (ENNReal.ofReal ((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) *
          ENNReal.ofReal ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) g x‖) ≤
      ENNReal.ofReal (ε * (4 ^ (n + 1) * Cc ^ n * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K) *
        (K.factorial : ℝ)) * profileSeminorm E K s Wf := by
  set i := j + 2 * (n + 1) with hi
  have hi2 : 2 ≤ i := by omega
  have hiM : i ≤ K + 2 * p := by omega
  have hgi : ContDiff ℝ (i : ℕ∞) g := hg.of_le (by exact_mod_cast hiM)
  have hjet := retCov_jet_le hgi x
  have hk := hker i hi2 hiM
  obtain ⟨a, ha⟩ : ∃ a, min K i = j + a := ⟨min K i - j, by omega⟩
  have haK : a ≤ K := by omega
  have hℓ1 : 1 ≤ j + a := by omega
  have hℓK : j + a ≤ K := by omega
  rw [ha] at hk
  have hCc : 0 ≤ Cc := hε.trans hεC
  have hc₂0 : 0 ≤ c₂ := by linarith
  have hE0 : 0 ≤ E := hE.le
  have hr0 : 0 ≤ r := hr.le
  have hblock := retCov_block_le (s := s) hE hℓ1 hℓK Wf
  have halg := retCov_alg (s := s) (j := j) (a := a) (l := n + 1) (M := K + 2 * p) (K := K) hE hr hrE hc₂ hε hεC
    hCn hCk (by omega) haK (by omega)
  rw [Nat.add_sub_cancel] at halg
  set SW := ∑ β ∈ multiIndicesBetween (j + a) (j + a), supNorm (partialDerivative β Wf) with hSW
  have hCk' : 0 ≤ Ck * r ^ (((j + a : ℕ) : ℝ) - (i : ℝ)) := mul_nonneg hCk (Real.rpow_nonneg hr.le _)
  calc ENNReal.ofReal (E ^ ((j : ℝ) - s)) *
        (ENNReal.ofReal ((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) * ENNReal.ofReal ‖iteratedFDeriv ℝ i g x‖)
      ≤ ENNReal.ofReal (E ^ ((j : ℝ) - s)) *
        (ENNReal.ofReal ((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) *
          (ENNReal.ofReal ((2 : ℝ) ^ i) * (ENNReal.ofReal (Ck * r ^ (((j + a : ℕ) : ℝ) - (i : ℝ))) * SW))) := by
        gcongr
        exact hjet.trans (mul_le_mul' le_rfl hk)
    _ = ENNReal.ofReal ((E ^ ((j : ℝ) - s)) * (((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) * 2 ^ i *
          (Ck * r ^ (((j + a : ℕ) : ℝ) - (i : ℝ))))) * SW :=
        retCov_ofReal_comb (E ^ ((j : ℝ) - s)) ((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) (2 ^ i)
          (Ck * r ^ (((j + a : ℕ) : ℝ) - (i : ℝ))) SW (Real.rpow_nonneg hE.le _) (by positivity)
          (by positivity)
    _ ≤ ENNReal.ofReal (ε * (4 ^ (n + 1) * Cc ^ n * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K) *
          E ^ (((j + a : ℕ) : ℝ) - s)) * SW := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal halg) le_rfl
    _ = ENNReal.ofReal (ε * (4 ^ (n + 1) * Cc ^ n * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K)) *
          (ENNReal.ofReal (E ^ (((j + a : ℕ) : ℝ) - s)) * SW) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ ENNReal.ofReal (ε * (4 ^ (n + 1) * Cc ^ n * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K)) *
          (ENNReal.ofReal (K.factorial : ℝ) * profileSeminorm E K s Wf) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- A jet of the retained covariance profile, against the profile seminorm of the input. -/
theorem retCov_word_bound {E r ε Cc Cn Ck c₂ s : ℝ} {K p : ℕ} (hE : 0 < E) (hr : 0 < r)
    (hrE : r ≤ c₂ * E) (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck)
    (hK : 1 ≤ K) (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, |A i j| ≤ ε * r ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (g Wf : Vec 2 → V)
    (hg : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf))
    {j : ℕ} (hj : j ≤ K) (β : DerivativeWord2 j) (x : Vec 2) :
    ENNReal.ofReal (E ^ ((j : ℝ) - s)) *
        ENNReal.ofReal ‖orderedDerivative β (covPolyP A p (fun y => R (g y)) - fun y => R (g y)) x‖ ≤
      ENNReal.ofReal (retCovConst Cn Cc Ck c₂ K p * ε) * profileSeminorm E K s Wf := by
  have hB : 0 ≤ ε * r ^ 2 := by positivity
  have hgj : ContDiff ℝ ((j + 2 * p : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast (by omega : j + 2 * p ≤ K + 2 * p))
  have hw := retCov_word_le A (ε * r ^ 2) Cn hB hA R hR p j hgj β x
  have hCc : 0 ≤ Cc := hε.trans hεC
  have hc₂0 : 0 ≤ c₂ := by linarith
  have hE0 : 0 ≤ E := hE.le
  have hr0 : 0 ≤ r := hr.le
  calc ENNReal.ofReal (E ^ ((j : ℝ) - s)) * ENNReal.ofReal ‖orderedDerivative β _ x‖
      ≤ ENNReal.ofReal (E ^ ((j : ℝ) - s)) * ENNReal.ofReal (∑ n ∈ Finset.range p,
          (4 * (ε * r ^ 2)) ^ (n + 1) * (Cn * ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) g x‖)) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hw)
    _ = ∑ n ∈ Finset.range p, ENNReal.ofReal (E ^ ((j : ℝ) - s)) *
          (ENNReal.ofReal ((4 * (ε * r ^ 2)) ^ (n + 1) * Cn) *
            ENNReal.ofReal ‖iteratedFDeriv ℝ (j + 2 * (n + 1)) g x‖) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity), Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← mul_assoc ((4 * (ε * r ^ 2)) ^ (n + 1)), ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∑ n ∈ Finset.range p, ENNReal.ofReal (ε * (4 ^ (n + 1) * Cc ^ n * Cn * 2 ^ (K + 2 * p) * Ck * c₂ ^ K) *
          (K.factorial : ℝ)) * profileSeminorm E K s Wf := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact retCov_term_le hE hr hrE hc₂ hε hεC hCn hCk hK hj (Finset.mem_range.mp hn) g Wf x hg hker
    _ = _ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
        congr 2
        unfold retCovConst
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring

theorem retCov_zero_word : ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : Vec 2 → F)
    (β : DerivativeWord2 0), orderedDerivative β G = G := by
  intro F _ _ G β
  simp [orderedDerivative]

/-- **The raw jet bound of the retained covariance profile.** -/
theorem retCov_raw_bound {E r ε Cc Cn Ck c₂ s : ℝ} {K p : ℕ} (hE : 0 < E) (hr : 0 < r)
    (hrE : r ≤ c₂ * E) (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck)
    (hK : 1 ≤ K) (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, |A i j| ≤ ε * r ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (g Wf : Vec 2 → V)
    (hg : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf)) :
    RawProfileJetBound E K s (covPolyP A p (fun y => R (g y)) - fun y => R (g y))
      (ENNReal.ofReal (retCovConst Cn Cc Ck c₂ K p * ε) * profileSeminorm E K s Wf) := by
  have hw := fun {j : ℕ} (hj : j ≤ K) (β : DerivativeWord2 j) (x : Vec 2) =>
    retCov_word_bound (s := s) hE hr hrE hc₂ hε hεC hCn hCk hK A hA R hR g Wf hg hker hj β x
  refine ⟨?_, ?_⟩
  · refine retCov_sup_le _ _ _ fun x => ?_
    have := hw (Nat.zero_le K) (fun i => i.elim0) x
    rwa [retCov_zero_word, Nat.cast_zero, zero_sub] at this
  · intro a ha
    have hj : a 0 + a 1 ≤ K := (Finset.mem_filter.mp ha).2.2
    refine retCov_sup_le _ _ _ fun x => ?_
    have hword := hw hj (Fin.append (fun _ : Fin (a 0) => (0 : Fin 2)) (fun _ : Fin (a 1) => (1 : Fin 2))) x
    have heq : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
    rw [weakPositive_sorted_word_eq_partial, ← heq] at hword
    exact hword

/-- **The profile norm bound of the retained covariance profile.** -/
theorem retCov_profile_norm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {E r ε Cc Cn Ck c₂ s : ℝ} {K p : ℕ} (hE : 0 < E) (hr : 0 < r)
    (hrE : r ≤ c₂ * E) (hc₂ : 1 ≤ c₂) (hε : 0 ≤ ε) (hεC : ε ≤ Cc) (hCn : 0 ≤ Cn) (hCk : 0 ≤ Ck)
    (hK : 1 ≤ K) (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, |A i j| ≤ ε * r ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ Cn) (g Wf : Vec 2 → V)
    (hg : ContDiff ℝ ((K + 2 * p : ℕ) : ℕ∞) g)
    (hker : ∀ i, 2 ≤ i → i ≤ K + 2 * p →
      ∑ α ∈ multiIndicesBetween i i, supNorm (partialDerivative α g) ≤
        ENNReal.ofReal (Ck * r ^ (((min K i : ℕ) : ℝ) - (i : ℝ))) *
          ∑ β ∈ multiIndicesBetween (min K i) (min K i), supNorm (partialDerivative β Wf)) :
    profileNorm E K s (covPolyP A p (fun y => R (g y)) - fun y => R (g y)) ≤
      (profileJetCount K : ℝ≥0∞) *
        (ENNReal.ofReal (retCovConst Cn Cc Ck c₂ K p * ε) * profileSeminorm E K s Wf) :=
  profile_jet_packing (H := W) E s K K _ _ hE le_rfl
    (retCov_raw_bound hE hr hrE hc₂ hε hεC hCn hCk hK A hA R hR g Wf hg hker)

end Main

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The retained lift profile at one stage**.

* `liftProfile_point_le`, `liftProfile_norm_le`: abstract packing. If the scaled jets of `F` are
  bounded pointwise by `C_P (d_*/ρ) Y_in(x)` (the positive bound of the lift), `Y_in` by
  `C_in ρ E^{s-1} P` (the input bound) and `e^{-s} d_* E^{s-1} ≤ C_sc E^μ` (the scale), then
  `𝓘_{e,K;s}(F) ≤ #jets · C_P C_in C_sc E^μ P` (`profile_jet_packing`).
* `passageLift_scale`: `e^{-s} d_* E^{s-1} ≤ C E^{μ_s}` along a band chain, from
  `√(κ_{m-1}/κ_m) ≤ C E^{-qγ}` (`bandChain_uniform_ledger`) and `e ≤ 2E^q` (`epsilon_q_step`).
* `liftSchedule_exponents`: `2σ₀ ≤ δ` and `σ₀N ≤ c(K-1)` from the schedule
  (`σ₀D_* ≤ δ/8`, `N ≤ D_*`, `3 ≤ K`, `c = γ/2 + δ`).
* `retainedLift_at_stage`: the profile bound for the slot lifts of a stage, with the input
  bound and the scale as hypotheses.

Special cases: a constant input (`Y_in = 0`, the profile vanishes); `P = ∞`; `K = 0` (only the
value term). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison.Lift
  AVRegularity.Finite AVRegularity.Finite.WeakLift
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- One jet of the profile: positive bound, input bound and scale. -/
theorem liftProfile_point_le {e E ρ dstar s μ CP Cin Csc Yin n : ℝ} {b : ℕ} {P : ℝ≥0∞}
    (he : 0 < e) (hρ : 0 < ρ) (hCP : 0 ≤ CP) (hCin : 0 ≤ Cin) (hd : 0 ≤ dstar)
    (hP : e ^ b * n ≤ CP * (dstar / ρ) * Yin)
    (hKS : ENNReal.ofReal Yin ≤ ENNReal.ofReal (Cin * (ρ * E ^ (s - 1))) * P)
    (hSC : e ^ (-s) * dstar * E ^ (s - 1) ≤ Csc * E ^ μ) :
    ENNReal.ofReal (e ^ ((b : ℝ) - s)) * ENNReal.ofReal n ≤
      ENNReal.ofReal (CP * Cin * Csc * E ^ μ) * P := by
  have hes : 0 ≤ e ^ (-s) := Real.rpow_nonneg he.le _
  have hsplit : e ^ ((b : ℝ) - s) = e ^ (-s) * e ^ b := by
    rw [sub_eq_add_neg, Real.rpow_add he, Real.rpow_natCast]
    ring
  have hc0 : 0 ≤ e ^ (-s) * (CP * (dstar / ρ)) := by positivity
  have hcancel : dstar / ρ * ρ = dstar := div_mul_cancel₀ _ hρ.ne'
  calc ENNReal.ofReal (e ^ ((b : ℝ) - s)) * ENNReal.ofReal n
      = ENNReal.ofReal (e ^ (-s) * (e ^ b * n)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg he.le _), hsplit, mul_assoc]
    _ ≤ ENNReal.ofReal (e ^ (-s) * (CP * (dstar / ρ) * Yin)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hP hes)
    _ = ENNReal.ofReal (e ^ (-s) * (CP * (dstar / ρ))) * ENNReal.ofReal Yin := by
        rw [← ENNReal.ofReal_mul hc0]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (e ^ (-s) * (CP * (dstar / ρ))) *
        (ENNReal.ofReal (Cin * (ρ * E ^ (s - 1))) * P) := mul_le_mul' le_rfl hKS
    _ = ENNReal.ofReal (CP * Cin * (e ^ (-s) * dstar * E ^ (s - 1))) * P := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc0]
        congr 2
        calc e ^ (-s) * (CP * (dstar / ρ)) * (Cin * (ρ * E ^ (s - 1)))
            = CP * Cin * (e ^ (-s) * (dstar / ρ * ρ) * E ^ (s - 1)) := by ring
          _ = _ := by rw [hcancel]
    _ ≤ ENNReal.ofReal (CP * Cin * Csc * E ^ μ) * P := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        calc CP * Cin * (e ^ (-s) * dstar * E ^ (s - 1)) ≤ CP * Cin * (Csc * E ^ μ) :=
              mul_le_mul_of_nonneg_left hSC (mul_nonneg hCP hCin)
          _ = _ := by ring

/-- The profile norm from the pointwise positive bound, the input bound and the scale. -/
theorem liftProfile_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e E ρ dstar s μ CP Cin Csc : ℝ} {K : ℕ} (F : Vec 2 → H) (Yin : Vec 2 → ℝ) (P : ℝ≥0∞)
    (he : 0 < e) (hρ : 0 < ρ) (hCP : 0 ≤ CP) (hCin : 0 ≤ Cin) (hd : 0 ≤ dstar)
    (hP : ∀ β : Fin 2 → ℕ, β 0 + β 1 ≤ K → ∀ x,
      e ^ (β 0 + β 1) * ‖partialDerivative β F x‖ ≤ CP * (dstar / ρ) * Yin x)
    (hKS : ∀ x, ENNReal.ofReal (Yin x) ≤ ENNReal.ofReal (Cin * (ρ * E ^ (s - 1))) * P)
    (hSC : e ^ (-s) * dstar * E ^ (s - 1) ≤ Csc * E ^ μ) :
    profileNorm e K s F ≤
      (profileJetCount K : ℝ≥0∞) * (ENNReal.ofReal (CP * Cin * Csc * E ^ μ) * P) := by
  refine profile_jet_packing (H := H) e s K K F _ he le_rfl ⟨?_, ?_⟩
  · refine retCov_sup_le _ _ _ fun x => ?_
    have h0 : partialDerivative (![0, 0] : Fin 2 → ℕ) F = F := by
      rw [← weakPositive_sorted_word_eq_partial 0 0 F]
      exact retCov_zero_word F _
    have hP0 : e ^ 0 * ‖F x‖ ≤ CP * (dstar / ρ) * Yin x := by
      have h := hP ![0, 0] (Nat.zero_le K) x
      rw [h0] at h
      exact h
    have h := liftProfile_point_le (b := 0) he hρ hCP hCin hd hP0 (hKS x) hSC
    simpa only [Nat.cast_zero, zero_sub] using h
  · intro a ha
    have hj : a 0 + a 1 ≤ K := (Finset.mem_filter.mp ha).2.2
    refine retCov_sup_le _ _ _ fun x => ?_
    exact liftProfile_point_le he hρ hCP hCin hd (hP a hj x) (hKS x) hSC

/-- **The scale of the retained lift profile**: `e^{-s} d_* E^{s-1} ≤ C E^{μ_s}`. -/
theorem passageLift_scale (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
    ∀ M : ℕ, IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ m : ℕ, 2 ≤ m → m ≤ M →
      D.eps m ^ (-s) * ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) * D.eps (m - 1) ^ (s - 1) ≤
        C * D.eps (m - 1) ^ ocMuS α q s := by
  obtain ⟨Cl, hCl, Λl, hΛl, hled⟩ :=
    CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨2 * Cl, by linarith, Λl, hΛl, ?_⟩
  intro Λ hΛ D hDα hDq hDΛ hDζ M hband _hterm m hm2 hmM
  subst hDα hDq hDΛ hDζ
  have hΛ128 : 128 ≤ D.Λ := hΛl.trans hΛ
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hk := (hled D.Λ hΛ M (by omega) D.κ hband).2 m hm2 hmM (D.κ m) (D.κ (m - 1)) rfl rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsq, _, _, _, _⟩ := hk
  have he : 0 < D.eps m := Construction.Stream.ocEpsilon_pos hΛ1
  have hE : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hstep : D.eps m ≤ 2 * D.eps (m - 1) ^ D.q :=
    Scales.epsilon_q_step hq.1 hq.2.1 hΛ128 (by omega)
  have hs1' : s < 1 := by linarith
  exact liftScale_alg (γ := ocGamma D.α D.q) he hE hs₀.le hs1' hstep (Real.sqrt_nonneg _) hsq

/-- The exponent conditions of the retained lift from the schedule. -/
theorem liftSchedule_exponents {σ₀ δ γ : ℝ} {K N Dstar : ℕ} (hσ : 0 ≤ σ₀) (hδ : 0 < δ)
    (hγ : 0 ≤ γ) (hK : 3 ≤ K) (hN : N ≤ Dstar) (h2 : 2 ≤ Dstar) (hσD : σ₀ * Dstar ≤ δ / 8) :
    2 * σ₀ ≤ δ ∧ σ₀ * N ≤ (γ / 2 + δ) * ((K - 1 : ℕ) : ℝ) := by
  have hD2 : (2 : ℝ) ≤ Dstar := by exact_mod_cast h2
  have hND : (N : ℝ) ≤ Dstar := by exact_mod_cast hN
  have hK2 : (2 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ K - 1)
  have h1 : 2 * σ₀ ≤ σ₀ * Dstar := by
    rw [mul_comm 2 σ₀]
    exact mul_le_mul_of_nonneg_left hD2 hσ
  have h2' : σ₀ * N ≤ σ₀ * Dstar := mul_le_mul_of_nonneg_left hND hσ
  have h3 : δ * 2 ≤ (γ / 2 + δ) * ((K - 1 : ℕ) : ℝ) :=
    mul_le_mul (by linarith) hK2 (by norm_num) (by linarith)
  exact ⟨by linarith, by linarith⟩

theorem liftPositiveCost_mono (P₀ Q Dm H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) {S S' : ℝ}
    (hS : 0 ≤ S) (hSS : S ≤ S') :
    liftPositiveCost P₀ Q Dm H N CG Cw Cj S ≤ liftPositiveCost P₀ Q Dm H N CG Cw Cj S' :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun hh _ => pow_le_pow_left₀ hS hSS hh)
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))

/-- The constant of the retained lift profile at a stage. -/
def liftProfileConst (Cχ : ℝ) (K Q Dm H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Sb Cin Csc : ℝ) : ℝ :=
  (profileJetCount K : ℝ) * ((∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r) *
    liftPositiveCost K Q Dm H N CG Cw Cj Sb * Cin * Csc)

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {H N Kp k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- **The retained lift profile at a stage**, with the input bound and the scale as hypotheses. -/
theorem retainedLift_at_stage
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N Kp k L CG Cw Cj S)
    {Sb : ℝ} (hS : 0 ≤ S) (hSb : S ≤ Sb) (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hterm : G.level ≤ D.term)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (K : ℕ) (hreserve : ∀ slot : OddSlot, K + (N + (slotLifts slot).cap) ≤
      Kp + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hKQ : K ≤ max k (L + 2)) {Cχ : ℝ} (hCχ : 1 ≤ Cχ) (t : ℝ)
    (hJ : ∀ j : ℤ, Odd j → ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (K + N) Cχ (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (K + N) Cχ (liftLength D G.level))
    (sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hCcT : IsPassageLift G G.level N H sX sZ CcT)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (hg : ContDiff ℝ ((K + N : ℕ) : ℕ∞) (g t)) (hgp : IsZ2Periodic (g t))
    {s μ Cin Csc : ℝ} (hCin : 0 ≤ Cin) (P : ℝ≥0∞)
    (hKS : ∀ x, ENNReal.ofReal (∑ γ ∈ multiIndicesBetween 1 (K + N),
        liftLength D G.level ^ (γ 0 + γ 1) * ‖partialDerivative γ (compField π (g t)) x‖) ≤
      ENNReal.ofReal (Cin * (liftLength D G.level * D.eps (G.level - 1) ^ (s - 1))) * P)
    (hSC : D.eps G.level ^ (-s) * ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) *
      D.eps (G.level - 1) ^ (s - 1) ≤ Csc * D.eps (G.level - 1) ^ μ)
    {C : ℝ} (hC : liftProfileConst Cχ K (max k (L + 2)) Dm H N CG Cw Cj Sb Cin Csc ≤ C) :
    profileNorm (D.eps G.level) K s (compField π
        (fun y => passageLift D G.level N H CcT g t y - g t y)) ≤
      ENNReal.ofReal (C * D.eps (G.level - 1) ^ μ) * P := by
  have he : 0 < D.eps G.level := (slotLifts ⟨1, by decide⟩).setting.e_pos
  have hρ : 0 < liftLength D G.level := (slotLifts ⟨1, by decide⟩).setting.ρ_pos
  have hE : 0 < D.eps (G.level - 1) := (slotLifts ⟨1, by decide⟩).setting.E_pos
  have hd : 0 ≤ ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) :=
    mul_nonneg he.le (Real.sqrt_nonneg _)
  have hε : 0 ≤ ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level := div_nonneg hd hρ.le
  have hprice : 0 ≤ ∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r :=
    Finset.sum_nonneg fun r _ => liftPositivePrice_nonneg hCχ K N r
  have hcost := liftPositiveCost_mono K (max k (L + 2)) Dm H N CG Cw Cj hS hSb
  have hCP : 0 ≤ (∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r) *
      liftPositiveCost K (max k (L + 2)) Dm H N CG Cw Cj Sb :=
    mul_nonneg hprice (liftPositiveCost_nonneg _ _ _ _ _ _ _ _ (hS.trans hSb))
  have hmain := liftProfile_norm_le (s := s) (μ := μ) (Csc := Csc) (K := K)
    (compField π (fun y => passageLift D G.level N H CcT g t y - g t y))
    (fun x => ∑ γ ∈ multiIndicesBetween 1 (K + N), liftLength D G.level ^ (γ 0 + γ 1) *
      ‖partialDerivative γ (compField π (g t)) x‖) P he hρ hCP hCin hd
    (fun β hβ x => (passageLift_positive_partial_bound slotLifts hS hi hΛ hζ hband hterm htorus
      K hreserve hKQ hCχ t hJ sX sZ CcT hCcT g hg hgp β hβ x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcost hprice) hε)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hρ.le _) (norm_nonneg _))))
    hKS hSC
  refine hmain.trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc (profileJetCount K : ℝ) * ((∑ r ∈ Finset.range (K + 1), liftPositivePrice Cχ K N r) *
        liftPositiveCost K (max k (L + 2)) Dm H N CG Cw Cj Sb * Cin * Csc *
          D.eps (G.level - 1) ^ μ)
      = liftProfileConst Cχ K (max k (L + 2)) Dm H N CG Cw Cj Sb Cin Csc *
        D.eps (G.level - 1) ^ μ := by unfold liftProfileConst; ring
    _ ≤ C * D.eps (G.level - 1) ^ μ :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hE.le _)

end AVRegularity.IterationPassage.Passage
end
end
end

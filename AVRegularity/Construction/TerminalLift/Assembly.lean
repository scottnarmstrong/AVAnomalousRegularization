-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.EntryWeak.FluxProductionArithmetic

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.Construction.TerminalLift

/-! The terminal band lower bound supplies a uniform balanced drift certificate on
both the terminal level and the plateau. The terminal and weak physical radii
also satisfy the setting scale clauses. These bounds precede the datum and phase. -/

open Preservation.FullLift EntryWeakProofs

private theorem plateau_peclet_of_band_lower (x y ν p γ : ℝ)
    (hx : 0 ≤ x) (hy : 0 < y) (hy1 : y ≤ 1) (hxy : x ≤ y)
    (hp : 0 ≤ p) (hγ : 0 ≤ γ) (hν : 0 < ν) (hlower : y ^ (p - γ) / 2 ≤ ν) :
    x ^ p / ν ≤ 2 := by
  apply (div_le_iff₀ hν).mpr
  have hsplit : y ^ p = y ^ (p - γ) * y ^ γ := by
    rw [← Real.rpow_add hy]
    congr 1
    ring
  calc
    x ^ p ≤ y ^ p := Real.rpow_le_rpow hx hxy hp
    _ = y ^ (p - γ) * y ^ γ := hsplit
    _ ≤ y ^ (p - γ) * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one hy.le hy1 hγ) (Real.rpow_nonneg hy.le _)
    _ = y ^ (p - γ) := mul_one _
    _ ≤ 2 * ν := by
      have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlower
      simpa only [mul_comm] using h

/-- The plateau Peclet number is at most two, already at the terminal level. -/
theorem terminal_plateau_peclet_bound {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (D : OCData) (hDα : D.α = α) (hDq : D.q = q) (hDΛ : D.Λ = Λ) (hDζ : D.ζ = ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (hm : D.term ≤ m) : D.eps m ^ (1 + D.α) / D.kap m ≤ 2 := by
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hν := weakData_kap_pos D hΛD hζD hband m
  have hγ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).1
  have he := Scales.epsilon_basic (m := m) hq.1 hΛ
  have hE := Scales.epsilon_basic (m := D.term) hq.1 hΛ
  have hEm : ocEpsilon q Λ m ≤ ocEpsilon q Λ D.term :=
    EntryScales.epsilon_antitone hq.1 hΛ hm
  have hlower : ocEpsilon q Λ D.term ^ ((1 + α) - ocGamma α q) / 2 ≤ D.κ D.term := by
    simpa only [hDα, hDq, hDΛ] using hband.1.1
  rw [weakData_kap_terminal D m hm] at hν
  rw [weakData_kap_terminal D m hm, OCData.eps, hDα, hDq, hDΛ]
  exact plateau_peclet_of_band_lower _ _ _ _ _ he.1.le hE.1 hE.2.1 hEm
    (by linarith only [hα₀]) hγ.le hν hlower

/-- Uniform raw balanced drift jets at terminal and plateau levels, with numerical budget
`2 * pulseFastDerivativeConstant n`. The radius and family do not enter this certificate. -/
theorem terminal_plateau_balanced_drift_bound {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (D : OCData) (hDα : D.α = α) (hDq : D.q = q) (hDΛ : D.Λ = Λ) (hDζ : D.ζ = ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (hm : D.term ≤ m) (hm1 : 1 ≤ m) (slot : ℤ) (hslot : Odd slot)
    (n : ℕ) (t : ℝ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun w => Real.sqrt (D.kap m / D.kap (m - 1)) •
      ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) slot t w) z‖ ≤
      2 * pulseFastDerivativeConstant n := by
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hν := weakData_kap_pos D hΛD hζD hband m
  have hB := weakData_kap_pos D hΛD hζD hband (m - 1)
  have hratio : D.kap m / D.kap (m - 1) ≤ 1 :=
    (div_le_one hB).mpr (native_kap_step_le D hΛD hζD hband m hm1)
  have hsqrt : Real.sqrt (D.kap m / D.kap (m - 1)) ≤ 1 :=
    Real.sqrt_le_iff.mpr ⟨zero_le_one, by simpa only [one_pow] using hratio⟩
  have hPe := terminal_plateau_peclet_bound hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ D
    hDα hDq hDΛ hDζ hband m hm
  have hamp : Real.sqrt (D.kap m / D.kap (m - 1)) *
      (D.eps m ^ (1 + D.α) / D.kap m) ≤ 2 := by
    calc
      _ ≤ 1 * (D.eps m ^ (1 + D.α) / D.kap m) :=
        mul_le_mul_of_nonneg_right hsqrt
          (div_nonneg (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛD).le _) hν.le)
      _ ≤ 2 := by simpa only [one_mul] using hPe
  exact balancedPulseDrift_vector_fast_bound hΛD hν hζD hslot n n le_rfl hamp t z

/-- The weak passage's parent wavelength is an admissible slow radius on the plateau. -/
theorem plateau_parent_lift_radius_bounds (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (hm : D.term < m) :
    0 < D.eps (m - 1) ∧
    ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / D.eps (m - 1) ≤ 1 ∧
    D.eps (m - 1) / D.eps (m - 1) ≤ 1 := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hE : 0 < D.eps (m - 1) := Construction.Stream.ocEpsilon_pos hΛ₁
  have hν := CycleReference.bandChain_pos hΛ₁ hζ hband (le_refl D.term)
  refine ⟨hE, ?_, ?_⟩
  · rw [weakData_kap_terminal D m (by omega), weakData_kap_terminal D (m - 1) (by omega)]
    simp only [ocDStar, div_self hν.ne', Real.sqrt_one, mul_one]
    exact (div_le_one hE).mpr (EntryScales.epsilon_antitone hq hΛ (Nat.sub_le m 1))
  · rw [div_self hE.ne']

end AVRegularity.Construction.TerminalLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.TerminalLift

/-! Shared native lift setting and existence at the terminal level and on the diffusivity
plateau. The slow radius and the effective source cap are arguments, so this interface serves
both terminal preparation and weak passages. Drift jets follow from the terminal band; there is
no strict interior-level premise. The original-slot clock window is retained. -/

open EntryWeakProofs Preservation

/-- Shared terminal/plateau setting and lift existence. The chosen metric budget, drift budget and floor
precede the family, datum, phase and marker. The input is a context-certified natural,
transverse family with an actual finite source cap and its scaled source envelope. The
balanced drift certificate is produced uniformly from the terminal band, even on the plateau.

The setting uses the measurable window extension at the effective cap; the same coefficient
array meets both that recurrence and the literal ambient-cap recurrence on the original slot.
Taking `G.level = D.term` and `ρ = cr * liftLength D D.term` supplies terminal preparation;
taking `D.term < G.level` and `ρ = D.eps (G.level - 1)` supplies a weak passage. -/
def TerminalLevelLiftStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2)
    (q : ℝ) (_hq : IsAdmissibleQ α s q) (Λ : ℕ) (_hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ)
    (H N K k L Ksrc : ℕ), 1 ≤ N → 2 ≤ Ksrc →
    ∃ (CG Cw : ℕ → ℝ) (m₀ : ℕ), (∀ n, 0 ≤ CG n) ∧ (∀ n, 0 ≤ Cw n) ∧ 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm j₀ Mnat : ℕ) (bw : ℝ) (G : GenStage D hr Dm bw j₀) (kI : InvConsts),
      0 < bw → G.IsContextCertified kI → G.IsSlotTransverse → G.IsNatural Mnat →
      m₀ ≤ G.level → D.term ≤ G.level → j₀ ≤ G.level →
      G.fam.HasDepthAtMost H →
      (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
      (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
      ∀ (slot : OddSlot) (ρ : ℝ), 0 < ρ →
      ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ ≤ 1 →
      ρ / D.eps (G.level - 1) ≤ 1 →
      ∀ (π : CompIn G.comps → ℝ), (∀ v, 0 < π v) →
      ∀ (hKD : Ksrc ≤ Dm) (Cj : ℕ → ℕ → ℝ)
        (price : CompIn G.comps → CompIn G.comps → ℝ) (Θ : ℝ),
      let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
      let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
      let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
        (G.fam.fiber slot (G.actual slot))
      let qs := K + 4 * (H + 1) * (N + Ksrc) ^ 2
      let qf := max k (L + 2) + H * Ksrc + 2 * N + 2 * Ksrc
      (∀ v u d, Ksrc < d.1 → Q.edge v u d = []) →
      IsScaledJetEnvelope π Q.edge (Set.Icc a b) (ρ / D.eps (G.level - 1)) Cj qs qf price Θ →
      IsLiftSetting (restrictLiftData Ksrc hKD {Q with edge := FullLift.windowEdges a b Q.edge})
        π a b (D.eps G.level) (D.kap G.level) (D.kap (G.level - 1)) ρ
        (D.eps (G.level - 1)) (D.eps G.level / Real.sqrt (D.kap G.level))
        (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
        (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ)
        (ρ / D.eps (G.level - 1)) (pulseParallel slot.1)
        (pulseShearProfile D.α D.q D.Λ G.level D.ζ (D.kap G.level) slot.1)
        H N K k L qs qf CG Cw Cj price Θ ∧
      ∃ Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root),
        IsLiftSequence (restrictLiftData Ksrc hKD {Q with edge := FullLift.windowEdges a b Q.edge})
          (K + Ksrc + 2) (max (k + 1) (L + 2)) a b N H Cc ∧
        IsLiftSequence Q (K + Ksrc + 2) (max (k + 1) (L + 2)) a b N H Cc

end AVRegularity.Construction.TerminalLift
end

section
open Homogenization
open scoped ENNReal Matrix Matrix.Norms.Elementwise
namespace AVRegularity.Construction.TerminalLift

/-! The existing global metric producers supply the shared terminal lift geometry.
Neither producer assumes a strict interior level or a fixed slow radius. -/

open Preservation.FullLift

/-- Uniform native metric jets and ellipticity, including terminal and plateau levels. -/
theorem terminal_lift_metric_certificates (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (K : ℕ) :
    ∃ (CG : ℕ → ℝ) (m₀ : ℕ), (∀ n, 0 ≤ CG n) ∧ 2 ≤ m₀ ∧
    ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ) (D : OCData),
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ m, m₀ ≤ m → ∀ slot : ℤ, Odd slot → ∀ ρ : ℝ, 0 ≤ ρ →
    ∀ edge : ConstituentEdges Dm h,
      let Q := familyLiftData D m slot (nativeChain m slot) ρ edge
      let a := D.slotStart m slot / D.cellScaleSq m
      let b := (((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m
      (∀ n ≤ K, (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ n (fun Y => Q.G t Y) X‖ₑ) ≤
          ENNReal.ofReal (CG n * (ρ / D.eps (m - 1)) ^ n)) ∧
      (∀ t ∈ Set.Icc a b, ∀ X ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2) := by
  obtain ⟨CG, hCG, MG, hMG, hG⟩ := uniform_native_lift_metric_radius_sup_all_carriers
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ K
  obtain ⟨ME, _hME, hEllip⟩ := uniform_native_lift_ellipticity_all_carriers
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ
  refine ⟨CG, max MG ME + 1, hCG, by omega, ?_⟩
  intro ι h _ _ Dm D hDα hDq hDΛ hDζ hseq hband m hm slot hslot ρ hρ edge Q a b
  exact ⟨hG ι h Dm D hDα hDq hDΛ hDζ hseq hband m (by omega) slot hslot ρ hρ edge,
    hEllip ι h Dm D hDα hDq hDΛ hDζ hseq hband m (by omega) slot hslot ρ edge⟩

end AVRegularity.Construction.TerminalLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.TerminalLift

/-! Assemble the terminal/plateau lift setting from the shared global geometry,
terminal band drift estimate and actual source envelope, then recover the original recurrence. -/

open Preservation.FullLift EntryWeakProofs

/-- The shared setting and coefficient construction, without a strict interior restriction. -/
theorem terminal_level_lift : TerminalLevelLiftStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ ζ hζ H N K k L Ksrc hN hKsrc
  let qs := K + 4 * (H + 1) * (N + Ksrc) ^ 2
  obtain ⟨CG, m₀, hCG, hm₀, hmetric⟩ := terminal_lift_metric_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ qs
  let Cw : ℕ → ℝ := fun n => 2 * pulseFastDerivativeConstant n
  refine ⟨CG, Cw, m₀, hCG,
    fun n => mul_nonneg (by norm_num) (EntryWeakProofs.pulseFastDerivativeConstant_nonneg n),
    hm₀, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband Dm j₀ Mnat bw G kI
    hbw hcert hpar hnat hm hterminal hj hdepth hreserve hreserve2 slot ρ hρ hcell hlam
    π hπ hKD Cj price Θ a b Q qs' qf hz hsource
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hi : 1 ≤ G.level := by omega
  have hgeometry := hmetric (CompIn G.comps) (fun v => hr v.1.root) Dm D
    hDα hDq hDΛ hDζ hseq hband G.level hm slot.1 slot.2 ρ hρ.le
    (G.fam.fiber slot (G.actual slot))
  have hrawSup := native_lift_balanced_drift_sup_of_bound D G.level slot.1
    (nativeChain G.level slot.1) ρ (G.fam.fiber slot (G.actual slot)) a b qf Cw
    (fun n _hn t _ht z => terminal_plateau_balanced_drift_bound
      hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ D hDα hDq hDΛ hDζ hband G.level
      hterminal hi slot.1 slot.2 n t z)
  have hsetting := native_lift_setting_of_certificates G kI Mnat hcert hpar hnat hi hj hbw
    hΛD hζD hband hreserve hreserve2 slot ρ hρ hcell hlam π hπ
    H N K k L Ksrc hN hKsrc hKD CG Cw Cj price Θ hdepth hz
    hgeometry.2 hgeometry.1 hrawSup hsource
  obtain ⟨Cc, hrestricted, hambient⟩ := effective_window_lift_exists_with_restricted hsetting hz
  exact ⟨hsetting, Cc, hrestricted, hambient⟩

end AVRegularity.Construction.TerminalLift
end

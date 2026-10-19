-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Finite.WeakLift.IdentitySeparation
public import AVRegularity.Finite.Assembly.WeakParentSettingOfIngredients
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Finite.Lift.PositivePhysicalIdentity

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Finite.TerminalLift

/-! The terminal word-fiber readout bound is independent of the number of weak roots. -/

open Construction.Preservation.FullLift

/-- Removing the sole new birth changes mass by at most max(1,cH). -/
theorem terminal_mass_ratio_le (q : ℝ) (Λ m : ℕ) (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (lawW lawT : BirthLaw) (hroot : lawT.rootMass = lawW.rootMass)
    (hη : 0 ≤ lawT.etaB) (c : Comp) (hparent : (compParent m c).births = []) :
    compMass q Λ lawT c / compMass q Λ lawW (compParent m c) ≤ max 1 lawT.cH := by
  have hmass : compMass q Λ lawT (compParent m c) =
      compMass q Λ lawW (compParent m c) := by
    simp only [compMass, hparent, List.map_nil, List.prod_nil, mul_one, hroot]
  have hp := Construction.Preservation.Buffer.birth_compMass_pos hq hΛ lawW (compParent m c)
  by_cases hw : compWord m c = []
  · have hc : c = compParent m c := by
      simpa only [hw, succComp, ↓reduceDIte] using (succComp_parent_word m c).symm
    conv_lhs => arg 1; rw [hc, hmass]
    rw [div_self hp.ne']
    exact le_max_left _ _
  · have he := Scales.epsilon_basic (m := m - 1) hq hΛ
    have hpre : lawT.cH / (lawT.wordCount : ℝ) ≤ lawT.cH :=
      div_le_self lawT.cH_pos.le (by exact_mod_cast lawT.wordCount_pos)
    have hprice : lawT.cH / (lawT.wordCount : ℝ) *
        ocEpsilon q Λ (m - 1) ^ lawT.etaB ≤ lawT.cH := by
      calc
        _ ≤ lawT.cH / (lawT.wordCount : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one he.1.le he.2.1 hη)
            (div_nonneg lawT.cH_pos.le (Nat.cast_nonneg _))
        _ ≤ _ := by simpa only [mul_one] using hpre
    calc
      _ = (lawT.cH / (lawT.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ lawT.etaB) := by
        conv_lhs => arg 1; rw [← succComp_parent_word m c, succComp_mass lawT _ hw]
        rw [hmass, mul_div_cancel_right₀ _ hp.ne']
      _ ≤ lawT.cH := hprice
      _ ≤ _ := le_max_right _ _

/-- A new terminal mass costs at most sqrt(cH), and an empty word costs one. -/
theorem terminal_mass_sqrt_ratio_le (q : ℝ) (Λ m : ℕ) (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (lawW lawT : BirthLaw) (hroot : lawT.rootMass = lawW.rootMass)
    (hη : 0 ≤ lawT.etaB) (c : Comp) (hparent : (compParent m c).births = []) :
    (Real.sqrt (compMass q Λ lawW (compParent m c)))⁻¹ *
      Real.sqrt (compMass q Λ lawT c) ≤ max 1 (Real.sqrt lawT.cH) := by
  rw [← div_eq_inv_mul, ← Real.sqrt_div (Construction.Preservation.Buffer.birth_compMass_pos hq hΛ lawT c).le]
  have h := Real.sqrt_le_sqrt (terminal_mass_ratio_le q Λ m hq hΛ lawW lawT hroot hη c hparent)
  have he : Real.sqrt (max 1 lawT.cH) = max 1 (Real.sqrt lawT.cH) := by
    by_cases hc : lawT.cH ≤ 1
    · rw [max_eq_left hc, Real.sqrt_one, max_eq_left (Real.sqrt_le_one.mpr hc)]
    · rw [max_eq_right (le_of_not_ge hc),
        max_eq_right (Real.one_le_sqrt.mpr (le_of_not_ge hc))]
  exact h.trans_eq he

/-- The moderate terminal readout leaf, using finite parent fibers rather than root count. -/
theorem terminal_readout_bounds : TerminalReadoutBoundsStatement := by
  intro q Λ m hq hΛ hm lawW lawT η A RT S S' hroot hηB hη hroots hsub
  classical
  let B := max 1 (Real.sqrt lawT.cH)
  let W : ℝ := (1 + (wordsUpTo A (RT + 1)).card : ℕ)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hW : 1 ≤ W := by dsimp [W]; exact_mod_cast Nat.le_add_right 1 _
  have hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale := by
    intro v hv e he
    rw [hroots v hv] at he
    exact False.elim (List.not_mem_nil he)
  have hparent (c : CompIn S') : compParent m c.1 ∈ S :=
    readout_parent_mem hm hold (hsub c.2)
  have hβ (c : CompIn S') :
      0 ≤ (Real.sqrt (compMass q Λ lawW (compParent m c.1)))⁻¹ *
        ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) *
        Real.sqrt (compMass q Λ lawT c.1) ∧
      (Real.sqrt (compMass q Λ lawW (compParent m c.1)))⁻¹ *
        ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) *
        Real.sqrt (compMass q Λ lawT c.1) ≤ B := by
    have hc0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) :=
      Real.rpow_nonneg (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _
    refine ⟨mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hc0)
      (Real.sqrt_nonneg _), ?_⟩
    calc
      _ = ((Real.sqrt (compMass q Λ lawW (compParent m c.1)))⁻¹ *
          Real.sqrt (compMass q Λ lawT c.1)) *
          ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) := by ring
      _ ≤ B * 1 := mul_le_mul
        (terminal_mass_sqrt_ratio_le q Λ m hq hΛ lawW lawT hroot hηB c.1
          (hroots _ (hparent c))) (readout_coefficient_le_one hq hΛ hη m c.1) hc0 hB
      _ = B := mul_one B
  have hentry (v : CompIn S) (c : CompIn S') :
      0 ≤ readoutMatrix m (ocEpsilon q Λ (m - 1)) η
        (fun v : CompIn S => compMass q Λ lawW v.1)
        (fun c : CompIn S' => compMass q Λ lawT c.1) v c := by
    dsimp only [readoutMatrix]
    split_ifs with hp
    · rw [← hp]
      exact (hβ c).1
    · exact le_rfl
  apply WeakLift.readoutCLM_norm_le_schur _ _ _ _ _ _
    (mul_nonneg (zero_le_one.trans hW) hB) hentry
  · intro v
    calc
      _ = ∑ c ∈ (Finset.univ.filter fun c : CompIn S' => compParent m c.1 = v.1),
          (Real.sqrt (compMass q Λ lawW v.1))⁻¹ *
            ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) *
              Real.sqrt (compMass q Λ lawT c.1) := by
        simp only [readoutMatrix, Finset.sum_filter]
      _ ≤ ∑ _c ∈ (Finset.univ.filter fun c : CompIn S' => compParent m c.1 = v.1), B := by
        apply Finset.sum_le_sum
        intro c hc
        rw [← (Finset.mem_filter.mp hc).2]
        exact (hβ c).2
      _ = (((Finset.univ.filter fun c : CompIn S' => compParent m c.1 = v.1).card : ℕ) : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ W * B := mul_le_mul_of_nonneg_right (by
        dsimp [W]
        exact_mod_cast (readout_indexed_fiber_card_le hm hold hsub v.1).trans_eq
          (Nat.add_comm _ _)) hB
  · intro c
    let v : CompIn S := ⟨compParent m c.1, hparent c⟩
    have he : (∑ u : CompIn S, readoutMatrix m (ocEpsilon q Λ (m - 1)) η
        (fun u => compMass q Λ lawW u.1) (fun c => compMass q Λ lawT c.1) u c) =
        (Real.sqrt (compMass q Λ lawW (compParent m c.1)))⁻¹ *
          ocEpsilon q Λ (m - 1) ^ (η * (compWord m c.1).length) *
            Real.sqrt (compMass q Λ lawT c.1) := by
      rw [Finset.sum_eq_single v]
      · simp only [readoutMatrix, v, ↓reduceIte]
      · intro u _ huv
        have hp : compParent m c.1 ≠ u.1 := fun h => huv (Subtype.ext h.symm)
        simp only [readoutMatrix, hp, ↓reduceIte]
      · intro hv
        exact False.elim (hv (Finset.mem_univ v))
    rw [he]
    exact (hβ c).2.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hW hB)

/-- The finite profile route from its general-depth/order analytic difference leaf alone. -/
theorem terminal_lift_rep_of_difference
    (hdiff : TerminalDifferenceBoundsGeneralStatement) : Assembly.TerminalLiftRepStatement := by
  exact terminal_lift_rep_of_ingredients (terminal_lift_profile_bounds_finite_of_general
    (terminal_lift_profile_bounds_general_of_ingredients terminal_readout_bounds hdiff))

end AVRegularity.Finite.TerminalLift
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Coupled covariance and oscillatory profile summation at their two physical wavelengths. -/

/-- Both profiles pay only the fixed tested-order jet count. -/
theorem terminal_profile_jet_packing : TerminalProfileJetPackingStatement := by
  intro H _ _ E e s C K Kmax X cov osc hE he hK hcov hosc
  have hc := profile_jet_packing E s K Kmax cov _ hE hK hcov
  have ho := profile_jet_packing e s K Kmax osc _ he hK hosc
  calc
    _ ≤ (profileJetCount Kmax : ℝ≥0∞) * (ENNReal.ofReal C * X) +
        (profileJetCount Kmax : ℝ≥0∞) * (ENNReal.ofReal C * X) := add_le_add hc ho
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      ring

/-- Physical scaled jets are the sole remaining input to the fixed E7-facing difference leaf. -/
theorem terminal_difference_bounds_of_jets (hjets : TerminalDifferenceJetBoundsGeneralStatement) :
    TerminalDifferenceBoundsGeneralStatement := by
  exact terminal_difference_bounds_of_ingredients terminal_profile_jet_packing hjets

/-- The existing general profile and finite representation assemblies remain intact. -/
theorem terminal_lift_rep_of_difference_jets (hjets : TerminalDifferenceJetBoundsGeneralStatement) :
    Assembly.TerminalLiftRepStatement := by
  exact terminal_lift_rep_of_difference (terminal_difference_bounds_of_jets hjets)

end AVRegularity.Finite.TerminalLift
end
end

section
@[expose] public noncomputable section

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Couple the two actual raw-jet budgets without changing their physical wavelengths. -/

/-- The shared constant dominates both budgets, including the positive-degree scale gain. -/
theorem terminal_raw_jet_coupling : TerminalRawJetCouplingStatement := by
  intro H _ _ e E s Cc Co K X cov osc he heE hs hc ho
  have hgain := positive_scale_gain e E s he heE hs
  have hcovY : ENNReal.ofReal Cc * X ≤ ENNReal.ofReal (max Cc Co) * X :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
  have hoscY : ENNReal.ofReal Co * ENNReal.ofReal ((e / E) ^ (1 - s)) * X ≤
      ENNReal.ofReal (max Cc Co) * X := by
    calc
      _ ≤ ENNReal.ofReal Co * ENNReal.ofReal 1 * X :=
        mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hgain)) le_rfl
      _ = ENNReal.ofReal Co * X := by rw [ENNReal.ofReal_one, mul_one]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  exact ⟨⟨hc.1.trans hcovY, fun a ha => (hc.2 a ha).trans hcovY⟩,
    ⟨ho.1.trans hoscY, fun a ha => (ho.2 a ha).trans hoscY⟩⟩

/-- Both pure covariance and actual oscillatory estimates remain in the named producer. -/
theorem terminal_difference_jets_of_physical_transfer (hmodel : TerminalSharedPhysicalTransferStatement) :
    TerminalDifferenceJetBoundsGeneralStatement := by
  exact terminal_difference_jets_of_ingredients hmodel terminal_raw_jet_coupling

end AVRegularity.Finite.TerminalLift
end

section
open Homogenization Filter Topology
namespace AVRegularity.Finite.TerminalLift

/-! Terminal slot-lift facts. The premise `G₀ ≤ H_prod + 1` gives the root-component reserve
interval required by terminal_level_lift. The terminal band gives a uniform effective-cell-length to
wavelength ratio, which pays the actual dStar/rho pulse power in the positive chart transfer. -/

/-- The reserve premise supplies every reserve of a re-rooted weak family, including the zero-reserve boundary. -/
theorem terminal_root_reserve_bounds (S : Finset Comp) (k : InvConsts)
    (hk : k.G0 ≤ k.Hprod + 1) (hbirths : ∀ v : CompIn S, v.1.births = []) :
    (∀ v : CompIn S, 0 ≤ compReserve k v.1) ∧
      (∀ v : CompIn S, compReserve k v.1 ≤ 2) := by
  have hden : 0 < (k.Hprod : ℝ) + 1 := by positivity
  have hG : (k.G0 : ℝ) ≤ (k.Hprod : ℝ) + 1 := by exact_mod_cast hk
  constructor
  · intro v
    simp only [compReserve, compGrade, hbirths v, List.length_nil, Nat.add_zero]
    exact sub_nonneg.mpr ((div_le_one hden).mpr hG)
  · intro v
    have hdiv : 0 ≤ ((k.G0 + compGrade v.1 : ℕ) : ℝ) / ((k.Hprod : ℝ) + 1) :=
      div_nonneg (Nat.cast_nonneg _) hden.le
    exact (sub_le_self (1 : ℝ) hdiv).trans (by norm_num)

/-- The actual terminal pulse scale differs from the wavelength by a fixed bounded factor.
The constant and construction threshold are selected before the terminal level and diffusivity. -/
theorem terminal_effective_cell_length_bound {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 2 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ocDStar q Λ M (κ M) (κ (M - 1)) ≤ A * ocEpsilon q Λ M := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hcontrast⟩ :=
    CycleReference.bandChain_terminal_contrast hα₀ hα₁ hs₀ hs₁ hq hζ
  have hsqrt : 1 ≤ Real.sqrt C := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hC
  refine ⟨Real.sqrt C, hsqrt, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hband
  have he := (Scales.epsilon_basic (m := M) hq.1 (hΛ₀.trans hΛ)).1
  unfold ocDStar
  exact (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hcontrast Λ hΛ M hM κ hband)) he.le).trans_eq (mul_comm _ _)

/-- Natural, shift-invariant terminal stages have the same uniform chart geometry at every
positive radius below the parent wavelength. The numerical chart budget precedes the stage. -/
theorem terminal_positive_physical_geometry {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (N U : ℕ) :
    ∃ chartC : ℝ, 1 ≤ chartC ∧ ∃ M₀ : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (Dm j₀ : ℕ) (bw : ℝ) (M Mnat : ℕ) (G : GenStage D ScalarH Dm bw j₀),
      G.level = M → G.IsNatural Mnat → G.IsShiftInvariant → D.term = M →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → M₀ ≤ M →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps (M - 1) →
      WeakLift.PositivePhysicalGeometry (N := N) (U := U) chartC M G ρ := by
  obtain ⟨Mf, _hMf, hflow⟩ := Construction.Preservation.FullLift.uniform_native_physical_flow_jets
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ (U + N)
  refine ⟨EntryWeakProofs.weakChartJetBudget (U + N) 0,
    EntryWeakProofs.weakChartJetBudget_ge_one (U + N) 0, Mf + 1, ?_⟩
  intro D hDα hDq hDΛ hDζ hstream Dm j₀ bw M Mnat G hlevel hnat hshift hterm hband hM
    ρ hρ hρE
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) (m := M) hΛD
  have htorus := GenStage.isTorusCompatible_of_shiftInvariant hnat hshift
  refine {
    level := hlevel
    q_gt := hDq.symm ▸ hq.1
    Λ_ge := hDΛ.symm ▸ hΛ
    fast := hDζ.symm ▸ hζ
    stream := ?_
    band := hband
    plateau := hterm.le
    torus := ?_
    forward := ?_
    backward := ?_ }
  · simpa only [hDα, hDq, hDΛ, hDζ] using hstream
  · simpa only [hlevel] using htorus
  · intro t slot hcut
    exact (hflow D hDα hDq hDΛ hDζ hstream M hM slot.1 slot.2 ρ hρ hρE t
      (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut)).1
  · intro t slot hcut
    exact (hflow D hDα hDq hDΛ hDζ hstream M hM slot.1 slot.2 ρ hρ hρE t
      (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut)).2

/-- The weak original lengths fit the terminal wavelength after a numeric floor.
This pays the original-record hypothesis of the shared source envelope without changing tags. -/
theorem terminal_record_length_floor {q : ℝ} {Λ : ℕ} (hq : 1 < q)
    (hq17 : q < 17 / 16) (hΛ : 128 ≤ Λ) (CL : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      |CL| * ocEpsilon q Λ (M + 1) ≤ ocEpsilon q Λ M := by
  have ht : Filter.Tendsto (fun M : ℕ => (2 * |CL|) * ocEpsilon q Λ M ^ (q - 1))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (EntryScales.epsilon_rpow_tendsto_zero hq hΛ (sub_pos.mpr hq))
  obtain ⟨m₀, hfloor⟩ := Filter.eventually_atTop.1
    (ht.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨m₀, ?_⟩
  intro M hM
  have hE := (Scales.epsilon_basic (m := M) hq hΛ).1
  have hstep := Scales.epsilon_q_step hq hq17 hΛ (by omega : 1 ≤ M + 1)
  simp only [Nat.add_sub_cancel] at hstep
  have hpow : ocEpsilon q Λ M ^ q =
      ocEpsilon q Λ M ^ (q - 1) * ocEpsilon q Λ M := by
    calc
      _ = ocEpsilon q Λ M ^ ((q - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hE, Real.rpow_one]
  calc
    |CL| * ocEpsilon q Λ (M + 1) ≤ |CL| * (2 * ocEpsilon q Λ M ^ q) :=
      mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
    _ = ((2 * |CL|) * ocEpsilon q Λ M ^ (q - 1)) * ocEpsilon q Λ M := by
      rw [hpow]
      ring
    _ ≤ 1 * ocEpsilon q Λ M := mul_le_mul_of_nonneg_right (hfloor M hM) hE.le
    _ = ocEpsilon q Λ M := one_mul _

end AVRegularity.Finite.TerminalLift
end
end
end

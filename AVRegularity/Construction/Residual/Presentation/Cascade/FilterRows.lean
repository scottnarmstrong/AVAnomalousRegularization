-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.Budget
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.RowMaster
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.Diagonal.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The two source ingredients of the letters statement `FrameReconLettersAt` at a cascade frame. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The high-order pulse setting and the GIVEN lifted sequence on the clipped window.
The analytic constants and orders may depend on kc; they precede the level in the prefix producer. -/
structure PulseInput
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) where
  K : ℕ
  L : ℕ
  order : fNc F kc ≤ K + 1
  CG : ℕ → ℝ
  Cw : ℕ → ℝ
  Cj : ℕ → ℕ → ℝ
  qs : ℕ
  qf : ℕ
  par : ℤ → Fin 2
  V : ℤ → ℝ → ℝ → ℝ
  price : ℝ
  settings : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (par k) (V k) F.depth F.N K L L
      qs qf CG Cw Cj (recordMajorant (F.G.mass law) F.G.fam) price
  sequences : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSequence (fLiftData F k) (K + Dm + 2) (max (L + 1) (L + 2))
      (fSeqStart F k) (fSeqEnd F k) F.N F.depth (F.CcT k)

section Model

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- Renewal chart and inverse of an observed pulse. -/
abbrev chart'' (k : ℤ) :=
  ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
    (ocPulseChartIndex D.α D.q D.Λ F.m k)

abbrev label'' (k : ℤ) :=
  ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
    (ocPulseChartIndex D.α D.q D.Λ F.m k)

/-- The explicit diagonal letter of the reconstruction window. -/
abbrev diagonalLetter (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ) :=
  adLetter (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) (F.N + Dm)
    (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fSeqStart F) (fSeqEnd F) Lsc (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))

/-- The explicit positive-grade letter of the reconstruction window. -/
abbrev positiveGradeLetter (Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn F.G.comps) (fun v => hr v.1.root)) :=
  ceLetter (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) (F.N + Dm)
    (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fSeqStart F) (fSeqEnd F) Lb

/-- G2 letters, their scalar reading, and G1's actual means, at the requested coarse order. -/
structure PulseModel (kc : ℕ) (p : PulseInput F law kc) where
  C₂ : ℝ
  C₂_nonneg : 0 ≤ C₂
  C₁ : ℝ
  Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn F.G.comps) (fun v => hr v.1.root)
  Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ
  pulse : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsPulseLetters (fLiftData F k) (F.CcT k) (F.G.mass law)
      (recordMajorant (F.G.mass law) F.G.fam) (fSeqStart F k) (fSeqEnd F k)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) C₂ F.N F.depth p.K (Lb k)
  scalar_smooth : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    ∀ n, 2 ≤ n → n ≤ F.N + Dm → ∀ d, 2 ≤ d → d ≤ n →
    ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k),
      ContDiff ℝ ((fNc F kc) : ℕ∞) (Lsc k n d α l s)
  reading : IsScalarReading (fun k n => Lb k 0 n) Lsc
    (refFallback (D.κ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)))
  actual : IsActualMeans F.N Dm F.depth (fNc F kc) C₁
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k)) F.tp (F.tp + fTobs F)
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (ocEpsilon D.q D.Λ (F.m - 1))
    (fLiftData F) F.CcT
    (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fSeqStart F) (fSeqEnd F) Lb
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) (diagonalLetter F Lsc) (positiveGradeLetter F Lb)

end Model

/-- G2 at the supplied sequence, followed by G1 at the actual charts and partition. -/
theorem pulseModel_of_input
    (F : Frame D hr Dm b j₀) (law : BirthLaw) (kc : ℕ) (p : PulseInput F law kc) (g : WindowGeometry F law kc)
    (hΛ : 128 ≤ D.Λ) (hν : 0 < D.κ F.m) (hDm : 2 ≤ Dm)
    (hfamily : ∃ T, FrameReconFamilyBody F 0 T reconCpart)
    (hjets : ∀ k t, (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t ∈
      Set.Icc (fSeqStart F k) (fSeqEnd F k) → ∀ j, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (chart'' F k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1) ∧
      ‖iteratedFDeriv ℝ j (label'' F k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1)) :
    Nonempty (PulseModel F law kc p) := by
  classical
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  have hE : 0 < ocEpsilon D.q D.Λ (F.m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hd : 0 ≤ ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) := by
    unfold ocDStar
    exact mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le (Real.sqrt_nonneg _)
  have hDt : 2 ≤ Dm := hDm
  have hnc : 1 ≤ fNc F kc := by
    have hp : 0 < (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4) :=
      Nat.mul_pos (by omega) (by omega)
    simp only [fNc]
    omega
  obtain ⟨C₂, hC₂, hletters⟩ := exists_pulseLetters F.N p.K p.L p.L Dm F.depth p.CG p.Cw p.Cj
  choose! Lb hLb using fun k (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)) =>
    hletters (ι := CompIn F.G.comps) (h := fun v => hr v.1.root)
      (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (p.par k) (p.V k) p.qs p.qf
      (recordMajorant (F.G.mass law) F.G.fam) p.price (p.settings k hk)
      (F.CcT k) (p.sequences k hk)
  choose! Ls hLs using fun k (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ F.N + Dm) => (hLb k hk).diag n hn hnN
  obtain ⟨T, hf⟩ := hfamily
  have htorus := hf.2.1
  have hpart := hf.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hwmeas, -, hsupp⟩ := partition_stage_facts hpart
  obtain ⟨C₁, -, hmeans⟩ := actual_means_explicit F.N Dm F.depth (fNc F kc) hDt
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  have hreg : (((fNc F kc : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast p.order
  obtain ⟨Lsc, -, hscC, hread, hAM⟩ := hmeans (ι := CompIn F.G.comps)
    (h := fun v => hr v.1.root)
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k)) F.tp (F.tp + fTobs F)
    (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (ocEpsilon D.q D.Λ (F.m - 1))
    (fLiftData F) F.CcT
    (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k))
    (fSeqStart F) (fSeqEnd F) Lb Ls
    (refFallback (D.κ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)))
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) hnc (pow_pos hℓ 2) g.rho_pos
    (div_nonneg hd g.rho_pos.le) hE rfl g.J_meas hwmeas
    (fun k hk t ht hn => cellTime_mem_liftWindow (pow_pos hℓ 2) (hsupp k hk t hn) ht)
    (fun k _ t y => CycleComparison.Charts.ocChartInv_ocChart _ _ _ _ _ _ _ t y)
    (fun k _ t y => CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ t y)
    (fun k _ t z y => CycleComparison.Charts.ocChart_latticeShift _ _ _ _ _ _ t z y)
    (fun k _ t y => CycleComparison.Charts.ocChart_det _ _ _ _ _ _ t y)
    (fun k _ => CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _)
    (fun k _ => CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _)
    (fun k _ t _ hwin j hj _ y => hjets k t hwin j hj y)
    (fun k hk r hr n hn hnN => (hLb k hk).pres r hr n hn hnN)
    (fun k hk r hr n hn hnN d _ _ α l v u s hs =>
      ((hLb k hk).smooth r hr n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk r hr n hn hnN d _ _ α l v u Y => (hLb k hk).meas r hr n hn hnN d α l v u Y)
    (fun k hk r hr n hn hnN d _ _ α l v u s hs z Y =>
      (hLb k hk).shift ((fRho F)⁻¹ • latticeShift z)
        (fun t Y i j => pulseLiftData_G_shift D.α D.q D.Λ F.m D.ζ (D.hΦ (F.m - 1))
          (D.κ F.m) (D.κ (F.m - 1)) g.rho_pos.ne' _ k _ z t Y i j)
        (fun v u d γ hγ α t Y Z => liftEdges_fiber_coeff_shift g.rho_pos.ne' htorus
          (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (oddSlotOf k) z hγ α t Y Z)
        r hr n hn hnN d α l v u s hs Y)
    (fun k hk n hn hnN d hd hdn α l s hs Y => hLs k hk n hn hnN d hd hdn α l s hs Y)
    (fun k _ n _ _ d _ _ α l s _ => contDiff_refFallback _ _ _ k n d α l s _)
    (fun k _ n _ _ d _ _ α l Y => measurable_refFallback _ _ g.J_meas k n d α l Y _ _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
  exact ⟨{
    C₂ := C₂
    C₂_nonneg := hC₂
    C₁ := C₁
    Lb := Lb
    Lsc := Lsc
    pulse := hLb
    scalar_smooth := hscC
    reading := hread
    actual := hAM }⟩
end

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The chart estimates used in the normalized mean budgets. -/
structure ChartBounds where
  jets : ∀ k t, (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t ∈
      Set.Icc (fSeqStart F k) (fSeqEnd F k) → ∀ j, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (chart'' F k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1) ∧
      ‖iteratedFDeriv ℝ j (label'' F k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon D.q D.Λ (F.m - 1))⁻¹ ^ (j - 1)
  deviation : ∀ k t, (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2)⁻¹ * t ∈
      Set.Icc (fSeqStart F k) (fSeqEnd F k) → ∀ K a b,
      ScaledJet K (ocEpsilon D.q D.Λ (F.m - 1))
        (fun y => jacMatrix (chart'' F k t) y a b -
          (if a = b then 1 else 0))
        (CycleComparison.Charts.chartDevConst K *
          (ocA D.α D.q D.Λ (F.m - 1) * ocTauPP D.α D.q D.Λ F.m))

/-- The physical record matrix (before conjugation by the masses). -/
abbrev physicalEdge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ :=
  Matrix.of fun v u => recordMajorant (F.G.mass law) F.G.fam v u /
    Real.sqrt ((F.G.mass law) u / (F.G.mass law) v)

private theorem physical_mask' :
    CycleComparison.Coarse.maskedEdgeMatrix (familyAdj F.G.actualFamily) (physicalEdge F law) =
      physicalEdge F law := by
  classical
  ext v u
  rw [CycleComparison.Coarse.maskedEdgeMatrix_apply]
  split_ifs with h
  · rfl
  · have he : IsEmpty (F.G.fam.Γ v u) := not_nonempty_iff.mp h
    simp only [physicalEdge, Matrix.of_apply, recordMajorant, Fintype.sum_empty, mul_zero, zero_div]

private theorem physical_nonneg' : ∀ v u, 0 ≤ physicalEdge F law v u := by
  intro v u
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
    mul_nonneg (norm_nonneg _) (F.G.fam.identity v u γ).record.size_nonneg)) (Real.sqrt_nonneg _)

private theorem setting_scales' (kc : ℕ) (p : PulseInput F law kc) (g : WindowGeometry F law kc)
    (hfamily : ∃ T, FrameReconFamilyBody F 0 T reconCpart) :
    ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) ≤ fRho F ∧
      fRho F ≤ ocEpsilon D.q D.Λ (F.m - 1) := by
  classical
  obtain ⟨T, hf⟩ := hfamily
  have hs := hf.2.2.2.2.2.2.2.2.1.2.2.1 F.tp ⟨le_rfl, g.window⟩
  obtain ⟨k, hk, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hs]; exact one_ne_zero)
  have hset := p.settings k hk
  exact ⟨(div_le_one hset.ρ_pos).mp hset.εc_le, (div_le_one hset.E_pos).mp hset.lam_le⟩

/-- The normalized positive-grade budget, at both the parent and observation radii. -/
theorem positive_mean_budget (kc : ℕ) (p : PulseInput F law kc)
    (m : PulseModel F law kc p) (g : WindowGeometry F law kc) (hΛ : 128 ≤ D.Λ) (hν : 0 < D.κ F.m) (cb : ChartBounds F)
    (hfamily : ∃ T, FrameReconFamilyBody F 0 T reconCpart) :
    ∃ C : ℝ, ∀ r ∈ Finset.Icc 1 F.depth, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((F.G.mass law) u / (F.G.mass law) v)) *
      ((∑ d : Finset.Icc 2 (F.N + Dm),
        coefficientSeminorm (ocEpsilon D.q D.Λ (F.m - 1)) (fNc F kc)
          F.tp (F.tp + fTobs F) ((positiveGradeLetter F m.Lb r v u d)) *
          (ENNReal.ofReal (D.κ (F.m - 1) * ocEpsilon D.q D.Λ (F.m - 1) ^ (d.1 - 2)))⁻¹) +
      ∑ d : Finset.Icc 2 (F.N + Dm),
        coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) ((positiveGradeLetter F m.Lb r v u d)) *
          (ENNReal.ofReal (D.κ (F.m - 1) * fRho F ^ (d.1 - 2)))⁻¹) ≤
      ENNReal.ofReal (C *
        (Real.sqrt ((F.G.mass law) u / (F.G.mass law) v) *
          (CycleComparison.Coarse.maskedEdgeMatrix (familyAdj F.G.actualFamily) (physicalEdge F law) ^ r) v u)) := by
  classical
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  obtain ⟨hdρ, hρE⟩ := setting_scales' F law kc p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  obtain ⟨Ct, hCt, hbound⟩ := ceLetter_means_bound F.N Dm (fNc F kc)
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨2 * ((F.N + Dm : ℕ) : ℝ) ^ 2 * ((fNc F kc : ℝ) + 1) * (Ct * m.C₂), ?_⟩
  intro r hr v u
  have hM0 : 0 ≤ m.C₂ * (physicalEdge F law ^ r) v u :=
    mul_nonneg m.C₂_nonneg (matrix_pow_apply_nonneg (physical_nonneg' F law) r v u)
  have hreg : (((fNc F kc : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast p.order
  have h3 := hbound
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m)) (D.κ (F.m - 1))
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1))) (fRho F)
    (ocEpsilon D.q D.Λ (F.m - 1)) F.tp (F.tp + fTobs F)
    (chart'' F) (label'' F) (fSeqStart F) (fSeqEnd F) m.Lb r v u
    (m.C₂ * (physicalEdge F law ^ r) v u) hℓ g.B_pos g.rho_pos
    (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _) hdρ hρE hM0 hϖ0 hϖ1
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj hjK y => cb.jets k t hwin j hj y)
    (fun k hk n hn hnN d _ _ α l s hs =>
      ((m.pulse k hk).smooth r (Finset.mem_Icc.mp hr).2 n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk n hn hnN d hd hdn α l i hi s hs Y =>
      (m.pulse k hk).bound r (Finset.mem_Icc.mp hr).2 n hn hnN d hd hdn α l v u i
        (hi.trans p.order) s hs Y) (fNc F kc) le_rfl
  rw [physical_mask' F law] 
  refine (mul_le_mul' le_rfl h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

/-- The diagonal letter has a finite normalized budget. Only boundedness is needed here:
the order-two letter may be bounded by the raw G2 mean plus the reference flux. -/
theorem diagonal_mean_budget (kc : ℕ) (p : PulseInput F law kc)
    (m : PulseModel F law kc p) (g : WindowGeometry F law kc) (hΛ : 128 ≤ D.Λ) (hν : 0 < D.κ F.m) (hζ : IsFastProfile D.ζ) (cb : ChartBounds F)
    (hfamily : ∃ T, FrameReconFamilyBody F 0 T reconCpart) :
    ∃ C : ℝ, ∑ d : Finset.Icc 2 (F.N + Dm),
      coefficientSeminorm (fRho F) (fNc F kc) F.tp (F.tp + fTobs F) (diagonalLetter F m.Lsc d) *
        (ENNReal.ofReal (D.κ (F.m - 1) * fRho F ^ (d.1 - 2)))⁻¹ ≤ ENNReal.ofReal C := by
  classical
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  have hE : 0 < ocEpsilon D.q D.Λ (F.m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  obtain ⟨hdρ, hρE⟩ := setting_scales' F law kc p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, hsupp⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  set B := D.κ (F.m - 1)
  set CJ := D.κ F.m + ocHStar D.α D.q D.Λ F.m (D.κ F.m)
  set gm := ocA D.α D.q D.Λ (F.m - 1) * ocTauPP D.α D.q D.Λ F.m
  have hCJ : 0 ≤ CJ := add_nonneg hν.le (CycleReference.ocHStar_pos hΛ1 hν).le
  have hgm : 0 ≤ gm := mul_nonneg (Real.rpow_nonneg hE.le _)
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hJ : ∀ t, ∀ a b, |ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t a b| ≤ CJ :=
    fun t a b => refFlux_entry_abs_le hΛ1 hζ hν t a b
  have hlam : 0 ≤ fRho F / ocEpsilon D.q D.Λ (F.m - 1) := div_nonneg g.rho_pos.le hE.le
  have hθ : 0 ≤ B * m.C₂ + CJ := add_nonneg (mul_nonneg g.B_pos.le m.C₂_nonneg) hCJ
  have hreg : ∀ i : ℕ, i ≤ fNc F kc →
      (((i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    intro i hi
    exact_mod_cast hi.trans p.order
  have hhigh : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
      ∀ n, 3 ≤ n → n ≤ F.N + Dm → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ fNc F kc →
      ∀ s ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k), ∀ Y,
        ‖iteratedFDeriv ℝ i (m.Lsc k n d α l s) Y‖ ≤
          m.C₂ * (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) ^ (n - d + i) := by
    intro k hk n hn hnN d hd hdn α l i hi s hs Y
    apply scalarReading_jet_le m.reading k n d α l s i Y
    · intro v
      exact ((m.pulse k hk).smooth 0 (Nat.zero_le _) n (by omega) hnN d α l v v s hs).of_le (hreg i hi)
    · intro v
      have hb := (m.pulse k hk).bound 0 (Nat.zero_le _) n (by omega) hnN d hd hdn α l v v i
        (hi.trans p.order) s hs Y
      rw [pow_zero, Matrix.one_apply_eq, mul_one] at hb
      exact hb
    · rw [refFallback_jet_of_ne _ _ _ k (by omega) d α l s i Y]
      exact mul_nonneg m.C₂_nonneg (pow_nonneg hlam _)
  have hpair : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
      ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ fNc F kc →
      ∀ s ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k), ∀ Y,
        ‖iteratedFDeriv ℝ i (fun Y' => B * m.Lsc k 2 2 α l s Y' +
          ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)
            (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 * s) l (α 0)) Y‖ ≤
          (B * m.C₂ + CJ) * (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) ^ i := by
    intro k hk α l i hi s hs Y
    apply scalarReading_pair_jet_le m.reading k 2 2 α l s i Y B _
    · intro v
      exact ((m.pulse k hk).smooth 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 α l v v s hs).of_le (hreg i hi)
    · intro v
      have hb := (m.pulse k hk).bound 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 le_rfl le_rfl α l v v i
        (hi.trans p.order) s hs Y
      simp only [pow_zero, Matrix.one_apply_eq, mul_one, Nat.sub_self, zero_add] at hb
      have hraw := CycleComparison.Diagonal.norm_iteratedFDeriv_smul_add_const_le i
        (fun Y' => m.Lb k 0 2 2 α s Y' l v v) (ContinuousLinearMap.id ℝ (hr v.1.root)) B 0
        (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)
          (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 * s) l (α 0)) g.B_pos.le
        (((m.pulse k hk).smooth 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 α l v v s hs).of_le (hreg i hi)) Y
      simp only [zero_smul, sub_zero, mul_zero, zero_add] at hraw
      refine hraw.trans ?_
      by_cases hi0 : i = 0
      · subst hi0
        simp only [ite_true, pow_zero, mul_one] at hb ⊢
        refine add_le_add (mul_le_mul_of_nonneg_left hb g.B_pos.le) ?_
        exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)).trans
          (by simpa only [mul_one] using hJ _ l (α 0))
      · rw [ite_eq_right hi0, add_zero, add_mul]
        exact (mul_le_mul_of_nonneg_left hb g.B_pos.le).trans
          (by simpa only [B, mul_assoc] using
            (le_add_of_nonneg_right (a := B * m.C₂ * (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) ^ i)
              (mul_nonneg hCJ (pow_nonneg hlam i))))
    · rw [refFallback_pair_jet B _ g.B_pos.ne' _ k α l s i Y]
      exact mul_nonneg hθ (pow_nonneg hlam _)
  obtain ⟨Cad, -, had⟩ := adLetter_means_bound F.N Dm (fNc F kc)
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨_, had
    (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (fun k => F.G.actualFamily.weight (oddSlotOf k))
    (ocEll D.q D.Λ F.m (D.κ F.m)) B
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1))) (fRho F)
    (ocEpsilon D.q D.Λ (F.m - 1)) F.tp (F.tp + fTobs F)
    (chart'' F) (label'' F) (fSeqStart F) (fSeqEnd F) m.Lsc
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) m.C₂ (B * m.C₂ + CJ)
    (CycleComparison.Charts.chartDevConst (fNc F kc) * gm) CJ g.D_ge hℓ g.B_pos g.rho_pos
    (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _) hdρ hρE m.C₂_nonneg hθ
    (mul_nonneg (CycleComparison.Charts.chartDevConst_nonneg _) hgm) hCJ hϖ0 hϖ1
    (fun k hk t ht hn => cellTime_mem_liftWindow (pow_pos hℓ 2) (hsupp k hk t hn) ht)
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj hjK y => cb.jets k t hwin j hj y)
    (fun k _ t _ hwin a b => cb.deviation k t hwin (fNc F kc) a b)
    (fun t _ a b => hJ t a b) m.scalar_smooth hhigh hpair (fNc F kc) le_rfl⟩

/-- G1's explicit mean model supplies the normalized budget input of the reconstruction letters. -/
theorem meanBudget_of_model (kc : ℕ) (p : PulseInput F law kc) (m : PulseModel F law kc p)
    (g : WindowGeometry F law kc) (hΛ : 128 ≤ D.Λ) (hν : 0 < D.κ F.m) (hζ : IsFastProfile D.ζ) (cb : ChartBounds F)
    (hfamily : ∃ T, FrameReconFamilyBody F 0 T reconCpart) : Nonempty (MeanBudget F law kc) := by
  obtain ⟨Ca, hCa⟩ := diagonal_mean_budget F law kc p m g hΛ hν hζ cb hfamily
  obtain ⟨Ce, hCe⟩ := positive_mean_budget F law kc p m g hΛ hν cb hfamily
  exact ⟨{
    AD := diagonalLetter F m.Lsc
    CE := positiveGradeLetter F m.Lb
    Lb := m.Lb
    transferCost := m.C₁
    physicalEdge := physicalEdge F law
    physical_nonneg := physical_nonneg' F law
    diagonalCost := Ca
    edgeCost := Ce
    actual := m.actual
    diagonal_bound := hCa
    edge_bound := hCe }⟩
end

/-! The two source ingredients of the reconstruction letters at a cascade frame. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The chart bounds are geometric consequences of the stream construction, at every anchor. -/
theorem chartBounds {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (F : Frame D hr Dm b j₀)
    (hα : D.α = α) (hqD : D.q = q)
    (hseq : IsOCStreamSeq α q D.Λ ζ D.Φ) (hΛ : 128 ≤ D.Λ)
    (hM : 2 ≤ F.m) (hν : 0 < D.κ F.m) : ChartBounds F := by
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hℓ : 0 < ocEll D.q D.Λ F.m (D.κ F.m) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  constructor
  · intro k t hwin j hj y
    have ha := abs_sub_anchor_le D.α D.q hΛ1 F.m hℓ F.tp (F.tp + fTobs F) k hwin
    simp only [chart'', label'', hα, hqD]
    exact CycleComparison.Charts.ocChart_window_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      D.Λ hΛ D.Φ hseq F.m hM (D.hΦ (F.m - 1)) _ t
      (by simpa only [hα, hqD] using ha) j hj y
  · intro k t hwin K a b
    have ha := abs_sub_anchor_le D.α D.q hΛ1 F.m hℓ F.tp (F.tp + fTobs F) k hwin
    dsimp only [chart'']
    simpa only [hα, hqD] using CycleComparison.Charts.ocChart_jac_deviation
      α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ D.Λ hΛ D.Φ hseq F.m hM
      (D.hΦ (F.m - 1)) (ocPulseChartIndex D.α D.q D.Λ F.m k) t
      (by simpa only [hα, hqD] using ha) K a b
end

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
open AVRegularity.Construction.Residual.Presentation AVRegularity
open AVRegularity.EntryTerminal.Ingredients.ResidualFlux
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **K3.1, step 1: the mass of the root flux defect rows of a successor with a FAMILY of
kernels** (generic over the stages).

The terminal row master `rootFlux_hasFluxBound` (`ResidualFlux/S179RowMaster.lean`) is stated for
two constant kernels (the weak kernel and the fresh kernel of the terminal menu). At a cascade
frame the kernel of an identity of the successor is `G'.kernelOf P seedK freshK`: a seed kernel of
arbitrary order and of the width of its record, or the fresh kernel of its birth. The generic
defect bound `FDData.timeBound` allows a family of kernels with one admissibility constant `Γ_k`,
one number of moments `L` and one width ratio `q`; so the rows are bounded in one step:

`rootFlux_hasFluxBound'`: if the coefficients of `G'` are regular on the window (`CoeffReg`),
every kernel of `G'` is admissible with `L` moments, of positive width at most `q ρ`, the kernel
Schur matrix of the coefficients of the identities out of the components of `G` has Schur bound
`θ`, and the zero extension of `aZ` has a representative of order `K + 1 ≥ k + (D_m - 2) + L + 1`
with gradient energy at most `E`, then the rows `rootFluxDefect` have a realization of order `k`
with mass at most `q^L · M_c · θ · E`.

Special cases: no identity out of `G` (the rows are `0`); `q = 0` is excluded by the positive
widths unless there is no identity; `L = 0` (no gain, the bound is `M_c θ E`); `t₀ = t₁`. -/

open scoped Classical

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The defect data of a successor `G'`: the kernels `G'.kernelOf` (all admissible at `Γ_k` with
`L` moments, of width at most `q ρ`) and the coefficients of `G'`. -/
def FilterFD (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (G' : GenStage D hr Dm b j₀)
    (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z)
    (hm : ∫ z, φ₀ z = 1) (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall) (t₀ t₁ ρ : ℝ)
    (hρ : 0 < ρ) (k : ℕ) (hD : 2 ≤ Dm) (L : ℕ) (Γk : ℝ) (hΓk : 0 ≤ Γk) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hreg : CoeffReg G' t₀ t₁ ρ k)
    (hadm : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).IsAdmissible Γk L)
    (hwpos : ∀ v u (γ : G'.fam.Γ v u), 0 < (G'.kernelOf P seedK freshK v u γ).width)
    (hwq : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).width ≤ q * ρ) :
    FDData (CompIn G'.comps) (fun v => hr v.1.root) G'.fam.Γ where
  φ₀ := φ₀
  hφ := hφ
  hd := hd
  hnonneg := hnn
  hmass := hm
  hsupp := hs
  t₀ := t₀
  t₁ := t₁
  ρ := ρ
  hρ := hρ
  k := k
  D := Dm
  hD := hD
  L := L
  Γk := Γk
  hΓk := hΓk
  q := q
  hq0 := hq0
  hq1 := hq1
  B := fun i j α d => G'.physCoeff i j α d.1
  hB_meas := fun i j α d => (hreg i j α d).1
  hB_smooth := fun i j α d => (hreg i j α d).2.1
  hB_per := fun i j α d => (hreg i j α d).2.2.1
  hB_fin := fun i j α d => (hreg i j α d).2.2.2
  Kern := fun i j α => G'.kernelOf P seedK freshK i j α
  hadm := hadm
  hwpos := hwpos
  hwq := hwq

/-- The price constant of the rows with the regularizer constants `1`:
`∑_{m ≤ D_m - 2} C₀(L, Γ_k) (k + L + m)!/k!`. -/
def FilterMc (φ₀ : Vec 2 → ℝ) (L k Dm : ℕ) (Γk : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (Dm - 1),
    kdUniformMomentConst φ₀ L Γk * (((k + (L + m)).factorial : ℝ) / k.factorial)

theorem FilterMc_nonneg (φ₀ : Vec 2 → ℝ) (L k Dm : ℕ) {Γk : ℝ} (hΓk : 0 ≤ Γk) :
    0 ≤ FilterMc φ₀ L k Dm Γk :=
  Finset.sum_nonneg fun m _ => mul_nonneg (kdUniformMomentConst_nonneg φ₀ L hΓk) (by positivity)

theorem FilterFD_Mconst (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (G' : GenStage D hr Dm b j₀) (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1)
    (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ) (k : ℕ)
    (hD : 2 ≤ Dm) (L : ℕ) (Γk : ℝ) (hΓk : 0 ≤ Γk) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hreg : CoeffReg G' t₀ t₁ ρ k)
    (hadm : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).IsAdmissible Γk L)
    (hwpos : ∀ v u (γ : G'.fam.Γ v u), 0 < (G'.kernelOf P seedK freshK v u γ).width)
    (hwq : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).width ≤ q * ρ) :
    (FilterFD P seedK freshK G' φ₀ hφ hd hnn hm hs t₀ t₁ ρ hρ k hD L Γk hΓk q hq0 hq1 hreg
      hadm hwpos hwq).Mconst (fun _ => 1) = FilterMc φ₀ L k Dm Γk := by
  simp only [FDData.Mconst, FilterFD, FilterMc, div_one]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **The root flux defect as a masked sum over all the identities of the successor**, on the zero
extension of the representative. -/
theorem rootFluxDefect_eq (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) :
    rootFluxDefect P seedK freshK φ₀ G G' aZ v' t x =
      ∑ j : CompIn G'.comps, ∑ α : G'.fam.Γ v' j, if j.1 ∈ G.comps then
        ∑ d : ↥(Finset.Icc 2 Dm),
          G'.physCoeff v' j α d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => extAZ G G' aZ j t y -
              (G'.kernelOf P seedK freshK v' j α).applyClassical φ₀ t (extAZ G G' aZ j t) y) x)
      else 0 := by
  unfold rootFluxDefect
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u.1 ∈ G.comps
  · have he : extAZ G G' aZ u t = fun y => aZ t y ⟨u.1, hu⟩ :=
      funext fun y => by simp only [extAZ, hu, ↓reduceDIte]
    simp only [hu, ↓reduceDIte, ↓reduceIte, he]
  · simp only [hu, ↓reduceDIte, ↓reduceIte, Finset.sum_const_zero]

/-- **The realized bound of the root flux defect rows of a successor with a family of kernels.** -/
theorem rootFlux_hasFluxBound' [∀ r, Nontrivial (hr r)] (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1)
    (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (t₀ t₁ ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν) (ht01 : t₀ ≤ t₁) (k : ℕ) (hD : 2 ≤ Dm) (L : ℕ)
    (Γk : ℝ) (hΓk : 0 ≤ Γk) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (π : CompIn G'.comps → ℝ) (hπ : ∀ i, 0 < π i) (hreg : CoeffReg G' t₀ t₁ ρ k)
    (hadm : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).IsAdmissible Γk L)
    (hwpos : ∀ v u (γ : G'.fam.Γ v u), 0 < (G'.kernelOf P seedK freshK v u γ).width)
    (hwq : ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).width ≤ q * ρ)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hS : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm t₀ t₁
      (fun _ => 1) (fun v u γ => (G'.kernelOf P seedK freshK v u γ).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff G' (fun _ u _ => u.1 ∈ G.comps))))
    {K : ℕ} (hK : k + (Dm - 2) + L ≤ K)
    (V : ∀ j : CompIn G'.comps, ℝ → TorusHk (K + 1) (hr j.1.root))
    (hcl : ∀ j, ∀ t ∈ Set.Icc t₀ t₁, IsClassicalRep (V j t) (extAZ G G' aZ j t) (K + 1))
    (hmeas : ∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc t₀ t₁)))
    (hint : Integrable (fun t => massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root)
      (K := fun _ => K) ρ π (fun j => (V j t).val)) (volume.restrict (Set.Icc t₀ t₁)))
    {E : ℝ} (hE : Real.sqrt (ν * ∫ s in Set.Icc t₀ t₁,
      massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root) (K := fun _ => K) ρ π
        (fun j => (V j s).val)) ≤ E) :
    HasFluxBound k (Set.Icc t₀ t₁) ν ρ π
      (fun v t x => rootFluxDefect P seedK freshK φ₀ G G' aZ v t x)
      (q ^ L * FilterMc φ₀ L k Dm Γk * θ * E) := by
  have h1 := fdFilt_hasFluxBound (FilterFD P seedK freshK G' φ₀ hφ hd hnn hm hs t₀ t₁ ρ hρ k
    hD L Γk hΓk q hq0 hq1 hreg hadm hwpos hwq) (fun _ u _ => u.1 ∈ G.comps) ht01 π hπ ν hν
    (fun _ => 1) (fun _ _ => one_pos) θ hθ hS hK V (extAZ G G' aZ) hcl hmeas hint hE
  rw [FilterFD_Mconst] at h1
  refine hasFluxBound_congr (fun v t x => ?_) h1
  rw [rootFluxDefect_eq P seedK freshK φ₀ G G' aZ v t x]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
  by_cases hj : j.1 ∈ G.comps
  · simp only [hj, ↓reduceIte]
    rfl
  · simp only [hj, ↓reduceIte]

end AVRegularity.Construction.Residual.Presentation.Cascade
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.InitialLayer

/-! Cell solutions and their energy norm depend only on the jets at times of the interval. -/

/-- The integrated weak identity depends only on the sections on `(s, t]`. -/
theorem cellWeakIdentity_congr_sections (C : CellCoefficients) (s t : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u u' : ℝ → Vec 2 → ℂ) (du du' : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hu : ∀ r ∈ Ioc s t, u r = u' r) (hdu : ∀ r ∈ Ioc s t, du r = du' r)
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t u0 u1 ψ dψ u' du' src F := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS C r (u' r) (du' r) ψ dψ (src r) (F r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t), R r = R' r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [R, R', hu r hr, hdu r hr]
  have hint : (fun r => ∫ x, R r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => ∫ x, R' r x ∂μ := he.mono fun r hr => by simp only [hr]
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1.congr hint, h.2.2.2.2.trans (integral_congr_ae hint)⟩
  filter_upwards [h.2.2.1, he] with r hr her
  rwa [← her]

/-- A cell solution on `I` is a cell solution for any jet agreeing with it at the times of `I`. -/
theorem cellSolution_congr_jet {I : Set ℝ} (hI : MeasurableSet I) {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ} (hDE : ∀ t ∈ I, D t = E t) (h : IsCellSolution I C src F D) :
    IsCellSolution I C src F E := by
  obtain ⟨hoc, hjet, hval, hmeas, hcont, hgrad, hweak⟩ := h
  have hv : ∀ t ∈ I, cellValue E t = cellValue D t := fun t ht => by
    simp only [cellValue, hDE t ht]
  refine ⟨hoc, ?_, fun t ht => hv t ht ▸ hval t ht, fun a => ?_, fun t₀ ht₀ => ?_, ?_, ?_⟩
  · filter_upwards [hjet, ae_restrict_mem hI] with t ht htI
    rwa [← hDE t htI]
  · refine (hmeas a).congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI)] with p hp
    simp only [hDE p.1 hp]
  · refine (hcont t₀ ht₀).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hv t ht, hv t₀ ht₀]
  · intro a ha b hb
    have hsub : Icc a b ⊆ I := hoc.out ha hb
    have hg := hgrad a ha b hb
    rwa [setLIntegral_congr_fun measurableSet_Icc
      (g := fun τ => cellL2Norm (cellGradient (E τ)) ^ 2)
      (fun τ hτ => by simp only [hDE τ (hsub hτ)])] at hg
  · intro s hs t ht hst ψ
    have hsub : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans (hoc.out hs ht)
    rw [hv s hs, hv t ht]
    exact cellWeakIdentity_congr_sections _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun r hr => (hv r (hsub hr)).symm)
      (fun r hr => funext fun k => by simp only [cellGradComp, hDE r (hsub hr)])
      (hweak s hs t ht hst ψ)

/-- The energy norm on `I` depends only on the jets at the times of `I`. -/
theorem cellEnergyNorm_congr_jet {I : Set ℝ} (hI : MeasurableSet I) {D E : ℝ → RawJet2 1 ℂ}
    (hDE : ∀ t ∈ I, D t = E t) : cellEnergyNorm I D = cellEnergyNorm I E := by
  unfold cellEnergyNorm
  congr 1
  · refine iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [cellValue, hDE t ht]
  · exact cellUlNorm_congr_sections I _ _
      ((ae_restrict_mem hI).mono fun t ht => by simp only [hDE t ht]; rfl)

/-- The energy norm is monotone in the interval. -/
theorem cellEnergyNorm_mono {I J : Set ℝ} (hIJ : I ⊆ J) (D : ℝ → RawJet2 1 ℂ) :
    cellEnergyNorm I D ≤ cellEnergyNorm J D := by
  unfold cellEnergyNorm cellUlNorm
  refine add_le_add (biSup_mono hIJ) (iSup_mono fun a => ?_)
  exact ENNReal.rpow_le_rpow (lintegral_mono_set (inter_subset_inter_right _ hIJ)) (by norm_num)

end AVRegularity.InitialLayer
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.InitialLayer

/-! The initial-layer comparison of the original-start and clipped-start lifts, under cell
regularity `1 ≤ sZ`. The degree-one grade-zero source reads only the identity lift `C_0`, which
both sequences fix on `[t₀', t₁]`, so the difference of the two cell inverses is a homogeneous cell
solution started from the trace of the original-start lift. The gradient jet of a difference is the
difference of the gradient jets only where both fields are differentiable, whence `1 ≤ sZ`. -/

/-- The value of the jet of a field. -/
theorem cellValue_cellJetOfField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E) (t : ℝ) (x : Vec 2) :
    cellValue (cellJetOfField ℓ c) t x = ((ℓ (c t x) : ℝ) : ℂ) := by
  simp [cellValue, cellJetOfField, valueIndex2, valueIndex]

/-- The jet of a difference of fields differentiable at the time `t`. -/
theorem cellJetOfField_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c c' : ℝ → Vec 2 → E) (t : ℝ) (hc : Differentiable ℝ (c t))
    (hc' : Differentiable ℝ (c' t)) :
    cellJetOfField ℓ c t + (-1 : ℝ) • cellJetOfField ℓ c' t =
      cellJetOfField ℓ (fun t z => c t z - c' t z) t := by
  funext a x
  simp only [cellJetOfField, Pi.add_apply, Pi.smul_apply]
  split_ifs with ha
  · rw [fderiv_fun_sub (hc x) (hc' x)]
    simp only [sub_apply, map_sub, Complex.ofReal_sub, Complex.real_smul,
      Complex.ofReal_neg, Complex.ofReal_one]
    ring
  · simp only [map_sub, Complex.ofReal_sub, Complex.real_smul, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring

theorem isFiniteMeasure_unitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have hsub : AVenhance.unitCube ⊆ Set.Icc (0 : Vec 2) 1 := fun x hx =>
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
  exact (measure_mono hsub).trans_lt measure_Icc_lt_top

/-- **Initial-layer comparison**, under the cell regularity `1 ≤ sZ` (conditional helper of
`comparison_lift_initial_layer`). -/
theorem comparison_lift_initial_layer_of_one_le_sZ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Dm : ℕ} (Q : LiftOperatorData ι h Dm) (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (t₀ t₀' t₁ : ℝ) (N H : ℕ)
    (ht : t₀ ≤ t₀') (hN : 1 ≤ N)
    (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hC' : IsLiftSequence Q sX sZ t₀' t₁ N H Cc') :
    ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ X,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀' t₁
        (fun z => liftApply 1 (Cc 0 1) (fun _ => a₀) t₀' X z)
        (fun _ _ => 0)
        (fun t z => liftApply 1 (Cc 0 1) (fun _ => a₀) t X z -
          liftApply 1 (Cc' 0 1) (fun _ => a₀) t X z) := by
  intro a₀ ha X
  set c1 : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply 1 (Cc 0 1) (fun _ => a₀) t X z
  set c2 : ℝ → Vec 2 → ∀ i, h i := fun t z => liftApply 1 (Cc' 0 1) (fun _ => a₀) t X z
  have h1 := hC.2.2.2.2.2.2 0 (Nat.zero_le _) 1 le_rfl hN a₀ ha X
  have h2 := hC'.2.2.2.2.2.2 0 (Nat.zero_le _) 1 le_rfl hN a₀ ha X
  have hsub : Icc t₀' t₁ ⊆ Icc t₀ t₁ := Icc_subset_Icc ht le_rfl
  have hsrc : ∀ t ∈ Icc t₀' t₁, ∀ z, liftCellSource Q Cc (fun _ => a₀) 0 1 t X z =
      liftCellSource Q Cc' (fun _ => a₀) 0 1 t X z := by
    intro t htI z
    have e : liftApply 0 (Cc 0 0) (fun _ => a₀) t = liftApply 0 (Cc' 0 0) (fun _ => a₀) t := by
      funext X' z'
      rw [hC.1 a₀ ha t (hsub htI) X' z', hC'.1 a₀ ha t htI X' z']
    simp [liftCellSource, liftMean, liftA, e]
  have hsZ0 : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.1 hsZ)
  have hjet : ∀ ℓ : (∀ i, h i) →L[ℝ] ℝ, ∀ t ∈ Icc t₀' t₁,
      (cellJetOfField ℓ c1 + (-1 : ℝ) • cellJetOfField ℓ c2) t =
        cellJetOfField ℓ (fun t z => c1 t z - c2 t z) t := fun ℓ t htI =>
    cellJetOfField_sub ℓ c1 c2 t ((h1.1 t (hsub htI)).differentiable hsZ0)
      ((h2.1 t htI).differentiable hsZ0)
  have := isFiniteMeasure_unitCube
  refine ⟨fun t htI => (h1.1 t (hsub htI)).sub (h2.1 t htI), fun ℓ => ?_⟩
  obtain ⟨S1, M1, -, E1⟩ := h1.2 ℓ
  obtain ⟨S2, M2, I2, E2⟩ := h2.2 ℓ
  have S1' := cellSolution_restrict hsub ordConnected_Icc S1
  have S := cellSolution_congr_jet measurableSet_Icc (hjet ℓ)
    (cellSolution_add S1' (cellSolution_smul S2 (-1)))
  refine ⟨cellSolution_source_congr_sections _ _ _ _ _ _ _ ?_ ?_ S, fun t htI => ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    refine Filter.Eventually.of_forall fun x => ?_
    simp [hsrc r hr x]
  · exact Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun x => by simp
  · have i1 := ((S1.2.2.1 t (hsub htI)).1).integrable one_le_two
    have i2 := ((S2.2.2.1 t htI).1).integrable one_le_two
    have hv : cellValue (cellJetOfField ℓ (fun t z => c1 t z - c2 t z)) t =
        fun x => cellValue (cellJetOfField ℓ c1) t x - cellValue (cellJetOfField ℓ c2) t x := by
      funext x
      simp only [cellValue_cellJetOfField, map_sub, Complex.ofReal_sub]
    have m1 := M1 t (hsub htI)
    have m2 := M2 t htI
    unfold cellMean at m1 m2 ⊢
    rw [hv, integral_sub i1 i2, m1, m2, sub_zero]
  · filter_upwards [I2] with x hx
    rw [cellValue_cellJetOfField] at hx ⊢
    rw [map_sub, Complex.ofReal_sub, hx, map_zero, Complex.ofReal_zero, sub_zero]
  · have hm1 := cellRawGradient_aestronglyMeasurable _ _ S1'.2.2.2.1
    have hm2 := cellRawGradient_aestronglyMeasurable _ _ S2.2.2.2.1
    rw [← cellEnergyNorm_congr_jet measurableSet_Icc (hjet ℓ)]
    refine (cellEnergyNorm_add _ _ _ hm1 ?_).trans_lt ?_
    · exact hm2.const_smul (-1 : ℝ)
    refine ENNReal.add_lt_top.2 ⟨(cellEnergyNorm_mono hsub _).trans_lt E1, ?_⟩
    refine (cellEnergyNorm_smul _ _ _ hm2).trans_lt ?_
    exact ENNReal.mul_lt_top (by simp) E2

end AVRegularity.InitialLayer
end

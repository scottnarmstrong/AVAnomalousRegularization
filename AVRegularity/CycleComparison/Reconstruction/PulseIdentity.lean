-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.FrozenMeasure
import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.QuietDecay.Jet.Cell
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.TailSample
public import AVRegularity.Statements.Intermediate.CycleOutput.OcChartInv
public import AVRegularity.Statements.Intermediate.CycleReference.OcChart
import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Space-time integrability of the tested label identity.** For the label lift of the
finite-rank chart-frame field and its density (`labels_chart_prim`), the integrand of the tested
label identity, `⟪∂_t V, φ(χ)⟫ + ⟪V, ∇φ(χ) · W(χ)⟫`, is integrable for the product of the
physical window and the unit cell (`setting_label_integrable`). This is the space-time
integrability that `tested_label_prim` (hence `tested_chart_prim`) requires. The density is the
bounded frozen part plus the mode lifts weighted by the integrable derivatives `c_k'` of the coarse
coefficients (`setting_labelDensity_decomp`), and the lift is the mode lifts weighted by the
continuous coefficients (`labelLift_decomp`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The material derivatives of the chart modes are periodic in the slow variable. -/
theorem chartModeDot_periodic {κ : Type*} (φ : κ → Vec 2 → ∀ i, h i)
    (hφp : ∀ k, IsZ2Periodic (φ k)) (χ W : ℝ → Vec 2 → Vec 2)
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    (hWp : ∀ t, IsZ2Periodic (W t)) {c ρ : ℝ} (hρ : 0 < ρ) (k : κ) (s : ℝ) (X : Vec 2)
    (n : Fin 2 → ℤ) :
    chartModeDot φ χ W c ρ k s (X + ρ⁻¹ • latticeShift n) = chartModeDot φ χ W c ρ k s X := by
  have hρX : ρ • (X + ρ⁻¹ • latticeShift n) = ρ • X + latticeShift n := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  simp only [chartModeDot, hρX, hχl, fderiv_periodic (hφp k), hWp _ n]

/-- A continuous periodic field is bounded. -/
theorem exists_bound_periodic_field {F : Type*} [NormedAddCommGroup F] {g : Vec 2 → F}
    (hg : Continuous g) (hp : IsZ2Periodic g) : ∃ M, ∀ x, ‖g x‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic (a := 0) (b := 0) one_pos
    (fun p : ℝ × Vec 2 => ‖g p.2‖) (hg.comp continuous_snd).norm
    (fun s X n => by simp only [inv_one, one_smul, hp n X])
  exact ⟨M, fun x => hM 0 ⟨le_rfl, le_rfl⟩ x⟩

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **Space-time integrability of the tested label identity.** -/
theorem setting_label_integrable (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    (hWp : ∀ t, IsZ2Periodic (W t)) (hWb : ∃ M, ∀ t x, ‖W t x‖ ≤ M)
    {c ρs : ℝ} (hc : 0 < c) (hρ : 0 < ρs) (A₀ B₀ : ℝ) (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {es νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹) (v : ι)
    (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    Integrable (Function.uncurry fun t y =>
        inner ℝ (labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
          (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v) (φt (χ t y)) +
        inner ℝ (labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v)
          (fderiv ℝ φt (χ t y) (W t (χ t y))))
      ((volume.restrict (Ioc (c * a) (c * b))).prod (volume.restrict AVenhance.unitCube)) := by
  have hab : a ≤ b := P.window
  have hcab : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab hc.le
  have hsub : uIcc (c * a) (c * b) ⊆ uIcc A₀ B₀ := by
    rw [uIcc_of_le hcab, uIcc_of_le (hA.trans (hcab.trans hB))]
    exact Icc_subset_Icc hA hB
  have hcfc : ∀ k, ContinuousOn (cf k) (Icc A₀ B₀) := fun k =>
    (hcf k).continuousOn (hA.trans (hcab.trans hB))
  have hmem : ∀ t ∈ Icc (c * a) (c * b), c⁻¹ * t ∈ Icc a b := fun t ht =>
    ⟨by rw [le_inv_mul_iff₀ hc]; exact ht.1, by rw [inv_mul_le_iff₀ hc]; exact ht.2⟩
  have hclamp : ∀ k, Continuous (fun p : ℝ × Vec 2 =>
      cf k (projIcc (c * a) (c * b) hcab p.1 : ℝ)) := fun k =>
    (hcfc k).comp_continuous (continuous_subtype_val.comp (continuous_projIcc.comp
      continuous_fst)) fun p => Icc_subset_Icc hA hB (projIcc (c * a) (c * b) hcab p.1).2
  -- the tests
  have hχc : Continuous (fun p : ℝ × Vec 2 => χ p.1 p.2) := hχ.continuous
  have hΦm : Measurable (fun p : ℝ × Vec 2 => φt (χ p.1 p.2)) :=
    (hφt.continuous.comp hχc).measurable
  obtain ⟨Mφ, hMφ⟩ := exists_bound_periodic_field hφt.continuous hφtp
  have hφ'p : IsZ2Periodic (fderiv ℝ φt) := fun n x => fderiv_periodic hφtp n x
  obtain ⟨Mφ', hMφ'⟩ := exists_bound_periodic_field (hφt.continuous_fderiv one_ne_zero) hφ'p
  obtain ⟨MW, hMW⟩ := hWb
  have hΨm : Measurable (fun p : ℝ × Vec 2 => fderiv ℝ φt (χ p.1 p.2) (W p.1 (χ p.1 p.2))) :=
    (((hφt.continuous_fderiv one_ne_zero).comp hχc).clm_apply
      (hW.continuous.comp (continuous_fst.prodMk hχc))).measurable
  have hI1 : Integrable (Function.uncurry fun t y =>
      inner ℝ (labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
        (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v) (φt (χ t y)))
      ((volume.restrict (Ioc (c * a) (c * b))).prod (volume.restrict AVenhance.unitCube)) := by
    refine integrable_inner_decomp hcab (fun t y => labelDensity Q Cc N H ε
        (chartField cf φ χ c ρs) (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v)
      (fun t y => labelFrozen Q Cc N H ε lam cf φ χ W c ρs es t y v)
      (fun k t y => labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v) dcf
      (fun t y => φt (χ t y))
      (fun t ht y => setting_labelDensity_decomp P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ χ W hχ
        hW hG w hc hv h1 h2 h3 hc₁ t (hmem t ht) y v) ?_ ?_
      (fun k => setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
        (chartMode_contDiff φ hφ χ hχ c ρs k) ρs es hc hcab v)
      (fun k => ?_) (fun k => ((hcf k).1).mono_set hsub) hΦm
      ⟨Mφ, fun t y => hMφ _⟩
    · -- measurability of the frozen part
      simp only [labelFrozen_eq]
      refine (setting_frozenCoeff_measurable P sX sZ hsX hsZ Cc hseq ε cf φ hφ χ hχ hc hcab
        hA hB hcfc v).add (Measurable.const_smul (Finset.measurable_sum _ fun k _ => ?_) _)
      exact (hclamp k).measurable.smul (setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
        (chartModeDot_contDiff φ hφ χ W hχ hW c ρs k) ρs es hc hcab v)
    · -- bound of the frozen part
      obtain ⟨M₀, hM₀⟩ := setting_frozenCoeff_bound P sX sZ hsZ Cc hseq ε cf φ hφ hφp χ hχ hχl
        (es := es) hc hρ hA hB hcfc v
      have hb : ∀ k, ∃ M : ℝ, ∀ t, c⁻¹ * t ∈ Icc a b → ∀ y,
          ‖labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v‖ ≤ M := fun k =>
        setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
          (chartModeDot_contDiff φ hφ χ W hχ hW c ρs k) hρ
          (fun s X n => chartModeDot_periodic φ hφp χ W hχl hWp hρ k s X n) es c v
      choose Mk hMk using hb
      have hcb : ∀ k, ∃ C : ℝ, ∀ x ∈ Icc A₀ B₀, ‖cf k x‖ ≤ C := fun k =>
        isCompact_Icc.exists_bound_of_continuousOn (hcfc k)
      choose Ck hCk using hcb
      refine ⟨M₀ + |c⁻¹| * ∑ k, max (Ck k) 0 * max (Mk k) 0, fun t ht y => ?_⟩
      have hs := hmem t ht
      have htI : t ∈ Icc A₀ B₀ := Icc_subset_Icc hA hB ht
      rw [labelFrozen_eq]
      refine (norm_add_le _ _).trans (add_le_add (hM₀ t hs y) ?_)
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _)
      rw [norm_smul]
      exact mul_le_mul ((hCk k t htI).trans (le_max_left _ _))
        ((hMk k t hs y).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
    · -- bounds of the mode lifts
      obtain ⟨M, hM⟩ := setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
        (chartMode_contDiff φ hφ χ hχ c ρs k) hρ
        (fun s X n => chartMode_periodic φ hφp χ hχl hρ k s X n) es c v
      exact ⟨M, fun t ht y => hM t (hmem t ht) y⟩
  have hI2 : Integrable (Function.uncurry fun t y =>
      inner ℝ (labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v)
        (fderiv ℝ φt (χ t y) (W t (χ t y))))
      ((volume.restrict (Ioc (c * a) (c * b))).prod (volume.restrict AVenhance.unitCube)) := by
    refine integrable_inner_decomp (κ := κ) hcab
      (fun t y => labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v)
      (fun _ _ => (0 : h v))
      (fun k t y => labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v) cf
      (fun t y => fderiv ℝ φt (χ t y) (W t (χ t y)))
      (fun t _ y => by
        simp only [labelLift_decomp Cc N H ε cf φ hφ χ hχ hc.ne' ρs es t y, Finset.sum_apply,
          Pi.smul_apply, zero_add])
      measurable_const ⟨0, fun _ _ _ => by simp⟩
      (fun k => setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
        (chartMode_contDiff φ hφ χ hχ c ρs k) ρs es hc hcab v)
      (fun k => ?_)
      (fun k => ((hcfc k).mono (Icc_subset_Icc hA hB)).intervalIntegrable_of_Icc hcab) hΨm
      ⟨Mφ' * MW, fun t y => ?_⟩
    · obtain ⟨M, hM⟩ := setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
        (chartMode_contDiff φ hφ χ hχ c ρs k) hρ
        (fun s X n => chartMode_periodic φ hφp χ hχl hρ k s X n) es c v
      exact ⟨M, fun t ht y => hM t (hmem t ht) y⟩
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hMφ' _) (hMW _ _)
        (norm_nonneg _) ((norm_nonneg _).trans (hMφ' 0)))
  exact hI1.add hI2
end

/-! **The label density at a fixed time.** At a time of the window the label density of the lift of
the finite-rank chart-frame field is a measurable and bounded function of the label
(`setting_labelDensity_section`): it is the frozen part plus the mode lifts weighted by the time
derivatives of the coarse coefficients at that time (`setting_labelDensity_decomp`), each of which
is a section of a jointly measurable bounded field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The label density at a fixed time of the window is measurable and bounded in the label.** -/
theorem setting_labelDensity_section (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    (hWp : ∀ t, IsZ2Periodic (W t))
    {c ρs : ℝ} (hc : 0 < c) (hρ : 0 < ρs) (A₀ B₀ : ℝ) (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {es νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹) (v : ι)
    (t : ℝ) (ht : t ∈ Icc (c * a) (c * b)) :
    Measurable (fun y => labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
        (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v) ∧
      ∃ M : ℝ, ∀ y, ‖labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
        (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v‖ ≤ M := by
  have hab : a ≤ b := P.window
  have hcab : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab hc.le
  have hs : c⁻¹ * t ∈ Icc a b :=
    ⟨by rw [le_inv_mul_iff₀ hc]; exact ht.1, by rw [inv_mul_le_iff₀ hc]; exact ht.2⟩
  have hcfc : ∀ k, ContinuousOn (cf k) (Icc A₀ B₀) := fun k =>
    (hcf k).continuousOn (hA.trans (hcab.trans hB))
  have hproj : (projIcc (c * a) (c * b) hcab t : ℝ) = t := by rw [projIcc_of_mem hcab ht]
  have hsec : ∀ {G' : ℝ → Vec 2 → h v},
      Measurable (fun p : ℝ × Vec 2 => G' (projIcc (c * a) (c * b) hcab p.1) p.2) →
      Measurable (fun y => G' t y) := by
    intro G' hG'
    have h0 := hG'.comp (measurable_const.prodMk measurable_id :
      Measurable fun y : Vec 2 => (t, y))
    simp only [Function.comp_def, hproj] at h0
    exact h0
  have hdec : ∀ y, labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
      (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v =
      frozenCoeff Q Cc N H ε lam cf φ χ c ρs es t y v +
        c⁻¹ • ∑ k, cf k t • labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v +
        ∑ k, dcf k t • labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v := fun y => by
    rw [setting_labelDensity_decomp P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ χ W hχ hW hG w hc hv
      h1 h2 h3 hc₁ t hs y v, labelFrozen_eq]
  have hmd : ∀ k, Measurable (fun y =>
      labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v) := fun k =>
    hsec (G' := fun s y => labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c s y v)
      (setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
      (chartModeDot_contDiff φ hφ χ W hχ hW c ρs k) ρs es hc hcab v)
  have hmo : ∀ k, Measurable (fun y =>
      labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v) := fun k =>
    hsec (G' := fun s y => labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c s y v)
      (setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
      (chartMode_contDiff φ hφ χ hχ c ρs k) ρs es hc hcab v)
  have hfr : Measurable (fun y => frozenCoeff Q Cc N H ε lam cf φ χ c ρs es t y v) :=
    hsec (G' := fun s y => frozenCoeff Q Cc N H ε lam cf φ χ c ρs es s y v)
      (setting_frozenCoeff_measurable P sX sZ hsX hsZ Cc hseq ε cf φ hφ χ hχ hc hcab hA hB
      hcfc v)
  refine ⟨?_, ?_⟩
  · simp only [hdec]
    exact (hfr.add ((Finset.measurable_sum _ fun k _ => (hmd k).const_smul _).const_smul _)).add
      (Finset.measurable_sum _ fun k _ => (hmo k).const_smul _)
  · obtain ⟨M₀, hM₀⟩ := setting_frozenCoeff_bound P sX sZ hsZ Cc hseq ε cf φ hφ hφp χ hχ hχl
      (es := es) hc hρ hA hB hcfc v
    have hbd : ∀ k, ∃ M : ℝ, ∀ y,
        ‖labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v‖ ≤ M := fun k => by
      obtain ⟨M, hM⟩ := setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
        (chartModeDot_contDiff φ hφ χ W hχ hW c ρs k) hρ
        (fun s X n => chartModeDot_periodic φ hφp χ W hχl hWp hρ k s X n) es c v
      exact ⟨M, fun y => hM t hs y⟩
    have hbo : ∀ k, ∃ M : ℝ, ∀ y,
        ‖labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v‖ ≤ M := fun k => by
      obtain ⟨M, hM⟩ := setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
        (chartMode_contDiff φ hφ χ hχ c ρs k) hρ
        (fun s X n => chartMode_periodic φ hφp χ hχl hρ k s X n) es c v
      exact ⟨M, fun y => hM t hs y⟩
    choose Md hMd using hbd
    choose Mo hMo using hbo
    refine ⟨M₀ + |c⁻¹| * ∑ k, |cf k t| * Md k + ∑ k, |dcf k t| * Mo k, fun y => ?_⟩
    rw [hdec]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hM₀ t hs y)
      ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
        (abs_nonneg _)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMd k y) (abs_nonneg _)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMo k y) (abs_nonneg _)
end

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Slow periodicity of the lift objects on the window** (on `𝕋²`, `e⁻¹ ∈ ℕ` and
`ρ⁻¹ℤ²`-periodicity in `X` are required). The lift objects at a time depend on the lift
coefficients only at that time and at grades not above the current one (`*_congr_time`). The lift
coefficients are invariant under a slow translation `T` that leaves the metric and the source
coefficients invariant (`setting_liftSequence_slowShift_invariant`), so with the translation
lemmas of `CycleComparison.LiftMeanEntrywise` (`sourceOp_slowShift`, …) the cell source of a
`T`-periodic coarse field is `T`-periodic on the window (`setting_liftCellSource_slowShift_eq`),
and so are the calibrated coefficient sources (`setting_calibrated_slowPeriodic`, through the
exponential tests) and the coefficient time densities (`setting_coeffDot_slowPeriodic`). -/

section Congr

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The lift of one degree at a time depends on the coefficients only at that time. -/
theorem liftApply_congr_time {n : ℕ} {c₁ c₂ : LiftCoeff ι h} {a b : ℝ → Vec 2 → ∀ i, h i}
    {t : ℝ} (hc : ∀ m α X z, c₁ m α t X z = c₂ m α t X z) (hab : a t = b t) :
    liftApply n c₁ a t = liftApply n c₂ b t := by
  funext X z v
  simp only [liftApply, hc, hab]

/-- `liftA` at a time depends on the coefficients only at that time and grades `≤ hh`. -/
theorem liftA_congr_time (Q : LiftOperatorData ι h D) {Cc₁ Cc₂ : ℕ → ℕ → LiftCoeff ι h}
    (a : ℝ → Vec 2 → ∀ i, h i) {hh : ℕ} (n : ℕ) {t : ℝ}
    (hc : ∀ p ≤ hh, ∀ q m α X z, Cc₁ p q m α t X z = Cc₂ p q m α t X z) :
    liftA Q Cc₁ a hh n t = liftA Q Cc₂ a hh n t := by
  have e1 : ∀ q, liftApply q (Cc₁ hh q) a t = liftApply q (Cc₂ hh q) a t := fun q =>
    liftApply_congr_time (hc hh le_rfl q) rfl
  have e2 : ∀ q, liftApply q (Cc₁ (hh - 1) q) a t = liftApply q (Cc₂ (hh - 1) q) a t := fun q =>
    liftApply_congr_time (hc (hh - 1) (Nat.sub_le _ _) q) rfl
  funext X z
  simp only [liftA, e1, e2]

/-- `liftMean` at a time depends on the coefficients only at that time and grades `≤ hh`. -/
theorem liftMean_congr_time (Q : LiftOperatorData ι h D) {Cc₁ Cc₂ : ℕ → ℕ → LiftCoeff ι h}
    (a : ℝ → Vec 2 → ∀ i, h i) {hh : ℕ} (n : ℕ) {t : ℝ}
    (hc : ∀ p ≤ hh, ∀ q m α X z, Cc₁ p q m α t X z = Cc₂ p q m α t X z) :
    liftMean Q Cc₁ a hh n t = liftMean Q Cc₂ a hh n t := by
  funext X
  simp only [liftMean, liftA_congr_time Q a n hc]

/-- The cell source at a time depends on the coefficients only at that time and grades
`≤ hh`. -/
theorem liftCellSource_congr_time (Q : LiftOperatorData ι h D)
    {Cc₁ Cc₂ : ℕ → ℕ → LiftCoeff ι h} (a : ℝ → Vec 2 → ∀ i, h i) {hh : ℕ} (n : ℕ) {t : ℝ}
    (hc : ∀ p ≤ hh, ∀ q m α X z, Cc₁ p q m α t X z = Cc₂ p q m α t X z) :
    liftCellSource Q Cc₁ a hh n t = liftCellSource Q Cc₂ a hh n t := by
  funext X z
  simp only [liftCellSource, liftA_congr_time Q a n hc, liftMean_congr_time Q a n hc]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [liftApply_congr_time (b := liftMean Q Cc₂ a p.2 (n - j))
    (hc p.1 (by omega) j) (liftMean_congr_time Q a (n - j) fun p' hp' => hc p' (by omega))]

end Congr

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The cell source of a translated coarse field is the translated cell source** on the
window. -/
theorem setting_liftCellSource_slowShift_eq (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (f g : ℝ → Vec 2 → ∀ i, h i) (hfg : ∀ s Y, g s Y = f s (Y + T))
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    liftCellSource Q Cc g hh n t X z = liftCellSource Q Cc f hh n t (X + T) z := by
  rw [← liftCellSource_slowShift Q Cc f g T hfg hG hc hh n t X z,
    liftCellSource_congr_time Q g n (Cc₂ := slowShiftSequence T Cc) fun p hp q m α X' z' => ?_]
  funext v u
  exact (setting_liftSequence_slowShift_invariant P sX sZ Cc hseq T hG hc p (hp.trans hhh) q m α
    t ht X' z' v u).symm

include P in
/-- The cell source is homogeneous in the coarse field on the window. -/
theorem setting_liftCellSource_smul (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (r : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Icc a b)
    (X z : Vec 2) :
    liftCellSource Q Cc (fun _ => r • f) hh n t X z =
      r • liftCellSource Q Cc (fun _ => f) hh n t X z := by
  funext v
  rw [Pi.smul_apply, ← setting_liftSource_blockCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh
    n hn hnN (r • f) (hf.const_smul r) t ht X z v, ← setting_liftSource_blockCoefficient_apply P
    sX sZ hsX hsZ Cc hseq hh hhh n hn hnN f hf t ht X z v]
  have hs := liftApply_synthesis (J := Unit) n
    (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
    (fun _ => r • f) (fun _ => r) (fun _ => f) (fun _ => hf.of_le (by exact_mod_cast le_top)) t
    (by funext Y; simp) X z
  rw [hs]
  simp

include P in
/-- **The calibrated coefficient sources are slow-periodic** on the window. -/
theorem setting_calibrated_slowPeriodic (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ)
    (α : DerivativeWord2 m) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t (X + T) z =
      calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z := by
  unfold calibratedLiftSourceEntry normalizedLiftSourceField
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  set A : Vec 2 →L[ℝ] ℝ := lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) with hA
  set f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ with hf
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have hshift : (fun Y => f (Y + T)) = Real.exp (A T) • f := by
    funext Y
    simp only [hf, map_add, Real.exp_add, Pi.smul_apply, smul_smul, mul_comm]
  have h1 := setting_liftCellSource_slowShift_eq P sX sZ Cc hseq T hG hc (fun _ => f)
    (fun _ Y => f (Y + T)) (fun _ _ => rfl) hh hhh n t ht X z
  have h2 : liftCellSource Q Cc (fun _ Y => f (Y + T)) hh n t X z =
      Real.exp (A T) • liftCellSource Q Cc (fun _ => f) hh n t X z := by
    rw [show (fun (_ : ℝ) (Y : Vec 2) => f (Y + T)) = fun _ => Real.exp (A T) • f from
      funext fun _ => hshift]
    exact setting_liftCellSource_smul P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN _ f hfs t ht X z
  change (Real.exp (A (X + T)))⁻¹ • liftCellSource Q Cc (fun _ => f) hh n t (X + T) z v =
    (Real.exp (A X))⁻¹ • liftCellSource Q Cc (fun _ => f) hh n t X z v
  rw [← h1, h2, Pi.smul_apply, smul_smul, map_add, Real.exp_add, mul_inv, mul_assoc,
    inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]

include P in
/-- **The coefficient time densities are slow-periodic** on the window. -/
theorem setting_coeffDot_slowPeriodic (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (T : Vec 2)
    (hG : ∀ t X i j, Q.G t (X + T) i j = Q.G t X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ)
    (α : DerivativeWord2 m) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    coeffDot Q Cc hh n m α lam u v ξ t (X + T) z = coeffDot Q Cc hh n m α lam u v ξ t X z := by
  have hC : (fun y => Cc hh n m α t (X + T) y v u ξ) = fun y => Cc hh n m α t X y v u ξ := by
    funext y
    rw [setting_liftSequence_slowShift_invariant P sX sZ Cc hseq T hG hc hh hhh n m α t ht X y v u]
  have hGX : Q.G t (X + T) = Q.G t X := by
    funext i j
    exact hG t X i j
  simp only [coeffDot, hC, hGX, setting_calibrated_slowPeriodic P sX sZ hsX hsZ Cc hseq T hG hc hh
    hhh n hn hnN m α u v ξ t ht X z]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- The cell drift is periodic in the fast variable on the window. -/
theorem setting_v_periodic (s : ℝ) (hs : s ∈ Icc a b) : IsZ2Periodic (Q.v s) := by
  intro n z
  rw [P.v_shear, P.v_shear]
  congr 1
  have hp := (P.V_per s hs).int_mul (n par.rev) (z par.rev)
  simpa [latticeShift, Pi.add_apply, add_comm] using hp

include P in
/-- **The coefficient time densities are periodic in the fast variable** on the window. -/
theorem setting_coeffDot_fastPeriodic (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ)
    (α : DerivativeWord2 m) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Icc a b) (X : Vec 2) :
    IsZ2Periodic (fun z => coeffDot Q Cc hh n m α lam u v ξ t X z) := by
  have src := setting_liftSequence_source_data P sX sZ (by omega) Cc hseq P₀ hh n hreserve hhh
    hn hnN
  have hψ : IsZ2Periodic (fun y => Cc hh n m α t X y v u ξ) := fun k y => by
    have hp := (hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).2 X k y
    simp only at hp
    simp only [hp]
  have hψ1 : ∀ j, IsZ2Periodic
      (fun y => fderiv ℝ (fun y' => Cc hh n m α t X y' v u ξ) y (basisVec j)) := fun j k y => by
    simp only [fderiv_periodic hψ k y]
  intro k z
  simp only [coeffDot, cellOperator, setting_v_periodic P t ht k z, fderiv_periodic hψ k z,
    fderiv_periodic (hψ1 _) k z, calibratedLiftSourceEntry_periodic src m α u v ξ t ht X k z]

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lift at the start of its window** (its diagonal is the identity and the positive lifts
vanish there). The positive-degree lift coefficients are zero-start
cell inverses (`IsLiftSequence`, last clause), so they vanish at the initial time of the window
(`liftSequence_start_positive`); hence every grade of the truncated lift is the coarse field (grade
`0`) or zero there (`liftPolyField_start`), and the label lift at the start is the coarse field
(`labelLift_start`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The positive lifts vanish at the start of the window.** -/
theorem liftSequence_start_positive {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (ht : t₀ ≤ t₁) {hh n : ℕ} (hhH : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (X z : Vec 2) :
    liftApply n (Cc hh n) (fun _ => a₀) t₀ X z = 0 := by
  have hc := hseq.2.2.2.2.2.2 hh hhH n hn hnN a₀ ha₀ X
  have ht₀ : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, ht⟩
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
  obtain ⟨hsol, -, hstart, -⟩ := hc.2 ℓ
  set f : Vec 2 → ℂ := fun z' => ((ℓ (liftApply n (Cc hh n) (fun _ => a₀) t₀ X z') : ℝ) : ℂ)
    with hf
  have hval : cellValue (cellJetOfField ℓ
      (fun t z' => liftApply n (Cc hh n) (fun _ => a₀) t X z')) t₀ = f := by
    funext z'
    simp [cellValue, cellJetOfField, valueIndex2, valueIndex, f]
  have hcont : Continuous f :=
    Complex.continuous_ofReal.comp (ℓ.continuous.comp (hc.1 t₀ ht₀).continuous)
  have hper : IsZ2Periodic f := by
    rw [← hval]
    exact (hsol.2.2.1 t₀ ht₀).2
  have hae : f =ᵐ[volume.restrict unitCube] 0 := by
    rw [← hval]
    filter_upwards [hstart] with x hx
    rw [hx]
    simp
  have h0 := congrFun (periodicContinuous_zero_of_cell_ae f hcont hper hae) z
  simpa [f] using h0

/-- **Every grade of the truncated lift at the start of the window** is the coarse field (grade
`0`) or zero. -/
theorem liftPolyField_start {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ht : t₀ ≤ t₁)
    {hh : ℕ} (hhH : hh ≤ H) (ε : ℝ) (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (X z : Vec 2) :
    liftPolyField Cc N ε hh (fun _ => a₀) t₀ X z = if hh = 0 then a₀ X else 0 := by
  have ht₀ : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, ht⟩
  simp only [liftPolyField]
  rw [Finset.sum_eq_single 0 (fun n hn hn0 => by
      rw [liftSequence_start_positive hseq ht hhH (Nat.one_le_iff_ne_zero.2 hn0)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) a₀ ha₀ X z, smul_zero])
    (fun h0 => absurd (Finset.mem_range.2 (Nat.succ_pos N)) h0), pow_zero, one_smul]
  by_cases hh0 : hh = 0
  · subst hh0
    rw [hseq.1 a₀ ha₀ t₀ ht₀ X z]
    simp
  · rw [liftApply_of_coeff_zero 0 (Cc hh 0)
      (fun m α t X' z' v u => hseq.2.1 hh (Nat.one_le_iff_ne_zero.2 hh0) hhH m α t X' z' v u)]
    simp [hh0]

/-- **The label lift at the start of the window is the coarse field.** -/
theorem labelLift_start {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ht : t₀ ≤ t₁)
    (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) (f t₀)) (ρs es c : ℝ)
    (hc : c ≠ 0) (y : Vec 2) :
    labelLift Cc N H ε f ρs es c (c * t₀) y = f t₀ (ρs⁻¹ • y) := by
  have hct : c⁻¹ * (c * t₀) = t₀ := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hcongr : ∀ hh, liftPolyField Cc N ε hh f t₀ (ρs⁻¹ • y) (es⁻¹ • y) =
      liftPolyField Cc N ε hh (fun _ => f t₀) t₀ (ρs⁻¹ • y) (es⁻¹ • y) := fun hh => by
    simp only [liftPolyField]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [liftApply_congr_time (c₁ := Cc hh n) (c₂ := Cc hh n) (a := f) (b := fun _ => f t₀)
      (t := t₀) (fun _ _ _ _ => rfl) rfl]
  simp only [labelLift, hct, hcongr]
  rw [Finset.sum_congr rfl fun hh hhm => liftPolyField_start hseq ht
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) ε (f t₀) hf (ρs⁻¹ • y) (es⁻¹ • y)]
  simp

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Periodicity of the label lift and of its density in the label.** If the slow translations
by `ρ⁻¹ℤ²` leave the metric and the source coefficients invariant and `e⁻¹ ∈ ℕ`, the lift
coefficients and their time densities are periodic in the slow variable for the lattice `ρ⁻¹ℤ²`
and in the fast variable, so on the window the label lift `V(t, ·)` of a `ρ⁻¹ℤ²`-periodic coarse
field and its density are `ℤ²`-periodic in the label (`setting_labelLift_periodic`,
`setting_labelDensity_periodic`). This is the periodicity the change of variables of the tested
identity (`tested_chart_prim`) consumes and that makes the physical lift a torus field. -/

/-- An integer multiple of a lattice translation. -/
theorem natCast_smul_latticeShift (M : ℕ) (n : Fin 2 → ℤ) :
    (M : ℝ) • latticeShift n = latticeShift (fun i => (M : ℤ) * n i) := by
  funext i
  simp [latticeShift]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The label lift of a slow-periodic coarse field is periodic in the label** on the window. -/
theorem setting_labelLift_periodic (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ) (g : ℝ → Vec 2 → ∀ i, h i)
    (hg : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (g s)) {ρs es c : ℝ} (M : ℕ) (hM : es⁻¹ = M)
    (hgp : ∀ s X (n : Fin 2 → ℤ), g s (X + ρs⁻¹ • latticeShift n) = g s X)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b) (v : ι) :
    IsZ2Periodic (fun y => labelLift Cc N H ε g ρs es c t y v) := by
  intro n y
  simp only [labelLift_coeff_sum]
  refine Finset.sum_congr rfl fun hh hhmem => Finset.sum_congr rfl fun q' _ => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hX : ρs⁻¹ • (y + latticeShift n) = ρs⁻¹ • y + ρs⁻¹ • latticeShift n := smul_add _ _ _
  have hz : es⁻¹ • (y + latticeShift n) =
      es⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hslow := setting_liftSequence_slowShift_invariant P sX sZ Cc hseq _ (hGs n) (hcs n) hh hhh
    q' p.1.val p.2.1 (c⁻¹ * t) ht (ρs⁻¹ • y) (es⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i))
    v p.2.2
  have hfast := (hseq.2.2.2.2.2.1 hh hhh q' p.1.val p.2.1 v p.2.2 (c⁻¹ * t) ht).2 (ρs⁻¹ • y)
    (fun i => (M : ℤ) * n i) (es⁻¹ • y)
  have hjet := orderedDerivative_periodic ((hg (c⁻¹ * t)).of_le (by exact_mod_cast le_top))
    (ρs⁻¹ • latticeShift n) (fun Y => hgp (c⁻¹ * t) Y n) p.2.1 (ρs⁻¹ • y)
  simp only at hfast
  rw [hX, hz, hslow, hfast, hjet]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The chart-frame field is periodic in the slow variable. -/
theorem chartField_periodic {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ)
    (φ : κ → Vec 2 → ∀ i, h i) (hφp : ∀ k, IsZ2Periodic (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    {c ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) (X : Vec 2) (n : Fin 2 → ℤ) :
    chartField cf φ χ c ρ s (X + ρ⁻¹ • latticeShift n) = chartField cf φ χ c ρ s X := by
  have h := fun k => chartMode_periodic φ hφp χ hχl (c := c) hρ k s X n
  simp only [chartMode] at h
  simp only [chartField, h]

include P in
/-- **The coefficient form of the frozen density is periodic in the label** on the window. -/
theorem setting_frozenCoeff_periodic (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (χ : ℝ → Vec 2 → Vec 2) (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    {c ρs es : ℝ} (hρ : 0 < ρs) (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b) (v : ι) :
    IsZ2Periodic (fun y => frozenCoeff Q Cc N H ε lam cf φ χ c ρs es t y v) := by
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  intro n y
  simp only [frozenCoeff]
  refine Finset.sum_congr rfl fun hh hhmem => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhmem)
  congr 1
  refine Finset.sum_congr rfl fun n' hn' => ?_
  have hn1 : 1 ≤ n' := (Finset.mem_Icc.1 hn').1
  have hnN : n' ≤ N := (Finset.mem_Icc.1 hn').2
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hX : ρs⁻¹ • (y + latticeShift n) = ρs⁻¹ • y + ρs⁻¹ • latticeShift n := smul_add _ _ _
  have hz : es⁻¹ • (y + latticeShift n) =
      es⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hjet := orderedDerivative_periodic
    ((chartField_contDiff cf φ hφ χ hχ c ρs (c⁻¹ * t)).of_le (by exact_mod_cast le_top))
    (ρs⁻¹ • latticeShift n) (fun Y => chartField_periodic cf φ hφp χ hχl hρ (c⁻¹ * t) Y n)
    p.2.1 (ρs⁻¹ • y)
  have hfast := setting_coeffDot_fastPeriodic P sX sZ hsZ Cc hseq 0 hr hh hhh n' hn1 hnN
    p.1.val p.2.1 p.2.2 v (orderedDerivative p.2.1 (chartField cf φ χ c ρs (c⁻¹ * t)) (ρs⁻¹ • y)
      p.2.2) (c⁻¹ * t) ht (ρs⁻¹ • y) (fun i => (M : ℤ) * n i) (es⁻¹ • y)
  simp only at hfast
  rw [hX, hz, hjet, setting_coeffDot_slowPeriodic P sX sZ hsX hsZ Cc hseq _ (hGs n) (hcs n) hh hhh
    n' hn1 hnN p.1.val p.2.1 p.2.2 v _ (c⁻¹ * t) ht (ρs⁻¹ • y) _, hfast]

include P in
/-- **The label density is periodic in the label** on the window. -/
theorem setting_labelDensity_periodic (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    (hWp : ∀ t, IsZ2Periodic (W t))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {ρs es c νs c₁ : ℝ} (hc : 0 < c) (hρ : 0 < ρs)
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹) (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (t : ℝ) (ht : c⁻¹ * t ∈ Icc a b) (v : ι) :
    IsZ2Periodic (fun y => labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
      (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v) := by
  intro n y
  have hdec := fun y' => setting_labelDensity_decomp P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ χ W
    hχ hW hG w hc hv h1 h2 h3 hc₁ t ht y' v
  simp only [hdec, labelFrozen_eq]
  have hfr := setting_frozenCoeff_periodic P sX sZ hsX hsZ Cc hseq ε cf φ hφ hφp χ hχ hχl
    (es := es) hρ M hM hGs hcs t ht v n y
  have hmd : ∀ k, labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t (y + latticeShift n) v =
      labelLift Cc N H ε (chartModeDot φ χ W c ρs k) ρs es c t y v := fun k =>
    setting_labelLift_periodic P sX sZ Cc hseq ε _
      (fun s => (chartModeDot_contDiff φ hφ χ W hχ hW c ρs k).comp
        (contDiff_const.prodMk contDiff_id)) M hM
      (fun s X m => chartModeDot_periodic φ hφp χ W hχl hWp hρ k s X m) hGs hcs t ht v n y
  have hmo : ∀ k, labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t (y + latticeShift n) v =
      labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c t y v := fun k =>
    setting_labelLift_periodic P sX sZ Cc hseq ε _
      (fun s => (chartMode_contDiff φ hφ χ hχ c ρs k).comp
        (contDiff_const.prodMk contDiff_id)) M hM
      (fun s X m => chartMode_periodic φ hφp χ hχl hρ k s X m) hGs hcs t ht v n y
  simp only [hfr, hmd, hmo]

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **Quiet entrance traces of the lift coefficients from the lift grading**. At every time `s` of
the lift window the positive-degree coefficients `C_n^{(hh)}` have actual quiet entrance traces
`I_hh = C Θ^hh` (`HasQuietEntranceTrace`) through slow order `K` and fast order `max k (L + 1)`.

* `mixedCellL2Jet_at_le_cellEnergyJet`: at one time `s ∈ I`, the word-based mixed cell jet of
  slow order `p` after fast order `q ≤ k` is at most `2^p` times the cell energy jet over `I`
  (a slow word is a coordinate of the slow `p`-jet; the slow `p`-jet of a fast word is controlled
  by the fast jets of the slow `p`-jet under the box regularity `(p, q)`,
  `CoarseFluxDiff.mixedCellJet_le_cellEnergyJet'`). Its Schur form is
  `schurMixedCellL2Jet_at_le_schurEnergyJet`.
* The order-zero columns `m = 0` vanish on the window (positive lifts annihilate constants,
  `CycleComparison.Lift.liftSequence_zero_order_coefficient_zero`), so their traces are zero
  (`schurMixedCellL2Jet_at_eq_zero`).
* `setting_raise_fast`: the energy fast order of a lift setting may be raised from `k` to
  `max k (L + 1)`; only the reserve `q_f = max k (L + 2) + ⋯` mentions `k`, and it is unchanged,
  as is the fast box order `max (k + 1) (L + 2)` of the lift sequence.
* `setting_quietEntranceTrace`: the lift grading (`Providers.cycle_lift_grading`) at the raised
  fast order, with `λ ≤ 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

universe u v

namespace AVRegularity.CycleComparison.Reconstruction

/-! ### One time of the window against the energy jets -/

section Compare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One time of the window against the energy jet.** At a time `s ∈ I`, the word-based mixed
cell jet (slow order `p` after fast order `q ≤ k`) is at most `2^p` times the cell energy jet of
fast order `k` and slow order `p` over `I`. -/
theorem mixedCellL2Jet_at_le_cellEnergyJet {I : Set ℝ} {s : ℝ} (hs : s ∈ I) {p q k : ℕ}
    (hqk : q ≤ k) (f : ℝ → Vec 2 → Vec 2 → E) (hf : ∀ t ∈ I, IsBoxSmooth p q (f t)) :
    mixedCellL2Jet {s} p q f ≤ 2 ^ p * cellEnergyJet I k p f := by
  unfold mixedCellL2Jet
  refine iSup₂_le fun t ht => iSup_le fun X => iSup_le fun α => iSup_le fun β => ?_
  have htI : t ∈ I := by
    rw [Set.mem_singleton_iff.1 ht]
    exact hs
  have hFt := hf t htI
  have h0 : IsBoxSmooth p 0 (FastJets.fastL (List.ofFn β) (f t)) :=
    FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) _ (by simpa using hFt)
  have hg : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X' => orderedDerivative β (f t X') z) := fun z =>
    h0.contDiff_slow z
  have h1 : eLpNorm (fun z => orderedDerivative α (fun X' => orderedDerivative β (f t X') z) X)
      2 (volume.restrict AVenhance.unitCube) ≤
      eLpNorm (fun z => iteratedFDeriv ℝ p (fun X' => orderedDerivative β (f t X') z) X) 2
        (volume.restrict AVenhance.unitCube) :=
    eLpNorm_mono (QuietDecay.continuous_orderedDerivative_orderedDerivative hFt le_rfl le_rfl
      α β X).aestronglyMeasurable fun z => norm_orderedDerivative_le (hg z) α X
  have h2 : eLpNorm (fun z => iteratedFDeriv ℝ p (fun X' => orderedDerivative β (f t X') z) X)
      2 (volume.restrict AVenhance.unitCube) ≤ MixedTail.mixedCellJet I p β f := by
    unfold MixedTail.mixedCellJet
    exact le_iSup₂_of_le t htI (le_iSup_of_le X le_rfl)
  exact h1.trans (h2.trans (CoarseFluxDiff.mixedCellJet_le_cellEnergyJet' I hqk β f hf))

end Compare

section Schur

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]

/-- **The Schur form**: at a time `s ∈ I`, the mixed Schur jet of a coefficient array is at most
`2^p` times its Schur energy jet over `I`. -/
theorem schurMixedCellL2Jet_at_le_schurEnergyJet (π : ι → ℝ) {I : Set ℝ} {s : ℝ} (hs : s ∈ I)
    {p q k : ℕ} (hqk : q ≤ k) (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth p q (fun X z => c a t X z v u)) :
    schurMixedCellL2Jet π {s} p q c ≤ 2 ^ p * schurEnergyJet π I k p c := by
  unfold schurMixedCellL2Jet schurEnergyJet
  refine le_trans (AVRegularity.schurSums_mono π fun v u => ?_)
    (MixedTail.schurSums_const_mul_le π _ _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    mixedCellL2Jet_at_le_cellEnergyJet hs hqk _ (fun t ht => hc a v u t ht)

/-- A coefficient array vanishing at the time `s` has zero mixed Schur jets at `s`. -/
theorem schurMixedCellL2Jet_at_eq_zero (π : ι → ℝ) (s : ℝ) (p q : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a X z v u, c a s X z v u = 0) : schurMixedCellL2Jet π {s} p q c = 0 := by
  have hz : ∀ (a : κ) (v u : ι),
      mixedCellL2Jet {s} p q (fun t X z => c a t X z v u) = 0 := by
    intro a v u
    refine le_antisymm ?_ zero_le
    unfold mixedCellL2Jet
    refine iSup₂_le fun t ht => iSup_le fun X => iSup_le fun α => iSup_le fun β => ?_
    have hzero : ∀ X' z', c a t X' z' v u = 0 := fun X' z' => by
      rw [Set.mem_singleton_iff.1 ht]
      exact hc a X' z' v u
    simp [hzero, orderedDerivative_zero_fun]
  have hS : schurSums π (fun _ _ => ∑ _a : κ, (0 : ℝ≥0∞)) = 0 :=
    le_antisymm (max_le (iSup_le fun v => by simp) (iSup_le fun u => by simp)) zero_le
  unfold schurMixedCellL2Jet
  rw [show (fun v u => ∑ a : κ, mixedCellL2Jet {s} p q (fun t X z => c a t X z v u)) =
      fun _ _ => ∑ _a : κ, (0 : ℝ≥0∞) from
    funext fun v => funext fun u => Finset.sum_congr rfl fun a _ => hz a v u, hS]

end Schur

/-! ### The entrance traces -/

/-- **The energy fast order of a lift setting can be raised to `max k (L + 1)`**: the only field
of `IsLiftSetting` mentioning `k` is the reserve `q_f = max k (L + 2) + HD + 2N + 2D`, which is
unchanged. -/
theorem setting_raise_fast {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {b : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ) :
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K (max k (L + 1)) L qs qf
      CG Cw Cj b Θ :=
  { P with
    qf_eq := by rw [P.qf_eq, show max (max k (L + 1)) (L + 2) = max k (L + 2) by omega] }

/-- **Quiet entrance traces from the lift grading.** Under the lift setting at the orders
`(K, k, L)` and the lift sequence at the box orders `(K + D + 2, max (k + 1) (L + 2))`, at every
time `s` of the window the positive-degree coefficients of grade `hh` have quiet entrance traces
`C Θ^hh` through slow order `K' ≤ K` and fast order `L' ≤ max k (L + 1)`; `C` depends only on the
orders and the normalized constants `CG Cw Cj`.

The fast range is that of the cell energy jets: the setting at the raised energy order
`max k (L + 1)` (`setting_raise_fast`) has the same reserve and the same fast box order of the
lift sequence, while fast order `L + 2` at one time is not controlled by the energy and Wiener
jets of the grading. The hypothesis `0 ≤ Θ` makes the traces nonnegative when the family is
empty (otherwise it follows from the envelope). -/
theorem setting_quietEntranceTrace (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
        0 ≤ Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      ∀ s ∈ Set.Icc t₀ t₁, ∀ K' L' : ℕ, K' ≤ K → L' ≤ max k (L + 1) →
        HasQuietEntranceTrace π Cc s lam N H K' L' (fun hh => C * Θ ^ hh) := by
  obtain ⟨C₀, hC₀, hg⟩ :=
    Providers.cycle_lift_grading.{u, v} N K (max k (L + 1)) L D H CG Cw Cj
  refine ⟨2 ^ K * C₀, mul_nonneg (pow_nonneg (by norm_num) _) hC₀, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ P hΘ Cc hseq s hs
    K' L' hK' hL'
  have hseq₂ : IsLiftSequence Q (K + D + 2) (max (max k (L + 1) + 1) (L + 2)) t₀ t₁ N H Cc := by
    rw [show max (max k (L + 1) + 1) (L + 2) = max (k + 1) (L + 2) by omega]
    exact hseq
  have hG := hg Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ (setting_raise_fast P) Cc
    hseq₂
  have hlam0 : 0 ≤ lam := by
    rw [P.lam_eq]
    exact div_nonneg P.ρ_pos.le P.E_pos.le
  refine ⟨fun hh _ => show (0 : ℝ) ≤ 2 ^ K * C₀ * Θ ^ hh from
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hC₀) (pow_nonneg hΘ _),
    fun hh hhH n hn hnN m hmn p hp q hq => ?_⟩
  by_cases hm0 : m = 0
  · -- the order-zero column vanishes on the window
    subst hm0
    exact (schurMixedCellL2Jet_at_eq_zero π s p q (Cc hh n 0) (fun α X z v u =>
      CycleComparison.Lift.liftSequence_zero_order_coefficient_zero P _ _ Cc hseq hh hhH n hn α
        s hs X z v u)).le.trans zero_le
  -- the positive columns: the energy jets of the grading
  have hbox : ∀ (a : DerivativeWord2 m) (v u : ι), ∀ t ∈ Set.Icc t₀ t₁,
      IsBoxSmooth p q (fun X z => Cc hh n m a t X z v u) := fun a v u t ht =>
    isBoxSmooth_mono (hseq.2.2.2.2.2.1 hh hhH n m a v u t ht).1 (by omega) (by omega)
  refine (schurMixedCellL2Jet_at_le_schurEnergyJet π hs (hq.trans hL') (Cc hh n m) hbox).trans ?_
  have hE : schurEnergyJet π (Set.Icc t₀ t₁) (max k (L + 1)) p (Cc hh n m) ≤
      ENNReal.ofReal (C₀ * Θ ^ hh * lam ^ (n - m + p)) :=
    (hG hh hhH n hn hnN m (by omega) hmn p (hp.trans hK')).1
  have h2 : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hA : 0 ≤ C₀ * Θ ^ hh := mul_nonneg hC₀ (pow_nonneg hΘ _)
  have h1 : (2 : ℝ) ^ p ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (hp.trans hK')
  have h3 : lam ^ (n - m + p) ≤ lam ^ p := pow_le_pow_of_le_one hlam0 P.lam_le (by omega)
  have hreal : (2 : ℝ) ^ p * (C₀ * Θ ^ hh * lam ^ (n - m + p)) ≤
      2 ^ K * C₀ * Θ ^ hh * lam ^ p := by
    calc (2 : ℝ) ^ p * (C₀ * Θ ^ hh * lam ^ (n - m + p))
        = 2 ^ p * (C₀ * Θ ^ hh) * lam ^ (n - m + p) := by ring
      _ ≤ 2 ^ K * (C₀ * Θ ^ hh) * lam ^ p :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 hA) h3 (pow_nonneg hlam0 _)
          (mul_nonneg (pow_nonneg (by norm_num) _) hA)
      _ = 2 ^ K * C₀ * Θ ^ hh * lam ^ p := by ring
  show _ ≤ ENNReal.ofReal (2 ^ K * C₀ * Θ ^ hh * lam ^ p)
  calc 2 ^ p * schurEnergyJet π (Set.Icc t₀ t₁) (max k (L + 1)) p (Cc hh n m)
      ≤ 2 ^ p * ENNReal.ofReal (C₀ * Θ ^ hh * lam ^ (n - m + p)) := mul_le_mul_right hE _
    _ = ENNReal.ofReal ((2 : ℝ) ^ p * (C₀ * Θ ^ hh * lam ^ (n - m + p))) := by
        rw [h2, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p)]
    _ ≤ ENNReal.ofReal (2 ^ K * C₀ * Θ ^ hh * lam ^ p) := ENNReal.ofReal_le_ofReal hreal

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tested identity of one pulse lift in physical coordinates**. For the lift of a pulse
with a finite-rank coarse field `∑_k c_k(t) φ_k` read in the pulse's renewal chart
`χ = Φ_{m,l}`, the physical lift `𝒯(t, x) = V(t, ψ(t, x))` (`ψ = Φ_{m,l}⁻¹`) tested against a
periodic `C¹` test `φ` is of integral type on the physical window, with density the label density
read at the labels plus the transport of the test by the background flow `b_{m-1}`
(`setting_pulse_tested`). The label density is turned into physical operators by
`chart_laplacian`, `chart_drift`, `sample_sourceOp_label` and `transportedCoeff_flux`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The tested identity of one pulse lift in physical coordinates.** -/
theorem setting_pulse_tested (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k))
    (α q : ℝ) (Λ m : ℕ) {φs : ℝ → Vec 2 → ℝ} (hφs : IsAdmissibleStream φs) (l : ℤ)
    {c ρs : ℝ} (hc : 0 < c) (hρ : 0 < ρs) (A₀ B₀ : ℝ) (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {es νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹) (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    IsPrimOn (c * a) (c * b)
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ
        (labelLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c t
          (ocChartInv α q Λ m φs hφs l t x) v) (φt x))
      (fun t => ∫ x in AVenhance.unitCube,
        (inner ℝ (labelDensity Q Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs)
            (chartFieldDot cf dcf φ (ocChart α q Λ m φs hφs l) (streamVel φs) c ρs) w ρs es c νs
            t (ocChartInv α q Λ m φs hφs l t x) v) (φt x) +
          inner ℝ (labelLift Cc N H ε (chartField cf φ (ocChart α q Λ m φs hφs l) c ρs) ρs es c
            t (ocChartInv α q Λ m φs hφs l t x) v) (fderiv ℝ φt x (streamVel φs t x)))) := by
  have hab : a ≤ b := P.window
  have hcab : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab hc.le
  have hmem : ∀ t ∈ Icc (c * a) (c * b), c⁻¹ * t ∈ Icc a b := fun t ht =>
    ⟨by rw [le_inv_mul_iff₀ hc]; exact ht.1, by rw [inv_mul_le_iff₀ hc]; exact ht.2⟩
  set χ := ocChart α q Λ m φs hφs l with hχdef
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2) :=
    Charts.contDiff_ocChart_joint hφs α q Λ m l
  have hvel := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφs
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => streamVel φs p.1 p.2) := hvel.smooth
  have hχt : ∀ t y, HasDerivAt (fun t' => χ t' y) (streamVel φs t (χ t y)) t :=
    ocChart_hasDerivAt_time α q Λ m hφs l
  have hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n :=
    fun t y n => Charts.ocChart_latticeShift hφs α q Λ m l t n y
  have hWp : ∀ t, IsZ2Periodic (streamVel φs t) := fun t n x => by
    simpa using hvel.periodic 0 n t x
  have hWb : ∃ M, ∀ t x, ‖streamVel φs t x‖ ≤ M := by
    obtain ⟨C, -, hC⟩ := AVenhance.Infra.Flow.exists_global_iteratedFDeriv_bound hvel 0
    exact ⟨C, fun t x => by simpa using hC (t, x)⟩
  have hgf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (chartField cf φ χ c ρs s) := fun s =>
    chartField_contDiff cf φ hφ χ hχ c ρs s
  refine tested_chart_prim α q Λ m hφs l hcab
    (fun t y => labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v)
    (fun t y => labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
      (chartFieldDot cf dcf φ χ (streamVel φs) c ρs) w ρs es c νs t y v)
    (fun y => labels_chart_prim P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ hφp χ (streamVel φs) hχ hW
      hχt hχl hWp hc hρ A₀ B₀ hA hB hcf hG w hv h1 h2 h3 hc₁ y v)
    (fun t ht => setting_labelLift_periodic P sX sZ Cc hseq ε _ hgf M hM
      (fun s X n => chartField_periodic cf φ hφp χ hχl hρ s X n) hGs hcs t (hmem t ht) v)
    (fun t ht => setting_labelDensity_periodic P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ hφp χ
      (streamVel φs) hχ hW hχl hWp hG w hc hρ hv h1 h2 h3 hc₁ M hM hGs hcs t (hmem t ht) v)
    φt hφt hφtp
    (setting_label_integrable P sX sZ hsX hsZ Cc hseq ε cf dcf φ hφ hφp χ (streamVel φs) hχ hW
      hχl hWp hWb hc hρ A₀ B₀ hA hB hcf hG w hv h1 h2 h3 hc₁ v φt hφt hφtp) ?_
  -- integrability at the initial time, through the modes
  have := isFiniteMeasure_restrict_unitCube
  have hca : c⁻¹ * (c * a) ∈ Icc a b := hmem _ (left_mem_Icc.2 hcab)
  have hdecV : ∀ y, labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c (c * a) y v =
      ∑ k, cf k (c * a) • labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c (c * a) y v := by
    intro y
    rw [labelLift_decomp Cc N H ε cf φ hφ χ hχ hc.ne' ρs es (c * a) y, Finset.sum_apply]
    rfl
  have hLm : ∀ k, Measurable (fun y =>
      labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c (c * a) y v) := by
    intro k
    have h0 := (setting_labelLift_measurable P sX sZ (by omega) Cc hseq ε _
      (chartMode_contDiff φ hφ χ hχ c ρs k) ρs es hc hcab v).comp
      (measurable_const.prodMk measurable_id : Measurable fun y : Vec 2 => (c * a, y))
    simp only [Function.comp_def, projIcc_of_mem hcab (left_mem_Icc.2 hcab)] at h0
    exact h0
  have hLb : ∀ k, ∃ M : ℝ, ∀ y,
      ‖labelLift Cc N H ε (chartMode φ χ c ρs k) ρs es c (c * a) y v‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := setting_labelLift_bound P sX sZ (by omega) Cc hseq ε _
      (chartMode_contDiff φ hφ χ hχ c ρs k) hρ
      (fun s X n => chartMode_periodic φ hφp χ hχl hρ k s X n) es c v
    exact ⟨M, fun y => hM _ hca y⟩
  choose ML hML using hLb
  obtain ⟨Mφ, hMφ⟩ := exists_bound_periodic_field hφt.continuous hφtp
  have hΦc : Continuous (fun y => φt (χ (c * a) y)) :=
    hφt.continuous.comp (hχ.continuous.comp (continuous_const.prodMk continuous_id))
  simp only [hdecV]
  refine Integrable.mono' (integrable_const ((∑ k, |cf k (c * a)| * ML k) * Mφ))
    ((Finset.measurable_sum _ fun k _ => (hLm k).const_smul _).inner
      hΦc.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (hMφ _) (norm_nonneg _)
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) ((norm_nonneg _).trans (hML k 0))))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hML k y) (abs_nonneg _)

end AVRegularity.CycleComparison.Reconstruction
end
end

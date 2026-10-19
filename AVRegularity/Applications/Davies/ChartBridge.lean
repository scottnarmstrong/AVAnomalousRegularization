-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Davies.Equation
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVRegularity.Applications.Pipe.LocalEnergy
public import AVRegularity.Applications.Local.LabelTrace
import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Limit
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
section
/-! # The cutoff energy inequality -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Matrix Filter Topology
open AVRegularity.Applications.LocalEnergy.Moll

namespace AVRegularity.Applications.Davies

theorem memLp_two_mul_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ f : α → ℝ}
    (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) (hf : MemLp f 2 μ) :
    MemLp (fun x => φ x * f x) 2 μ :=
  (memLp_top_of_bound hφ C hb).mul hf

section Setup

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}
  {B : Set (Vec 2)}

theorem ae_mem_cyl {B : Set (Vec 2)} (hB : MeasurableSet B) :
    ∀ᵐ p ∂(volume.restrict (Set.Ioo ta tb ×ˢ B)), p.1 ∈ Set.Icc ta tb := by
  have hm : MeasurableSet (Set.Ioo ta tb ×ˢ B) := measurableSet_Ioo.prod hB
  filter_upwards [ae_restrict_mem hm] with p hp
  exact ⟨hp.1.1.le, hp.1.2.le⟩

theorem memLp_flux (hc : LabelCoeffs G V V₀ ta tb) (hB : MeasurableSet B) {κ : ℝ}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (i : Fin 2) :
    MemLp (fun p => (κ • (G p).mulVec (DU p) - U p • V p) i) 2
      (volume.restrict (Set.Ioo ta tb ×ˢ B)) := by
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hB
  have hG : ∀ j : Fin 2, MemLp (fun p => G p i j * DU p j) 2 μ := fun j =>
    memLp_two_mul_bdd (hc.Gmeas i j).aestronglyMeasurable (C := 9 / 4)
      (hae.mono fun p hp => by rw [Real.norm_eq_abs]; exact hc.entry_bound hp i j) (hDU j)
  have hV : MemLp (fun p => V p i * U p) 2 μ :=
    memLp_two_mul_bdd ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable (C := V₀)
      (hae.mono fun p hp => by rw [Real.norm_eq_abs]; exact hc.Ventry_bound hp i) hU
  have h := ((hG 0).add (hG 1)).const_smul κ |>.sub hV
  refine h.ae_eq (Filter.Eventually.of_forall fun p => ?_)
  fin_cases i <;> simp <;> ring

/-- The two pieces of `fluxE` are integrable on the cylinder. -/
theorem flux_parts_integrable (hc : LabelCoeffs G V V₀ ta tb) {R : ℝ}
    {κ : ℝ} {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    {η : Vec 2 → ℝ} (hη : IsSpTest (euclidBall 0 R) η) (hη1 : ∀ y, |η y| ≤ 1) {N : ℝ} (hN : 0 ≤ N)
    (hηN : ∀ y, vecNormSq (spGrad η y) ≤ N ^ 2) :
    Integrable (fun p : ℝ × Vec 2 => vecDot (κ • (G p).mulVec (DU p) - U p • V p)
      (η p.2 ^ 2 • DU p + (2 * η p.2 * U p) • spGrad η p.2))
      (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)) ∧
    Integrable (fun p : ℝ × Vec 2 => (η p.2 * U p) *
      vecDot (V p) (η p.2 • DU p + U p • spGrad η p.2))
      (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)) := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBo : IsOpen B := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet B := hBo.measurableSet
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hP := memLp_flux hc hBm (κ := κ) hU hDU
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hηc : Continuous η := hη.1.continuous
  have hgc : ∀ i : Fin 2, Continuous fun y => spGrad η y i := fun i =>
    (contDiff_fderiv_apply_of_smooth hη.1 (basisVec i)).continuous
  have hgb : ∀ y (i : Fin 2), |spGrad η y i| ≤ N :=
    fun y i => (abs_coord_le_sqrt _ i).trans (Real.sqrt_le_iff.2 ⟨hN, hηN y⟩)
  have hη_aesm : AEStronglyMeasurable (fun p : ℝ × Vec 2 => η p.2) μ :=
    (hηc.comp continuous_snd).aestronglyMeasurable
  have hg_aesm : ∀ i : Fin 2, AEStronglyMeasurable (fun p : ℝ × Vec 2 => spGrad η p.2 i) μ :=
    fun i => ((hgc i).comp continuous_snd).aestronglyMeasurable
  -- memberships
  have hηU : MemLp (fun p => η p.2 * U p) 2 μ :=
    memLp_two_mul_bdd hη_aesm (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hη1 _) hU
  have hηDU : ∀ i, MemLp (fun p => η p.2 * DU p i) 2 μ := fun i =>
    memLp_two_mul_bdd hη_aesm (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hη1 _) (hDU i)
  have hUg : ∀ i, MemLp (fun p => spGrad η p.2 i * U p) 2 μ := fun i =>
    memLp_two_mul_bdd (hg_aesm i) (C := N)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hgb _ i) hU
  have hDψ : ∀ i, MemLp (fun p => (η p.2 • DU p + U p • spGrad η p.2) i) 2 μ := fun i => by
    refine ((hηDU i).add (hUg i)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
    simp [mul_comm]
  have hW : ∀ i, MemLp (fun p => (η p.2 ^ 2 • DU p + (2 * η p.2 * U p) • spGrad η p.2) i) 2 μ :=
    fun i => by
      have h1 : MemLp (fun p => η p.2 * (η p.2 * DU p i)) 2 μ :=
        memLp_two_mul_bdd hη_aesm (C := 1)
          (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hη1 _) (hηDU i)
      have h2 : MemLp (fun p => (2 * η p.2) * (spGrad η p.2 i * U p)) 2 μ :=
        memLp_two_mul_bdd (hη_aesm.const_mul 2) (C := 2)
          (Filter.Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_mul]; have := hη1 p.2; norm_num; linarith) (hUg i)
      refine (h1.add h2).ae_eq (Filter.Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hψV : ∀ i, MemLp (fun p => V p i * (η p.2 * U p)) 2 μ := fun i =>
    memLp_two_mul_bdd ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable (C := V₀)
      (hae.mono fun p hp => by rw [Real.norm_eq_abs]; exact hc.Ventry_bound hp i) hηU
  -- the two integrands
  set Fh : ℝ × Vec 2 → ℝ := fun p => vecDot (κ • (G p).mulVec (DU p) - U p • V p)
    (η p.2 ^ 2 • DU p + (2 * η p.2 * U p) • spGrad η p.2) with hFh
  set Fψ : ℝ × Vec 2 → ℝ := fun p => (η p.2 * U p) *
    vecDot (V p) (η p.2 • DU p + U p • spGrad η p.2) with hFψ
  have iFh : Integrable Fh μ := by
    have : Fh = fun p => ∑ i : Fin 2, (κ • (G p).mulVec (DU p) - U p • V p) i *
        (η p.2 ^ 2 • DU p + (2 * η p.2 * U p) • spGrad η p.2) i := rfl
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hP i).integrable_mul (hW i)
  have iFψ : Integrable Fψ μ := by
    have : Fψ = fun p => ∑ i : Fin 2, V p i * (η p.2 * U p) *
        (η p.2 • DU p + U p • spGrad η p.2) i := by
      funext p; simp only [hFψ, vecDot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => by
      have := (hψV i).integrable_mul (hDψ i)
      exact this
  exact ⟨iFh, iFψ⟩

theorem cutoff_energy_identity (hc : LabelCoeffs G V V₀ ta tb) (hab : ta < tb) {R : ℝ}
    {κ : ℝ} {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) φ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R,
        (-(U p * stTimeDeriv φ p) + vecDot (κ • (G p).mulVec (DU p) - U p • V p)
          (stSpaceGrad φ p)) = 0)
    {η : Vec 2 → ℝ} (hη : IsSpTest (euclidBall 0 R) η) (hη1 : ∀ y, |η y| ≤ 1) {N : ℝ} (hN : 0 ≤ N)
    (hηN : ∀ y, vecNormSq (spGrad η y) ≤ N ^ 2) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R)), ContinuousOn W (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => η y * U (τ, y)) ∧
      ∀ τ₁ ∈ Set.Icc ta tb, ∀ τ₂ ∈ Set.Icc ta tb, τ₁ ≤ τ₂ →
        ‖W τ₂‖ ^ 2 - ‖W τ₁‖ ^ 2 = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ euclidBall 0 R,
          fluxE κ (G p) (V p) (η p.2) (U p) (DU p) (spGrad η p.2) := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBo : IsOpen B := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet B := hBo.measurableSet
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hP := memLp_flux hc hBm (κ := κ) hU hDU
  have hweak' : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ B) φ →
      ∫ p in Set.Ioo ta tb ×ˢ B, (-(U p * stTimeDeriv φ p) +
        vecDot (κ • (G p).mulVec (DU p) - U p • V p) (stSpaceGrad φ p) -
          (fun _ => (0 : ℝ)) p * φ p) = 0 := by
    intro φ hφ
    simpa using hweak φ hφ
  obtain ⟨W, hWc, hWae, hid⟩ := local_trace_aux hab hBo hU hDU hgrad hP
    (g := fun _ => (0 : ℝ)) MemLp.zero hweak' η hη
  refine ⟨W, hWc, hWae, fun τ₁ h₁ τ₂ h₂ h12 => ?_⟩
  rw [hid τ₁ h₁ τ₂ h₂ h12]
  congr 1
  obtain ⟨iFh, iFψ⟩ := flux_parts_integrable hc (κ := κ) hU hDU hη hη1 hN hηN
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  set Fh : ℝ × Vec 2 → ℝ := fun p => vecDot (κ • (G p).mulVec (DU p) - U p • V p)
    (η p.2 ^ 2 • DU p + (2 * η p.2 * U p) • spGrad η p.2) with hFh
  set Fψ : ℝ × Vec 2 → ℝ := fun p => (η p.2 * U p) *
    vecDot (V p) (η p.2 • DU p + U p • spGrad η p.2) with hFψ
  have hpt : ∀ p, fluxE κ (G p) (V p) (η p.2) (U p) (DU p) (spGrad η p.2) = Fh p + Fψ p := by
    intro p
    have := P_dot_eq κ (G p) (V p) (DU p) (spGrad η p.2) (η p.2) (U p)
    simp only [hFh, hFψ]
    linarith
  have hsl : ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, Fψ p = 0 := by
    rw [setIntegral_Ioc_prod (integrableOn_Ioc_of_Ioo iFψ h₁.1 h₂.2)]
    refine integral_eq_zero_of_ae ?_
    refine ae_Ioc_of_ae_Ioo h₁.1 h₂.2 ?_
    have hUs := ae_slice_memLp_gen hU
    have hDs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)), ∀ i : Fin 2,
        MemLp (fun y => DU (τ, y) i) 2 (volume.restrict B) := by
      rw [Filter.eventually_all]
      exact fun i => ae_slice_memLp_gen (hDU i)
    filter_upwards [hUs, hDs, hgrad, ae_restrict_mem measurableSet_Ioo] with τ hτU hτD hτg hτm
    have hτI : τ ∈ Set.Icc ta tb := ⟨hτm.1.le, hτm.2.le⟩
    have hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => V (τ, y) i) (volume.restrict B) :=
      fun i => (((measurable_pi_apply i).comp hc.Vmeas).comp
        (measurable_prodMk_left (x := τ))).aestronglyMeasurable
    have hbd : ∀ᵐ y ∂(volume.restrict B), vecNormSq (V (τ, y)) ≤ V₀ ^ 2 :=
      Filter.Eventually.of_forall fun y => hc.Vbd (τ, y) hτI
    have hdiv : ∀ ψ0, IsSpTest B ψ0 → ∫ y in B, vecDot (V (τ, y)) (spGrad ψ0 y) = 0 := by
      intro ψ0 hψ0
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hc.Vdiv τ hτI ψ0 hψ0.1 hψ0.2.1
      · intro y hy
        have : y ∉ tsupport ψ0 := fun h => hy (hψ0.2.2 h)
        have h0 : spGrad ψ0 y = 0 := by
          ext i
          simp [spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
        simp [h0, vecDot]
    have hψw := hasWeakGradientOn_smul_smooth hBo hτg hτU hτD hη
    have hψ : MemLp (fun y => η y * U (τ, y)) 2 (volume.restrict B) :=
      memLp_two_mul_bdd hη.1.continuous.aestronglyMeasurable (C := 1)
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hη1 y) hτU
    have hDψ : ∀ i : Fin 2,
        MemLp (fun y => (η y • DU (τ, y) + U (τ, y) • spGrad η y) i) 2 (volume.restrict B) := by
      intro i
      have h1 : MemLp (fun y => η y * DU (τ, y) i) 2 (volume.restrict B) :=
        memLp_two_mul_bdd hη.1.continuous.aestronglyMeasurable (C := 1)
          (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hη1 y) (hτD i)
      have h2 : MemLp (fun y => spGrad η y i * U (τ, y)) 2 (volume.restrict B) :=
        memLp_two_mul_bdd
          (contDiff_fderiv_apply_of_smooth hη.1 (basisVec i)).continuous.aestronglyMeasurable
          (C := N) (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]
            exact (abs_coord_le_sqrt _ i).trans (Real.sqrt_le_iff.2 ⟨hN, hηN y⟩)) hτU
      refine (h1.add h2).ae_eq (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := divFree_slice_mul_grad hBo (pipe_volume_euclidBall_lt_top R).ne hdm hbd hdiv hψ hDψ
      hψw hη.2.1 hη.2.2 (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
    simpa [hFψ, vecDot, mul_comm, mul_left_comm, mul_assoc] using this
  have iFh' := integrableOn_Ioc_of_Ioo iFh h₁.1 h₂.2
  have iFψ' := integrableOn_Ioc_of_Ioo iFψ h₁.1 h₂.2
  simp only [zero_mul, sub_zero]
  change ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, Fh p = _
  simp_rw [hpt]
  rw [integral_add iFh' iFψ', hsl, add_zero]

end Setup

end AVRegularity.Applications.Davies
end
end
end

section
/-! # The cutoff energy bound

`cutoff_energy_bound`: from the cutoff energy inequality
`E(τ₂) + κ∬_{(τ₁,τ₂)×B} ζ² DU·G DU ≤ E(τ₁) + c₁ ∬_{(τ₁,τ₂)×B} U²`, `c₁ = 9κN² + 2V₀N`, averaged
over the initial layer `τ₁ ∈ (ta, ta + σ)`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Matrix Filter Topology
open AVRegularity.Applications.LocalEnergy

namespace AVRegularity.Applications.Davies

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}

/-- Averaging of a pointwise-in-`τ₁` inequality over the initial layer. -/
theorem layer_average {E : ℝ → ℝ} {a σ A B Mx : ℝ} (hσ : 0 < σ)
    (hE : ContinuousOn E (Set.Icc a (a + σ)))
    (hpt : ∀ τ ∈ Set.Icc a (a + σ), A ≤ E τ + B)
    (hint : ∫ τ in Set.Ioc a (a + σ), E τ ≤ Mx) :
    A ≤ Mx / σ + B := by
  have hI : IntegrableOn E (Set.Ioc a (a + σ)) :=
    (hE.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h1 : ∫ τ in Set.Ioc a (a + σ), (A - B) ≤ ∫ τ in Set.Ioc a (a + σ), E τ := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) hI measurableSet_Ioc ?_
    intro τ hτ
    have := hpt τ (Set.Ioc_subset_Icc_self hτ)
    linarith
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)] at h1
  simp only [add_sub_cancel_left, smul_eq_mul] at h1
  rw [div_add' _ _ _ hσ.ne', le_div_iff₀ hσ]
  nlinarith

theorem integrable_quad (hc : LabelCoeffs G V V₀ ta tb) {R : ℝ}
    {DU : ℝ × Vec 2 → Vec 2}
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest (euclidBall 0 R) ζ) (hζ1 : ∀ y, |ζ y| ≤ 1) :
    Integrable (fun p : ℝ × Vec 2 => ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)))
      (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)) := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 R).measurableSet
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hζc : AEStronglyMeasurable (fun p : ℝ × Vec 2 => ζ p.2 ^ 2) μ :=
    ((hζ.1.continuous.comp continuous_snd).pow 2).aestronglyMeasurable
  have hDm : ∀ i, AEStronglyMeasurable (fun p => DU p i) μ := fun i => (hDU i).aestronglyMeasurable
  have hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ := fun i j =>
    (hc.Gmeas i j).aestronglyMeasurable
  have hform : ∀ p, ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) =
      ζ p.2 ^ 2 * (DU p 0 * (G p 0 0 * DU p 0 + G p 0 1 * DU p 1) +
        DU p 1 * (G p 1 0 * DU p 0 + G p 1 1 * DU p 1)) := by
    intro p
    simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p))) μ := by
    simp_rw [hform]
    exact hζc.mul (((hDm 0).mul (((hGm 0 0).mul (hDm 0)).add ((hGm 0 1).mul (hDm 1)))).add
      ((hDm 1).mul (((hGm 1 0).mul (hDm 0)).add ((hGm 1 1).mul (hDm 1)))))
  have hi : Integrable (fun p : ℝ × Vec 2 => (9 / 4) * (DU p 0 ^ 2 + DU p 1 ^ 2)) μ :=
    (((hDU 0).integrable_sq).add (hDU 1).integrable_sq).const_mul _
  refine hi.mono' hmeas ?_
  filter_upwards [hae] with p hp
  have h1 := hc.quad_le hp (DU p)
  have h2 := hc.psd hp (DU p)
  have h3 : ζ p.2 ^ 2 ≤ 1 := by
    have := hζ1 p.2
    rw [abs_le] at this
    nlinarith
  have h4 : vecNormSq (DU p) = DU p 0 ^ 2 + DU p 1 ^ 2 := by
    rw [vecNormSq_two, sq, sq]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
  rw [h4] at h1
  calc ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤ 1 * vecDot (DU p) ((G p).mulVec (DU p)) :=
        mul_le_mul_of_nonneg_right h3 h2
    _ ≤ _ := by linarith


/-- Energy inequality between two times, in integrated form. -/
theorem cutoff_energy_ineq (hc : LabelCoeffs G V V₀ ta tb) {R κ : ℝ} (hκ : 0 ≤ κ)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest (euclidBall 0 R) ζ) (hζ0 : ∀ y, 0 ≤ ζ y)
    (hζ1 : ∀ y, ζ y ≤ 1) {N : ℝ} (hN : 0 ≤ N) (hζN : ∀ y, vecNormSq (spGrad ζ y) ≤ N ^ 2)
    {τ₁ τ₂ : ℝ} (h₁ : ta ≤ τ₁) (h₂ : τ₂ ≤ tb)
    {E₁ E₂ : ℝ}
    (hE : E₂ - E₁ = -2 * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ euclidBall 0 R,
          fluxE κ (G p) (V p) (ζ p.2) (U p) (DU p) (spGrad ζ p.2)) :
    E₂ + κ * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ euclidBall 0 R,
        ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤
      E₁ + (9 * κ * N ^ 2 + 2 * V₀ * N) *
        ∫ p in Set.Ioc τ₁ τ₂ ×ˢ euclidBall 0 R, U p ^ 2 := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hζ1' : ∀ y, |ζ y| ≤ 1 := fun y => by rw [abs_of_nonneg (hζ0 y)]; exact hζ1 y
  obtain ⟨iFh, iFψ⟩ := flux_parts_integrable hc (κ := κ) hU hDU hζ hζ1' hN hζN
  have iflux : Integrable (fun p : ℝ × Vec 2 =>
      fluxE κ (G p) (V p) (ζ p.2) (U p) (DU p) (spGrad ζ p.2))
      (volume.restrict (Set.Ioo ta tb ×ˢ B)) := by
    refine (iFh.add iFψ).congr (Filter.Eventually.of_forall fun p => ?_)
    have := P_dot_eq κ (G p) (V p) (DU p) (spGrad ζ p.2) (ζ p.2) (U p)
    simp only [Pi.add_apply]
    linarith
  have iQ := integrable_quad hc hDU hζ hζ1'
  have iU : Integrable (fun p => U p ^ 2) (volume.restrict (Set.Ioo ta tb ×ˢ B)) :=
    hU.integrable_sq
  have iflux' := integrableOn_Ioc_of_Ioo iflux h₁ h₂
  have iQ' := (integrableOn_Ioc_of_Ioo iQ h₁ h₂).const_mul κ
  have iU' := integrableOn_Ioc_of_Ioo iU h₁ h₂
  have hmono : ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B,
      (-2 * fluxE κ (G p) (V p) (ζ p.2) (U p) (DU p) (spGrad ζ p.2) +
        κ * (ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)))) ≤
      ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, (9 * κ * N ^ 2 + 2 * V₀ * N) * U p ^ 2 := by
    refine setIntegral_mono_on (iflux'.const_mul (-2) |>.add iQ') (iU'.const_mul _)
      (measurableSet_Ioc.prod hBm) ?_
    intro p hp
    have hpI : p.1 ∈ Set.Icc ta tb := ⟨h₁.trans hp.1.1.le, hp.1.2.trans h₂⟩
    have := energy_pointwise_bound (u := U p) (hc.symm p) (hc.ell p hpI) (hc.bdd p hpI) hκ (hζ0 p.2)
      (hζ1 p.2) hN hc.V0 (hc.Vbd p hpI) (DU p) (spGrad ζ p.2) (hζN p.2)
    linarith
  rw [integral_add (iflux'.const_mul (-2)) iQ', integral_const_mul, integral_const_mul,
    integral_const_mul] at hmono
  linarith


theorem setIntegral_sq_Ioc_le {U : ℝ × Vec 2 → ℝ} {ta tb τ₁ τ₂ : ℝ} {B : Set (Vec 2)}
    (hU : IntegrableOn (fun p => U p ^ 2) (Set.Ioo ta tb ×ˢ B)) (h₁ : ta ≤ τ₁) (h₂ : τ₂ ≤ tb) :
    ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, U p ^ 2 ≤ ∫ p in Set.Ioo ta tb ×ˢ B, U p ^ 2 := by
  rw [← setIntegral_Ioc_prod_eq_Ioo (a := ta) (b := tb)]
  have h3 : IntegrableOn (fun p => U p ^ 2) (Set.Ioc ta tb ×ˢ B) :=
    (integrableOn_congr_set_ae (Ioc_prod_ae_eq_Ioo_prod ta tb B)).2 hU
  exact setIntegral_mono_set h3 (Filter.Eventually.of_forall fun p => sq_nonneg _)
    (Filter.Eventually.of_forall (Set.prod_mono (Set.Ioc_subset_Ioc h₁ h₂) le_rfl))

/-- **Cutoff energy bound**: for `τ ∈ [ta + σ, tb]` the cutoff energy
and the cutoff dissipation are bounded by `(1/σ + 9κN² + 2V₀N) ∬ U²` (the bound (8.16) in the
proof of Lemma 8.3 of the paper). -/
theorem cutoff_energy_bound (hc : LabelCoeffs G V V₀ ta tb) (hab : ta < tb) {R κ σ : ℝ}
    (hκ : 0 ≤ κ) (hσ : 0 < σ) (hσb : ta + σ ≤ tb)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) φ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R,
        (-(U p * stTimeDeriv φ p) + vecDot (κ • (G p).mulVec (DU p) - U p • V p)
          (stSpaceGrad φ p)) = 0)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest (euclidBall 0 R) ζ) (hζ0 : ∀ y, 0 ≤ ζ y)
    (hζ1 : ∀ y, ζ y ≤ 1) {N : ℝ} (hN : 0 ≤ N) (hζN : ∀ y, vecNormSq (spGrad ζ y) ≤ N ^ 2) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R)), ContinuousOn W (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => ζ y * U (τ, y)) ∧
      (∀ τ ∈ Set.Icc (ta + σ) tb, ‖W τ‖ ^ 2 ≤
        (1 / σ + (9 * κ * N ^ 2 + 2 * V₀ * N)) *
          ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, U p ^ 2) ∧
      κ * ∫ p in Set.Ioo (ta + σ) tb ×ˢ euclidBall 0 R,
          ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤
        (1 / σ + (9 * κ * N ^ 2 + 2 * V₀ * N)) *
          ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, U p ^ 2 := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hζ1' : ∀ y, |ζ y| ≤ 1 := fun y => by rw [abs_of_nonneg (hζ0 y)]; exact hζ1 y
  obtain ⟨W, hWc, hWae, hid⟩ := cutoff_energy_identity hc hab hU hDU hgrad hweak hζ hζ1' hN hζN
  set M := ∫ p in Set.Ioo ta tb ×ˢ B, U p ^ 2 with hM
  set c₁ := 9 * κ * N ^ 2 + 2 * V₀ * N with hc₁
  have hc₁0 : 0 ≤ c₁ := by have := hc.V0; positivity
  have iU : IntegrableOn (fun p => U p ^ 2) (Set.Ioo ta tb ×ˢ B) := hU.integrable_sq
  have iQ := integrable_quad hc hDU hζ hζ1'
  have hQ0 : ∀ p : ℝ × Vec 2, p.1 ∈ Set.Icc ta tb →
      0 ≤ ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) :=
    fun p hp => mul_nonneg (sq_nonneg _) (hc.psd hp _)
  have hQnn : ∀ {τ₁ τ₂ : ℝ}, ta ≤ τ₁ → τ₂ ≤ tb →
      0 ≤ ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) := by
    intro τ₁ τ₂ h₁ h₂
    refine setIntegral_nonneg (measurableSet_Ioc.prod hBm) fun p hp => hQ0 p ?_
    exact ⟨h₁.trans hp.1.1.le, hp.1.2.trans h₂⟩
  -- the basic inequality
  have key : ∀ τ₁ ∈ Set.Icc ta tb, ∀ τ₂ ∈ Set.Icc ta tb, τ₁ ≤ τ₂ →
      ‖W τ₂‖ ^ 2 + κ * ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B,
          ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤ ‖W τ₁‖ ^ 2 + c₁ * M := by
    intro τ₁ h₁ τ₂ h₂ h12
    have := cutoff_energy_ineq hc hκ hU hDU hζ hζ0 hζ1 hN hζN h₁.1 h₂.2
      (hid τ₁ h₁ τ₂ h₂ h12)
    have h3 := setIntegral_sq_Ioc_le iU h₁.1 h₂.2
    have h4 := mul_le_mul_of_nonneg_left h3 hc₁0
    linarith
  -- the layer average of the energy
  have hEint : ∫ τ in Set.Ioc ta (ta + σ), ‖W τ‖ ^ 2 ≤ M := by
    have hsl := ae_slice_memLp_gen hU
    have hF : Integrable (fun p => U p ^ 2) ((volume.restrict (Set.Ioc ta (ta + σ))).prod
        (volume.restrict B)) := by
      rw [← volume_restrict_prod_eq]
      exact integrableOn_Ioc_of_Ioo iU le_rfl (by linarith)
    have hφ := hF.integral_prod_left
    have hEc : ContinuousOn (fun τ => ‖W τ‖ ^ 2) (Set.Icc ta tb) := (hWc.norm).pow 2
    have hEi : IntegrableOn (fun τ => ‖W τ‖ ^ 2) (Set.Ioc ta (ta + σ)) :=
      (hEc.mono (Set.Icc_subset_Icc le_rfl hσb)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hle : ∫ τ in Set.Ioc ta (ta + σ), ‖W τ‖ ^ 2 ≤
        ∫ τ in Set.Ioc ta (ta + σ), ∫ y in B, U (τ, y) ^ 2 := by
      refine integral_mono_ae hEi hφ ?_
      have h1 := ae_Ioc_of_ae_Ioo (a := ta) (b := tb) (τ₁ := ta) (τ₂ := ta + σ) le_rfl
        (by linarith) hWae
      have h2 := ae_Ioc_of_ae_Ioo (a := ta) (b := tb) (τ₁ := ta) (τ₂ := ta + σ) le_rfl
        (by linarith) hsl
      filter_upwards [h1, h2] with τ hτW hτU
      rw [← integral_sq_lp]
      have e1 : ∫ y, ((W τ : Vec 2 → ℝ) y) ^ 2 ∂(volume.restrict B) =
          ∫ y in B, (ζ y * U (τ, y)) ^ 2 := integral_congr_ae (hτW.mono fun y hy => by simp only [hy])
      rw [e1]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
        ((memLp_two_iff_integrable_sq hτU.aestronglyMeasurable).1 hτU)
        (Filter.Eventually.of_forall fun y => ?_)
      have := hζ0 y
      have := hζ1 y
      simp only [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
    refine hle.trans ?_
    have h5 := setIntegral_Ioc_prod (τ₁ := ta) (τ₂ := ta + σ) (B := B)
      (F := fun p => U p ^ 2) (integrableOn_Ioc_of_Ioo iU le_rfl (by linarith))
    rw [← h5]
    exact setIntegral_sq_Ioc_le iU le_rfl (by linarith)
  have hEcσ : ContinuousOn (fun τ => ‖W τ‖ ^ 2) (Set.Icc ta (ta + σ)) :=
    ((hWc.norm).pow 2).mono (Set.Icc_subset_Icc le_rfl hσb)
  have hI1 : ∀ τ₂ ∈ Set.Icc (ta + σ) tb, ‖W τ₂‖ ^ 2 ≤ (1 / σ + c₁) * M := by
    intro τ₂ h₂
    have := layer_average (E := fun τ => ‖W τ‖ ^ 2) (A := ‖W τ₂‖ ^ 2) (B := c₁ * M)
      hσ hEcσ (fun τ₁ h₁ => by
        have := key τ₁ ⟨h₁.1, h₁.2.trans hσb⟩ τ₂ ⟨by linarith [h₂.1], h₂.2⟩ (h₁.2.trans h₂.1)
        have := hQnn (τ₁ := τ₁) (τ₂ := τ₂) h₁.1 h₂.2
        nlinarith) hEint
    exact this.trans_eq (by ring)
  refine ⟨W, hWc, hWae, hI1, ?_⟩
  have := layer_average (E := fun τ => ‖W τ‖ ^ 2)
    (A := κ * ∫ p in Set.Ioo (ta + σ) tb ×ˢ B,
      ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p))) (B := c₁ * M)
    hσ hEcσ (fun τ₁ h₁ => by
      have h1 := key τ₁ ⟨h₁.1, h₁.2.trans hσb⟩ tb ⟨hab.le, le_rfl⟩ (h₁.2.trans hσb)
      have h2 : ∫ p in Set.Ioo (ta + σ) tb ×ˢ B,
          ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤
          ∫ p in Set.Ioc τ₁ tb ×ˢ B,
            ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) := by
        rw [← setIntegral_Ioc_prod_eq_Ioo (a := ta + σ) (b := tb)]
        have iQ3 : IntegrableOn (fun p : ℝ × Vec 2 =>
            ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p))) (Set.Ioc τ₁ tb ×ˢ B) :=
          integrableOn_Ioc_of_Ioo iQ h₁.1 le_rfl
        refine setIntegral_mono_set iQ3 ?_ (Filter.Eventually.of_forall
          (Set.prod_mono (Set.Ioc_subset_Ioc h₁.2 le_rfl) le_rfl))
        exact (ae_restrict_iff' (measurableSet_Ioc.prod hBm)).2
          (Filter.Eventually.of_forall fun p hp => hQ0 p ⟨h₁.1.trans hp.1.1.le, hp.1.2⟩)
      have h3 := mul_le_mul_of_nonneg_left h2 hκ
      nlinarith [sq_nonneg ‖W tb‖]) hEint
  exact this.trans_eq (by ring)

end AVRegularity.Applications.Davies
end
end
end

section
/-! # `L²` membership of bilinear expressions and weak gradients of scaled functions -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Matrix

namespace AVRegularity.Applications.Davies

theorem memLp_dot_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} {a v : α → Vec 2} {C : ℝ}
    (ham : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (hab : ∀ᵐ x ∂μ, ∀ i, ‖a x i‖ ≤ C) (hv : ∀ i, MemLp (fun x => v x i) 2 μ) :
    MemLp (fun x => vecDot (a x) (v x)) 2 μ := by
  have h : ∀ i, MemLp (fun x => a x i * v x i) 2 μ := fun i =>
    memLp_two_mul_bdd (ham i) (hab.mono fun x hx => hx i) (hv i)
  have := (h 0).add (h 1)
  refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
  simp [vecDot, Fin.sum_univ_two]

theorem memLp_matvec_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {M : α → Matrix (Fin 2) (Fin 2) ℝ} {v : α → Vec 2} {C : ℝ}
    (hM : ∀ i j, AEStronglyMeasurable (fun x => M x i j) μ)
    (hb : ∀ᵐ x ∂μ, ∀ i j, ‖M x i j‖ ≤ C) (hv : ∀ i, MemLp (fun x => v x i) 2 μ) (i : Fin 2) :
    MemLp (fun x => ((M x).mulVec (v x)) i) 2 μ := by
  have h : ∀ j, MemLp (fun x => M x i j * v x j) 2 μ := fun j =>
    memLp_two_mul_bdd (hM i j) (hb.mono fun x hx => hx i j) (hv j)
  have := (h 0).add (h 1)
  refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Scalar multiples of weak gradients. -/
theorem hasWeakGradientOn_const_mul {B : Set (Vec 2)} {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : HasWeakGradientOn B u Du) (c : ℝ) :
    HasWeakGradientOn B (fun y => c * u y) (fun y => c • Du y) := by
  intro i φ hφ hφc hφB
  have := h i φ hφ hφc hφB
  have e1 : ∫ x in B, c * u x * fderiv ℝ φ x (basisVec i) =
      c * ∫ x in B, u x * fderiv ℝ φ x (basisVec i) := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  have e2 : ∫ x in B, (c • Du x) i * φ x = c * ∫ x in B, Du x i * φ x := by
    rw [← integral_const_mul]; congr 1; ext x; simp [mul_assoc]
  rw [e1, e2, this]
  ring

/-- Sums and differences of weak gradients of `L²` functions with `L²` gradients. -/
theorem hasWeakGradientOn_sub_memLp {B : Set (Vec 2)} {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : MemLp u 2 (volume.restrict B)) (hv : MemLp v 2 (volume.restrict B))
    (hDu : ∀ i : Fin 2, MemLp (fun y => Du y i) 2 (volume.restrict B))
    (hDv : ∀ i : Fin 2, MemLp (fun y => Dv y i) 2 (volume.restrict B))
    (h1 : HasWeakGradientOn B u Du) (h2 : HasWeakGradientOn B v Dv) :
    HasWeakGradientOn B (fun y => u y - v y) (fun y => Du y - Dv y) := by
  intro i φ hφ hφc hφB
  have hc : Continuous φ := hφ.continuous
  have hdc : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcs : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have a1 := integrableOn_mul_cpt hu hdc hdcs
  have a2 := integrableOn_mul_cpt hv hdc hdcs
  have b1 := integrableOn_mul_cpt (hDu i) hc hφc
  have b2 := integrableOn_mul_cpt (hDv i) hc hφc
  have e1 : ∫ x in B, (u x - v x) * fderiv ℝ φ x (basisVec i) =
      (∫ x in B, u x * fderiv ℝ φ x (basisVec i)) - ∫ x in B, v x * fderiv ℝ φ x (basisVec i) := by
    rw [← integral_sub a1 a2]; congr 1; ext x; ring
  have e2 : ∫ x in B, (Du x - Dv x) i * φ x =
      (∫ x in B, Du x i * φ x) - ∫ x in B, Dv x i * φ x := by
    rw [← integral_sub b1 b2]; congr 1; ext x; simp [sub_mul]
  rw [e1, e2, h1 i φ hφ hφc hφB, h2 i φ hφ hφc hφB]
  ring

end AVRegularity.Applications.Davies
end
end
end

section
/-! # The weighted local energy estimate for `Z = χ D`

`local_weighted_energy`: if `D` solves `∂ₜD = div(κ G∇D) - V·∇D` weakly in the label cylinder, then
the trace `W` of `ζ θ χ D` (with `ζ = e^{ℓψ} η`, `θ = e^{-Λ(t-ta)}`) satisfies
`‖W(τ)‖² ≤ ‖W(ta)‖² + ∬ ζ² (18 κ⁻¹ |H|² + λ⁻¹ g'²)`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Matrix Filter Topology
open AVRegularity.Applications.LocalEnergy

namespace AVRegularity.Applications.Davies

/-- The weight `ζ = e^{ℓψ} η`. -/
def zeta (ℓ : ℝ) (ψ η : Vec 2 → ℝ) (y : Vec 2) : ℝ := Real.exp (ℓ * ψ y) * η y

theorem isSpTest_zeta {B : Set (Vec 2)} {ℓ : ℝ} {ψ η : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hη : IsSpTest B η) : IsSpTest B (zeta ℓ ψ η) :=
  ⟨(Real.contDiff_exp.comp (contDiff_const.mul hψ)).mul hη.1, hη.2.1.mul_left,
    (tsupport_mul_subset_right).trans hη.2.2⟩

theorem spGrad_zeta {ℓ : ℝ} {ψ η : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (y : Vec 2) (i : Fin 2) :
    spGrad (zeta ℓ ψ η) y i = η y * (Real.exp (ℓ * ψ y) * (ℓ * spGrad ψ y i)) +
      Real.exp (ℓ * ψ y) * spGrad η y i := by
  have hψd : DifferentiableAt ℝ ψ y := (hψ.differentiable (by simp)) y
  have hηd : DifferentiableAt ℝ η y := (hη.differentiable (by simp)) y
  have h1 : HasFDerivAt (fun z => Real.exp (ℓ * ψ z))
      (Real.exp (ℓ * ψ y) • (ℓ • fderiv ℝ ψ y)) y :=
    (hψd.hasFDerivAt.const_mul ℓ).exp
  have h2 := h1.mul hηd.hasFDerivAt
  simp only [spGrad]
  have e : zeta ℓ ψ η = (fun z => Real.exp (ℓ * ψ z)) * η := rfl
  rw [e, h2.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring


section Main

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}

/-- The pointwise bound for the localized flux integrand. -/
theorem flux_pointwise (hc : LabelCoeffs G V V₀ ta tb) {κ lam ℓ : ℝ} (hκ : 0 < κ)
    (hlam : 0 < lam) {D : ℝ × Vec 2 → ℝ} {DD : ℝ × Vec 2 → Vec 2}
    {χ ψ η : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηχ : ∀ y, y ∈ tsupport χ → η y = 1 ∧ spGrad η y = 0)
    (hψ1 : ∀ y, vecNormSq (spGrad ψ y) ≤ 1) {p : ℝ × Vec 2} (hp : p.1 ∈ Set.Icc ta tb) :
    -2 * (vecDot (Pt (decayRate κ ℓ V₀ lam) ta κ G χ D DD p)
        (zeta ℓ ψ η p.2 ^ 2 • DZt (decayRate κ ℓ V₀ lam) ta χ D DD p +
          (2 * zeta ℓ ψ η p.2 * Zt (decayRate κ ℓ V₀ lam) ta χ D p) • spGrad (zeta ℓ ψ η) p.2) -
        gt (decayRate κ ℓ V₀ lam) ta κ G V χ D DD p * zeta ℓ ψ η p.2 ^ 2 *
          Zt (decayRate κ ℓ V₀ lam) ta χ D p) ≤
      zeta ℓ ψ η p.2 ^ 2 * (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam) := by
  by_cases hy : p.2 ∈ tsupport χ
  · obtain ⟨hη1, hη2⟩ := hηχ _ hy
    have hz : zeta ℓ ψ η p.2 = Real.exp (ℓ * ψ p.2) := by simp [zeta, hη1]
    have hg : spGrad (zeta ℓ ψ η) p.2 = (ℓ * Real.exp (ℓ * ψ p.2)) • spGrad ψ p.2 := by
      funext i
      rw [spGrad_zeta hψ hη, hη1]
      have : spGrad η p.2 i = 0 := by rw [hη2]; rfl
      simp only [this, Pi.smul_apply, smul_eq_mul]
      ring
    have h := weighted_pointwise (G := G p) (V := V p) (V₀ := V₀) (κ := κ) (ℓ := ℓ)
      (lam := lam) (θ := tw (decayRate κ ℓ V₀ lam) ta p.1) (w := Real.exp (ℓ * ψ p.2))
      (Z := χ p.2 * D p) (g' := srcG κ G V χ D DD p) (d := dZ χ D DD p)
      (e := spGrad ψ p.2) (H := srcH κ G χ D p) (hc.symm p) (hc.ell p hp) (hc.bdd p hp) hκ hlam
      (hc.Vbd p hp) (hψ1 _)
    have hθ : tw (decayRate κ ℓ V₀ lam) ta p.1 ^ 2 ≤ 1 := by
      have h0 : 0 ≤ decayRate κ ℓ V₀ lam := by
        unfold decayRate; have := hc.V0; positivity
      have := tw_le_one h0 hp.1
      have := tw_pos (decayRate κ ℓ V₀ lam) ta p.1
      nlinarith
    have hnn : 0 ≤ Real.exp (ℓ * ψ p.2) ^ 2 *
        (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam) := by
      have := vecNormSq_nonneg (srcH κ G χ D p)
      positivity
    rw [hz, hg]
    simp only [Pt, DZt, Zt, gt]
    have e : (ℓ * Real.exp (ℓ * ψ p.2)) • spGrad ψ p.2 = (ℓ * Real.exp (ℓ * ψ p.2)) • spGrad ψ p.2 :=
      rfl
    refine h.trans ?_
    have e2 : tw (decayRate κ ℓ V₀ lam) ta p.1 ^ 2 * Real.exp (ℓ * ψ p.2) ^ 2 *
        (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam) =
        tw (decayRate κ ℓ V₀ lam) ta p.1 ^ 2 * (Real.exp (ℓ * ψ p.2) ^ 2 *
        (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam)) := by ring
    rw [e2]
    exact mul_le_of_le_one_left hnn hθ
  · have h0 : χ p.2 = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : spGrad χ p.2 = 0 := by
      funext i
      simp [spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
    have hd : dZ χ D DD p = 0 := by simp [dZ, h0, h1]
    have hH : srcH κ G χ D p = 0 := by simp [srcH, h1]
    have hg' : srcG κ G V χ D DD p = 0 := by simp [srcG, h1, vecDot]
    have hZ : Zt (decayRate κ ℓ V₀ lam) ta χ D p = 0 := by simp [Zt, h0]
    have hP : Pt (decayRate κ ℓ V₀ lam) ta κ G χ D DD p = 0 := by simp [Pt, hd, hH]
    have hgt : gt (decayRate κ ℓ V₀ lam) ta κ G V χ D DD p = 0 := by
      simp [gt, hd, hg', hZ, vecDot]
    rw [hP, hgt, hZ, hH, hg']
    have h00 : vecNormSq (0 : Vec 2) = 0 := by simp [vecNormSq, vecDot]
    simp [vecDot, h00]


theorem coef_mulVec_bound (hc : LabelCoeffs G V V₀ ta tb) {w : Vec 2 → Vec 2} {N : ℝ}
    (hw : ∀ y i, |w y i| ≤ N) {p : ℝ × Vec 2} (hp : p.1 ∈ Set.Icc ta tb)
    (i : Fin 2) : |((G p).mulVec (w p.2)) i| ≤ 2 * (9 / 4 * N) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 : |G p i 0 * w p.2 0| ≤ 9 / 4 * N := by
    rw [abs_mul]; exact mul_le_mul (hc.entry_bound hp i 0) (hw _ 0) (abs_nonneg _) (by norm_num)
  have h1 : |G p i 1 * w p.2 1| ≤ 9 / 4 * N := by
    rw [abs_mul]; exact mul_le_mul (hc.entry_bound hp i 1) (hw _ 1) (abs_nonneg _) (by norm_num)
  calc _ ≤ |G p i 0 * w p.2 0| + |G p i 1 * w p.2 1| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem coef_dot_bound (hc : LabelCoeffs G V V₀ ta tb) {w : Vec 2 → Vec 2} {N : ℝ}
    (hw : ∀ y i, |w y i| ≤ N) {p : ℝ × Vec 2} (hp : p.1 ∈ Set.Icc ta tb) :
    |vecDot (V p) (w p.2)| ≤ 2 * (V₀ * N) := by
  simp only [vecDot, Fin.sum_univ_two]
  have h0 : |V p 0 * w p.2 0| ≤ V₀ * N := by
    rw [abs_mul]; exact mul_le_mul (hc.Ventry_bound hp 0) (hw _ 0) (abs_nonneg _) hc.V0
  have h1 : |V p 1 * w p.2 1| ≤ V₀ * N := by
    rw [abs_mul]; exact mul_le_mul (hc.Ventry_bound hp 1) (hw _ 1) (abs_nonneg _) hc.V0
  calc _ ≤ |V p 0 * w p.2 0| + |V p 1 * w p.2 1| := abs_add_le _ _
    _ ≤ _ := by linarith


variable {R κ : ℝ}

theorem spGrad_bound {χ : Vec 2 → ℝ} {Nχ : ℝ} (hNχ : 0 ≤ Nχ)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2) (y : Vec 2) (i : Fin 2) :
    |spGrad χ y i| ≤ Nχ :=
  (abs_coord_le_sqrt _ i).trans (Real.sqrt_le_iff.2 ⟨hNχ, hχN y⟩)

theorem spGrad_cont {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (i : Fin 2) :
    Continuous fun p : ℝ × Vec 2 => spGrad χ p.2 i :=
  ((contDiff_fderiv_apply_of_smooth hχ (basisVec i)).continuous).comp continuous_snd

section Memb

variable {μ : Measure (ℝ × Vec 2)} {χ : Vec 2 → ℝ} {D : ℝ × Vec 2 → ℝ} {DD : ℝ × Vec 2 → Vec 2}

theorem dZ_memLp (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ y, |χ y| ≤ 1) {Nχ : ℝ} (hNχ : 0 ≤ Nχ)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2) (hD : MemLp D 2 μ)
    (hDD : ∀ i : Fin 2, MemLp (fun p => DD p i) 2 μ) (i : Fin 2) :
    MemLp (fun p => dZ χ D DD p i) 2 μ := by
  have hχc : Continuous fun p : ℝ × Vec 2 => χ p.2 := hχ.continuous.comp continuous_snd
  have h1 : MemLp (fun p => χ p.2 * DD p i) 2 μ :=
    memLp_two_mul_bdd hχc.aestronglyMeasurable (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hχ1 _) (hDD i)
  have h2 : MemLp (fun p => spGrad χ p.2 i * D p) 2 μ :=
    memLp_two_mul_bdd (spGrad_cont hχ i).aestronglyMeasurable (C := Nχ)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact spGrad_bound hNχ hχN _ i) hD
  refine (h1.add h2).ae_eq (Filter.Eventually.of_forall fun p => ?_)
  simp only [dZ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tw_aesm_bdd (Λ ta : ℝ) (hΛ : 0 ≤ Λ) (S : Set (ℝ × Vec 2))
    (hS : ∀ p ∈ S, ta ≤ p.1) (hm : MeasurableSet S) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => tw Λ ta p.1) (volume.restrict S) ∧
    ∀ᵐ p ∂(volume.restrict S), ‖tw Λ ta p.1‖ ≤ 1 := by
  refine ⟨((tw_contDiff Λ ta).continuous.comp continuous_fst).aestronglyMeasurable, ?_⟩
  filter_upwards [ae_restrict_mem hm] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (tw_pos _ _ _)]
  exact tw_le_one hΛ (hS p hp)

end Memb



theorem dot_grad_matvec_memLp {μ : Measure (ℝ × Vec 2)} {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {Nχ : ℝ} (hNχ : 0 ≤ Nχ)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2) {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {DD : ℝ × Vec 2 → Vec 2}
    (hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ)
    (hGb : ∀ᵐ p ∂μ, ∀ i j, ‖G p i j‖ ≤ 9 / 4)
    (hDD : ∀ i : Fin 2, MemLp (fun p => DD p i) 2 μ) :
    MemLp (fun p : ℝ × Vec 2 => vecDot (spGrad χ p.2) ((G p).mulVec (DD p))) 2 μ :=
  memLp_dot_bdd (a := fun p : ℝ × Vec 2 => spGrad χ p.2) (v := fun p => (G p).mulVec (DD p))
    (fun i => (spGrad_cont hχ i).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p i => by
      rw [Real.norm_eq_abs]; exact spGrad_bound hNχ hχN _ i)
    (fun i => memLp_matvec_bdd (M := G) (v := DD) hGm hGb hDD i)

section Memb2

variable {B : Set (Vec 2)} {χ : Vec 2 → ℝ} {D : ℝ × Vec 2 → ℝ} {DD : ℝ × Vec 2 → Vec 2}

theorem srcH_memLp (hc : LabelCoeffs G V V₀ ta tb) (hBm : MeasurableSet B) {κ : ℝ} (hκ : 0 < κ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {Nχ : ℝ} (hNχ : 0 ≤ Nχ)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2)
    (hD : MemLp D 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))) (i : Fin 2) :
    MemLp (fun p => srcH κ G χ D p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)) := by
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hgb := spGrad_bound hNχ hχN
  have hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ := fun i j =>
    (hc.Gmeas i j).aestronglyMeasurable
  have hGgrad : AEStronglyMeasurable (fun p => ((G p).mulVec (spGrad χ p.2)) i) μ := by
    have : (fun p : ℝ × Vec 2 => ((G p).mulVec (spGrad χ p.2)) i) =
        fun p => G p i 0 * spGrad χ p.2 0 + G p i 1 * spGrad χ p.2 1 := by
      funext p; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this]
    exact ((hGm i 0).mul (spGrad_cont hχ 0).aestronglyMeasurable).add
      ((hGm i 1).mul (spGrad_cont hχ 1).aestronglyMeasurable)
  have hco : AEStronglyMeasurable (fun p => -(κ * ((G p).mulVec (spGrad χ p.2)) i)) μ :=
    (hGgrad.const_mul κ).neg
  have := memLp_two_mul_bdd (μ := μ) (φ := fun p => -(κ * ((G p).mulVec (spGrad χ p.2)) i))
    hco (C := κ * (2 * (9 / 4 * Nχ)))
    (hae.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hκ]
      exact mul_le_mul_of_nonneg_left (coef_mulVec_bound hc hgb hp i) hκ.le) hD
  refine this.ae_eq (Filter.Eventually.of_forall fun p => ?_)
  simp only [srcH, Pi.smul_apply, smul_eq_mul]
  ring

theorem srcG_memLp (hc : LabelCoeffs G V V₀ ta tb) (hBm : MeasurableSet B) {κ : ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {Nχ : ℝ} (hNχ : 0 ≤ Nχ)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2)
    (hD : MemLp D 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)))
    (hDD : ∀ i : Fin 2, MemLp (fun p => DD p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B))) :
    MemLp (srcG κ G V χ D DD) 2 (volume.restrict (Set.Ioo ta tb ×ˢ B)) := by
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hgb := spGrad_bound hNχ hχN
  have hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ := fun i j =>
    (hc.Gmeas i j).aestronglyMeasurable
  have hGb : ∀ᵐ p ∂μ, ∀ i j, ‖G p i j‖ ≤ 9 / 4 :=
    hae.mono fun p hp i j => by rw [Real.norm_eq_abs]; exact hc.entry_bound hp i j
  have hVm : ∀ i, AEStronglyMeasurable (fun p => V p i) μ := fun i =>
    ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable
  have h1 := dot_grad_matvec_memLp hχ hNχ hχN hGm hGb hDD
  have hVgm : AEStronglyMeasurable (fun p => vecDot (V p) (spGrad χ p.2)) μ := by
    have : (fun p : ℝ × Vec 2 => vecDot (V p) (spGrad χ p.2)) =
        fun p => V p 0 * spGrad χ p.2 0 + V p 1 * spGrad χ p.2 1 := by
      funext p; simp [vecDot, Fin.sum_univ_two]
    rw [this]
    exact ((hVm 0).mul (spGrad_cont hχ 0).aestronglyMeasurable).add
      ((hVm 1).mul (spGrad_cont hχ 1).aestronglyMeasurable)
  have h2 : MemLp (fun p => vecDot (V p) (spGrad χ p.2) * D p) 2 μ :=
    memLp_two_mul_bdd hVgm (C := 2 * (V₀ * Nχ))
      (hae.mono fun p hp => by rw [Real.norm_eq_abs]; exact coef_dot_bound hc hgb hp) hD
  refine ((h1.const_mul κ).sub h2).ae_eq (Filter.Eventually.of_forall fun p => ?_)
  simp only [srcG, Pi.sub_apply]
  ring

end Memb2

/-- **Weighted local energy estimate.** -/
theorem local_weighted_energy (hc : LabelCoeffs G V V₀ ta tb) (hab : ta < tb) {κ lam ℓ : ℝ}
    (hκ : 0 < κ) (hlam : 0 < lam) {R : ℝ}
    {D : ℝ × Vec 2 → ℝ} {DD : ℝ × Vec 2 → Vec 2}
    (hD : MemLp D 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDD : ∀ i : Fin 2,
      MemLp (fun p => DD p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => D (τ, y)) (fun y => DD (τ, y)))
    (heq : ∀ ξ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, (-(D p * stTimeDeriv ξ p) +
        vecDot (V p) (DD p) * ξ p + κ * vecDot ((G p).mulVec (DD p)) (stSpaceGrad ξ p)) = 0)
    {χ : Vec 2 → ℝ} (hχ : IsSpTest (euclidBall 0 R) χ) (hχ1 : ∀ y, |χ y| ≤ 1) {Nχ : ℝ}
    (hNχ : 0 ≤ Nχ) (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ Nχ ^ 2)
    {η ψ : Vec 2 → ℝ} (hη : IsSpTest (euclidBall 0 R) η)
    (hηχ : ∀ y, y ∈ tsupport χ → η y = 1 ∧ spGrad η y = 0)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1 : ∀ y, vecNormSq (spGrad ψ y) ≤ 1) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R)), ContinuousOn W (Set.Icc ta tb) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)]
          fun y => zeta ℓ ψ η y * Zt (decayRate κ ℓ V₀ lam) ta χ D (τ, y)) ∧
      ∀ τ ∈ Set.Icc ta tb, ‖W τ‖ ^ 2 ≤ ‖W ta‖ ^ 2 +
        ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, zeta ℓ ψ η p.2 ^ 2 *
          (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam) := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBo : IsOpen B := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet B := hBo.measurableSet
  set Λ := decayRate κ ℓ V₀ lam with hΛdef
  have hΛ : 0 ≤ Λ := by
    have := hc.V0
    unfold decayRate at hΛdef
    rw [hΛdef]; positivity
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  obtain ⟨htwm, htwb⟩ := tw_aesm_bdd Λ ta hΛ (Set.Ioo ta tb ×ˢ B)
    (fun p hp => hp.1.1.le) (measurableSet_Ioo.prod hBm)
  have hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ := fun i j =>
    (hc.Gmeas i j).aestronglyMeasurable
  have hGb : ∀ᵐ p ∂μ, ∀ i j, ‖G p i j‖ ≤ 9 / 4 :=
    hae.mono fun p hp i j => by rw [Real.norm_eq_abs]; exact hc.entry_bound hp i j
  have hVm : ∀ i, AEStronglyMeasurable (fun p => V p i) μ := fun i =>
    ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable
  have hVb : ∀ᵐ p ∂μ, ∀ i, ‖V p i‖ ≤ V₀ :=
    hae.mono fun p hp i => by rw [Real.norm_eq_abs]; exact hc.Ventry_bound hp i
  have hχc : Continuous fun p : ℝ × Vec 2 => χ p.2 := hχ.1.continuous.comp continuous_snd
  have hdZ := dZ_memLp hχ.1 hχ1 hNχ hχN hD hDD
  have hsH := srcH_memLp hc hBm hκ hχ.1 hNχ hχN hD
  have hsG := srcG_memLp (κ := κ) hc hBm hχ.1 hNχ hχN hD hDD
  have hχD : MemLp (fun p => χ p.2 * D p) 2 μ :=
    memLp_two_mul_bdd hχc.aestronglyMeasurable (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hχ1 _) hD
  have hZ : MemLp (Zt Λ ta χ D) 2 μ :=
    (memLp_two_mul_bdd htwm htwb hχD).ae_eq (Filter.Eventually.of_forall fun p => by simp [Zt])
  have hDZ : ∀ i, MemLp (fun p => DZt Λ ta χ D DD p i) 2 μ := fun i =>
    (memLp_two_mul_bdd htwm htwb (hdZ i)).ae_eq (Filter.Eventually.of_forall fun p => by simp [DZt])
  have hGdZ : ∀ i, MemLp (fun p => ((G p).mulVec (dZ χ D DD p)) i) 2 μ := fun i =>
    memLp_matvec_bdd (M := G) (v := dZ χ D DD) hGm hGb hdZ i
  have hP : ∀ i, MemLp (fun p => Pt Λ ta κ G χ D DD p i) 2 μ := fun i =>
    (memLp_two_mul_bdd htwm htwb (((hGdZ i).const_mul κ).add (hsH i))).ae_eq
      (Filter.Eventually.of_forall fun p => by
        simp only [Pt, Pi.smul_apply, Pi.add_apply, smul_eq_mul])
  have hVdZ : MemLp (fun p => vecDot (V p) (dZ χ D DD p)) 2 μ :=
    memLp_dot_bdd (a := V) (v := dZ χ D DD) hVm hVb hdZ
  have hg : MemLp (gt Λ ta κ G V χ D DD) 2 μ :=
    ((memLp_two_mul_bdd htwm htwb (hVdZ.neg.sub hsG)).sub (hZ.const_mul Λ)).ae_eq
      (Filter.Eventually.of_forall fun p => by simp [gt])
  -- slice gradients
  have hUs := ae_slice_memLp_gen hD
  have hDs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)), ∀ i : Fin 2,
      MemLp (fun y => DD (τ, y) i) 2 (volume.restrict B) := by
    rw [Filter.eventually_all]
    exact fun i => ae_slice_memLp_gen (hDD i)
  have hgrad' : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn B (fun y => Zt Λ ta χ D (τ, y)) (fun y => DZt Λ ta χ D DD (τ, y)) := by
    filter_upwards [hUs, hDs, hgrad] with τ h1 h2 h3
    exact hasWeakGradientOn_const_mul (hasWeakGradientOn_smul_smooth hBo h3 h1 h2 hχ) (tw Λ ta τ)
  have hweak := Zt_weak (G := G) (V := V) (κ := κ) (D := D) (DD := DD) Λ ta hχ.1 heq
  have hζ := isSpTest_zeta (ℓ := ℓ) hψ hη
  obtain ⟨W, hWc, hWae, hid⟩ := local_trace_aux hab hBo hZ hDZ hgrad' hP hg hweak _ hζ
  refine ⟨W, hWc, hWae, fun τ hτ => ?_⟩
  set ρ : ℝ × Vec 2 → ℝ := fun p => zeta ℓ ψ η p.2 ^ 2 *
    (18 / κ * vecNormSq (srcH κ G χ D p) + srcG κ G V χ D DD p ^ 2 / lam) with hρ
  have hρnn : ∀ p, 0 ≤ ρ p := fun p => by
    have := vecNormSq_nonneg (srcH κ G χ D p)
    simp only [hρ]; positivity
  have hsum : Integrable (fun p => 18 / κ * vecNormSq (srcH κ G χ D p) +
      srcG κ G V χ D DD p ^ 2 / lam) μ := by
    have := (((hsH 0).integrable_sq.add (hsH 1).integrable_sq).const_mul (18 / κ)).add
      (hsG.integrable_sq.div_const lam)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [vecNormSq_two, sq, Pi.add_apply]
  have hζc : Continuous fun p : ℝ × Vec 2 => zeta ℓ ψ η p.2 ^ 2 :=
    (hζ.1.continuous.comp continuous_snd).pow 2
  have hζcc : HasCompactSupport fun y => zeta ℓ ψ η y ^ 2 := by
    have : (fun y => zeta ℓ ψ η y ^ 2) = fun y => zeta ℓ ψ η y * zeta ℓ ψ η y := by
      funext y; ring
    rw [this]; exact hζ.2.1.mul_left
  obtain ⟨Cz, hCz⟩ := (hζ.1.continuous.pow 2).bounded_above_of_compact_support hζcc
  have hρint : Integrable ρ μ :=
    hsum.bdd_mul (c := Cz) hζc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hCz p.2)
  have hρle : ∫ p in Set.Ioc ta τ ×ˢ B, ρ p ≤ ∫ p in Set.Ioo ta tb ×ˢ B, ρ p := by
    rw [← setIntegral_Ioc_prod_eq_Ioo (a := ta) (b := tb)]
    have h3 : IntegrableOn ρ (Set.Ioc ta tb ×ˢ B) :=
      (integrableOn_congr_set_ae (Ioc_prod_ae_eq_Ioo_prod ta tb B)).2 hρint
    exact setIntegral_mono_set h3 (Filter.Eventually.of_forall hρnn)
      (Filter.Eventually.of_forall (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hτ.2) le_rfl))
  have hρnn' : 0 ≤ ∫ p in Set.Ioo ta tb ×ˢ B, ρ p := setIntegral_nonneg
    (measurableSet_Ioo.prod hBm) fun p _ => hρnn p
  have hid' := hid ta ⟨le_rfl, hab.le⟩ τ hτ hτ.1
  set F : ℝ × Vec 2 → ℝ := fun p => vecDot (Pt Λ ta κ G χ D DD p)
    (zeta ℓ ψ η p.2 ^ 2 • DZt Λ ta χ D DD p +
      (2 * zeta ℓ ψ η p.2 * Zt Λ ta χ D p) • spGrad (zeta ℓ ψ η) p.2) -
    gt Λ ta κ G V χ D DD p * zeta ℓ ψ η p.2 ^ 2 * Zt Λ ta χ D p with hF
  have hFle : ∀ p ∈ Set.Ioc ta τ ×ˢ B, -2 * F p ≤ ρ p := by
    intro p hp
    exact flux_pointwise hc hκ hlam hψ hη.1 hηχ hψ1 (p := p) ⟨hp.1.1.le, hp.1.2.trans hτ.2⟩
  by_cases hFi : IntegrableOn F (Set.Ioc ta τ ×ˢ B)
  · have h1 : ∫ p in Set.Ioc ta τ ×ˢ B, -2 * F p ≤ ∫ p in Set.Ioc ta τ ×ˢ B, ρ p :=
      setIntegral_mono_on (hFi.const_mul (-2)) (integrableOn_Ioc_of_Ioo hρint le_rfl hτ.2)
        (measurableSet_Ioc.prod hBm) hFle
    rw [integral_const_mul] at h1
    have : ‖W τ‖ ^ 2 - ‖W ta‖ ^ 2 ≤ ∫ p in Set.Ioo ta tb ×ˢ B, ρ p := by
      rw [hid']; exact h1.trans hρle
    linarith
  · have h0 : ∫ p in Set.Ioc ta τ ×ˢ B, F p = 0 := integral_undef hFi
    have : ‖W τ‖ ^ 2 - ‖W ta‖ ^ 2 = 0 := by rw [hid']; simp [h0]
    linarith

end Main

end AVRegularity.Applications.Davies
end
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity
namespace AVRegularity.Applications.Davies

/-! # The amplitude `A` and the label cylinder

`∬_{(t₁-8T,t₁)×B_R} U² = ∬_{𝒫_out} θ² = |𝒫_out| A² ≤ 32 T R² A²`. -/

open AVRegularity.Applications

theorem volume_euclidBall_le (R : ℝ) :
    (volume (euclidBall (0 : Vec 2) R)).toReal ≤ (2 * |R|) ^ 2 := by
  have hsub : euclidBall (0 : Vec 2) R ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-|R|) |R|) := by
    intro y hy i _
    have h2 : vecNormSq y < R ^ 2 := by simpa [euclidBall] using hy
    have h3 := abs_coord_le_sqrt y i
    have h4 : Real.sqrt (vecNormSq y) ≤ |R| :=
      Real.sqrt_le_iff.2 ⟨abs_nonneg _, by rw [sq_abs]; exact h2.le⟩
    exact abs_le.1 (h3.trans h4)
  have hfin : volume (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-|R|) |R|)) =
      ENNReal.ofReal ((2 * |R|) ^ 2) := by
    rw [volume_pi, Measure.pi_pi]
    have h2 : |R| - -|R| = 2 * |R| := by ring
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h2]
    rw [← ENNReal.ofReal_pow (by positivity)]
  have := measure_mono (μ := volume) hsub
  rw [hfin] at this
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans (by
    rw [ENNReal.toReal_ofReal (by positivity)])

theorem integral_cyl_eq {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (θ : ℝ → Vec 2 → ℝ) :
    ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R, θ p.1 (X p.1 p.2 t₁) ^ 2 =
      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2 := by
  have hmp := (pipeMap_mp ch hT).restrict_preimage_emb (pipeMap_measurableEmbedding ch hT)
    (outerPipe (fun t y => X t y t₁) t₁ T R)
  rw [pipeMap_preimage_outerPipe ch] at hmp
  have h := hmp.integral_comp (pipeMap_measurableEmbedding ch hT) (fun p => θ p.1 p.2 ^ 2)
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod (pipe_isOpen_euclidBall 0 R).measurableSet)
    fun p hp => ?_
  have htI : p.1 ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨hp.1.1.le, hp.1.2.le⟩
  simp only [pipeMap_apply_of_mem htI]

theorem amp_bound {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (θ : ℝ → Vec 2 → ℝ) :
    ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R, θ p.1 (X p.1 p.2 t₁) ^ 2 ≤
      32 * T * R ^ 2 * pipeAmp X t₁ T R θ ^ 2 := by
  set P := outerPipe (fun t y => X t y t₁) t₁ T R with hP
  have hvol : volume P = volume (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R) := by
    rw [← (pipeMap_mp ch hT).measure_preimage_emb (pipeMap_measurableEmbedding ch hT) P,
      pipeMap_preimage_outerPipe ch]
  have hB : 0 < volume (euclidBall (0 : Vec 2) R) := by
    refine (pipe_isOpen_euclidBall 0 R).measure_pos volume ⟨0, ?_⟩
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero]
    have : vecNormSq (0 : Vec 2) = 0 := by simp [vecNormSq, vecDot]
    rw [this]; positivity
  have hBfin := pipe_volume_euclidBall_lt_top R
  have hvc : volume (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall (0 : Vec 2) R) =
      ENNReal.ofReal (8 * T) * volume (euclidBall (0 : Vec 2) R) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    congr 2; ring
  have hm : (volume P).toReal = 8 * T * (volume (euclidBall (0 : Vec 2) R)).toReal := by
    rw [hvol, hvc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hmpos : 0 < (volume P).toReal := by
    rw [hm]
    exact mul_pos (by positivity) (ENNReal.toReal_pos hB.ne' hBfin.ne)
  have hmle : (volume P).toReal ≤ 32 * T * R ^ 2 := by
    rw [hm]
    have := volume_euclidBall_le R
    rw [mul_pow, sq_abs] at this
    calc 8 * T * (volume (euclidBall (0 : Vec 2) R)).toReal ≤ 8 * T * (2 ^ 2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 32 * T * R ^ 2 := by ring
  have hI : 0 ≤ ∫ p in P, θ p.1 p.2 ^ 2 := integral_nonneg fun p => sq_nonneg _
  · have hA : pipeAmp X t₁ T R θ ^ 2 = (volume P).toReal⁻¹ * ∫ p in P, θ p.1 p.2 ^ 2 := by
      unfold pipeAmp
      rw [Real.sq_sqrt (by positivity)]
    rw [integral_cyl_eq ch hT θ, hA]
    calc ∫ p in P, θ p.1 p.2 ^ 2
        = (volume P).toReal * ((volume P).toReal⁻¹ * ∫ p in P, θ p.1 p.2 ^ 2) := by
          field_simp
      _ ≤ 32 * T * R ^ 2 * ((volume P).toReal⁻¹ * ∫ p in P, θ p.1 p.2 ^ 2) :=
          mul_le_mul_of_nonneg_right hmle (by positivity)

end AVRegularity.Applications.Davies
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications.Davies

/-! # The material chart as the flow of an admissible stream

Any flow `X` of `streamVel φ`, `φ` admissible, is `streamFlow φ hφ`; this gives the lattice
equivariance, the measure preservation and the cell-integral invariance of the chart maps
`y ↦ X t y s`. -/

section

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X)

include hφ hX

theorem X_eq_streamFlow : X = AVRegularity.streamFlow φ hφ :=
  Infra.Flow.flow_eq_of_isFlow _ hφ.vel_lipschitz hX
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz)

theorem X_lattice (t s : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
    X t (x + latticeShift k) s = X t x s + latticeShift k := by
  rw [X_eq_streamFlow hφ hX]
  exact CycleReference.streamFlow_lattice_equivariant hφ t s x k

theorem X_mp (t s : ℝ) : MeasurePreserving (fun x => X t x s) volume volume := by
  rw [X_eq_streamFlow hφ hX]
  exact CycleReference.streamFlow_measurePreserving hφ t s

theorem X_cell_integral (t s : ℝ) {u : Vec 2 → ℝ} (hu : IsZ2Periodic u) :
    ∫ y in unitCube, u (X t y s) = ∫ x in unitCube, u x := by
  rw [X_eq_streamFlow hφ hX]
  exact CycleReference.streamFlow_cell_integral hφ t s u hu

theorem X_cell_memL2 (t s : ℝ) {u : Vec 2 → ℝ} (hp : IsZ2Periodic u) (hu : MemL2On unitCube u) :
    MemL2On unitCube (fun y => u (X t y s)) := by
  rw [X_eq_streamFlow hφ hX]
  exact CycleReference.streamFlow_cell_memL2 hφ t s hp hu

end

end AVRegularity.Applications.Davies
end
end
end

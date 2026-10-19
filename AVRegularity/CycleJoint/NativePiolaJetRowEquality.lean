-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneWeakCurveCongruenceOn
import AVRegularity.CycleJoint.PlaneWindowScalarDiffusion
public import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
import AVRegularity.Families.TorusCompatible.WeakStage

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Weak Hilbert curves depend only on the derivative on their physical time window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Changing a weak dual outside the solution window preserves the weak Hilbert curve. -/
theorem planeWeakHilbertCurve_dual_congr_on {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (he : ∀ t ∈ Icc a b, dual t = dual' t) :
    PlaneWeakHilbertCurve a b u slice dual' := by
  have hae : dual =ᵐ[volume.restrict (Icc a b)] dual' := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact he t ht
  refine ⟨h.trace, h.state, MemLp.ae_eq hae h.dual_mem, h.agrees, ?_⟩
  intro s hs t ht hst z
  refine (h.increment s hs t ht hst z).trans ?_
  apply intervalIntegral.integral_congr
  intro r hr
  have hrab : r ∈ Icc a b :=
    Icc_subset_Icc hs.1 ht.2 (by simpa only [uIcc_of_le hst] using hr)
  change inner ℝ (dual r) z = inner ℝ (dual' r) z
  rw [he r hrab]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Restriction of the actual weak Hilbert curve preserves its fixed-test equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_subwindow {a b c d : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual) (hsub : Icc c d ⊆ Icc a b) :
    PlaneWeakHilbertCurve c d u slice dual := by
  refine ⟨h.trace.mono hsub, h.state.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.dual_mem.mono_measure (Measure.restrict_mono hsub le_rfl),
    ae_restrict_of_ae_restrict_of_subset hsub h.agrees, ?_⟩
  intro s hs t ht hst z
  exact h.increment s (hsub hs) t (hsub ht) hst z

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Periodization is an actual linear map on the genuine finite-moment domain. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodizeRadialPlaneCarrier_add (f g : PlaneHk Set.univ K E) (z : Vec 2)
    (hf : HasRadialPlaneMoments f z) (hg : HasRadialPlaneMoments g z) :
    periodizeRadialPlaneCarrier (f + g) z (hf.add hg) =
      periodizeRadialPlaneCarrier f z hf + periodizeRadialPlaneCarrier g z hg := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [torusJetComponent_add,
    periodizeRadialPlaneCarrier_component_eq_series (f + g) z (hf.add hg) a,
    periodizeRadialPlaneCarrier_component_eq_series f z hf a,
    periodizeRadialPlaneCarrier_component_eq_series g z hg a]
  have he (n : Fin 2 → ℤ) :=
    (planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a).map_add f g
  simp_rw [he]
  exact (radialCarrier_images_summable f z hf a).tsum_add (radialCarrier_images_summable g z hg a)

theorem periodizeRadialPlaneCarrier_smul (c : ℝ) (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hf : HasRadialPlaneMoments f z) :
    periodizeRadialPlaneCarrier (c • f) z (hf.smul c) = c • periodizeRadialPlaneCarrier f z hf := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rw [torusJetComponent_smul,
    periodizeRadialPlaneCarrier_component_eq_series (c • f) z (hf.smul c) a,
    periodizeRadialPlaneCarrier_component_eq_series f z hf a]
  have he (n : Fin 2 → ℤ) :=
    (planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a).map_smul c f
  simp_rw [he]
  exact (radialCarrier_images_summable f z hf a).tsum_const_smul c

def periodizeRadialPlaneLinear (K : ℕ) (z : Vec 2) :
    radialPlaneMomentSubmodule (E := E) K z →ₗ[ℝ] TorusHk K E where
  toFun f := periodizeRadialPlaneCarrier f.val z f.property
  map_add' f g := periodizeRadialPlaneCarrier_add f.val g.val z f.property g.property
  map_smul' c f := periodizeRadialPlaneCarrier_smul c f.val z f.property

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Almost-everywhere moment bounds produce the actual periodized Sobolev curve in L2 time. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace X] {K : ℕ}

theorem exists_periodized_radial_carrier_time_memLp (μ : Measure X)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2)
    (hm : ∀ᵐ t ∂μ, HasRadialPlaneMoments (f t) z)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hb : ∀ᵐ t ∂μ, ∀ a, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    ∃ u : X → TorusHk K E, MemLp u 2 μ ∧
      ∀ᵐ t ∂μ, ∀ a, (u t).val a =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (f t).toFunction.jet a := by
  let g := radialMomentGoodPart f z
  have hg : MemLp g 2 μ := radialMomentGoodPart_memLp μ f z hf hm
  have hgm (t : X) : HasRadialPlaneMoments (g t) z := radialMomentGoodPart_hasMoments f z t
  let u : X → TorusHk K E := fun t => periodizeRadialPlaneCarrier (g t) z (hgm t)
  have hgb : ∀ᵐ t ∂μ, ∀ a, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (g t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal ‖M t‖ := by
    filter_upwards [hm, hb] with t ht hm'
    have he : g t = f t := radialMomentGoodPart_eq f z t ht
    rw [he]
    exact hm'
  refine ⟨u, periodizeRadialPlaneCarrier_time_memLp μ g hg z hgm M hM hgb, ?_⟩
  filter_upwards [hm] with t ht
  intro a
  have he : g t = f t := radialMomentGoodPart_eq f z t ht
  have hp := periodizeRadialPlaneCarrier_component_ae (g t) z (hgm t) a
  apply hp.trans
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun v : PlaneHk Set.univ K E => periodizeRawJet v.toFunction.jet a x) he)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Literal value readout of the genuine native compact Hilbert spacetime carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem compactSpacetimeHilbertHk_value_ae (K : ℕ) (f : ℝ × Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (t : ℝ) :
    planeValue (compactSpacetimeHilbertHk K f hf hs t) =ᵐ[volume] fun x => f (t, x) := by
  rw [planeValue_eq_stored]
  have h := compactSpacetimeHilbertHk_jet_ae K f hf hs t 0 (Nat.zero_le K) Fin.elim0
  have hv := (ae_restrict_iff' MeasurableSet.univ).mp h
  filter_upwards [hv] with x hx
  exact hx (mem_univ x)

end AVRegularity.CycleJointProofs
end

section
open Homogenization Set
namespace AVRegularity.CycleJointProofs

/-! A compact smooth Hilbert spatial field extends to a compact spacetime field with fixed slices on the window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_compact_spacetime_fixed_hilbert_field (a b : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ∃ η : ℝ × Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      ∀ t ∈ Icc a b, ∀ x, η (t, x) = f x := by
  obtain ⟨τ, hτ, hsτ, _, hτ1⟩ := Weighted.exists_compact_time_cutoff a b
  let η := fun p : ℝ × Vec 2 => τ p.1 • f p.2
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := (hτ.comp contDiff_fst).smul (hf.comp contDiff_snd)
  have hsη : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact (hsτ.isCompact.prod hs.isCompact)
    intro p hp
    have ht : τ p.1 ≠ 0 := by
      intro ht
      exact hp (by simp only [η, ht, zero_smul])
    have hx : f p.2 ≠ 0 := by
      intro hx
      exact hp (by simp only [η, hx, smul_zero])
    exact ⟨subset_tsupport τ ht, subset_tsupport f hx⟩
  refine ⟨η, hη, hsη, ?_⟩
  intro t ht x
  simp only [η, (hτ1 t ht).1, one_smul]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The natural constituent operator has the full spatial reserve before partition weighting. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem natural_constituent_operator_smooth (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (hE : E ≠ 0) (K : ι → ℕ) (dom : F.Domain)
    (hs : F.IsSmoothOn dom E K) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (s t : ℝ)
    (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c) :
    ContDiff ℝ (K v : ℕ) (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) := by
  let B := fun d (I : DerivativeWord2 (d - 1)) y => F.dimFlux ν e E p c v u γ d I t
    (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)
  have hy : ContDiff ℝ (K v : ℕ) (fun y : Vec 2 => streamFlow φ hφ s y t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  have hB d I : ContDiff ℝ (K v : ℕ) (B d I) := by
    have hh := molecular_joint_contDiff F dom E hE K hs p c t hdom v u γ d I
    exact (hh.comp ((hy.const_smul E⁻¹).prodMk (hy.const_smul e⁻¹))).const_smul
      (ν * e ^ (d - 2))
  apply nativeArrayAssembly_spatial_smooth r (K v) (F.identity v u γ).map
  intro a A
  exact transportedCoeff_spatial_smooth (naturalPreparationJacobian hφ s t)
    (fun i j => (naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)) (F.identity v u γ).maxOrder (K v) B
    (fun d I i => contDiff_pi.mp (hB d I) i) r A a
end

/-! The natural constituent operator has the full spatial reserve before partition weighting. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem natural_flow_constituent_operator_smooth (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (hE : E ≠ 0) (K : ι → ℕ) (dom : F.Domain)
    (hs : F.IsSmoothOn dom E K) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (s t τ : ℝ)
    (hdom : ∀ Y : Vec 2, (τ, Y) ∈ dom p c) :
    ContDiff ℝ (K v : ℕ) (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I τ
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) := by
  let B := fun d (I : DerivativeWord2 (d - 1)) y => F.dimFlux ν e E p c v u γ d I τ
    (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)
  have hy : ContDiff ℝ (K v : ℕ) (fun y : Vec 2 => streamFlow φ hφ s y t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  have hB d I : ContDiff ℝ (K v : ℕ) (B d I) := by
    have hh := molecular_joint_contDiff F dom E hE K hs p c τ hdom v u γ d I
    exact (hh.comp ((hy.const_smul E⁻¹).prodMk (hy.const_smul e⁻¹))).const_smul
      (ν * e ^ (d - 2))
  apply nativeArrayAssembly_spatial_smooth r (K v) (F.identity v u γ).map
  intro a A
  exact transportedCoeff_spatial_smooth (naturalPreparationJacobian hφ s t)
    (fun i j => (naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)) (F.identity v u γ).maxOrder (K v) B
    (fun d I i => contDiff_pi.mp (hB d I) i) r A a
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal component readouts uniquely determine the actual periodized torus carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem torusCarrier_eq_of_raw_readouts (u v : TorusHk K E) (D : RawJet2 K E)
    (hu : ∀ a, u.val a =ᵐ[volume.restrict AVenhance.unitCube] D a)
    (hv : ∀ a, v.val a =ᵐ[volume.restrict AVenhance.unitCube] D a) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  exact Lp.ext ((hu a).trans (hv a).symm)

theorem torusCarrier_eq_periodization (u : TorusHk K E) (f : PlaneHk Set.univ K E)
    (z : Vec 2) (hf : HasRadialPlaneMoments f z)
    (hu : ∀ a, u.val a =ᵐ[volume.restrict AVenhance.unitCube] periodizeRawJet f.toFunction.jet a) :
    u = periodizeRadialPlaneCarrier f z hf :=
  torusCarrier_eq_of_raw_readouts u _ _ hu (periodizeRadialPlaneCarrier_component_ae f z hf)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Polarization gives the exact variable pairing identity of two weak plane curves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_pair_increment {a b : ℝ} (hab : a ≤ b)
    {u u' : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual slice' dual' : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (h' : PlaneWeakHilbertCurve a b u' slice' dual') :
    inner ℝ (u b) (u' b) - inner ℝ (u a) (u' a) =
      ∫ t in a..b, inner ℝ (dual t) (slice' t) + inner ℝ (dual' t) (slice t) := by
  have hint (f g : ℝ → PlaneHk Set.univ 1 E)
      (hf : MemLp f 2 (volume.restrict (Icc a b)))
      (hg : MemLp g 2 (volume.restrict (Icc a b))) :
      IntervalIntegrable (fun t => inner ℝ (f t) (g t)) volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    exact (memLp_two_inner_integrable _ f g hf hg).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have h11 := hint dual slice h.dual_mem h.state
  have h22 := hint dual' slice' h'.dual_mem h'.state
  have h12 := hint dual slice' h.dual_mem h'.state
  have h21 := hint dual' slice h'.dual_mem h.state
  have hs := (h.sub h').energy_increment hab
  have hr (t : ℝ) :
      2 * inner ℝ (dual t - dual' t) (slice t - slice' t) =
      2 * inner ℝ (dual t) (slice t) + 2 * inner ℝ (dual' t) (slice' t) -
        2 * (inner ℝ (dual t) (slice' t) + inner ℝ (dual' t) (slice t)) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  simp_rw [hr] at hs
  rw [intervalIntegral.integral_sub ((h11.const_mul 2).add (h22.const_mul 2))
      ((h12.add h21).const_mul 2),
    intervalIntegral.integral_add (h11.const_mul 2) (h22.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hs
  rw [norm_sub_sq_real, norm_sub_sq_real] at hs
  have hE := h.energy_increment hab
  have hE' := h'.energy_increment hab
  rw [intervalIntegral.integral_const_mul] at hE hE'
  linear_combination (hE + hE' - hs) / 2

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Positive time dilation preserves a weak plane Hilbert trajectory and scales its dual derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakHilbertCurve_time_dilation {a b ν : ℝ} (hν : 0 < ν)
    {u : ℝ → Lp E 2 (volume : Measure (Homogenization.Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual) :
    PlaneWeakHilbertCurve (ν * a) (ν * b)
      (fun t => u (ν⁻¹ * t)) (fun t => slice (ν⁻¹ * t))
      (fun t => ν⁻¹ • dual (ν⁻¹ * t)) := by
  have hmem {t : ℝ} (ht : t ∈ Icc (ν * a) (ν * b)) : ν⁻¹ * t ∈ Icc a b := by
    have hh : t / ν ∈ Icc a b :=
      ⟨(le_div_iff₀ hν).2 (by simpa only [mul_comm] using ht.1),
        (div_le_iff₀ hν).2 (by simpa only [mul_comm] using ht.2)⟩
    simpa only [div_eq_mul_inv, mul_comm] using hh
  refine ⟨h.trace.comp (continuous_const.mul continuous_id).continuousOn
      (fun _ ht => hmem ht),
    memLp_comp_inv_mul_restrict_Icc hν h.state,
    (memLp_comp_inv_mul_restrict_Icc hν h.dual_mem).const_smul ν⁻¹,
    ae_comp_inv_mul_restrict_Icc hν h.agrees, ?_⟩
  intro s hs t ht hst z
  have he := h.increment (ν⁻¹ * s) (hmem hs) (ν⁻¹ * t) (hmem ht)
    (mul_le_mul_of_nonneg_left hst (inv_nonneg.mpr hν.le)) z
  rw [he]
  simp only [real_inner_smul_left]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun r => inner ℝ (dual r) z) (inv_ne_zero hν.ne')]
  simp only [inv_inv, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The molecular envelope bounds the actual dimensional diagonal sample before chart transport. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pointwise_molecular_physical_sample_raw_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom p c) → ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y)) x‖ ≤
        (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
          (pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
            (fun z => F.dimFlux ν e E z.1 z.2 v u γ d I)).toReal := by
  intro t hdom j hj x
  have ht := pointwise_molecular_physical_sample_jet_budget F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b henv v u γ hγ d hd I p c t
  exact (ht hdom j hj x).trans_eq
    (molecular_sample_price_cancellation ν e ρ _ hν he hρ (K v) (d - 2) _)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Subtraction commutes with the actual image periodization on its moment domain. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem HasRadialPlaneMoments.sub {f g : PlaneHk Set.univ K E} {z : Vec 2}
    (hf : HasRadialPlaneMoments f z) (hg : HasRadialPlaneMoments g z) :
    HasRadialPlaneMoments (f - g) z := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.smul (-1))

theorem periodizeRadialPlaneCarrier_sub
    (f g : PlaneHk Set.univ K E) (z : Vec 2)
    (hf : HasRadialPlaneMoments f z) (hg : HasRadialPlaneMoments g z) :
    periodizeRadialPlaneCarrier (f - g) z (hf.sub hg) =
      periodizeRadialPlaneCarrier f z hf - periodizeRadialPlaneCarrier g z hg := by
  exact (periodizeRadialPlaneLinear K z).map_sub
    (⟨f, hf⟩ : radialPlaneMomentSubmodule K z) ⟨g, hg⟩
end

/-! Actual moment periodization commutes with Sobolev truncation. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem HasRadialPlaneMoments.truncate {f : PlaneHk Set.univ L E} {z : Vec 2}
    (hf : HasRadialPlaneMoments f z) (hKL : K ≤ L) :
    HasRadialPlaneMoments (truncatePlaneHk hKL f) z := by
  intro a
  exact hf (truncateJetIndex hKL a)

theorem periodizeRadialPlaneCarrier_truncate (hKL : K ≤ L) (f : PlaneHk Set.univ L E)
    (z : Vec 2) (hf : HasRadialPlaneMoments f z) :
    periodizeRadialPlaneCarrier (truncatePlaneHk hKL f) z (hf.truncate hKL) =
      truncateTorusHk hKL (periodizeRadialPlaneCarrier f z hf) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [truncateTorusHk_apply]
  calc
    _ = ∑' n : Fin 2 → ℤ, planeImageJetCLM AVenhance.unitCube
        (AVenhance.latticeShift n) a (truncatePlaneHk hKL f) :=
      periodizeRadialPlaneCarrier_component_eq_series (truncatePlaneHk hKL f) z
        (hf.truncate hKL) a
    _ = ∑' n : Fin 2 → ℤ, planeImageJetCLM AVenhance.unitCube
        (AVenhance.latticeShift n) (truncateJetIndex hKL a) f := rfl
    _ = _ := (periodizeRadialPlaneCarrier_component_eq_series f z hf
      (truncateJetIndex hKL a)).symm
end

/-! Almost-everywhere plane lifts retain their exact truncation after genuine carrier periodization. -/

section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace X] {K L : ℕ}

theorem periodized_carrier_lift_ae (μ : Measure X) (hKL : K ≤ L) (z : Vec 2)
    (u : X → PlaneHk Set.univ K E) (w : X → PlaneHk Set.univ L E)
    (hu : ∀ t, HasRadialPlaneMoments (u t) z)
    (hlift : ∀ᵐ t ∂μ, truncatePlaneHk hKL (w t) = u t)
    (W : X → TorusHk L E)
    (hW : ∀ᵐ t ∂μ, ∀ a, (W t).val a =ᵐ[volume.restrict AVenhance.unitCube]
      periodizeRawJet (w t).toFunction.jet a) :
    ∀ᵐ t ∂μ, truncateTorusHk hKL (W t) = periodizeRadialPlaneCarrier (u t) z (hu t) := by
  filter_upwards [hlift, hW] with t ht hw
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  have he := congrArg (fun f : PlaneHk Set.univ K E => periodizeRawJet f.toFunction.jet a) ht
  change periodizeRawJet (w t).toFunction.jet (truncateJetIndex hKL a) =
    periodizeRawJet (u t).toFunction.jet a at he
  have hr := (hw (truncateJetIndex hKL a)).trans
    (Filter.Eventually.of_forall (fun x => congrFun he x))
  exact hr.trans (periodizeRadialPlaneCarrier_component_ae (u t) z (hu t) a).symm
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! A strongly differentiable H1 test is a weak plane curve with its exact L2 dual derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeWeakCurve_of_strong_test {a b : ℝ} (hab : a ≤ b)
    (z dz : ℝ → PlaneHk Set.univ 1 E) (hz : StrongTimeRegularity a b z dz)
    (hzm : MemLp z 2 (volume.restrict (Icc a b)))
    (hdzm : MemLp dz 2 (volume.restrict (Icc a b))) :
    PlaneWeakHilbertCurve a b (fun t => planeHkValueOperator 1 (z t)) z
      (fun t => (planeHkValueOperator (E := E) 1).adjoint (planeHkValueOperator 1 (dz t))) := by
  let L := planeHkValueOperator (E := E) 1
  have htime := hz.map L
  refine ⟨?_, hzm, ?_, Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  · simpa only [uIcc_of_le hab] using htime.ac.continuousOn
  · exact (L.adjoint.comp L).comp_memLp' hdzm
  · intro s hs t ht hst ψ
    have hsub : uIcc s t ⊆ uIcc a b := by
      rw [uIcc_of_le hst, uIcc_of_le hab]
      exact Icc_subset_Icc hs.1 ht.2
    have hinc := (htime.mono hsub).pairing_increment (L ψ)
    apply hinc.trans
    apply intervalIntegral.integral_congr
    intro r _
    exact (ContinuousLinearMap.adjoint_inner_left L ψ (L (dz r))).symm

theorem planeWeakCurve_strong_test_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (z dz : ℝ → PlaneHk Set.univ 1 E) (hz : StrongTimeRegularity a b z dz)
    (hzm : MemLp z 2 (volume.restrict (Icc a b)))
    (hdzm : MemLp dz 2 (volume.restrict (Icc a b))) :
    inner ℝ (u b) (planeHkValueOperator 1 (z b)) -
      inner ℝ (u a) (planeHkValueOperator 1 (z a)) =
      ∫ t in a..b, inner ℝ (dual t) (z t) +
        inner ℝ (planeHkValueOperator 1 (dz t)) (u t) := by
  have hp := planeWeakCurve_pair_increment hab h
    (planeWeakCurve_of_strong_test hab z dz hz hzm hdzm)
  apply hp.trans
  apply intervalIntegral.integral_congr_ae_restrict
  have ha := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self h.agrees
  rw [uIoc_of_le hab]
  filter_upwards [ha] with t ht
  rw [ContinuousLinearMap.adjoint_inner_left, ← ht]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Uniform finite-reserve constants preserve every positive native-order and word summand. -/

theorem uniform_native_vector_transport_assembly_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ Dmax Kmax n r : ℕ)
    (hD : Dγ ≤ Dmax) (hkn : n ≤ Kmax) (C E ρ : ℝ) (hC : 1 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I, ContDiff ℝ (n : ℕ) (B d I))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hMB : ∀ d I, 0 ≤ MB d I)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (B d I) y‖ ≤ MB d I)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) r A y a)) x‖ ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, ‖Cmap‖ *
        (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) *
              (MB d I * E⁻¹ ^ (d - 1 - r))) := by
  exact uniform_native_transport_assembly_jet_bound K hK N Dγ Dmax Kmax n r hD hkn
    C E ρ hC hE hρ hρE hn hKC B
    (fun d I i => contDiff_pi.mp (hB d I) i) MB hMB
    (fun d hd I i j hj y => vector_component_jet_budget (B d I) j
      ((hB d I).of_le (by exact_mod_cast hj)) ρ (MB d I) hρ (hBj d hd I j hj) i y)
    Cmap x

/-! The actual transported coefficient array reproduces the Piola flux of every positive native source order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseChart_native_flux (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (D : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (g : Vec 2 → E) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Vec 2) (a : Fin 2) :
    (∑ r ∈ Finset.Icc 1 D, ∑ A : DerivativeWord2 r,
      transportedCoeff (chartInvJacobian ⇑X.symm) D B r A y a •
        orderedDerivative A (g ∘ X.symm) y) =
      ∑ d ∈ Finset.Icc 2 D, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
        (chartInvJacobian ⇑X.symm y a i * B d I i) • orderedDerivative I g (X.symm y) := by
  rw [transportedCoeff_all_orders_flux]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro i hi
  rw [inverseChart_ordered_native_jet_expansion X hX hY
    (show 0 < d - 1 from by have hh := Finset.mem_Icc.mp hd; omega) I g hg y]
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! A true weak curve retains its time equation when the diffusion deviation is reassigned to its computed source flux. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_diffusion_reallocation {a b : ℝ}
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (state : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (T : ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D D' : ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (h : PlaneWeakHilbertCurve a b u state
      (fun t => planeWeakDualRepresentative (T t) (D t) (state t) (F t))) :
    PlaneWeakHilbertCurve a b u state
      (fun t => planeWeakDualRepresentative (T t) (D' t) (state t)
        ((D t - D' t) (planeH1GradientOperator (state t)) + F t)) := by
  have he : (fun t => planeWeakDualRepresentative (T t) (D' t) (state t)
      ((D t - D' t) (planeH1GradientOperator (state t)) + F t)) =
      (fun t => planeWeakDualRepresentative (T t) (D t) (state t) (F t)) := by
    funext t
    exact (planeWeakDual_diffusion_reallocation (T t) (D t) (D' t) (state t) (F t)).symm
  rw [he]
  exact h

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A smooth Eulerian state has exactly the native-chart Piola source flux prescribed by the
coefficient array `B`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem forwardChart_native_flux (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (D : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (u : Vec 2 → E) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (a : Fin 2) :
    (∑ r ∈ Finset.Icc 1 D, ∑ A : DerivativeWord2 r,
      transportedCoeff (chartInvJacobian ⇑X.symm) D B r A y a • orderedDerivative A u y) =
      ∑ d ∈ Finset.Icc 2 D, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
        (chartInvJacobian ⇑X.symm y a i * B d I i) •
          orderedDerivative I (u ∘ X) (X.symm y) := by
  have he := inverseChart_native_flux X hX hY D B (u ∘ X) (hu.comp hX) y a
  have hc : (u ∘ X) ∘ X.symm = u := by
    funext z
    exact congrArg u (X.apply_symm_apply z)
  rw [hc] at he
  exact he

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The literal metric-plus-source coefficient supplies the regularity needed
by the full coupled feedback theorem, from its actual constituent bounds. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeMetricSource_coefficient_data
    (K : ι → ℕ) (D : ℕ) (ρ a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ v u, (d : admissibleOrders K D v u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v))
    (hA : ∀ v u d, coefficientSeminorm ρ (K v) a b (A v u d) ≠ ⊤)
    (hAc : ∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ) (A v u d t))
    (hG : ∀ v t, t ∈ Set.Icc a b → ∀ k j, ContDiff ℝ (K v : ℕ) (fun x => G t x k j))
    (M : ∀ v, Fin (K v + 1) → ℝ)
    (hb : ∀ v (l : Fin (K v + 1)) t, t ∈ Set.Icc a b → ∀ x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M v l) :
    (∀ v u d, coefficientSeminorm ρ (K v) a b (planeMetricSourceCoefficient K D G A v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc a b →
      ContDiff ℝ (K v : ℕ) (planeMetricSourceCoefficient K D G A v u d t)) := by
  constructor
  · intro v u d
    exact coefficientSeminorm_add_ne_top _ _ ρ (K v) a b
      (fun t ht => metric_order_coefficient_contDiff K D G v u d t (hG v t ht))
      (hAc v u d) (metric_order_coefficients_finite K D G ρ a b v u d (hG v) (M v) (hb v)) (hA v u d)
  · intro v u d t ht
    exact (metric_order_coefficient_contDiff K D G v u d t (hG v t ht)).add (hAc v u d t ht)

theorem planeMetricSource_coefficient_data_of_window_metric_envelope
    (K : ι → ℕ) (Kmax D : ℕ) (hK : ∀ v, K v ≤ Kmax) (ρ a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ v u, (d : admissibleOrders K D v u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v))
    (hA : ∀ v u d, coefficientSeminorm ρ (K v) a b (A v u d) ≠ ⊤)
    (hAc : ∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ) (A v u d t))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hg4 : g ≤ 1 / 4)
    (hnear : CycleWords.IsMetricNearIdentityOn (Set.Icc a b) G g)
    (hsym : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (hG : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ (max Kmax 1 : ℕ) (fun x => G t x k j))
    (hjets : ∀ t ∈ Set.Icc a b, ∀ x, ∀ j, 1 ≤ j → j ≤ Kmax → ∀ k l,
      ‖iteratedFDeriv ℝ j (fun y => G t y k l) x‖ ≤ CG j * g * δ ^ j) :
    (∀ v u d, coefficientSeminorm ρ (K v) a b (planeMetricSourceCoefficient K D G A v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc a b →
      ContDiff ℝ (K v : ℕ) (planeMetricSourceCoefficient K D G A v u d t)) := by
  let Gc := CycleWords.metricClamp a b G
  have heq t (ht : t ∈ Set.Icc a b) : Gc t = G t :=
    CycleWords.metricClamp_of_mem G ht
  have hsymc : ∀ t ∈ Set.Icc a b, ∀ x, (Gc t x).IsSymm := by
    intro t ht x
    rw [heq t ht]
    exact hsym t ht x
  have hjetsc : ∀ t ∈ Set.Icc a b, ∀ x, ∀ j, 1 ≤ j → j ≤ Kmax → ∀ k l,
      ‖iteratedFDeriv ℝ j (fun y => Gc t y k l) x‖ ≤ CG j * g * δ ^ j := by
    intro t ht x j hj hjmax k l
    rw [heq t ht]
    exact hjets t ht x j hj hjmax k l
  apply planeMetricSource_coefficient_data K D ρ a b G A hA hAc
    (fun v t ht k j => (hG t ht k j).of_le
      (by exact_mod_cast (hK v).trans (le_max_left Kmax 1)))
    (fun _ l => metricEntryEnvelope CG g δ l.val)
  intro v l t ht x k j
  have hb := metricEntryEnvelope_bound (hK v) Gc CG g δ hg hδ hg4
    (CycleWords.isMetricNearIdentity_metricClamp hab hnear) hsymc hjetsc t ht l x k j
  rwa [heq t ht] at hb

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The positive-viscosity weak trajectory has the literal normalized diffusion operator in cell time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakHilbertCurve_diffusion_time_normalization {a b ν : ℝ} (hν : 0 < ν)
    (T : ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeWeakDualRepresentative (T t) (ν • D t) (slice t) (F t))) :
    PlaneWeakHilbertCurve (ν * a) (ν * b)
      (fun t => u (ν⁻¹ * t)) (fun t => slice (ν⁻¹ * t))
      (fun t => planeWeakDualRepresentative (ν⁻¹ • T (ν⁻¹ * t)) (D (ν⁻¹ * t))
        (slice (ν⁻¹ * t)) (ν⁻¹ • F (ν⁻¹ * t))) := by
  simpa only [planeWeakDualRepresentative_diffusion_normalization ν hν.ne'] using
    planeWeakHilbertCurve_time_dilation hν h

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The literal finite-family torus flux is spatially L2 for every actual lift value. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusRawCouplingFlux_component_memLp (K : ι → ℕ) (D : ℕ) (s : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i : ι)
    (hc : ∀ i' d, Continuous (A i i' d s))
    (M : ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ i' d, 0 ≤ M i' d) (hb : ∀ i' d x, ‖A i i' d s x‖ ≤ M i' d)
    (w : ∀ i, TorusHk (K i + 1) (h i)) (k : Fin 2) :
    MemLp (fun x => torusRawCouplingFlux K D s A w i x k) 2
      (volume.restrict AVenhance.unitCube) := by
  have hi (i' : ι) (d : admissibleOrders K D i i') :
      MemLp (fun x => A i i' d s x (WithLp.toLp 2
        (fun word : DerivativeWord2 (d.1 - 1) => (w i').toFunction.jet
          ⟨⟨d.1 - 1, Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D i i' d)⟩, word⟩ x)) k)
        2 (volume.restrict AVenhance.unitCube) := by
    apply couplingFlux_component_memLp i i' AVenhance.unitCube (A i i' d s)
      (hc i' d) (M i' d) (hM i' d) (hb i' d)
    intro word
    exact periodicJetRepresentative_memL2 (w i').val _
  simp only [torusRawCouplingFlux, WithLp.ofLp_sum, Finset.sum_apply]
  exact memLp_finsetSum Finset.univ (fun i' _ =>
    memLp_finsetSum Finset.univ (fun d _ => hi i' d))

theorem torusRawCouplingFlux_periodic (K : ι → ℕ) (D : ℕ) (s : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i : ι)
    (hp : ∀ i' d, AVenhance.IsZ2Periodic (A i i' d s))
    (w : ∀ i, TorusHk (K i + 1) (h i)) :
    AVenhance.IsZ2Periodic (torusRawCouplingFlux K D s A w i) := by
  intro n x
  unfold torusRawCouplingFlux
  apply Finset.sum_congr rfl
  intro i' _
  apply Finset.sum_congr rfl
  intro d _
  rw [hp i' d n x]
  congr 1
  apply PiLp.ext
  intro word
  exact periodicJetRepresentative_periodic (w i').val _ n x

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Fourth response moments pay the full integer-image sum before time integration. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem translated_coefficient_pairing_time_summable (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    Summable (fun n : Fin 2 → ℤ => ∫ t,
      ‖∫ x, inner ℝ (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
        (φ.toFunction.jet β x)‖ ∂μ) := by
  let g := restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  let p := fun n : Fin 2 → ℤ =>
    (MC * (1 + R + ‖z‖) ^ 4 * ‖g‖) * (1 / spatialLatticeWeight n) ^ 2
  apply summable_integral_norm_of_majorant μ _
    (fun n => translated_coefficient_pairing_time_integrable μ C hc hj MC hMC hC
      f hf (AVenhance.latticeShift n) α φ β) p
    (spatialLatticeReciprocal_square_summable.mul_left _) (fun t => ‖M t‖)
    (hM.norm.integrable (by norm_num))
  filter_upwards [hw, hb] with t ht hbt
  intro n
  rw [translated_compact_coefficient_pairing U (AVenhance.latticeShift n)
    (C t) (hc t) hMC (hC t) (f t) α φ β hφ]
  have he := localImage_coefficient_pairing_radial_bound U R hR hU z α
    (C t) (hc t) MC hMC (hC t) (f t) g ‖M t‖ (norm_nonneg _) ht hbt n
  convert he using 1
  simp only [p, norm_norm]
  ring

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The scalar finite native jet row of a transported constituent is its exact native Piola flux. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transportedNativeScalarJetCoefficient {K : ℕ} (X : Vec 2 ≃ₜ Vec 2) (D : ℕ)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (a : Fin 2) (j : JetIndex2 K) (y : Vec 2) : ℝ :=
  if 1 ≤ j.1.val ∧ j.1.val < D then
    transportedCoeff (chartInvJacobian ⇑X.symm) D
      (fun d I => B (d - 1) I (X.symm y)) j.1.val j.2 y a
  else 0

theorem transportedNativeScalarJetCoefficient_flux {K : ℕ}
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm) (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (u : Vec 2 → E) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (a : Fin 2) :
    (∑ j : JetIndex2 K, transportedNativeScalarJetCoefficient X D B a j y •
      orderedDerivative j.2 u y) =
      ∑ d ∈ Finset.Icc 2 D, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
        (chartInvJacobian ⇑X.symm y a i * B (d - 1) I (X.symm y) i) •
          orderedDerivative I (u ∘ X) (X.symm y) := by
  classical
  simp only [transportedNativeScalarJetCoefficient, ite_smul, zero_smul]
  rw [nativeJet_source_order_sum K D hD
    (fun r A => transportedCoeff (chartInvJacobian ⇑X.symm) D
      (fun d I => B (d - 1) I (X.symm y)) r A y a • orderedDerivative A u y)]
  rw [transportedCoeff_positive_flux_sum]
  exact forwardChart_native_flux X hX hY D _ u hu y a

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.TorusCompatible
namespace AVRegularity.CycleJointProofs

/-! Any integer-equivariant chart transports a periodic native array to periodic scalar jet rows. -/

theorem transportedNativeScalarJetCoefficient_periodic {J : ℕ}
    (X : Vec 2 ≃ₜ Vec 2)
    (hX : ∀ n y, X (y + latticeShift n) = X y + latticeShift n)
    (D : ℕ) (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (hB : ∀ r I, IsZ2Periodic (B r I)) (k : Fin 2) (j : JetIndex2 J) :
    IsZ2Periodic (transportedNativeScalarJetCoefficient X D B k j) := by
  have hY := symm_equivariant X hX
  have hb : IsZ2Periodic (fun x : Vec 2 => fun d (I : DerivativeWord2 (d - 1)) =>
      B (d - 1) I (X.symm x)) := by
    intro n x
    funext d I
    dsimp only
    rw [hY n x]
    exact hB (d - 1) I n _
  have hp := isZ2Periodic_transportedCoeff (isZ2Periodic_chartInvJacobian hY) D hb j.1.val j.2
  intro n x
  unfold transportedNativeScalarJetCoefficient
  by_cases hj : 1 ≤ j.1.val ∧ j.1.val < D
  · simp only [ite_eq_left hj]
    exact congrArg (fun z : Vec 2 => z k) (hp n x)
  · simp only [ite_eq_right hj]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The finite transported native jet row equals the Piola combination of the original source rows. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transportedNativeScalarJetCoefficient_flux_rows {K : ℕ}
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm) (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (u : Vec 2 → E) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (a : Fin 2) :
    (∑ j : JetIndex2 K, transportedNativeScalarJetCoefficient X D B a j y •
      orderedDerivative j.2 u y) =
      ∑ i : Fin 2, chartInvJacobian ⇑X.symm y a i •
        (∑ j : JetIndex2 K, nativeSourceScalarJetCoefficient D B i j (X.symm y) •
          orderedDerivative j.2 (u ∘ X) (X.symm y)) := by
  classical
  rw [transportedNativeScalarJetCoefficient_flux X hX hY D hD B u hu y a]
  simp_rw [nativeSourceScalarJetCoefficient_flux D hD B (u ∘ X) (X.symm y)]
  simp only [Finset.smul_sum, mul_smul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]

end AVRegularity.CycleJointProofs
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.CycleJoint.TorusHkNorm
import AVRegularity.CycleJoint.PlaneCoefficientZeroCarrier

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Weighted fluxes retain the exact spatial smoothness reserve, including unsupported times. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_dimFlux_spatial_smooth (F : ChartedFamily ι h D P Ctx)
    (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (fun yz : Vec 2 × Vec 2 =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
  by_cases hw : F.weight p t = 0
  · simp only [hw, zero_smul]
    exact contDiff_const
  have ht : (t : ℝ) ∈ (F.piece p).output := by
    by_contra hout
    exact hw (F.weight_zero p t hout)
  apply contDiff_iff_contDiffAt.mpr
  intro yz
  have hf : ContDiffAt ℝ (n v : ℕ)
      (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2)
      (E⁻¹ • yz.1, yz.2) :=
    hs p c v u γ d I (t, yz.1) ⟨⟨ht, t.property⟩, Set.mem_univ _⟩ yz.2
  have hg : ContDiff ℝ (n v : ℕ) (fun w : Vec 2 × Vec 2 => (E⁻¹ • w.1, w.2)) :=
    (contDiff_fst.const_smul (E⁻¹)).prodMk contDiff_snd
  have hcomp : ContDiffAt ℝ (n v : ℕ)
      (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t (E⁻¹ • w.1) w.2) yz :=
    ContDiffAt.comp (f := fun w : Vec 2 × Vec 2 => (E⁻¹ • w.1, w.2))
      (g := fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2) yz hf hg.contDiffAt
  simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul] using
    hcomp.const_smul (F.weight p t * (ν * e ^ (d - 2)))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Measurable weights and independent time fields give jointly measurable weighted
dimensional fluxes. Regularity is needed only where the piece's weight is nonzero. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_dimFlux_spatial_continuous (F : ChartedFamily ι h D P Ctx)
    (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : Set.Icc tS tZ) :
    Continuous (fun yz : Vec 2 × Vec 2 => (F.weight p t *
      (ν * e ^ (d - 2))) • F.flux p c v u γ d I t (E⁻¹ • yz.1) yz.2) := by
  by_cases hw : F.weight p t = 0
  · simp only [hw, zero_mul, zero_smul]
    exact continuous_const
  have ht : (t : ℝ) ∈ (F.piece p).output := by
    by_contra hout
    exact hw (F.weight_zero p t hout)
  apply continuous_iff_continuousAt.mpr
  intro yz
  have hr : ContinuousAt (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2)
      (E⁻¹ • yz.1, yz.2) :=
    (hs p c v u γ d I (t, yz.1) ⟨⟨ht, t.property⟩, Set.mem_univ _⟩ yz.2).continuousAt
  have hc : Continuous (fun w : Vec 2 × Vec 2 => (E⁻¹ • w.1, w.2)) :=
    (continuous_fst.const_smul (E⁻¹)).prodMk continuous_snd
  have hcomp : ContinuousAt
      (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t (E⁻¹ • w.1) w.2) yz :=
    ContinuousAt.comp (f := fun w : Vec 2 × Vec 2 => (E⁻¹ • w.1, w.2))
      (g := fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2) hr hc.continuousAt
  exact hcomp.const_smul (F.weight p t * (ν * e ^ (d - 2)))

theorem weighted_dimFlux_joint_measurable (F : ChartedFamily ι h D P Ctx)
    (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tS tZ × (Vec 2 × Vec 2) =>
      F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1 z.2.1 z.2.2) := by
  have hc (t : Set.Icc tS tZ) : Continuous (fun yz : Vec 2 × Vec 2 =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, smul_smul] using
      weighted_dimFlux_spatial_continuous F ν e E tS tZ n hs p c v u γ d I t
  have hm (yz : Vec 2 × Vec 2) : Measurable (fun t : Set.Icc tS tZ =>
      F.weight p t • F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
    change Measurable (fun t : Set.Icc tS tZ => F.weight p t •
      ((ν * e ^ (d - 2)) • F.flux p c v u γ d I t (E⁻¹ • yz.1) yz.2))
    exact ((hwmeas p).comp measurable_subtype_coe).smul
      (((hmeas p c v u γ d I (E⁻¹ • yz.1) yz.2).comp measurable_subtype_coe).const_smul
        (ν * e ^ (d - 2)))
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! The interval extension of the identity metric has the exact identity diffusion operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

theorem identityMetric_nearIdentity :
    IsMetricNearIdentity (fun (_ : ℝ) (_ : Vec 2) => 1) 0 := by
  intro t z ξ
  simp only [sub_self, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    abs_zero, le_refl]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The certificate bounds the actual family's chart derivative uniformly, for an
arbitrary shear. The hypotheses about T and a are scalar construction facts, not chart bounds. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparation_material_eq_streamFlow
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) :
    ⇑((F.piece p).material r) = fun y => streamFlow φ hφ r y (F.piece p).anchor := by
  funext y
  simpa only [ocChart, hc.schedule.anchor_label p hp] using hc.schedule.natural p hp r hr y
end

/-! Uniform derivative bounds for every certified short flow, with constants independent of F. -/

section
variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_flow_fderiv_deviation_jets
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1))
    (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (j : ℕ) (hj : j ≤ Jchart) (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (fun z => streamFlow φ hφ r z σ) x -
      ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
      max (Cchart j) 0 * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j / 2 := by
  have hscale : 0 ≤ (ocEpsilon q Λ (m - 1))⁻¹ ^ j := by
    apply pow_nonneg
    apply inv_nonneg.mpr
    unfold ocEpsilon
    split <;> positivity
  have hbase : 0 ≤ max (Cchart j) 0 * (j.factorial : ℝ) *
      (ocEpsilon q Λ (m - 1))⁻¹ ^ j := by positivity
  have hs : ocA α q Λ (m - 1) * |r - σ| ≤ 1 / 2 := by
    calc
      _ ≤ ocA α q Λ (m - 1) * (2 * Cage * ocTauPP α q Λ m) :=
        mul_le_mul_of_nonneg_left hage ha
      _ = 2 * Cage * ocA α q Λ (m - 1) * ocTauPP α q Λ m := by ring
      _ ≤ _ := hc.short_age
  calc
    _ ≤ Cchart j * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j *
        ocA α q Λ (m - 1) * |r - σ| := hc.jets r hr σ hσ hage j hj y
    _ ≤ max (Cchart j) 0 * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j *
        ocA α q Λ (m - 1) * |r - σ| := by
      gcongr
      exact le_max_left _ _
    _ = (max (Cchart j) 0 * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j) *
        (ocA α q Λ (m - 1) * |r - σ|) := by ring
    _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hs hbase
end

/-! The preparation certificate supplies both endpoints and ages of every active piece. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparation_piece_flow_endpoints
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty)
    (t : ℝ) (ht : t ∈ (F.piece p).geometry)
    (hT : 0 ≤ ocTauPP α q Λ m) :
    (F.piece p).anchor ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) ∧
    t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) ∧
    |t - (F.piece p).anchor| ≤ 2 * Cage * ocTauPP α q Λ m := by
  have ha : (F.piece p).anchor ∈ (F.piece p).geometry :=
    hc.schedule.anchor_segments p hp t ht (Set.left_mem_uIcc)
  refine ⟨hc.schedule.geometry_padded p hp ha, hc.schedule.geometry_padded p hp ht, ?_⟩
  exact (hc.schedule.anchor_age p hp t ht).trans (by
    have hh : 0 ≤ Cage * ocTauPP α q Λ m := mul_nonneg hc.schedule.age_pos.le hT
    nlinarith)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive-radius factorial bounds control the full stored torus carrier norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusHkNorm_full {K : ℕ} (ρ : ℝ) (U : TorusHk K E) :
    torusHkNorm ρ (le_refl K) U = Real.sqrt (factorialNormSq ρ U.val) := by
  have he : truncateTorusHk (le_refl K) U = U := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rfl
  simp only [torusHkNorm, he]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! Uniform positive-order jets of certified forward, inverse and transition flows. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_flow_first_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m) (y : Vec 2) :
    ‖iteratedFDeriv ℝ 1 (fun z => streamFlow φ hφ r z σ) y‖ ≤ 1 + max (Cchart 0) 0 / 2 := by
  have hd := preparation_flow_fderiv_deviation_jets hc ha r σ hr hσ hage 0 (Nat.zero_le _) y
  simp only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one] at hd
  rw [norm_iteratedFDeriv_one]
  calc
    _ = ‖(fderiv ℝ (fun z => streamFlow φ hφ r z σ) y - ContinuousLinearMap.id ℝ (Vec 2)) +
        ContinuousLinearMap.id ℝ (Vec 2)‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ max (Cchart 0) 0 / 2 + 1 := add_le_add hd ContinuousLinearMap.norm_id_le
    _ = _ := add_comm _ _

theorem preparation_flow_higher_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (j : ℕ) (hj0 : j ≠ 0) (hj : j ≤ Jchart) (y : Vec 2) :
    ‖iteratedFDeriv ℝ (j + 1) (fun z => streamFlow φ hφ r z σ) y‖ ≤
      max (Cchart j) 0 * (j.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ j / 2 := by
  have hd := preparation_flow_fderiv_deviation_jets hc ha r σ hr hσ hage j hj y
  have hf : ContDiff ℝ (j : ℕ)
      (fderiv ℝ (fun z => streamFlow φ hφ r z σ)) :=
    (hc.smooth r hr σ hσ).fderiv_right (by exact_mod_cast Nat.add_le_add_right hj 1)
  change ‖iteratedFDeriv ℝ j ((fderiv ℝ (fun z => streamFlow φ hφ r z σ)) -
    (fun _ : Vec 2 => ContinuousLinearMap.id ℝ (Vec 2))) y‖ ≤ _ at hd
  rw [iteratedFDeriv_sub_apply (f := fderiv ℝ (fun z => streamFlow φ hφ r z σ))
    (g := fun _ : Vec 2 => ContinuousLinearMap.id ℝ (Vec 2)) hf.contDiffAt contDiffAt_const,
    congrFun (iteratedFDeriv_const_of_ne hj0 (ContinuousLinearMap.id ℝ (Vec 2))) y,
    Pi.zero_apply, sub_zero, norm_iteratedFDeriv_fderiv] at hd
  exact hd

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Periodic L2 fields and a compact cutoff give integrable actual weak coefficient pairings. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem periodic_compact_coefficient_pairing_integrable (f : Vec 2 → E) (g : Vec 2 → F)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C) (MC : ℝ) (hMC : 0 ≤ MC)
    (hbC : ∀ x, ‖C x‖ ≤ MC) (χ : Vec 2 → ℝ) (hχ : Continuous χ)
    (hcχ : HasCompactSupport χ) :
    Integrable (fun x => inner ℝ (C x (f x)) (g x) * χ x) volume := by
  obtain ⟨B, hbχ⟩ := hχ.bounded_above_of_compact_support hcχ
  obtain ⟨R, hr⟩ := hcχ.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 1)
  have hsupp (x : Vec 2) (hx : χ x ≠ 0) : ‖x‖ ≤ R := hr x (subset_closure hx)
  have hft := finiteCellTruncation_memLp N f hf hfp
  have hCt : MemLp (fun x => C x (finiteCellTruncation N f x)) 2 volume := by
    simpa only [Measure.restrict_univ] using memLp_operator_mul (U := Set.univ) hC
      (by simpa only [Measure.restrict_univ] using hft) hMC hbC
  have hχg := periodic_bounded_supported_multiplier_memLp g hg hgp χ
    hχ.aestronglyMeasurable B R hbχ hsupp
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (hCt.toLp (fun x => C x (finiteCellTruncation N f x)))
    (hχg.toLp (fun x => χ x • g x))
  apply hi.congr
  filter_upwards [hCt.coeFn_toLp, hχg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  by_cases hz : χ x = 0
  · simp [hz]
  · rw [finiteCellTruncation_eq_on_ball hN f (hsupp x hz), inner_smul_right]
    ring
end

/-! Compact operator coefficients localize periodic cell data into global plane L2. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem periodic_supported_operator_memLp (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hp : AVenhance.IsZ2Periodic f)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C) (B R : ℝ) (hB : 0 ≤ B)
    (hcB : ∀ x, ‖C x‖ ≤ B) (hcR : ∀ x, C x ≠ 0 → ‖x‖ ≤ R) :
    MemLp (fun x => C x (f x)) 2 volume := by
  obtain ⟨M, hM⟩ := exists_nat_ge (R + 1)
  have hg := finiteCellTruncation_memLp M f hf hp
  have hs : MemLp (fun x => C x (finiteCellTruncation M f x)) 2 volume := by
    simpa only [Measure.restrict_univ] using memLp_operator_mul (U := Set.univ) hc
      (by simpa only [Measure.restrict_univ] using hg) hB hcB
  have he : (fun x => C x (finiteCellTruncation M f x)) = (fun x => C x (f x)) := by
    funext x
    by_cases hz : C x = 0
    · simp [hz]
    · rw [finiteCellTruncation_eq_on_ball hM f (hcR x hz)]
  rwa [he] at hs

theorem periodic_compact_operator_memLp (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hp : AVenhance.IsZ2Periodic f)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C) (hcs : HasCompactSupport C) :
    MemLp (fun x => C x (f x)) 2 volume := by
  obtain ⟨B, hb⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨R, hr⟩ := hcs.isBounded.exists_norm_le
  have hB : 0 ≤ B := (norm_nonneg (C 0)).trans (hb 0)
  apply periodic_supported_operator_memLp f hf hp C hc B R hB hb
  intro x hx
  exact hr x (subset_closure hx)
end

end AVRegularity.CycleJointProofs
end

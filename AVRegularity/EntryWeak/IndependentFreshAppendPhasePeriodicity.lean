-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.ActualZeroChildReferenceFamily
import AVRegularity.EntryWeak.MolecularUlFluxNormBound

section
section
/-! Equal stored geometries and genuine unit cutoff germs give a common extended metric germ. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem independentFreshExtendedMetric_geometry_germ {r : ℕ} (D : OCData) (level : ℕ)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (slots slots' : Fin r → ℤ) (birthLength birthLength' : Fin r → ℝ)
    (ρ a b : ℝ) (Y Z : Vec (2 + 4 * r))
    (hgeom : (independentFreshStoredFamily A slots birthLength
        (independentStoredParameterProjection (4 * r) Y)).geom D =
      (independentFreshStoredFamily B slots' birthLength'
        (independentStoredParameterProjection (4 * r) Z)).geom D)
    (hslow : independentIntrinsicSlowProjection (4 * r) Y =
      independentIntrinsicSlowProjection (4 * r) Z)
    (χ ψ : Vec (2 + 4 * r) → ℝ)
    (hχ : χ =ᶠ[𝓝 Y] fun _ => 1) (hψ : ψ =ᶠ[𝓝 Z] fun _ => 1) :
    ∃ U : Set (Vec 2), IsOpen U ∧ (0 : Vec 2) ∈ U ∧ ∀ i j,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding (4 * r)) U Y Z
        (fun t (_ : Vec 2) W => clampedParameterMetric
          (cutoffParameterMetric χ (independentFreshNativeMetric D level A slots birthLength ρ))
            a b t W i j)
        (fun t _ W => clampedParameterMetric
          (cutoffParameterMetric ψ (independentFreshNativeMetric D level B slots' birthLength' ρ))
            a b t W i j) := by
  obtain ⟨U, hU, hzero, hχU, hψU⟩ := independent_unit_cutoff_slice_neighborhood
    χ ψ (independentIntrinsicSlowEmbedding (4 * r)) Y Z hχ hψ
  refine ⟨U, hU, hzero, ?_⟩
  exact cutoff_clamped_metric_slow_slice_congr χ ψ _ _ a b
    (independentIntrinsicSlowEmbedding (4 * r)) U Y Z hχU hψU
    (independentFreshNativeMetric_slow_slice_geom_congr D level A B hA hB slots slots'
      birthLength birthLength' ρ Y Z hgeom hslow U)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Equal-depth native metric germs compare without casts of stored coordinate vectors. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem independentFreshExtendedMetric_equalDepth_geometry_germ
    (r s : ℕ) (hrs : r = s) (D : OCData) (level : ℕ)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (slots : Fin r → ℤ) (slots' : Fin s → ℤ)
    (birth : Fin r → ℝ) (birth' : Fin s → ℝ)
    (ρ a b : ℝ) (Y : Vec (2 + 4 * r)) (Z : Vec (2 + 4 * s))
    (hgeom : (independentFreshStoredFamily A slots birth
        (independentStoredParameterProjection (4 * r) Y)).geom D =
      (independentFreshStoredFamily B slots' birth'
        (independentStoredParameterProjection (4 * s) Z)).geom D)
    (hslow : independentIntrinsicSlowProjection (4 * r) Y =
      independentIntrinsicSlowProjection (4 * s) Z)
    (χ : Vec (2 + 4 * r) → ℝ) (ψ : Vec (2 + 4 * s) → ℝ)
    (hχ : χ =ᶠ[𝓝 Y] fun _ => 1) (hψ : ψ =ᶠ[𝓝 Z] fun _ => 1) :
    ∃ U : Set (Vec 2), IsOpen U ∧ (0 : Vec 2) ∈ U ∧ ∀ i j t X, X ∈ U →
      clampedParameterMetric
        (cutoffParameterMetric χ (independentFreshNativeMetric D level A slots birth ρ)) a b t
          (independentIntrinsicSlowEmbedding (4 * r) X + Y) i j =
      clampedParameterMetric
        (cutoffParameterMetric ψ (independentFreshNativeMetric D level B slots' birth' ρ)) a b t
          (independentIntrinsicSlowEmbedding (4 * s) X + Z) i j := by
  subst s
  obtain ⟨U, hU, hzero, he⟩ := independentFreshExtendedMetric_geometry_germ D level
    A B hA hB slots slots' birth birth' ρ a b Y Z hgeom hslow χ ψ hχ hψ
  exact ⟨U, hU, hzero, fun i j t X hX => he i j t X hX 0⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal moving-center transition matrices and their determinant-one slow Jacobians. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*}

theorem weak_recenter_ctxLevel_slot (D : OCData) (A : RealChain) (h : Vec 2) :
    (A.recenter D h).ctxLevel = A.ctxLevel ∧ (A.recenter D h).slot = A.slot ∧
      ((A.recenter D h).WellSlotted ↔ A.WellSlotted) := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  simp only [RealChain.ctxLevel, RealChain.lastLevel, RealChain.slot, RealChain.WellSlotted,
    hb, hs, hc, and_self]

theorem independent_moving_centered_transfer_copy
    (D : OCData) (family : P → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot)
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (Y : (P × Vec 2) × (Vec 2 × Vec 2)) :
    weakTransferCenteredJoint D ((family Y.1.1).recenter D (ρ • Y.1.2)) slot t Y.2 =
      independentCenteredTransfer
        (independentMovingCenteredChart (fun Z : P × Vec 2 =>
          centeredGeometryChart ((family Z.1).geom D) ρ
            (D.slotAnchor (m + 1) slot) Z.2) θ)
        D m pslot (D.slotAnchor (m + 1) slot) t Y := by
  obtain ⟨hc, hp, _⟩ := weak_recenter_ctxLevel_slot D (family Y.1.1) (ρ • Y.1.2)
  unfold weakTransferCenteredJoint
  rw [hc, hp, hm, hs, hscale]
  exact centeredGeometryChart_recenter_scale D (family Y.1.1) (hfamily _) ρ θ _ _ _

theorem independent_moving_transfer_inverse_copy
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : P → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot)
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (Y : ((P × Vec 2) × Vec 2) × Vec 2) :
    let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
    (childTransition D slot t (C.recenter D (D.eps m • Y.2))
      (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ =
      (jacMatrix (fun x => independentCenteredTransfer
        (independentMovingCenteredChart (fun Z : P × Vec 2 =>
          centeredGeometryChart ((family Z.1).geom D) ρ
            (D.slotAnchor (m + 1) slot) Z.2) θ)
        D m pslot (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x)) Y.2)⁻¹ := by
  dsimp only
  obtain ⟨hc, _, hw⟩ := weak_recenter_ctxLevel_slot D (family Y.1.1.1) (ρ • Y.1.1.2)
  have hcm : ((family Y.1.1.1).recenter D (ρ • Y.1.1.2)).ctxLevel = m := hc.trans (hm _)
  conv_lhs => rw [← hcm]
  rw [weak_transfer_matrix_inverse_eq_centered_slow_jacobian_inverse
    D hΛ hζ _ (hw.mpr (hfamily _)) slot t (Y.1.2, Y.2)]
  have he : (fun x => weakTransferCenteredJoint D
      ((family Y.1.1.1).recenter D (ρ • Y.1.1.2)) slot t (Y.1.2, x)) =
      fun x => independentCenteredTransfer
        (independentMovingCenteredChart (fun Z : P × Vec 2 =>
          centeredGeometryChart ((family Z.1).geom D) ρ
            (D.slotAnchor (m + 1) slot) Z.2) θ)
        D m pslot (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x) := by
    funext x
    exact independent_moving_centered_transfer_copy D family hfamily m pslot hm hs
      ρ θ hscale slot t (Y.1.1, Y.1.2, x)
  rw [he]

theorem independent_moving_transfer_slow_jacobian_det_one
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : P → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (Y : ((P × Vec 2) × Vec 2) × Vec 2) :
    (jacMatrix (fun x => independentCenteredTransfer
      (independentMovingCenteredChart (fun Z : P × Vec 2 => centeredGeometryChart
        ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2) θ)
      D m pslot (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x)) Y.2).det = 1 := by
  let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
  obtain ⟨_hc, hslot, hw⟩ := weak_recenter_ctxLevel_slot D (family Y.1.1.1) (ρ • Y.1.1.2)
  have hcp : Odd C.slot := by
    change Odd ((family Y.1.1.1).recenter D (ρ • Y.1.1.2)).slot
    rw [hslot, hs]
    exact hp
  have hca : GeomAreaPreserving (C.geom D) := by
    change GeomAreaPreserving (((family Y.1.1.1).recenter D (ρ • Y.1.1.2)).geom D)
    rw [geom_recenter D _ (hfamily _) _]
    exact harea _
  have hd := weak_transfer_centered_slow_jacobian_det_one D hΛ hζ C
    (hw.mpr (hfamily _)) hcp hca slot t (Y.1.2, Y.2)
  have heq : (fun x => weakTransferCenteredJoint D C slot t (Y.1.2, x)) =
      fun x => independentCenteredTransfer
        (independentMovingCenteredChart (fun Z : P × Vec 2 => centeredGeometryChart
          ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2) θ)
        D m pslot (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x) := by
    funext x
    exact independent_moving_centered_transfer_copy D family hfamily m pslot hm hs
      ρ θ hscale slot t (Y.1.1, Y.1.2, x)
  rw [heq] at hd
  exact hd

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual transition inverse is jointly smooth in stored centers, phases and both slow scales. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_moving_transfer_entry_contDiff
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : P → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hscale : D.eps m = ρ * θ) (slot : ℤ) (t : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => centeredGeometryChart
      ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : ((P × Vec 2) × Vec 2) × Vec 2 =>
      let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
      (childTransition D slot t (C.recenter D (D.eps m • Y.2))
        (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ i j) := by
  let f := fun Z : P × Vec 2 => centeredGeometryChart ((family Z.1).geom D) ρ
    (D.slotAnchor (m + 1) slot) Z.2
  have he : (fun Y : ((P × Vec 2) × Vec 2) × Vec 2 =>
      let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
      (childTransition D slot t (C.recenter D (D.eps m • Y.2))
        (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ i j) =
      fun Y => (jacMatrix (fun x => independentCenteredTransfer
        (independentMovingCenteredChart f θ) D m pslot
        (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x)) Y.2)⁻¹ i j := by
    funext Y
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j)
      (independent_moving_transfer_inverse_copy D hΛ hζ family hfamily m pslot hm hs
        ρ θ hscale slot t Y)
  rw [he]
  exact independent_centered_transfer_inverse_entry_contDiff (independentMovingCenteredChart f θ)
    (independentMovingCenteredChart_contDiff f hf θ) D m pslot
    (D.slotAnchor (m + 1) slot) t
    (independent_moving_transfer_slow_jacobian_det_one D hΛ hζ family hfamily
      m pslot hm hs hp harea ρ θ hscale slot t) i j

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine native chart reserves produce moving-center inverse transition jets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_moving_transfer_entry_jet_production
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (family : P → RealChain) (hfamily : ∀ p, (family p).WellSlotted)
    (m : ℕ) (pslot : ℤ) (hm : ∀ p, (family p).ctxLevel = m)
    (hs : ∀ p, (family p).slot = pslot) (hp : Odd pslot)
    (harea : ∀ p, GeomAreaPreserving ((family p).geom D))
    (ρ θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hscale : D.eps m = ρ * θ)
    (slot : ℤ) (t : ℝ)
    (hsmall : |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 =>
      centeredGeometryChart ((family Z.1).geom D) ρ (D.slotAnchor (m + 1) slot) Z.2))
    (K n : ℕ) (hn : n ≤ K) (B R S : ℝ) (hB : 0 ≤ B)
    (X : ((P × Vec 2) × Vec 2) × Vec 2)
    (hX : ‖X.1.1.2‖ ≤ R) (hS : ‖X.2‖ ≤ S)
    (hb : ∀ a, 1 ≤ a → a ≤ K + 2 → ∀ Z : Vec 2,
      ‖Z‖ ≤ R + (S + 2 * Real.pi) →
        ‖iteratedFDeriv ℝ a (fun Y : P × Vec 2 => centeredGeometryChart
          ((family Y.1).geom D) ρ (D.slotAnchor (m + 1) slot) Y.2) (X.1.1.1, Z)‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Y : ((P × Vec 2) × Vec 2) × Vec 2 =>
      let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
      (childTransition D slot t (C.recenter D (D.eps m • Y.2))
        (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ i j) X‖ ≤
      independentMovingTransferJetCost K B S := by
  let f := fun Z : P × Vec 2 => centeredGeometryChart ((family Z.1).geom D) ρ
    (D.slotAnchor (m + 1) slot) Z.2
  have he : (fun Y : ((P × Vec 2) × Vec 2) × Vec 2 =>
      let C := (family Y.1.1.1).recenter D (ρ • Y.1.1.2)
      (childTransition D slot t (C.recenter D (D.eps m • Y.2))
        (Y.1.2 + (D.eps m)⁻¹ • (D.eps m • Y.2)))⁻¹ i j) =
      fun Y => (jacMatrix (fun x => independentCenteredTransfer
        (independentMovingCenteredChart f θ) D m pslot
        (D.slotAnchor (m + 1) slot) t (Y.1.1, Y.1.2, x)) Y.2)⁻¹ i j := by
    funext Y
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j)
      (independent_moving_transfer_inverse_copy D hΛ hζ family hfamily m pslot hm hs
        ρ θ hscale slot t Y)
  rw [he]
  apply independent_moving_transfer_inverse_jacobian_jets f hf θ hθ hθ₁ D hΛ hζ
    m pslot hp (D.slotAnchor (m + 1) slot) t hsmall K n hn B R S hB _ X hX hS hb i j
  exact independent_moving_transfer_slow_jacobian_det_one D hΛ hζ family hfamily
    m pslot hm hs hp harea ρ θ hscale slot t

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine mixed primitive reserves and source support uniformly produce the fast carriers of every inverse word. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {d H : ℕ}

theorem coordinate_word_uniform_higher_carrier_exists {a b : ℝ} (hab : a < b)
    (N : ℕ) (hN : N ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (P : Vec d → MolecularData)
    (hP : ∀ Y, dataCoefficients (P Y) = ⟨(fun t _ => G t Y), (P Y).v, 0, 0⟩)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hPv : ∀ Y, (P Y).v = v)
    (V : ∀ Y K, K ≤ H → MolecularFiniteDriftBudget (P Y) K)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hf : ∀ t, t ≤ a → ∀ z Y, f t z Y = 0)
    (hF : ∀ t, t ≤ a → ∀ z Y, F t z Y = 0)
    (w : List (Fin d)) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (c w Y) t := by
  have hc Y u (hu : u.length ≤ N) := hsol Y u hu
  have hc' Y u (hu : u.length ≤ N) : IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f u Y t))
      (coordinateSourceWord F u Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) u) (c u Y) := by
    have hh := hc Y u hu
    rw [hP Y, hPv Y] at hh
    exact hh
  have hz := coordinate_word_inverse_past_zero N QG hv c hc' a hf hF
  let Ns := fun (u : List (Fin d)) (K : ℕ) => ∑ j : JetIndex2 K, 2 * Qf.budget (u.length + j.1.val)
  let Nf := fun (u : List (Fin d)) (K : ℕ) => ∑ j : JetIndex2 K, QF.budget (u.length + j.1.val)
  apply uniform_word_higher_carrier_of_initial_zero hab N H P
    (fun Y u t => independentMetricWordJet G u.length (coordinateWordDirections u) Y t)
    (fun Y u t => cellQ0 (coordinateSourceWord f u Y t))
    (fun Y u => coordinateSourceWord F u Y) (fun Y u => c u Y) V
    (fun Y u _ K hK => coordinateWordHigherSourceData Qf QF u K hK a b Y) Ns Nf
    (fun u K => Finset.sum_nonneg (fun j _ => mul_nonneg (by norm_num) (Qf.budget_nonneg _)))
    (fun u K => Finset.sum_nonneg (fun j _ => QF.budget_nonneg _))
    (fun Y u _ K hK => by rw [coordinateWordHigherSourceData_scalar_budget])
    (fun Y u _ K hK => by rw [coordinateWordHigherSourceData_flux_budget])
    (fun u => QG.budget u.length) (fun u _ => QG.budget_nonneg _)
    (fun Y u hu t i j => QG.word_entry_bound u.length (hu.trans hN) _ (coordinateWordDirections_norm u) Y t i j)
    (fun Y u _ i j => QG.word_entry_measurable u.length _ Y i j)
    (fun Y u hu => hc Y u hu) (fun Y u hu => hz Y u hu a le_rfl) w hw K hK

end AVRegularity.EntryWeakProofs
end
end

section
/-! Common primitive budgets produce higher inverse-word prices before every actual family datum. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {A : Type*} {d H : ℕ}

theorem family_variable_window_coordinate_word_uniform_higher_carrier_exists {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N : ℕ) (hN : N ≤ H)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : A → ℝ → Vec 2 → Vec d → ℂ}
    {F : A → ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qf : ∀ x, IndependentParameterSourceReserve H (f x))
    (QF : ∀ x, IndependentParameterSourceReserve H (F x))
    (BG Bs Bf : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n) (hBf : ∀ n, 0 ≤ Bf n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (hQf : ∀ x n, n ≤ H → (Qf x).budget n ≤ Bs n)
    (hQF : ∀ x n, n ≤ H → (QF x).budget n ≤ Bf n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (c : A → List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ x Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (coordinateSourceWord (f x) w Y t))
      (coordinateSourceWord (F x) w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) w) (c x w Y))
    (hf : ∀ x t, t ≤ a x → ∀ z Y, f x t z Y = 0)
    (hF : ∀ x t, t ≤ a x → ∀ z Y, F x t z Y = 0)
    (w : List (Fin d)) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x Y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧ ∀ t ∈ Icc (a x) (b x),
        torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c x w Y) t := by
  have hc x Y p (hp : p.length ≤ N) : IsCellInverseValue ⟨(fun t _ => G x t Y), v x, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord (f x) p Y t))
      (coordinateSourceWord (F x) p Y + independentWordMetricFlux
        (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) p) (c x p Y) := by
    have hh := hsol x Y p hp
    rw [hP x Y, hPv x Y] at hh
    exact hh
  have hz x := coordinate_word_inverse_past_zero N (QG x) (hv x) (c x) (hc x) (a x) (hf x) (hF x)
  let Ns := fun (p : List (Fin d)) (r : ℕ) => ∑ j : JetIndex2 r, 2 * Bs (p.length + j.1.val)
  let Nf := fun (p : List (Fin d)) (r : ℕ) => ∑ j : JetIndex2 r, Bf (p.length + j.1.val)
  have hpriceS (y : A × Vec d) (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hr : r + p.length ≤ H) :
      (coordinateWordHigherSourceData (Qf y.1) (QF y.1) p r hr (a y.1) (b y.1) y.2).Ns ≤ Ns p r := by
    rw [coordinateWordHigherSourceData_scalar_budget]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hQf y.1 _ (by have := j.1.isLt; omega)) (by norm_num)
  have hpriceF (y : A × Vec d) (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hr : r + p.length ≤ H) :
      (coordinateWordHigherSourceData (Qf y.1) (QF y.1) p r hr (a y.1) (b y.1) y.2).Nf ≤ Nf p r := by
    rw [coordinateWordHigherSourceData_flux_budget]
    apply Finset.sum_le_sum
    intro j _
    exact hQF y.1 _ (by have := j.1.isLt; omega)
  obtain ⟨R, hR, hh⟩ := uniform_word_higher_carrier_variable_window_of_initial_zero (fun y : A × Vec d => a y.1)
    (fun y => b y.1) (fun y => hab y.1) N H
    (fun y : A × Vec d => P y.1 y.2)
    (fun y p t => independentMetricWordJet (G y.1) p.length (coordinateWordDirections p) y.2 t)
    (fun y p t => cellQ0 (coordinateSourceWord (f y.1) p y.2 t))
    (fun y p => coordinateSourceWord (F y.1) p y.2) (fun y p => c y.1 p y.2)
    (fun y r hr => V y.1 y.2 r hr)
    (fun y p _ r hr => coordinateWordHigherSourceData (Qf y.1) (QF y.1) p r hr (a y.1) (b y.1) y.2) Ns Nf
    (fun p r => Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num) (hBs _))
    (fun p r => Finset.sum_nonneg fun j _ => hBf _) hpriceS hpriceF
    (fun p => BG p.length) (fun p _ => hBG _)
    (fun y p hp t i j => ((QG y.1).word_entry_bound p.length (hp.trans hN) _
      (coordinateWordDirections_norm p) y.2 t i j).trans (hQG y.1 _ (hp.trans hN)))
    (fun y p _ i j => (QG y.1).word_entry_measurable p.length _ y.2 i j)
    (fun y p hp => hsol y.1 y.2 p hp) (fun y p hp => hz y.1 y.2 p hp (a y.1) le_rfl) w hw K hK
  exact ⟨R, hR, fun x Y => hh (x, Y)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Select genuine word carriers with prices before all family data and parameter points. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {A : Type*} {d H : ℕ}

theorem family_variable_window_coordinate_word_uniform_carrier_family_exists {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N : ℕ) (hN : N ≤ H)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : A → ℝ → Vec 2 → Vec d → ℂ}
    {F : A → ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qf : ∀ x, IndependentParameterSourceReserve H (f x))
    (QF : ∀ x, IndependentParameterSourceReserve H (F x))
    (BG Bs Bf : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n) (hBs : ∀ n, 0 ≤ Bs n) (hBf : ∀ n, 0 ≤ Bf n)
    (hQG : ∀ x n, n ≤ H → (QG x).budget n ≤ BG n)
    (hQf : ∀ x n, n ≤ H → (Qf x).budget n ≤ Bs n)
    (hQF : ∀ x n, n ≤ H → (QF x).budget n ≤ Bf n)
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x))
    (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y K, K ≤ H → MolecularFiniteDriftBudget (P x Y) K)
    (c : A → List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ x Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (coordinateSourceWord (f x) w Y t))
      (coordinateSourceWord (F x) w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) w) (c x w Y))
    (hf : ∀ x t, t ≤ a x → ∀ z Y, f x t z Y = 0)
    (hF : ∀ x t, t ≤ a x → ∀ z Y, F x t z Y = 0)
    (K : ℕ) (hK : K + N ≤ H) :
    ∃ (u : A → List (Fin d) → Vec d → ℝ → TorusHk K ℂ) (R : List (Fin d) → ℝ),
      ∀ w, w.length ≤ N → 0 ≤ R w ∧ ∀ x Y,
        StronglyMeasurable (u x w Y) ∧ (∀ t, ‖u x w Y t‖ ≤ R w) ∧ ∀ t ∈ Icc (a x) (b x),
          torusHkValueCLM (u x w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c x w Y) t := by
  let W := {w : List (Fin d) // w.length ≤ N}
  have hp (w : W) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x Y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧ ∀ t ∈ Icc (a x) (b x),
        torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c x w.val Y) t :=
    family_variable_window_coordinate_word_uniform_higher_carrier_exists hab N hN QG Qf QF BG Bs Bf hBG hBs hBf
      hQG hQf hQF P hP v hv hPv V c hsol hf hF w.val w.property K (by have := w.property; omega)
  choose R hR uu huu using hp
  let index : List (Fin d) → W := fun w => if h : w.length ≤ N then ⟨w, h⟩ else ⟨[], by simp⟩
  refine ⟨fun x w => uu (index w) x, fun w => R (index w), ?_⟩
  intro w hw
  have hi : (index w).val = w := by simp only [index, dite_eq_left hw]
  refine ⟨hR (index w), ?_⟩
  intro x Y
  have hh := huu (index w) x Y
  rw [hi] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal fresh forward chart inherits its full mixed reserve from the earlier chart disk. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshForward_mixed_step {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ)
    (ρ θ ell u : ℝ) (hρ : 0 < ρ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hell : |ell| ≤ 1)
    (he : D.eps (A.ctxLevel + r) ≠ 0) (hscale : D.eps (A.ctxLevel + r) = ρ * θ)
    (hbirth : birthLength (Fin.last r) = ρ * ell)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (B S : ℝ) (hB : 1 ≤ B)
    (Y : Vec (4 * (r + 1)) × Vec 2) (hY : independentFreshCenterStrip Y.1)
    (hS : ‖Y.2‖ ≤ S) :
    let parent := fun P => independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    let p := independentFreshPrefixProjection r Y.1
    let slot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
    let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
    Odd slot → |u - anchor| * ocA D.α D.q D.Λ (A.ctxLevel + r) ≤ 1 →
    (∀ x, ‖fderiv ℝ (fun y => ((parent p).geom D).1 anchor y ((parent p).geom D).2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) →
    (∀ x, ‖fderiv ℝ (fun y => ((parent p).geom D).1 ((parent p).geom D).2.2 y anchor) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) →
    (∀ t ∈ [u, anchor], ∀ inverse : Bool, ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ X : Vec 2,
      ‖X‖ ≤ centeredParentRadius (2 * Real.pi) S →
      ‖iteratedFDeriv ℝ i (fun Z : Vec (4 * r) × Vec 2 =>
        if inverse then centeredGeometryChartInv ((parent Z.1).geom D) ρ t Z.2
        else centeredGeometryChart ((parent Z.1).geom D) ρ t Z.2) (p, X)‖ ≤ B) →
    ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * (r + 1)) × Vec 2 =>
      centeredGeometryChart ((independentFreshChain A slots birthLength Z.1).geom D)
        (D.eps (A.ctxLevel + r)) u Z.2) Y‖ ≤ nativeMixedChartStepCost K B S := by
  dsimp only
  intro hp hsmall hforward hinverse hb
  let parent := fun P => independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) P
  let g := fun P => (parent P).geom D
  let p := independentFreshPrefixProjection r Y.1
  let slot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
  let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
  let Fu := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
  let Fi := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChartInv (g Z.1) ρ anchor Z.2
  let Fa := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart (g Z.1) ρ anchor Z.2
  let F := independentCenteredChildChart D (A.ctxLevel + r) slot u anchor Fu Fi Fa θ
  let L := independentFreshScaledStepCoordinates r ell
  have hFu : ContDiff ℝ (⊤ : ℕ∞) Fu := independentFreshChainChart_joint_smooth D A hA _ _ ρ u
  have hFi : ContDiff ℝ (⊤ : ℕ∞) Fi := independentFreshChainChartInv_joint_smooth D A hA _ _ ρ anchor
  have hFa : ContDiff ℝ (⊤ : ℕ∞) Fa := independentFreshChainChart_joint_smooth D A hA _ _ ρ anchor
  have hF : ContDiff ℝ (n : ℕ∞) F :=
    (independentCenteredChildChart_contDiff D _ slot u anchor Fu Fi Fa hFu hFi hFa θ).of_le (by simp)
  have hfun : (fun Z : Vec (4 * (r + 1)) × Vec 2 =>
      centeredGeometryChart ((independentFreshChain A slots birthLength Z.1).geom D)
        (D.eps (A.ctxLevel + r)) u Z.2) = F ∘ L := by
    funext Z
    exact independentFreshScaledStepChart_eq_model D A hA slots birthLength ρ θ ell u
      hρ.ne' hθ he hscale hbirth Z
  rw [hfun]
  have hslice := finite_affine_derivative_norm_le F n hF L
    (independentFreshScaledStepCoordinates_norm_le r ell hell) 0 Y
  simp only [add_zero] at hslice
  apply hslice.trans
  apply le_trans ?_ (nativeMixedChartStepCost_forward K B S)
  have hc : ‖ell • independentFreshChildProjection (Fin.last r) false Y.1‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hell (independentFreshCenterStrip_last Y.1 hY)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hc' : ‖ell • independentFreshChildProjection (Fin.last r) false Y.1‖ ≤ 1 + 2 * Real.pi :=
    hc.trans (le_add_of_nonneg_right (by positivity))
  apply centered_native_forward_mixed_production D hΛ hζ _ slot hp u anchor hsmall
    g p (geomSpatialSmooth_geom D (parent p)) ρ hρ θ hθ hθ₁ hforward hinverse K n hn hnK B hB
    (ell • independentFreshChildProjection (Fin.last r) false Y.1)
    (independentFreshChildProjection (Fin.last r) true Y.1) Y.2 hc' S hS hFu hFi hFa
  intro f hf i hi hiK X hX
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hb u (by simp) false i hi hiK X hX
  · simpa only [↓reduceIte] using hb anchor (by simp [anchor]) true i hi hiK X hX
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hb anchor (by simp [anchor]) false i hi hiK X hX

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Genuine primitive reserves produce uniform higher carriers of every literal inverse-word quotient. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {d H : ℕ}

theorem coordinate_word_uniform_quotient_carrier_exists {a b : ℝ} (hab : a < b)
    (N L : ℕ) (hH : N + L + 1 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (P : Vec d → MolecularData)
    (hP : ∀ Y, dataCoefficients (P Y) = ⟨(fun t _ => G t Y), (P Y).v, 0, 0⟩)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hPv : ∀ Y, (P Y).v = v)
    (V : ∀ Y K, K ≤ H → MolecularFiniteDriftBudget (P Y) K)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hf : ∀ t, t ≤ a → ∀ z Y, f t z Y = 0)
    (hF : ∀ t, t ≤ a → ∀ z Y, F t z Y = 0)
    (w : List (Fin d)) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ L) (i : Fin d) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (Y : Vec d) (h : ℝ), h ≠ 0 → ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (h⁻¹ • (c w (Y + h • basisVec i) - c w Y)) t := by
  let T := Vec d × NonzeroIncrement
  let Y1 := fun y : T => y.1 + y.2.val • basisVec i
  let G0 := fun y : T => fun p : List (Fin d) =>
    fun t => independentMetricWordJet G p.length (coordinateWordDirections p) y.1 t
  let G1 := fun y : T => fun p : List (Fin d) =>
    fun t => independentMetricWordJet G p.length (coordinateWordDirections p) (Y1 y) t
  let f0 := fun y : T => fun p : List (Fin d) => fun t => cellQ0 (coordinateSourceWord f p y.1 t)
  let f1 := fun y : T => fun p : List (Fin d) => fun t => cellQ0 (coordinateSourceWord f p (Y1 y) t)
  let F0 := fun y : T => fun p : List (Fin d) => coordinateSourceWord F p y.1
  let F1 := fun y : T => fun p : List (Fin d) => coordinateSourceWord F p (Y1 y)
  let D0 := fun y : T => fun p : List (Fin d) => c p y.1
  let D1 := fun y : T => fun p : List (Fin d) => c p (Y1 y)
  have hc Y p (hp : p.length ≤ N) : IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f p Y t))
      (coordinateSourceWord F p Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) p) (c p Y) := by
    have hh := hsol Y p hp
    rw [hP Y, hPv Y] at hh
    exact hh
  have hi := coordinate_word_inverse_past_zero N QG hv c hc a hf hF
  have hnil (Y : Vec d) (t : ℝ) :
      independentMetricWordJet G 0 (coordinateWordDirections []) Y t = G t Y := by
    ext a b
    exact iteratedFDeriv_zero_apply _
  have hP0 (y : T) : dataCoefficients (P y.1) = ⟨fun t _ => G0 y [] t, (P y.1).v, 0, 0⟩ := by
    have he : (fun t (_ : Vec 2) => G0 y [] t) = fun t _ => G t y.1 := by
      funext t z
      exact hnil y.1 t
    rw [he]
    exact hP y.1
  have hD (y : T) (p : List (Fin d)) (hp : p.length ≤ N) :
      IsCellInverseValue (dataCoefficients (P y.1)) (f0 y p)
        (F0 y p + independentWordMetricFlux (fun q t _ => G0 y q t) (D0 y) p) (D0 y p) :=
    hsol y.1 p hp
  have hE (y : T) (p : List (Fin d)) (hp : p.length ≤ N) :
      IsCellInverseValue ⟨fun t _ => G1 y [] t, (P y.1).v, 0, 0⟩ (f1 y p)
        (F1 y p + independentWordMetricFlux (fun q t _ => G1 y q t) (D1 y) p) (D1 y p) := by
    have he : (fun t (_ : Vec 2) => G1 y [] t) = fun t _ => G t (Y1 y) := by
      funext t z
      exact hnil (Y1 y) t
    rw [he, hPv y.1]
    exact hc (Y1 y) p hp
  let Ns := fun (p : List (Fin d)) (r : ℕ) =>
    ∑ j : JetIndex2 r, 2 * (Qf.budget (p.length + (j.1.val + 1)) * ‖basisVec (0 : Fin 2)‖)
  let Nf := fun (p : List (Fin d)) (r : ℕ) =>
    ∑ j : JetIndex2 r, QF.budget (p.length + (j.1.val + 1)) * ‖basisVec (0 : Fin 2)‖
  let Q := fun (y : T) (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hr : r ≤ L) =>
    coordinateWordQuotientHigherSourceData Qf QF p r (by omega) a b y.1 i y.2.val y.2.property
  have hcar (p : List (Fin d)) (hp : p.length ≤ N) (r : ℕ) (hr : r ≤ L + 1) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y : T, ∃ u : ℝ → TorusHk r ℂ,
        StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (D1 y p) t := by
    obtain ⟨R, hR, hh⟩ := coordinate_word_uniform_higher_carrier_exists hab N (by omega)
      QG Qf QF P hP v hv hPv V c hsol hf hF p hp r (by omega)
    exact ⟨R, hR, fun y => hh (Y1 y)⟩
  obtain ⟨R, hR, hq⟩ := uniform_word_difference_higher_carrier_exists hab N L
    (fun y : T => P y.1) G0 G1 hP0 f0 f1 F0 F1 D0 D1 (fun y => y.2.val⁻¹)
    (fun y t => by
      change (independentMetricWordJet G 0 (coordinateWordDirections []) y.1 t).IsSymm
      rw [hnil]
      exact (QG.metric y.1).2.2.1 t 0)
    (fun y t => by
      change (independentMetricWordJet G 0 (coordinateWordDirections []) (Y1 y) t).IsSymm
      rw [hnil]
      exact (QG.metric (Y1 y)).2.2.1 t 0) hD hE
    (fun y r hr => V y.1 r (by omega)) Q Ns Nf
    (fun p r => Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num)
      (mul_nonneg (Qf.budget_nonneg _) (norm_nonneg _)))
    (fun p r => Finset.sum_nonneg fun j _ => mul_nonneg (QF.budget_nonneg _) (norm_nonneg _))
    (fun y p hp r hr => le_refl _) (fun y p hp r hr => le_refl _)
    (fun p => QG.budget p.length) (fun p => QG.budget (p.length + 1) * ‖(basisVec i : Vec d)‖)
    (fun p _ => QG.budget_nonneg _) (fun p _ => mul_nonneg (QG.budget_nonneg _) (norm_nonneg _))
    (fun y p hp t a b => QG.word_entry_bound p.length (by omega) _ (coordinateWordDirections_norm p) y.1 t a b)
    (fun y p _ a b => QG.word_entry_measurable p.length _ y.1 a b)
    (fun y p hp t a b => QG.word_quotient_entry_bound p.length (by omega) _
      (coordinateWordDirections_norm p) y.1 (basisVec i) y.2.val y.2.property t a b)
    (fun y p _ a b => ((QG.word_entry_measurable p.length _ (Y1 y) a b).sub
      (QG.word_entry_measurable p.length _ y.1 a b)).const_mul _)
    hcar (fun y p hp => hi y.1 p hp a le_rfl) (fun y p hp => hi (Y1 y) p hp a le_rfl) w hw K hK
  exact ⟨R, hR, fun Y h hh => hq (Y, ⟨h, hh⟩)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal fresh inverse chart inherits its full mixed reserve from the earlier chart disk. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshInverse_mixed_step {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ)
    (ρ θ ell u : ℝ) (hρ : 0 < ρ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hell : |ell| ≤ 1)
    (he : D.eps (A.ctxLevel + r) ≠ 0) (hscale : D.eps (A.ctxLevel + r) = ρ * θ)
    (hbirth : birthLength (Fin.last r) = ρ * ell)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (B S : ℝ) (hB : 1 ≤ B)
    (Y : Vec (4 * (r + 1)) × Vec 2) (hY : independentFreshCenterStrip Y.1)
    (hS : ‖Y.2‖ ≤ S) :
    let parent := fun P => independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    let p := independentFreshPrefixProjection r Y.1
    let slot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
    let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
    Odd slot → |u - anchor| * ocA D.α D.q D.Λ (A.ctxLevel + r) ≤ 1 →
    (∀ x, ‖fderiv ℝ (fun y => ((parent p).geom D).1 u y ((parent p).geom D).2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) →
    (∀ x, ‖fderiv ℝ (fun y => ((parent p).geom D).1 ((parent p).geom D).2.2 y u) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) →
    (∀ t ∈ [u, anchor], ∀ inverse : Bool, ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ X : Vec 2,
      ‖X‖ ≤ centeredParentRadius (2 * Real.pi) S →
      ‖iteratedFDeriv ℝ i (fun Z : Vec (4 * r) × Vec 2 =>
        if inverse then centeredGeometryChartInv ((parent Z.1).geom D) ρ t Z.2
        else centeredGeometryChart ((parent Z.1).geom D) ρ t Z.2) (p, X)‖ ≤ B) →
    ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * (r + 1)) × Vec 2 =>
      centeredGeometryChartInv ((independentFreshChain A slots birthLength Z.1).geom D)
        (D.eps (A.ctxLevel + r)) u Z.2) Y‖ ≤ nativeMixedChartStepCost K B S := by
  dsimp only
  intro hp hsmall hforward hinverse hb
  let parent := fun P => independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) P
  let g := fun P => (parent P).geom D
  let p := independentFreshPrefixProjection r Y.1
  let slot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
  let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
  let Fu := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart (g Z.1) ρ anchor Z.2
  let Fi := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChartInv (g Z.1) ρ u Z.2
  let Fa := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
  let F := independentCenteredChildInverseModel D (A.ctxLevel + r) slot u anchor Fu Fi Fa θ
  let L := independentFreshScaledStepCoordinates r ell
  have hFu : ContDiff ℝ (⊤ : ℕ∞) Fu := independentFreshChainChart_joint_smooth D A hA _ _ ρ anchor
  have hFi : ContDiff ℝ (⊤ : ℕ∞) Fi := independentFreshChainChartInv_joint_smooth D A hA _ _ ρ u
  have hFa : ContDiff ℝ (⊤ : ℕ∞) Fa := independentFreshChainChart_joint_smooth D A hA _ _ ρ u
  have hF : ContDiff ℝ (n : ℕ∞) F :=
    ((independentCenteredChildChart_contDiff D _ slot anchor u Fu Fi Fa hFu hFi hFa θ).comp
      (independentCenteredChildReanchorInput_contDiff D _ slot u anchor θ)).of_le (by simp)
  have hfun : (fun Z : Vec (4 * (r + 1)) × Vec 2 =>
      centeredGeometryChartInv ((independentFreshChain A slots birthLength Z.1).geom D)
        (D.eps (A.ctxLevel + r)) u Z.2) = F ∘ L := by
    funext Z
    exact independentFreshScaledStepChartInv_eq_model D A hA slots birthLength ρ θ ell u
      hρ.ne' hθ he hscale hbirth Z
  rw [hfun]
  have hslice := finite_affine_derivative_norm_le F n hF L
    (independentFreshScaledStepCoordinates_norm_le r ell hell) 0 Y
  simp only [add_zero] at hslice
  apply hslice.trans
  apply le_trans ?_ (nativeMixedChartStepCost_inverse K B S)
  have hc : ‖ell • independentFreshChildProjection (Fin.last r) false Y.1‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hell (independentFreshCenterStrip_last Y.1 hY)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  apply centered_native_inverse_mixed_production D hΛ hζ _ slot hp u anchor hsmall
    g p (geomSpatialSmooth_geom D (parent p)) ρ hρ θ hθ hθ₁ hforward hinverse K n hn hnK B hB
    (ell • independentFreshChildProjection (Fin.last r) false Y.1)
    (independentFreshChildProjection (Fin.last r) true Y.1) Y.2 hc S hS hFu hFi hFa
  intro f hf i hi hiK X hX
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hb anchor (by simp [anchor]) false i hi hiK X hX
  · simpa only [↓reduceIte] using hb u (by simp) true i hi hiK X hX
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hb u (by simp) false i hi hiK X hX

end AVRegularity.EntryWeakProofs
end
end

section
/-! A native chart reserve quantifies every independent center, phase and spatial mixed derivative. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshNativeChartReserve {r : ℕ} (D : OCData) (A : RealChain)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ)
    (T : Set ℝ) (K : ℕ) (S B : ℝ) : Prop :=
  ∀ u ∈ T, ∀ Y : Vec (4 * r) × Vec 2, independentFreshCenterStrip Y.1 → ‖Y.2‖ ≤ S →
    ∀ inverse : Bool, ∀ n, 1 ≤ n → n ≤ K →
      ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * r) × Vec 2 =>
        if inverse then centeredGeometryChartInv ((independentFreshChain A slots birthLength Z.1).geom D) ρ u Z.2
        else centeredGeometryChart ((independentFreshChain A slots birthLength Z.1).geom D) ρ u Z.2) Y‖ ≤ B

theorem independentFreshNativeChartReserve_mixed_step {r : ℕ}
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ)
    (ρ θ ell : ℝ) (hρ : 0 < ρ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (hell : |ell| ≤ 1)
    (he : D.eps (A.ctxLevel + r) ≠ 0) (hscale : D.eps (A.ctxLevel + r) = ρ * θ)
    (hbirth : birthLength (Fin.last r) = ρ * ell)
    (T U : Set ℝ) (K : ℕ) (B S : ℝ) (hB : 1 ≤ B) :
    let parent := fun P => independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    let slot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
    let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
    Odd slot → T ⊆ U → anchor ∈ U →
    (∀ u ∈ T, |u - anchor| * ocA D.α D.q D.Λ (A.ctxLevel + r) ≤ 1) →
    (∀ P : Vec (4 * r), independentFreshCenterStrip P → ∀ u ∈ U, ∀ x,
      ‖fderiv ℝ (fun y => ((parent P).geom D).1 u y ((parent P).geom D).2.2) x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 ∧
      ‖fderiv ℝ (fun y => ((parent P).geom D).1 ((parent P).geom D).2.2 y u) x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) →
    independentFreshNativeChartReserve D A (fun j => slots j.castSucc) (fun j => birthLength j.castSucc)
      ρ U (K + 1) (centeredParentRadius (2 * Real.pi) S) B →
    independentFreshNativeChartReserve D A slots birthLength (D.eps (A.ctxLevel + r)) T K S
      (nativeMixedChartStepCost K B S) := by
  dsimp only
  intro hp hTU ha hsmall hclose hreserve u hu Y hY hS inverse n hn hnK
  have hpY := independentFreshCenterStrip_prefix Y.1 hY
  have hbound : ∀ t ∈ [u, D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))],
      ∀ inv : Bool, ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ X : Vec 2,
      ‖X‖ ≤ centeredParentRadius (2 * Real.pi) S →
      ‖iteratedFDeriv ℝ i (fun Z : Vec (4 * r) × Vec 2 =>
        if inv then centeredGeometryChartInv ((independentFreshChain A (fun j => slots j.castSucc)
          (fun j => birthLength j.castSucc) Z.1).geom D) ρ t Z.2
        else centeredGeometryChart ((independentFreshChain A (fun j => slots j.castSucc)
          (fun j => birthLength j.castSucc) Z.1).geom D) ρ t Z.2)
        (independentFreshPrefixProjection r Y.1, X)‖ ≤ B := by
    intro t ht inv i hi hiK X hX
    have htU : t ∈ U := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with rfl | rfl
      · exact hTU hu
      · exact ha
    exact hreserve t htU (independentFreshPrefixProjection r Y.1, X) hpY hX inv i hi hiK
  cases inverse with
  | false =>
    exact independentFreshForward_mixed_step D hΛ hζ A hA slots birthLength ρ θ ell u
      hρ hθ hθ₁ hell he hscale hbirth K n hn hnK B S hB Y hY hS hp (hsmall u hu)
      (fun x => (hclose _ hpY _ ha x).1) (fun x => (hclose _ hpY _ ha x).2) hbound
  | true =>
    exact independentFreshInverse_mixed_step D hΛ hζ A hA slots birthLength ρ θ ell u
      hρ hθ hθ₁ hell he hscale hbirth K n hn hnK B S hB Y hY hS hp (hsmall u hu)
      (fun x => (hclose _ hpY u (hTU hu) x).1) (fun x => (hclose _ hpY u (hTU hu) x).2) hbound

end AVRegularity.EntryWeakProofs
end
end

section
/-! The empty-history native mixed reserve follows from the genuine coarse stream flow estimates. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeChartReserve_base (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (A : RealChain) (hm : 1 ≤ A.baseLevel) (slot : ℤ)
    (hchildren : A.children = []) (hslots : A.slots = [slot])
    (slots : Fin 0 → ℤ) (birthLength : Fin 0 → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hρe : ρ ≤ D.eps A.baseLevel) (T : Set ℝ)
    (hT : ∀ u ∈ T, |u - D.slotAnchor (A.baseLevel + 1) slot| ≤
      2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ A.baseLevel)⁻¹)
    (K : ℕ) (S : ℝ) :
    independentFreshNativeChartReserve D A slots birthLength ρ T K S (weakBaseChartJetBudget K) := by
  have hg : ∀ P : Vec 0, (independentFreshChain A slots birthLength P).geom D =
      (D.flowOf A.baseLevel, A.base, D.slotAnchor (A.baseLevel + 1) slot) := by
    intro P
    simp [independentFreshChain, RealChain.geom, hchildren, hslots, OCData.geomAux]
  intro u hu Y _ _ inverse n hn hnK
  have he : (fun Z : Vec 0 × Vec 2 =>
      if inverse then centeredGeometryChartInv ((independentFreshChain A slots birthLength Z.1).geom D) ρ u Z.2
      else centeredGeometryChart ((independentFreshChain A slots birthLength Z.1).geom D) ρ u Z.2) =
      (fun Z : Vec 0 × Vec 2 => if inverse then
        ρ⁻¹ • (D.flowOf A.baseLevel (D.slotAnchor (A.baseLevel + 1) slot)
          (D.flowOf A.baseLevel u A.base (D.slotAnchor (A.baseLevel + 1) slot) + ρ • Z.2) u - A.base)
        else ρ⁻¹ • (D.flowOf A.baseLevel u (A.base + ρ • Z.2)
          (D.slotAnchor (A.baseLevel + 1) slot) -
          D.flowOf A.baseLevel u A.base (D.slotAnchor (A.baseLevel + 1) slot))) := by
    funext Z
    rw [hg]
    rfl
  rw [he]
  cases inverse with
  | false =>
    exact independent_scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      A.baseLevel hm (D.slotAnchor (A.baseLevel + 1) slot) u (hT u hu) ρ hρ hρe
      (D.flowOf A.baseLevel u A.base (D.slotAnchor (A.baseLevel + 1) slot)) A.base K n hn hnK Y
  | true =>
    have ht : |D.slotAnchor (A.baseLevel + 1) slot - u| ≤
        2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ A.baseLevel)⁻¹ := by
      simpa only [abs_sub_comm] using hT u hu
    exact independent_scaled_coarse_flow_derivative_norm D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      A.baseLevel hm u (D.slotAnchor (A.baseLevel + 1) slot) ht ρ hρ hρe A.base
      (D.flowOf A.baseLevel u A.base (D.slotAnchor (A.baseLevel + 1) slot)) K n hn hnK Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite-depth mixed chart production from genuine coarse windows and spatial flow estimates. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeChartReserve_of_primitive_windows (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (A : RealChain) (hA : A.WellSlotted) (hm : 1 ≤ A.baseLevel) (slot : ℤ)
    (hchildren : A.children = []) (hslots : A.slots = [slot])
    (slots : ℕ → ℤ) (birthLength ρ θ ell : ℕ → ℝ) (T : ℕ → Set ℝ) (J : ℕ)
    (hρ : ∀ n ≤ J, 0 < ρ n) (hρe : ρ 0 ≤ D.eps A.baseLevel)
    (hT : ∀ u ∈ T 0, |u - D.slotAnchor (A.baseLevel + 1) slot| ≤
      2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ A.baseLevel)⁻¹)
    (hstep : ∀ n < J,
      θ n ≠ 0 ∧ |θ n| ≤ 1 ∧ |ell n| ≤ 1 ∧ D.eps (A.ctxLevel + n) ≠ 0 ∧
      D.eps (A.ctxLevel + n) = ρ n * θ n ∧ birthLength n = ρ n * ell n ∧
      ρ (n + 1) = D.eps (A.ctxLevel + n))
    (hp : ∀ n < J, Odd ((A.slots ++ List.ofFn (fun j : Fin n => slots j)).getLastD 0))
    (hTU : ∀ n < J, T (n + 1) ⊆ T n)
    (ha : ∀ n < J, D.slotAnchor (A.ctxLevel + n + 1) (slots n) ∈ T n)
    (hsmall : ∀ n < J, ∀ u ∈ T (n + 1),
      |u - D.slotAnchor (A.ctxLevel + n + 1) (slots n)| * ocA D.α D.q D.Λ (A.ctxLevel + n) ≤ 1)
    (hclose : ∀ n < J, ∀ P : Vec (4 * n), independentFreshCenterStrip P →
      ∀ u ∈ T n, ∀ x,
      let g := (independentFreshChain A (fun j : Fin n => slots j) (fun j => birthLength j) P).geom D
      ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 ∧
      ‖fderiv ℝ (fun y => g.1 g.2.2 y u) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) :
    ∀ n ≤ J, ∀ K S, independentFreshNativeChartReserve D A
      (fun j : Fin n => slots j) (fun j => birthLength j) (ρ n) (T n) K S
      (nativeMixedChartBudget K n S) := by
  intro n
  induction n with
  | zero =>
    intro _ K S
    rw [nativeMixedChartBudget]
    exact independentFreshNativeChartReserve_base D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
      A hm slot hchildren hslots _ _ (ρ 0) (hρ 0 (Nat.zero_le J)) hρe (T 0) hT K S
  | succ n ih =>
    intro hn K S
    have hnJ : n < J := by omega
    obtain ⟨hθ, hθ₁, hell, he, hscale, hbirth, hρnext⟩ := hstep n hnJ
    rw [nativeMixedChartBudget, hρnext]
    apply independentFreshNativeChartReserve_mixed_step D
      (le_trans (by norm_num : 1 ≤ (128 : ℕ)) hΛ) hζ A hA
      (fun j : Fin (n + 1) => slots j) (fun j => birthLength j)
      (ρ n) (θ n) (ell n) (hρ n (by omega)) hθ hθ₁ hell he hscale hbirth
      (T (n + 1)) (T n) K _ S (nativeMixedChartBudget_ge_one _ _ _)
      (hp n hnJ) (hTU n hnJ) (ha n hnJ) (hsmall n hnJ) (hclose n hnJ)
    exact ih (by omega) (K + 1) (centeredParentRadius (2 * Real.pi) S)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual recentered metrics inherit full stored-family and slow-coordinate jets from produced centered charts. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem independent_fresh_metric_jet_bound_of_chart_reserve {r : ℕ}
    (D : OCData) (A : RealChain) (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (T : Set ℝ) (K : ℕ) (S B : ℝ) (hB : 0 ≤ B)
    (harea : ∀ P, GeomAreaPreserving ((independentFreshChain A slots birthLength P).geom D))
    (hreserve : independentFreshNativeChartReserve D A slots birthLength ρ T (K + 1) S B)
    (u : ℝ) (hu : u ∈ T) (Y : Vec (4 * r) × Vec 2)
    (hY : independentFreshCenterStrip Y.1) (hS : ‖Y.2‖ ≤ S) (n : ℕ) (hn : n ≤ K) :
    ‖iteratedFDeriv ℝ n (fun Z : Vec (4 * r) × Vec 2 =>
      ((independentFreshChain A slots birthLength Z.1).recenter D (ρ • Z.2)).famMetric D u) Y‖ ≤
      planarGramJetBudget n B := by
  let family := fun P => independentFreshChain A slots birthLength P
  let F := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((family Z.1).geom D) ρ u Z.2
  let J := fun Z : Vec (4 * r) × Vec 2 => jacMatrix (fun X => F (Z.1, X)) Z.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := independentFreshChainChart_joint_smooth D A hA slots birthLength ρ u
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact independent_parameter_jacobian_entry_contDiff F hF i j
  have hdet : ∀ Z, (J Z).det = 1 := by
    intro Z
    change (jacMatrix (centeredGeometryChart ((family Z.1).geom D) ρ u) Z.2).det = 1
    rw [centeredGeometryChart_jacMatrix _ (geomSpatialSmooth_geom D _) ρ hρ]
    exact harea Z.1 u ((family Z.1).geom D).2.2 (((family Z.1).geom D).2.1 + ρ • Z.2)
  have he : (fun Z : Vec (4 * r) × Vec 2 => ((family Z.1).recenter D (ρ • Z.2)).famMetric D u) =
      fun Z => (J Z)⁻¹ * Matrix.transpose (J Z)⁻¹ := by
    funext Z
    exact centeredGeometryChart_metric_recenter D (family Z.1)
      (independentFreshChain_wellSlotted A hA slots birthLength Z.1) ρ hρ u Z.2
  change ‖iteratedFDeriv ℝ n (fun Z => ((family Z.1).recenter D (ρ • Z.2)).famMetric D u) Y‖ ≤ _
  rw [he]
  apply planar_inverse_gram_derivative_bound J hJ hdet n Y B hB
  intro a ha i j
  apply (independent_parameter_jacobian_entry_jet_bound F hF i j a Y).trans
  exact hreserve u hu Y hY hS false (a + 1) (by omega) (by omega)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full fresh-family phase lattice equivalence preserves the literal native geometry. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem childPhaseLatticeEquivalent_refl (c : ChainChild) : childPhaseLatticeEquivalent c c := by
  refine ⟨rfl, 0, ?_⟩
  have hz : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
    funext i
    change ((0 : ℤ) : ℝ) = 0
    norm_num
  rw [hz, add_zero]

theorem independentFreshChain_geom_eq_of_phase_lattice {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (hp : ∀ p ∈ A.slots ++ List.ofFn slots, Odd p) (P Q : Vec (4 * r))
    (hc : ∀ j, independentFreshChildProjection j false P = independentFreshChildProjection j false Q)
    (hphase : ∀ j, ∃ n : Fin 2 → ℤ,
      independentFreshChildProjection j true P = independentFreshChildProjection j true Q + latticeShift n) :
    (independentFreshChain A slots birthLength P).geom D =
      (independentFreshChain A slots birthLength Q).geom D := by
  apply realChain_geom_eq_of_phase_lattice D hΛ
    (independentFreshChain A slots birthLength P) (independentFreshChain A slots birthLength Q)
    rfl rfl rfl hp
  have hold : List.Forall₂ childPhaseLatticeEquivalent A.children A.children := by
    induction A.children with
    | nil => exact .nil
    | cons c cs ih => exact .cons (childPhaseLatticeEquivalent_refl c) ih
  have hnew : List.Forall₂ childPhaseLatticeEquivalent
      (List.ofFn (fun j : Fin r => independentFreshChild birthLength j P))
      (List.ofFn (fun j : Fin r => independentFreshChild birthLength j Q)) := by
    apply List.forall₂_of_length_eq_of_get (by simp only [List.length_ofFn])
    intro j hj hj'
    have hjr : j < r := by simpa only [List.length_ofFn] using hj
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    refine ⟨?_, hphase ⟨j, hjr⟩⟩
    exact congrArg (fun X : Vec 2 => birthLength ⟨j, hjr⟩ • X) (hc ⟨j, hjr⟩)
  exact List.rel_append hold hnew

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every literal unit-determinant fresh centered metric is smooth in all mixed independent coordinates. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem independent_fresh_centered_metric_contDiff_of_area {r : ℕ}
    (D : OCData) (A : RealChain) (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ)
    (harea : ∀ P, GeomAreaPreserving ((independentFreshChain A slots birthLength P).geom D)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 =>
      ((independentFreshChain A slots birthLength Z.1).recenter D (ρ • Z.2)).famMetric D u) := by
  let family := fun P => independentFreshChain A slots birthLength P
  let F := fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((family Z.1).geom D) ρ u Z.2
  let J := fun Z : Vec (4 * r) × Vec 2 => jacMatrix (fun X => F (Z.1, X)) Z.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := independentFreshChainChart_joint_smooth D A hA slots birthLength ρ u
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact independent_parameter_jacobian_entry_contDiff F hF i j
  have hdet : ∀ Z, (J Z).det = 1 := by
    intro Z
    change (jacMatrix (centeredGeometryChart ((family Z.1).geom D) ρ u) Z.2).det = 1
    rw [centeredGeometryChart_jacMatrix _ (geomSpatialSmooth_geom D _) ρ hρ]
    exact harea Z.1 u ((family Z.1).geom D).2.2 (((family Z.1).geom D).2.1 + ρ • Z.2)
  have he : (fun Z : Vec (4 * r) × Vec 2 => ((family Z.1).recenter D (ρ • Z.2)).famMetric D u) =
      fun Z => (J Z)⁻¹ * Matrix.transpose (J Z)⁻¹ := by
    funext Z
    exact centeredGeometryChart_metric_recenter D (family Z.1)
      (independentFreshChain_wellSlotted A hA slots birthLength Z.1) ρ hρ u Z.2
  change ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * r) × Vec 2 => ((family Z.1).recenter D (ρ • Z.2)).famMetric D u)
  rw [he]
  exact planar_inverse_gram_contDiff J hJ hdet

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual native metric on Vec (2+4r) retains the proved full mixed chart price. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeMetric_jet_bound_of_chart_reserve {r : ℕ}
    (D : OCData) (level : ℕ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (T : Set ℝ) (K : ℕ) (S B : ℝ) (hB : 0 ≤ B)
    (harea : ∀ P, GeomAreaPreserving ((independentFreshChain A slots birthLength P).geom D))
    (hreserve : independentFreshNativeChartReserve D A slots birthLength ρ T (K + 1) S B)
    (t : ℝ) (ht : D.cellScaleSq level * t ∈ T) (Y : Vec (2 + 4 * r))
    (hY : independentFreshCenterStrip (independentStoredParameterProjection (4 * r) Y))
    (hS : ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ S) (n : ℕ) (hn : n ≤ K) :
    ‖iteratedFDeriv ℝ n (independentFreshNativeMetric D level A slots birthLength ρ t) Y‖ ≤
      planarGramJetBudget n B := by
  let F := fun Z : Vec (4 * r) × Vec 2 =>
    ((independentFreshChain A slots birthLength Z.1).recenter D (ρ • Z.2)).famMetric D (D.cellScaleSq level * t)
  let L := independentFreshParameterCoordinates r
  have hF : ContDiff ℝ (n : ℕ∞) F :=
    (independent_fresh_centered_metric_contDiff_of_area D A hA slots birthLength ρ hρ
      (D.cellScaleSq level * t) harea).of_le (by simp)
  have he : independentFreshNativeMetric D level A slots birthLength ρ t = F ∘ L := by
    funext Z
    unfold independentFreshNativeMetric
    rw [independentFreshStoredFamily_eq_chain]
    rfl
  rw [he]
  have hs := finite_affine_derivative_norm_le F n hF L (independentFreshParameterCoordinates_norm_le r) 0 Y
  simp only [add_zero] at hs
  exact hs.trans (independent_fresh_metric_jet_bound_of_chart_reserve D A hA slots birthLength ρ hρ
    T K S B hB harea hreserve (D.cellScaleSq level * t) ht (L Y) hY hS n hn)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Appended sampling respects simultaneous fast and stored-phase lattice shifts. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshInsertCoordinates_phase_equivalent (r : ℕ)
    (P : Vec (4 * r)) (c z : Vec 2) (n : Fin 2 → ℤ) :
    (∀ j, independentFreshChildProjection j false
      (independentFreshInsertCoordinates r (P, c, z + latticeShift n)) =
        independentFreshChildProjection j false (independentFreshInsertCoordinates r (P, c, z))) ∧
    (∀ j, ∃ q : Fin 2 → ℤ, independentFreshChildProjection j true
      (independentFreshInsertCoordinates r (P, c, z + latticeShift n)) =
        independentFreshChildProjection j true (independentFreshInsertCoordinates r (P, c, z)) + latticeShift q) := by
  have hprefix (j : Fin r) (phase : Bool) (w : Vec 2) :
      independentFreshChildProjection j.castSucc phase
        (independentFreshInsertCoordinates r (P, c, w)) = independentFreshChildProjection j phase P := by
    rw [← independentFreshPrefixProjection_component, independentFreshInsertCoordinates_prefix]
  constructor
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [independentFreshInsertCoordinates_last_center]
    · rw [hprefix, hprefix]
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact ⟨n, by simp only [independentFreshInsertCoordinates_last_phase]⟩
    · refine ⟨0, ?_⟩
      rw [hprefix, hprefix]
      have hz : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
        funext i
        change ((0 : ℤ) : ℝ) = 0
        norm_num
      rw [hz, add_zero]

end AVRegularity.EntryWeakProofs
end
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.CycleReference.TestDriftIntegrability
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.Velocity.Port.AppB2FieldBounds
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux
import AVenhance.Infra.Section4.Amnr.SpatialPrimitive
public import AVenhance.Statements.Construction.BarNorm
import AVenhance.Infra.Section5.GradientChain
import AVenhance.Infra.Section5.PulledGradientTransport
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open AVenhance.Infra.Torus
namespace AVRegularity.CycleReference

/-! Measure bridges between the quotient torus and the open unit cell. -/

local instance torusCellBridgeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusCellBridgeHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusCellBridgeProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

 theorem torusRepresentative_measurePreserving :
    MeasurePreserving (unitTorusRepresentative 2) (volume : Measure ChartTorus)
      (volume.restrict unitCube) := by
  have hsub := measurePreserving_subtype_coe (μa := (volume : Measure (Vec 2)))
    (measurableSet_unitCell 2)
  have hmp := hsub.comp (UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin 2 => (0 : ℝ)))
  rw [Measure.restrict_congr_set unitCell_ae_eq_unitCube] at hmp
  exact hmp

 theorem toUnitTorus_cell_measurePreserving :
    MeasurePreserving (toUnitTorus 2) (volume.restrict unitCube) (volume : Measure ChartTorus) := by
  refine ⟨toUnitTorus_continuous.measurable, ?_⟩
  rw [← torusRepresentative_measurePreserving.map_eq,
    Measure.map_map toUnitTorus_continuous.measurable torusRepresentative_measurePreserving.measurable]
  simp only [Function.comp_def, toUnitTorus_unitTorusRepresentative, Measure.map_id']

 theorem cell_memLp_toTorus {E : Type*} [NormedAddCommGroup E] {p : ENNReal}
    {u : Vec 2 → E} (hu : MemLp u p (volume.restrict unitCube)) :
    MemLp (periodicToTorus u) p (volume : Measure ChartTorus) :=
  hu.comp_measurePreserving torusRepresentative_measurePreserving

 theorem cell_eLpNorm_toTorus {E : Type*} [NormedAddCommGroup E] {p : ENNReal}
    {u : Vec 2 → E} (hu : AEStronglyMeasurable u (volume.restrict unitCube)) :
    eLpNorm (periodicToTorus u) p (volume : Measure ChartTorus) =
      eLpNorm u p (volume.restrict unitCube) :=
  eLpNorm_comp_measurePreserving hu torusRepresentative_measurePreserving

 theorem periodicToTorus_chart {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) {u : Vec 2 → E} (hp : IsZ2Periodic u) :
    periodicToTorus (fun x => u (AVRegularity.streamFlow φ hφ t x s)) =
      (periodicToTorus u) ∘ torusChart hφ s t := by
  funext z
  have h := congrFun (fromUnitTorus_periodicToTorus
    ((isZdPeriodic_iff_frozen u).mpr hp))
    (AVRegularity.streamFlow φ hφ t (unitTorusRepresentative 2 z) s)
  exact h.symm

 theorem streamFlow_cell_ae_eq {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {u v : Vec 2 → E}
    (hpu : IsZ2Periodic u) (hpv : IsZ2Periodic v)
    (he : u =ᵐ[volume.restrict unitCube] v) :
    (fun x => u (AVRegularity.streamFlow φ hφ t x s)) =ᵐ[volume.restrict unitCube]
      (fun x => v (AVRegularity.streamFlow φ hφ t x s)) := by
  have h := torusRepresentative_measurePreserving.quasiMeasurePreserving.ae_eq_comp he
  have h' := (torusChart_measurePreserving hφ s t).quasiMeasurePreserving.ae_eq_comp h
  have h'' := toUnitTorus_cell_measurePreserving.quasiMeasurePreserving.ae_eq_comp h'
  filter_upwards [h''] with x hx
  change periodicToTorus u (torusChart hφ s t (toUnitTorus 2 x)) =
    periodicToTorus v (torusChart hφ s t (toUnitTorus 2 x)) at hx
  rw [torusChart_coe] at hx
  have hu := congrFun (fromUnitTorus_periodicToTorus ((isZdPeriodic_iff_frozen u).mpr hpu))
    (AVRegularity.streamFlow φ hφ t x s)
  have hv := congrFun (fromUnitTorus_periodicToTorus ((isZdPeriodic_iff_frozen v).mpr hpv))
    (AVRegularity.streamFlow φ hφ t x s)
  exact hu.symm.trans (hx.trans hv)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! Diagonal coercivity over a renewal block. -/

theorem refFlux_block_diagonal_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (l : ℤ) (i : Fin 2) :
    (ν + (1 - Real.exp (-2)) / 96 * ocHStar α q Λ m ν) * ocTauPP α q Λ m ≤
      ∫ t in (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..
        (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t i i := by
  let τ := ocTau α q Λ m
  let h := ocTauPP α q Λ m
  let A := ((l : ℝ) - 1 / 2) * h
  let B := ((l : ℝ) + 1 / 2) * h
  let c := ocHStar α q Λ m ν * (1 - Real.exp (-2))
  let r : ℤ := if i = 1 then 1 else 3
  have hr : r = 1 ∨ r = 3 := by dsimp [r]; split_ifs <;> simp
  obtain ⟨S, hcard, hS⟩ := complete_cores_exist hΛ l r hr
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hc : 0 ≤ c := by
    apply mul_nonneg (ocHStar_pos hΛ hν).le
    have hx : Real.exp (-2) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith only [hx]
  have hi : IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν t i i) volume A B :=
    refFlux_entry_intervalIntegrable hΛ hζ hν i i A B
  have hAB : A ≤ B := by dsimp [A, B]; linarith only [hh]
  have hint := integral_disjoint_interval_lower S (fun k => (k : ℝ) * τ)
    (fun k => ((k : ℝ) + 1 / 3) * τ) A B c hc
    (fun t => ocRefFlux α q Λ ζ m ν t i i - ν) (hi.sub intervalIntegrable_const) hAB
    (by
      intro k hk
      have hcore := (hS k hk).2
      have h0 : (k : ℝ) * τ ∈ Set.Icc (((k : ℝ) - 1 / 3) * τ)
          (((k : ℝ) + 1 / 3) * τ) := ⟨by linarith only [hτ], by linarith only [hτ]⟩
      have he : ((k : ℝ) + 1 / 3) * τ ∈ Set.Icc (((k : ℝ) - 1 / 3) * τ)
          (((k : ℝ) + 1 / 3) * τ) := ⟨by linarith only [hτ], le_rfl⟩
      exact ⟨(slowEnvelope_one_inside_block hΛ l _ (hcore.2.2 _ h0)).1,
        by linarith only [hτ], (slowEnvelope_one_inside_block hΛ l _ (hcore.2.2 _ he)).2⟩)
    (by
      intro k _ j _ hkj
      apply Set.disjoint_left.mpr
      intro t htk htj
      have hne : (k : ℝ) ≠ (j : ℝ) := by exact_mod_cast hkj
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsep : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show k + 1 ≤ j by exact_mod_cast hlt)
        have hmul := mul_le_mul_of_nonneg_right hsep hτ.le
        linarith only [htk.1, htk.2, htj.1, htj.2, hmul, hτ]
      · have hsep : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by exact_mod_cast hgt)
        have hmul := mul_le_mul_of_nonneg_right hsep hτ.le
        linarith only [htk.1, htk.2, htj.1, htj.2, hmul, hτ])
    (by intro t _; exact sub_nonneg.mpr (refFlux_diagonal_molecular_lower hΛ hζ hν t i))
    (by
      intro k hk t ht
      have hori : (i = 1 ∧ k % 4 = 1) ∨ (i = 0 ∧ k % 4 = 3) := by
        have hm := (hS k hk).1
        fin_cases i <;> simp_all [r]
      have hb := refFlux_diagonal_core_lower hΛ hζ hν l k (hS k hk).2 hrelax t
        ⟨ht.1.le, ht.2⟩ i hori
      dsimp [c]
      linarith only [hb])
  have hsum : (∑ k ∈ S, c * (((k : ℝ) + 1 / 3) * τ - (k : ℝ) * τ)) =
      (S.card : ℝ) * c * τ / 3 := by
    simp_rw [show ∀ k : ℤ, c * (((k : ℝ) + 1 / 3) * τ - (k : ℝ) * τ) = c * τ / 3 from
      fun k => by ring]
    simp
    ring
  rw [hsum, intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  have hlen : B - A = h := by dsimp [A, B]; ring
  rw [hlen] at hint
  have hscale : (ocL α q Λ m : ℝ) ^ 2 * τ = h := by
    dsimp [τ, h]
    rw [ocTau]
    have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
      have hp : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast hp.ne'
    field_simp
  have hcount := mul_le_mul_of_nonneg_right hcard (mul_nonneg hc hτ.le)
  have hgain : c * h / 96 ≤ (S.card : ℝ) * c * τ / 3 := by
    rw [← hscale]
    nlinarith only [hcount]
  change (ν + (1 - Real.exp (-2)) / 96 * ocHStar α q Λ m ν) * h ≤ _
  dsimp [c] at hgain
  simp only [smul_eq_mul] at hint
  linarith only [hint, hgain]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! Scalar extraction of all-order bounds for the Jacobian displacement. -/

theorem jacMatrix_partial_bound {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (n : ℕ) (hn : 1 ≤ n) (w : Fin n → Fin 2) (x : Vec 2) (i a : Fin 2) :
    |iteratedFDeriv ℝ (n + 1) f x
      (Fin.snoc (fun j => basisVec (w j)) (basisVec a)) i| ≤
      B * (n.factorial : ℝ) * R ^ n / ((n : ℝ) + 1) ^ 2 := by
  have hs := jacMatrix_entry_smooth hf i a
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => jacMatrix f y i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) :=
    hs.sub contDiff_const
  have ht := AVenhance.Infra.Section4.amnr_partial_norm_le_of_barNorm _ n
    (hh.of_le (by simp)) hR hB (hb n i a) x w
  have he := iteratedFDeriv_sub_apply (x := x) (hs.of_le (by simp) : ContDiff ℝ n _).contDiffAt
    (contDiff_const : ContDiff ℝ n (fun _ : Vec 2 => (1 : Matrix (Fin 2) (Fin 2) ℝ) i a)).contDiffAt

  change iteratedFDeriv ℝ n (fun y => jacMatrix f y i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) x = _ at he
  rw [he, iteratedFDeriv_const_of_ne (by omega : n ≠ 0)] at ht
  simp only [Pi.zero_apply, sub_zero] at ht
  rw [iteratedFDeriv_jacMatrix_entry hf] at ht
  simpa only [Real.norm_eq_abs] using ht


theorem orderedPartial_component_bound {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (n : ℕ) (hn : 1 ≤ n) (w : AVRegularity.Sobolev.DerivativeWord2 (n + 1))
    (x : Vec 2) (i : Fin 2) :
    |orderedPartial f (n + 1) w x i| ≤
      B * (n.factorial : ℝ) * R ^ n / ((n : ℝ) + 1) ^ 2 := by
  rw [orderedPartial_eq_reversed_iteratedFDeriv hf]
  have ht := jacMatrix_partial_bound hf hR hB hb n hn
    (fun j => w j.castSucc.rev) x i (w (Fin.last n).rev)
  have he : Fin.snoc (fun j : Fin n => basisVec (w j.castSucc.rev))
      (basisVec (w (Fin.last n).rev)) =
      (fun j : Fin (n + 1) => basisVec (w j.rev)) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
  rw [he] at ht
  exact ht

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Topology
open AVenhance.Infra.Torus
namespace AVRegularity.CycleReference

/-! Cell-space-time change of variables for periodic fields. -/

local instance torusChartSpacetimeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusChartSpacetimeHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusChartSpacetimeProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

 theorem torusRepresentative_measurableEmbedding : MeasurableEmbedding (unitTorusRepresentative 2) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_unitCell 2)).comp
    (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))).measurableEmbedding

noncomputable def torusChartTimeHomeomorph {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) : (ℝ × ChartTorus) ≃ₜ (ℝ × ChartTorus) where
  toFun := fun p => (p.1, torusChart hφ s p.1 p.2)
  invFun := fun p => (p.1, torusChart hφ p.1 s p.2)
  left_inv := fun p => Prod.ext rfl (torusChart_inverse hφ s p.1 p.2)
  right_inv := fun p => Prod.ext rfl (torusChart_inverse hφ p.1 s p.2)
  continuous_toFun := continuous_fst.prodMk (torusChart_joint_continuous hφ s)
  continuous_invFun := continuous_fst.prodMk (torusChart_inverse_joint_continuous hφ s)

 theorem torusChartTime_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) :
    MeasurePreserving (torusChartTimeHomeomorph hφ s)
      ((volume.restrict (Set.Ioo a c)).prod (volume : Measure ChartTorus))
      ((volume.restrict (Set.Ioo a c)).prod (volume : Measure ChartTorus)) := by
  exact (MeasurePreserving.id (volume.restrict (Set.Ioo a c))).skew_product
    (g := fun t z => torusChart hφ s t z) (torusChart_joint_continuous hφ s).measurable
    (Filter.Eventually.of_forall (fun t => (torusChart_measurePreserving hφ s t).map_eq))

 theorem cellSlab_measure_eq_prod (a c : ℝ) :
    volume.restrict (Set.Ioo a c ×ˢ unitCube) =
      (volume.restrict (Set.Ioo a c)).prod (volume.restrict unitCube) := by
  rw [Measure.volume_eq_prod ℝ (Vec 2), Measure.prod_restrict]

 theorem torusTimeRepresentative_measurePreserving (a c : ℝ) :
    MeasurePreserving (Prod.map id (unitTorusRepresentative 2))
      ((volume.restrict (Set.Ioo a c)).prod (volume : Measure ChartTorus))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  rw [cellSlab_measure_eq_prod]
  exact (MeasurePreserving.id _).prod torusRepresentative_measurePreserving

 theorem torusTimeRepresentative_measurableEmbedding :
    MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (unitTorusRepresentative 2)) :=
  MeasurableEmbedding.id.prodMap torusRepresentative_measurableEmbedding

 theorem cellSlab_integral_toTorus (a c : ℝ) (u : ℝ × Vec 2 → ℝ) :
    (∫ p : ℝ × ChartTorus, u (p.1, unitTorusRepresentative 2 p.2)
      ∂((volume.restrict (Set.Ioo a c)).prod volume)) =
    ∫ p in Set.Ioo a c ×ˢ unitCube, u p :=
  (torusTimeRepresentative_measurePreserving a c).integral_comp
    torusTimeRepresentative_measurableEmbedding u

 theorem cellSlab_integrable_toTorus (a c : ℝ) (u : ℝ × Vec 2 → ℝ) :
    Integrable (fun p : ℝ × ChartTorus => u (p.1, unitTorusRepresentative 2 p.2))
      ((volume.restrict (Set.Ioo a c)).prod volume) ↔
    Integrable u (volume.restrict (Set.Ioo a c ×ˢ unitCube)) :=
  (torusTimeRepresentative_measurePreserving a c).integrable_comp_emb
    torusTimeRepresentative_measurableEmbedding

 theorem cellSlab_chart_transport {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x))) :
    (Integrable (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ↔
      Integrable u (volume.restrict (Set.Ioo a c ×ˢ unitCube))) ∧
    (∫ p in Set.Ioo a c ×ˢ unitCube, u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) =
      ∫ p in Set.Ioo a c ×ˢ unitCube, u p := by
  let U : ℝ × ChartTorus → ℝ := fun p => u (p.1, unitTorusRepresentative 2 p.2)
  have he : (fun p : ℝ × ChartTorus =>
      u (p.1, AVRegularity.streamFlow φ hφ p.1 (unitTorusRepresentative 2 p.2) s)) =
      U ∘ torusChartTimeHomeomorph hφ s := by
    funext p
    exact congrFun (periodicToTorus_chart hφ s p.1 (hp p.1)) p.2
  have hm := torusChartTime_measurePreserving hφ s a c
  have ht := cellSlab_integrable_toTorus a c
    (fun p => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s))
  rw [he] at ht
  refine ⟨?_, ?_⟩
  · exact ht.symm.trans ((hm.integrable_comp_emb
      (torusChartTimeHomeomorph hφ s).measurableEmbedding).trans
      (cellSlab_integrable_toTorus a c u))
  · rw [← cellSlab_integral_toTorus a c
      (fun p => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)), he]
    simp only [Function.comp_def]
    rw [hm.integral_comp (torusChartTimeHomeomorph hφ s).measurableEmbedding U]
    exact cellSlab_integral_toTorus a c u

 theorem cellSlab_chart_aestronglyMeasurable {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x)))
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  let U : ℝ × ChartTorus → ℝ := fun p => u (p.1, unitTorusRepresentative 2 p.2)
  have hU := hu.comp_measurePreserving (torusTimeRepresentative_measurePreserving a c)
  have hUX := hU.comp_measurePreserving (torusChartTime_measurePreserving hφ s a c)
  have hproj := (MeasurePreserving.id (volume.restrict (Set.Ioo a c))).prod
    toUnitTorus_cell_measurePreserving
  have hback := hUX.comp_measurePreserving hproj
  rw [← cellSlab_measure_eq_prod a c] at hback
  have he : ((U ∘ torusChartTimeHomeomorph hφ s) ∘ Prod.map id (toUnitTorus 2)) =
      (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) := by
    funext p
    change u (p.1, unitTorusRepresentative 2 (torusChart hφ s p.1 (toUnitTorus 2 p.2))) = _
    rw [torusChart_coe]
    exact congrFun (fromUnitTorus_periodicToTorus
      ((isZdPeriodic_iff_frozen _).mpr (hp p.1))) _
  change AEStronglyMeasurable
    ((U ∘ torusChartTimeHomeomorph hφ s) ∘ Prod.map id (toUnitTorus 2))
    (volume.restrict (Set.Ioo a c ×ˢ unitCube)) at hback
  rw [he] at hback
  exact hback

 theorem cellSlab_chart_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x)))
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  apply (memLp_two_iff_integrable_sq
    (cellSlab_chart_aestronglyMeasurable hφ s a c u hp hu.aestronglyMeasurable)).mpr
  have hi := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  exact (cellSlab_chart_transport hφ s a c (fun p => u p ^ 2)
    (fun t k x => congrArg (fun v : ℝ => v ^ 2) (hp t k x))).1.mpr hi

 theorem cellSlab_ae_time (a c : ℝ) {P : ℝ → Prop}
    (hp : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), P t) :
    ∀ᵐ p : ℝ × Vec 2 ∂(volume.restrict (Set.Ioo a c ×ˢ unitCube)), P p.1 := by
  rw [cellSlab_measure_eq_prod]
  exact Measure.quasiMeasurePreserving_fst.ae hp

 theorem cellSlab_chart_transport_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => u (t, x))) :
    (Integrable (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ↔
      Integrable u (volume.restrict (Set.Ioo a c ×ˢ unitCube))) ∧
    (∫ p in Set.Ioo a c ×ˢ unitCube, u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) =
      ∫ p in Set.Ioo a c ×ˢ unitCube, u p := by
  classical
  let U : ℝ × Vec 2 → ℝ := fun p =>
    if IsZ2Periodic (fun x => u (p.1, x)) then u p else 0
  have hper (t : ℝ) : IsZ2Periodic (fun x => U (t, x)) := by
    by_cases h : IsZ2Periodic (fun x => u (t, x))
    · simpa only [U, ite_eq_left h] using h
    · intro k x
      simp only [U, ite_eq_right h]
  have he : U =ᵐ[volume.restrict (Set.Ioo a c ×ˢ unitCube)] u := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  have heX : (fun p : ℝ × Vec 2 => U (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) =ᵐ[
      volume.restrict (Set.Ioo a c ×ˢ unitCube)]
      (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  have ht := cellSlab_chart_transport hφ s a c U hper
  exact ⟨(integrable_congr heX).symm.trans (ht.1.trans (integrable_congr he)),
    (integral_congr_ae heX).symm.trans (ht.2.trans (integral_congr_ae he))⟩

 theorem cellSlab_chart_memL2_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => u (t, x)))
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  classical
  let U : ℝ × Vec 2 → ℝ := fun p =>
    if IsZ2Periodic (fun x => u (p.1, x)) then u p else 0
  have hper (t : ℝ) : IsZ2Periodic (fun x => U (t, x)) := by
    by_cases h : IsZ2Periodic (fun x => u (t, x))
    · simpa only [U, ite_eq_left h] using h
    · intro k x
      simp only [U, ite_eq_right h]
  have he : U =ᵐ[volume.restrict (Set.Ioo a c ×ˢ unitCube)] u := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  have heX : (fun p : ℝ × Vec 2 => U (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) =ᵐ[
      volume.restrict (Set.Ioo a c ×ˢ unitCube)]
      (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)) := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  exact (cellSlab_chart_memL2 hφ s a c U hper (hu.ae_eq he.symm)).ae_eq heX

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Weighted odd-slot squares and their fast periodic primitive. -/

noncomputable def fastWeightedSquare (ζ : ℝ → ℝ) (τ : ℝ)
    (w : {k : ℤ // Odd k} → ℝ) (t : ℝ) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, ζ (t / τ - k.1) ^ 2 * w k

noncomputable def pulseWeightedSquare (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (w : {k : ℤ // Odd k} → ℝ) (t : ℝ) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ^ 2 * w k

theorem fastWeightedSquare_single {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (τ t : ℝ) (w : {k : ℤ // Odd k} → ℝ) (k : {k : ℤ // Odd k})
    (hk : ζ (t / τ - k.1) ≠ 0) :
    fastWeightedSquare ζ τ w t = ζ (t / τ - k.1) ^ 2 * w k := by
  unfold fastWeightedSquare
  apply tsum_eq_single k
  intro j hj
  have hz : ζ (t / τ - j.1) = 0 := by
    by_contra hz
    exact hj (Subtype.ext (odd_fast_support_unique hζ j.2 k.2 hz hk))
  simp [hz]

theorem fastWeightedSquare_range {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (τ t : ℝ) {w : {k : ℤ // Odd k} → ℝ} (hw : ∀ k, w k ∈ Set.Icc 0 1) :
    fastWeightedSquare ζ τ w t ∈ Set.Icc 0 1 := by
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / τ - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    rw [fastWeightedSquare_single hζ τ t w k hk]
    have hz := hζ.2.2.2.1 (t / τ - k.1)
    have hs : ζ (t / τ - k.1) ^ 2 ≤ 1 := by nlinarith only [hz.1, hz.2]
    exact ⟨mul_nonneg (sq_nonneg _) (hw k).1,
      by simpa using mul_le_mul hs (hw k).2 (hw k).1 (by norm_num : (0 : ℝ) ≤ 1)⟩
  · have hz (k : {k : ℤ // Odd k}) : ζ (t / τ - k.1) = 0 := by
      by_contra hk
      exact he ⟨k, hk⟩
    simp [fastWeightedSquare, hz]

theorem fastWeightedSquare_intervalIntegrable {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (τ : ℝ) {w : {k : ℤ // Odd k} → ℝ} (hw : ∀ k, w k ∈ Set.Icc 0 1)
    (a b : ℝ) : IntervalIntegrable (fastWeightedSquare ζ τ w) volume a b := by
  have hm : Measurable (fastWeightedSquare ζ τ w) :=
    Measurable.tsum (fun k => ((hζ.1.continuous.comp (by fun_prop)).pow 2).measurable.mul_const _)
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := (1 : ℝ))
  · exact (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) measure_Icc_lt_top).ne
  · exact hm.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (fastWeightedSquare_range hζ τ t hw).1]
    exact (fastWeightedSquare_range hζ τ t hw).2

theorem fastWeightedSquare_periodic (ζ : ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {w : {k : ℤ // Odd k} → ℝ} (hw : ∀ k, w (oddSlotAddEquiv 4 (by decide) k) = w k) :
    Function.Periodic (fastWeightedSquare ζ τ w) (4 * τ) := by
  intro t
  unfold fastWeightedSquare
  rw [← (oddSlotAddEquiv 4 (by decide)).tsum_eq]
  apply tsum_congr
  intro k
  rw [hw]
  have he : (t + 4 * τ) / τ - ((oddSlotAddEquiv 4 (by decide) k).1 : ℝ) = t / τ - k.1 := by
    dsimp [oddSlotAddEquiv]
    push_cast
    field_simp
    ring
  rw [he]

theorem pulseWeightedSquare_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (w : {k : ℤ // Odd k} → ℝ)
    (k : {k : ℤ // Odd k}) (hk : ζ (t / ocTau α q Λ m - k.1) ≠ 0) :
    pulseWeightedSquare α q Λ m ζ w t = ocPulse α q Λ ζ m k.1 t ^ 2 * w k := by
  unfold pulseWeightedSquare
  apply tsum_eq_single k
  intro j hj
  have hz : ζ (t / ocTau α q Λ m - j.1) = 0 := by
    by_contra hz
    exact hj (Subtype.ext (odd_fast_support_unique hζ j.2 k.2 hz hk))
  rw [ocPulse_eq_scaledProduct hΛ j.1 t, hz]
  simp

theorem weightedSquare_discrepancy {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {w : {k : ℤ // Odd k} → ℝ}
    (hw : ∀ k, w k ∈ Set.Icc 0 1) (t : ℝ) :
    |pulseWeightedSquare α q Λ m ζ w t - fastWeightedSquare ζ (ocTau α q Λ m) w t| ≤
      fastSquareSum ζ (ocTau α q Λ m) t - pulseSquareSum α q Λ ζ m t := by
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    have hp := pulseSquareSum_le_fast (α := α) (q := q) (m := m) hΛ hζ t
    rw [pulseSquareSum_eq_at_fast hΛ hζ t k hk,
      fastSquareSum_eq_at_nonzero hζ _ _ k hk] at hp ⊢
    rw [pulseWeightedSquare_single hΛ hζ t w k hk, fastWeightedSquare_single hζ _ t w k hk,
      ← sub_mul, abs_mul, abs_of_nonneg (hw k).1,
      abs_of_nonpos (sub_nonpos.mpr hp.2)]
    have h := mul_le_mul_of_nonneg_left (hw k).2 (sub_nonneg.mpr hp.2)
    simpa only [neg_sub, mul_one] using h
  · have hz (k : {k : ℤ // Odd k}) : ζ (t / ocTau α q Λ m - k.1) = 0 := by
      by_contra hk
      exact he ⟨k, hk⟩
    have hp (k : {k : ℤ // Odd k}) : ocPulse α q Λ ζ m k.1 t = 0 := by
      rw [ocPulse_eq_scaledProduct hΛ k.1 t, hz k, mul_zero]
    simp [pulseWeightedSquare, fastWeightedSquare, fastSquareSum, pulseSquareSum, hz, hp]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleReference

/-! Elementary comparison between component bounds and Euclidean array norms. -/

theorem finite_euclidean_bound {ι : Type*} [Fintype ι] {v : ι → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    Real.sqrt (∑ i, (v i) ^ 2) ≤ (Fintype.card ι : ℝ) * B := by
  apply (Real.sqrt_le_left (by positivity)).2
  have hs : (∑ i, (v i) ^ 2) ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _ : ι, B ^ 2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v i)) hB).2 (hv i))
      _ = _ := by simp
  have hc : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
    exact_mod_cast (show Fintype.card ι ≤ Fintype.card ι ^ 2 by
      by_cases h : Fintype.card ι = 0
      · simp [h]
      · nlinarith)
  calc
    _ ≤ (Fintype.card ι : ℝ) * B ^ 2 := hs
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring

theorem derivArrayNorm_le_components {f : Vec 2 → Vec 2} {n : ℕ} {x : Vec 2} {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ w : DerivativeWord2 n, ∀ i, |orderedPartial f n w x i| ≤ B) :
    derivArrayNorm f n x ≤ (2 : ℝ) ^ (n + 1) * B := by
  have hs := finite_euclidean_bound hB (fun p : DerivativeWord2 n × Fin 2 => hv p.1 p.2)
  simpa [derivArrayNorm, vecNormSq, vecDot, Fintype.sum_prod_type, DerivativeWord2,
    Fintype.card_fun, pow_succ] using hs

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Integral consequences of lower bounds on consecutive renewal blocks. -/

theorem consecutive_blocks_lower (f : ℝ → ℝ) (h c : ℝ)
    (hi : ∀ a b, IntervalIntegrable f volume a b)
    (hb : ∀ l : ℤ, c * h ≤ ∫ t in (((l : ℝ) - 1 / 2) * h)..(((l : ℝ) + 1 / 2) * h), f t)
    (k : ℤ) (n : ℕ) :
    (n : ℝ) * c * h ≤ ∫ t in (((k : ℝ) - 1 / 2) * h)..
      (((k : ℝ) + n - 1 / 2) * h), f t := by
  let a : ℕ → ℝ := fun j => ((k : ℝ) + j - 1 / 2) * h
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (a := a) (n := n) (fun j _ => hi (a j) (a (j + 1)))
  have hl : ∑ j ∈ Finset.range n, c * h ≤
      ∑ j ∈ Finset.range n, ∫ t in a j..a (j + 1), f t := by
    apply Finset.sum_le_sum
    intro j _
    have he0 : a j = (((k + j : ℤ) : ℝ) - 1 / 2) * h := by
      dsimp [a]
      push_cast
      ring
    have he1 : a (j + 1) = (((k + j : ℤ) : ℝ) + 1 / 2) * h := by
      dsimp [a]
      push_cast
      ring
    rw [he0, he1]
    exact hb (k + j)
  rw [hs] at hl
  simpa [a, mul_assoc] using hl

theorem long_interval_block_lower (f : ℝ → ℝ) (h c : ℝ) (hh : 0 < h) (hc : 0 ≤ c)
    (hi : ∀ a b, IntervalIntegrable f volume a b) (hf : ∀ t, 0 ≤ f t)
    (hb : ∀ l : ℤ, c * h ≤ ∫ t in (((l : ℝ) - 1 / 2) * h)..(((l : ℝ) + 1 / 2) * h), f t)
    (s t : ℝ) (hst : 3 * h ≤ t - s) :
    c / 3 * (t - s) ≤ ∫ r in s..t, f r := by
  let k : ℤ := ⌈s / h + 1 / 2⌉
  let z : ℤ := ⌊t / h + 1 / 2⌋
  have hklo : s / h + 1 / 2 ≤ (k : ℝ) := Int.le_ceil _
  have hkhi : (k : ℝ) < s / h + 1 / 2 + 1 := Int.ceil_lt_add_one _
  have hzlo : t / h + 1 / 2 - 1 < (z : ℝ) := Int.sub_one_lt_floor _
  have hzhi : (z : ℝ) ≤ t / h + 1 / 2 := Int.floor_le _
  have hkloh := mul_le_mul_of_nonneg_right hklo hh.le
  have hkhih := mul_lt_mul_of_pos_right hkhi hh
  have hzloh := mul_lt_mul_of_pos_right hzlo hh
  have hzhih := mul_le_mul_of_nonneg_right hzhi hh.le
  field_simp at hkloh hkhih hzloh hzhih
  have hkz : k ≤ z := by
    have hrmul : (k : ℝ) * h < (z : ℝ) * h := by linarith
    have hr : (k : ℝ) ≤ (z : ℝ) := ((mul_lt_mul_iff_of_pos_right hh).mp hrmul).le
    exact_mod_cast hr
  let n := (z - k).toNat
  have hn : (n : ℝ) = (z : ℝ) - (k : ℝ) := by
    dsimp [n]
    have he : ((z - k).toNat : ℤ) = z - k := Int.toNat_of_nonneg (sub_nonneg.mpr hkz)
    exact_mod_cast he
  have hlo : s ≤ ((k : ℝ) - 1 / 2) * h := by linarith
  have hhi : ((k : ℝ) + n - 1 / 2) * h ≤ t := by rw [hn]; linarith
  have hab : ((k : ℝ) - 1 / 2) * h ≤ ((k : ℝ) + n - 1 / 2) * h := by
    have := mul_nonneg (show 0 ≤ (n : ℝ) by positivity) hh.le
    linarith
  have hlength : (t - s) / 3 ≤ (n : ℝ) * h := by rw [hn]; linarith
  have hmono := intervalIntegral.integral_mono_interval hlo hab hhi
    (Filter.Eventually.of_forall hf) (hi s t)
  have hblocks := consecutive_blocks_lower f h c hi hb k n
  have hgain := mul_le_mul_of_nonneg_left hlength hc
  linarith

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Slow envelopes affect the fast square average only in renewal quiet margins. -/

theorem pulse_time_scale_relations {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    ocTau α q Λ m ≤ ocTauP α q Λ m ∧
      4 * ocTauP α q Λ m ≤ ocTauPP α q Λ m := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hN : 1 ≤ ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos he _)
  have hL : 5 ≤ (ocL α q Λ m : ℝ) := by
    have hn : 5 ≤ ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn
  have hscale : (ocL α q Λ m : ℝ) ^ 2 * ocTau α q Λ m = ocTauPP α q Λ m := by
    rw [ocTau]
    have hne : (ocL α q Λ m : ℝ) ≠ 0 := by linarith
    field_simp
  have hP : ocTauP α q Λ m = (ocL α q Λ m : ℝ) * ocTau α q Λ m := by
    rw [ocTauP, ← hscale]
    field_simp
  rw [hP, ← hscale]
  constructor
  · nlinarith only [hτ, hL]
  · have hs : 4 * (ocL α q Λ m : ℝ) ≤ (ocL α q Λ m : ℝ) ^ 2 := by nlinarith only [hL]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hs hτ.le

theorem pulseSquareSum_eq_fast_on_plateau {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (l : ℤ) (t : ℝ)
    (hlo : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + 2 * ocTauP α q Λ m ≤ t)
    (hhi : t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - 2 * ocTauP α q Λ m) :
    pulseSquareSum α q Λ ζ m t = fastSquareSum ζ (ocTau α q Λ m) t := by
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    have hd := profile_ne_support_interval hζ hk
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have htd1 := (lt_div_iff₀ hτ).mp (show -(2 / 3) <
        (t - (k.1 : ℝ) * ocTau α q Λ m) / ocTau α q Λ m from by
      convert hd.1 using 1; field_simp)
    have htd2 := (div_lt_iff₀ hτ).mp (show
        (t - (k.1 : ℝ) * ocTau α q Λ m) / ocTau α q Λ m < 2 / 3 from by
      convert hd.2 using 1; field_simp)
    have hP := (pulse_time_scale_relations (α := α) (q := q) (m := m) hΛ).1
    have hlabel : ocLabel α q Λ m k.1 = l := by
      apply ocLabel_eq_of_center hΛ l k.1
      · linarith only [hlo, hP, htd2, hτ]
      · linarith only [hhi, hP, htd1, hτ]
    rw [pulseSquareSum_eq_at_fast hΛ hζ t k hk, fastSquareSum_eq_at_nonzero hζ _ _ k hk,
      ocPulse_eq_scaledProduct hΛ k.1 t, hlabel,
      slowEnvelope_eq_one_on_plateau hΛ l t hlo hhi, one_mul]
  · have hq : ∀ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) = 0 := by
      intro k
      by_contra hk
      exact he ⟨k, hk⟩
    rw [pulseSquareSum_eq_zero_of_fast_quiet hΛ t hq]
    simp [fastSquareSum, hq]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleReference

/-! Differentiating the finite spatial and locally finite temporal corrector sums. -/

theorem coordDerivative_sum {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ k ∈ S, Differentiable ℝ (f k)) (i : Fin 2) :
    (fun y => fderiv ℝ (fun z => ∑ k ∈ S, f k z) y (basisVec i)) =
      fun y => ∑ k ∈ S, fderiv ℝ (f k) y (basisVec i) := by
  funext y
  rw [fderiv_fun_sum (fun k hk => hf k hk y)]
  simp

theorem coordDerivative_const_mul (c : ℝ) (f : Vec 2 → ℝ)
    (hf : Differentiable ℝ f) (i : Fin 2) :
    (fun y => fderiv ℝ (fun z => c * f z) y (basisVec i)) =
      fun y => c * fderiv ℝ f y (basisVec i) := by
  funext y
  rw [fderiv_const_mul (hf y)]
  simp

theorem secondDerivative_sum {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ k ∈ S, ContDiff ℝ 2 (f k)) (i : Fin 2) (y : Vec 2) :
    fderiv ℝ (fun z => fderiv ℝ (fun x => ∑ k ∈ S, f k x) z (basisVec i)) y (basisVec i) =
      ∑ k ∈ S, fderiv ℝ (fun z => fderiv ℝ (f k) z (basisVec i)) y (basisVec i) := by
  rw [coordDerivative_sum S f (fun k hk => (hf k hk).differentiable (by norm_num)) i]
  have hdf (k : ι) (hk : k ∈ S) : Differentiable ℝ
      (fun z => fderiv ℝ (f k) z (basisVec i)) := by
    exact ((hf k hk).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) |>.clm_apply (differentiable_const _)
  exact congrFun (coordDerivative_sum S _ hdf i) y

theorem secondDerivative_const_mul (c : ℝ) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ 2 f) (i : Fin 2) (y : Vec 2) :
    fderiv ℝ (fun z => fderiv ℝ (fun x => c * f x) z (basisVec i)) y (basisVec i) =
      c * fderiv ℝ (fun z => fderiv ℝ f z (basisVec i)) y (basisVec i) := by
  rw [coordDerivative_const_mul c f (hf.differentiable (by norm_num)) i]
  have hdf : Differentiable ℝ (fun z => fderiv ℝ f z (basisVec i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.clm_apply (differentiable_const _)
  exact congrFun (coordDerivative_const_mul c _ hdf i) y

theorem refCorrector_laplacian {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, fderiv ℝ
      (fun z => fderiv ℝ (fun x => ocRefCorrector α q Λ ζ m ν t x j)
        z (basisVec i)) y (basisVec i)) =
      -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 * ocRefCorrector α q Λ ζ m ν t y j := by
  classical
  let S := (ocCutoff_support_finite (α := α) (q := q) (Λ := Λ) (m := m)
    hΛ (t := t)).toFinset
  rw [ocRefCorrector_component_sum hΛ ν t j]
  change (∑ i : Fin 2, fderiv ℝ
      (fun z => fderiv ℝ (fun x => ∑ k ∈ S, ocCutoff α q Λ m k.1 t *
        ocPulseCorrector α q Λ ζ m ν k.1 t x j) z (basisVec i)) y (basisVec i)) = _
  have hdiff (k : {k : ℤ // Odd k}) : ContDiff ℝ 2
      (fun x => ocCutoff α q Λ m k.1 t * ocPulseCorrector α q Λ ζ m ν k.1 t x j) :=
    contDiff_const.mul ((pulseCorrector_component_contDiff k.2 ν t j).of_le (by simp))
  simp_rw [secondDerivative_sum S _ (fun k _ => hdiff k)]
  have hterm (k : {k : ℤ // Odd k}) (i : Fin 2) :
      fderiv ℝ (fun z => fderiv ℝ (fun x => ocCutoff α q Λ m k.1 t *
        ocPulseCorrector α q Λ ζ m ν k.1 t x j) z (basisVec i)) y (basisVec i) =
      ocCutoff α q Λ m k.1 t * fderiv ℝ
        (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k.1 t x j)
          z (basisVec i)) y (basisVec i) :=
    secondDerivative_const_mul _ _ ((pulseCorrector_component_contDiff k.2 ν t j).of_le
      (by simp)) i y
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [congrFun (ocRefCorrector_component_sum hΛ ν t j) y]
  change _ = _ * ∑ k ∈ S, _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pulseCorrector_laplacian k.2]
  ring

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Topology
open AVenhance.Infra.Torus
namespace AVRegularity.CycleReference

/-! Inverse chart transport on the periodic time slab. -/

local instance inverseTorusChartSpacetimeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance inverseTorusChartSpacetimeHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance inverseTorusChartSpacetimeProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

 theorem cellSlab_inverseChart_transport {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x))) :
    (Integrable (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ↔
      Integrable u (volume.restrict (Set.Ioo a c ×ˢ unitCube))) ∧
    (∫ p in Set.Ioo a c ×ˢ unitCube, u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) =
      ∫ p in Set.Ioo a c ×ˢ unitCube, u p := by
  let U : ℝ × ChartTorus → ℝ := fun p => u (p.1, unitTorusRepresentative 2 p.2)
  have he : (fun p : ℝ × ChartTorus =>
      u (p.1, AVRegularity.streamFlow φ hφ s (unitTorusRepresentative 2 p.2) p.1)) =
      U ∘ (torusChartTimeHomeomorph hφ s).symm := by
    funext p
    exact congrFun (periodicToTorus_chart hφ p.1 s (hp p.1)) p.2
  have hm : MeasurePreserving (torusChartTimeHomeomorph hφ s).symm
      ((volume.restrict (Set.Ioo a c)).prod (volume : Measure ChartTorus))
      ((volume.restrict (Set.Ioo a c)).prod volume) :=
    (torusChartTime_measurePreserving hφ s a c).symm
      (torusChartTimeHomeomorph hφ s).toMeasurableEquiv
  have ht := cellSlab_integrable_toTorus a c
    (fun p => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1))
  rw [he] at ht
  refine ⟨?_, ?_⟩
  · exact ht.symm.trans ((hm.integrable_comp_emb
      ((torusChartTimeHomeomorph hφ s).symm).measurableEmbedding).trans
      (cellSlab_integrable_toTorus a c u))
  · rw [← cellSlab_integral_toTorus a c
      (fun p => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)), he]
    simp only [Function.comp_def]
    rw [hm.integral_comp ((torusChartTimeHomeomorph hφ s).symm).measurableEmbedding U]
    exact cellSlab_integral_toTorus a c u

 theorem cellSlab_inverseChart_aestronglyMeasurable {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x)))
    (hu : AEStronglyMeasurable u (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  let U : ℝ × ChartTorus → ℝ := fun p => u (p.1, unitTorusRepresentative 2 p.2)
  have hU := hu.comp_measurePreserving (torusTimeRepresentative_measurePreserving a c)
  have hUX := hU.comp_measurePreserving ((torusChartTime_measurePreserving hφ s a c).symm (torusChartTimeHomeomorph hφ s).toMeasurableEquiv)
  have hproj := (MeasurePreserving.id (volume.restrict (Set.Ioo a c))).prod
    toUnitTorus_cell_measurePreserving
  have hback := hUX.comp_measurePreserving hproj
  rw [← cellSlab_measure_eq_prod a c] at hback
  have he : ((U ∘ (torusChartTimeHomeomorph hφ s).symm) ∘ Prod.map id (toUnitTorus 2)) =
      (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) := by
    funext p
    change u (p.1, unitTorusRepresentative 2 (torusChart hφ p.1 s (toUnitTorus 2 p.2))) = _
    rw [torusChart_coe]
    exact congrFun (fromUnitTorus_periodicToTorus
      ((isZdPeriodic_iff_frozen _).mpr (hp p.1))) _
  change AEStronglyMeasurable
    ((U ∘ (torusChartTimeHomeomorph hφ s).symm) ∘ Prod.map id (toUnitTorus 2))
    (volume.restrict (Set.Ioo a c ×ˢ unitCube)) at hback
  rw [he] at hback
  exact hback

 theorem cellSlab_inverseChart_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => u (t, x)))
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  apply (memLp_two_iff_integrable_sq
    (cellSlab_inverseChart_aestronglyMeasurable hφ s a c u hp hu.aestronglyMeasurable)).mpr
  have hi := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  exact (cellSlab_inverseChart_transport hφ s a c (fun p => u p ^ 2)
    (fun t k x => congrArg (fun v : ℝ => v ^ 2) (hp t k x))).1.mpr hi

 theorem cellSlab_inverseChart_memL2_ae {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (u : ℝ × Vec 2 → ℝ)
    (hp : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsZ2Periodic (fun x => u (t, x)))
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  classical
  let U : ℝ × Vec 2 → ℝ := fun p =>
    if IsZ2Periodic (fun x => u (p.1, x)) then u p else 0
  have hper (t : ℝ) : IsZ2Periodic (fun x => U (t, x)) := by
    by_cases h : IsZ2Periodic (fun x => u (t, x))
    · simpa only [U, ite_eq_left h] using h
    · intro k x
      simp only [U, ite_eq_right h]
  have he : U =ᵐ[volume.restrict (Set.Ioo a c ×ˢ unitCube)] u := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  have heX : (fun p : ℝ × Vec 2 => U (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) =ᵐ[
      volume.restrict (Set.Ioo a c ×ˢ unitCube)]
      (fun p : ℝ × Vec 2 => u (p.1, AVRegularity.streamFlow φ hφ s p.2 p.1)) := by
    filter_upwards [cellSlab_ae_time a c hp] with p hp
    exact ite_eq_left hp
  exact (cellSlab_inverseChart_memL2 hφ s a c U hper (hu.ae_eq he.symm)).ae_eq heX

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! A nonzero switching term can only belong to the outgoing pulse. -/

theorem switching_nonzero_falling {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ) (y : Vec 2)
    (hne : deriv (ocCutoff α q Λ m k) t • ocPulseCorrector α q Λ ζ m ν k t y ≠ 0) :
    ((k : ℝ) + 3 / 4) * ocTau α q Λ m < t ∧
      t < ((k : ℝ) + 5 / 4) * ocTau α q Λ m := by
  have hd : deriv (ocCutoff α q Λ m k) t ≠ 0 := by
    intro hd
    exact hne (by rw [hd, zero_smul])
  have hM : ocPulseMemory α q Λ ζ m ν k t ≠ 0 := by
    intro hM
    apply hne
    simp [ocPulseCorrector, hM]
  have hh := cutoff_derivative_nonzero_distance hΛ k t hd
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hpos : 0 ≤ t - (k : ℝ) * ocTau α q Λ m := by
    by_contra hpos
    have hneg := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at hh
    have ht : t ≤ ((k : ℝ) - 2 / 3) * ocTau α q Λ m := by linarith
    exact hM (pulseMemory_zero_before hΛ hζ ν k t ht)
  rw [abs_of_nonneg hpos] at hh
  constructor <;> linarith

theorem switching_nonzero_unique {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (k j : ℤ)
    (hk : deriv (ocCutoff α q Λ m k) t • ocPulseCorrector α q Λ ζ m ν k t y ≠ 0)
    (hj : deriv (ocCutoff α q Λ m j) t • ocPulseCorrector α q Λ ζ m ν j t y ≠ 0) : k = j := by
  have hkt := switching_nonzero_falling hΛ hζ ν k t y hk
  have hjt := switching_nonzero_falling hΛ hζ ν j t y hj
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hlt : (k : ℝ) < (j : ℝ) + 1 := by
    by_contra h
    have hh : (j : ℝ) + 1 ≤ (k : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hh hτ.le
    nlinarith
  have hgt : (j : ℝ) < (k : ℝ) + 1 := by
    by_contra h
    have hh : (k : ℝ) + 1 ≤ (j : ℝ) := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hh hτ.le
    nlinarith
  have hklt : k < j + 1 := by exact_mod_cast hlt
  have hjlt : j < k + 1 := by exact_mod_cast hgt
  omega

theorem switching_residual_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2)
    (k : {k : ℤ // Odd k})
    (hk : deriv (ocCutoff α q Λ m k.1) t • ocPulseCorrector α q Λ ζ m ν k.1 t y ≠ 0) :
    (∑' j : {j : ℤ // Odd j}, deriv (ocCutoff α q Λ m j.1) t •
      ocPulseCorrector α q Λ ζ m ν j.1 t y) =
      deriv (ocCutoff α q Λ m k.1) t • ocPulseCorrector α q Λ ζ m ν k.1 t y := by
  apply tsum_eq_single k
  intro j hj
  by_contra hne
  exact hj (Subtype.ext (switching_nonzero_unique hΛ hζ ν t y j.1 k.1 hne hk))

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Mean enhancement implied by complete-core coercivity. -/

theorem core_coercivity_constant_range : 0 < (1 - Real.exp (-2)) / 96 ∧
    (1 - Real.exp (-2)) / 96 ≤ 1 := by
  have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hp := Real.exp_pos (-2)
  constructor <;> linarith

theorem refFlux_mean_core_bounds {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) :
    (1 - Real.exp (-2)) / 96 * (ν + ocHStar α q Λ m ν) ≤ ocMeanFlux α q Λ ζ m ν ∧
      ocMeanFlux α q Λ ζ m ν ≤ ν + ocHStar α q Λ m ν := by
  let h := ocTauPP α q Λ m
  let C := ν + (1 - Real.exp (-2)) / 96 * ocHStar α q Λ m ν
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hi : ∀ a b, IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν t 0 0) volume a b :=
    refFlux_entry_intervalIntegrable hΛ hζ hν 0 0
  have hb : ∀ l : ℤ, C * h ≤ ∫ t in (((l : ℝ) - 1 / 2) * h)..
      (((l : ℝ) + 1 / 2) * h), ocRefFlux α q Λ ζ m ν t 0 0 :=
    fun l => refFlux_block_diagonal_lower hΛ hζ hν hrelax l 0
  have hl := consecutive_blocks_lower _ h C hi hb 0 4
  have hm := refFlux_window_mean_entry (α := α) (q := q) (m := m) hΛ hζ hν (-h / 2) (0 : Fin 2) 0
  have hB : ocMeanFlux α q Λ ζ m ν * (4 * h) =
      ∫ t in (-h / 2)..(-h / 2 + 4 * h), ocRefFlux α q Λ ζ m ν t 0 0 := by
    simp only [Matrix.one_apply, ite_true, mul_one] at hm
    change (4 * h)⁻¹ * _ = _ at hm
    exact (eq_div_iff (by positivity : (4 * h) ≠ 0)).mp (by simpa [div_eq_mul_inv, mul_comm] using hm.symm)
  have hlo : C ≤ ocMeanFlux α q Λ ζ m ν := by
    have he1 : ((0 : ℤ) : ℝ) - 1 / 2 = -(1 / 2) := by norm_num
    have he2 : ((0 : ℤ) : ℝ) + (4 : ℕ) - 1 / 2 = 7 / 2 := by norm_num
    rw [he1, he2] at hl
    have hend : (7 / 2 : ℝ) * h = -h / 2 + 4 * h := by ring
    have hstart : (-(1 / 2) : ℝ) * h = -h / 2 := by ring
    rw [hend, hstart, ← hB] at hl
    apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * h by positivity)).mp
    norm_num at hl
    convert hl using 1
    ring
  constructor
  · have hcν := mul_le_mul_of_nonneg_right core_coercivity_constant_range.2 hν.le
    dsimp [C] at hlo
    linarith
  · have hup : (∫ t in (-h / 2)..(-h / 2 + 4 * h), ocRefFlux α q Λ ζ m ν t 0 0) ≤
        (ν + ocHStar α q Λ m ν) * (4 * h) := by
      calc
        _ ≤ ∫ t in (-h / 2)..(-h / 2 + 4 * h), (ν + ocHStar α q Λ m ν) := by
          apply intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const
          intro t _
          have hx := refFlux_entry_norm_le (α := α) (q := q) (m := m) (ν := ν) (t := t) hΛ hζ hν 0 0
          exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hx)
        _ = _ := by simp; ring
    rw [← hB] at hup
    exact (mul_le_mul_iff_of_pos_right (show 0 < 4 * h by positivity)).mp hup

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Chain rules for smooth test functions in a fixed-start chart. -/

theorem spaceGrad_comp_jacMatrix {f : Vec 2 → ℝ} {X : Vec 2 → Vec 2} {y : Vec 2}
    (hf : DifferentiableAt ℝ f (X y)) (hX : DifferentiableAt ℝ X y) :
    spaceGrad (fun x => f (X x)) y = (jacMatrix X y)ᵀ.mulVec (spaceGrad f (X y)) := by
  ext i
  have h := Infra.Section5.spaceGrad_comp_eq_gradMatrix_mul hf.hasFDerivAt hX.hasFDerivAt i
  rw [h]
  change (∑ j, gradMatrix X y i j * spaceGrad f (X y) j) =
    ∑ j, jacMatrix X y j i * spaceGrad f (X y) j
  apply Finset.sum_congr rfl
  intro j _
  rw [Infra.Section5.gradMatrix_entry_eq_fderiv hX i j]
  rfl

theorem fderiv_eq_vecDot_spaceGrad (f : Vec 2 → ℝ) (x v : Vec 2) :
    fderiv ℝ f x v = vecDot (spaceGrad f x) v := by
  have he : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  conv_lhs => rw [he]
  simp [vecDot, spaceGrad, Fin.sum_univ_two, mul_comm]

theorem streamFlow_test_time_chain {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (y : Vec 2)
    {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    deriv (fun r => η r (AVRegularity.streamFlow φ hφ r y s)) t =
      deriv (fun r => η r (AVRegularity.streamFlow φ hφ t y s)) t +
        vecDot (spaceGrad (η t) (AVRegularity.streamFlow φ hφ t y s))
          (streamVel φ t (AVRegularity.streamFlow φ hφ t y s)) := by
  have ho := (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz).2 y s t
  have he := AVRegularity.Velocity.Port.MaterialPullback.constructionMaterialDerivative_eq_deriv_pullback
    (b := streamVel φ) (X := fun r => AVRegularity.streamFlow φ hφ r y s) hη t ho
  rw [← he]
  change deriv (fun r => η r _) t + fderiv ℝ (η t) _ _ = _
  rw [fderiv_eq_vecDot_spaceGrad]

theorem streamFlow_test_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      η p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s)) := by
  exact hη.comp (contDiff_fst.prodMk ((streamFlow_joint_smooth hφ).comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))))

theorem inverseStreamFlow_test_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      η p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1)) := by
  exact hη.comp (contDiff_fst.prodMk ((streamFlow_joint_smooth hφ).comp
    (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))))

theorem streamFlow_test_compact {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    HasCompactSupport (fun p : ℝ × Vec 2 =>
      η p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s)) :=
  hc.comp_homeomorph (streamFlowTimeHomeomorph hφ s)

theorem inverseStreamFlow_test_compact {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {η : ℝ → Vec 2 → ℝ}
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    HasCompactSupport (fun p : ℝ × Vec 2 =>
      η p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1)) :=
  hc.comp_homeomorph (streamFlowTimeHomeomorph hφ s).symm

end AVRegularity.CycleReference
end
end

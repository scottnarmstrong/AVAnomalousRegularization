-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.NativeLiftMetric
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
public import AVRegularity.EntryWeak.ScheduledAnchorDistance
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.EntryWeak.WeakCarrierAppend
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleJoint.TransitionAffineSampling
import AVRegularity.CycleComparison.Lift.TransverseModeFactor
public import AVRegularity.CycleComparison.Lift.NormalizedCellB1MixedGrading
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVenhance.Infra.Heat.SmoothClassical
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Genuine finite real parameter derivatives preserve measurability. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finite_realParameterWordJet_measurable {S : Type*} [MeasurableSpace S]
    (f : S → Vec 2 → E) (n : ℕ) :
    (∀ s, ContDiff ℝ (n : ℕ∞) (f s)) → (∀ Y, Measurable (fun s => f s Y)) →
    ∀ (w : Fin n → Vec 2) (Y : Vec 2),
      Measurable (fun s => realParameterWordJet (f s) n w Y) := by
  induction n with
  | zero =>
      intro _ hm w Y
      simpa only [realParameterWordJet, iteratedFDeriv_zero_apply] using hm Y
  | succ n ih =>
      intro hf hm w Y
      obtain ⟨u, w, rfl⟩ := Fin.exists_cons w
      have hsmall (s : S) : ContDiff ℝ (n : ℕ∞) (f s) :=
        (hf s).of_le (by exact_mod_cast (show n ≤ n + 1 by omega))
      let h : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
      have hseq : Tendsto h atTop (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
        exact Filter.Eventually.of_forall fun k => by
          change h k ≠ 0
          dsimp only [h]
          positivity
      apply measurable_of_tendsto_metrizable
        (f := fun k s => (h k)⁻¹ • (realParameterWordJet (f s) n w (Y + h k • u) -
          realParameterWordJet (f s) n w Y))
      · intro k
        exact (ih hsmall hm w (Y + h k • u)).sub (ih hsmall hm w Y) |>.const_smul _
      · apply tendsto_pi_nhds.mpr
        intro s
        have hL := finite_realParameterWordJet_hasFDerivAt (f s) n (hf s) w Y
        have hline : HasDerivAt (fun a : ℝ => Y + a • u) u 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add Y
        have hd := hL.comp_hasDerivAt_of_eq 0 hline (by simp)
        have ht := hd.tendsto_slope_zero.comp hseq
        simpa only [Function.comp_def, zero_add, zero_smul, add_zero,
          realParameterWordJet_derivative_cons] using ht

theorem finite_realParameterCanonicalJet_measurable {S : Type*} [MeasurableSpace S]
    (f : S → Vec 2 → E) (p : ℕ × ℕ)
    (hf : ∀ s, ContDiff ℝ ((p.1 + p.2 : ℕ) : ℕ∞) (f s))
    (hm : ∀ Y, Measurable (fun s => f s Y)) (Y : Vec 2) :
    Measurable (fun s => realParameterCanonicalJet (f s) p Y) :=
  finite_realParameterWordJet_measurable f _ hf hm _ Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Reuse the joint chronological recursion with a genuine fast-coordinate parameter. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem transitionT_independent_slow_smooth (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun z : P × Vec 2 => K z.1 z.2 i j)) :
    ∀ I A : List (Fin 2), ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × Vec 2 => transitionT (K z.1) I A z.2) := by
  intro I
  induction I with
  | nil =>
    intro A
    cases A <;> exact contDiff_const
  | cons i I ih =>
    intro A
    have hd := Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff
      (fun z : P × Vec 2 => transitionT (K z.1) I A z.2) (ih A)
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : P × Vec 2 =>
        ∑ b : Fin 2, K z.1 z.2 b i *
          fderiv ℝ (transitionT (K z.1) I A) z.2 (basisVec b)) := by
      exact ContDiff.sum (fun b _ => (hK b i).mul (hd.clm_apply contDiff_const))
    cases A with
    | nil => simpa only [transitionT, add_zero] using hs
    | cons a A =>
      simpa only [transitionT] using hs.add ((hK a i).mul (ih A))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Exact frequency products for arbitrary ordered weak derivatives. -/

theorem realJetFourier_word_norm (K : ℕ) (f : TorusHk K ℝ) (n : ℕ) (hn : n ≤ K)
    (w : DerivativeWord2 n) (k : Frequency) :
    ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖ =
      (2 * Real.pi) ^ n * (∏ j : Fin n, |(k (w j) : ℝ)|) *
        ‖realJetFourier K f (valueIndex2 K) k‖ := by
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    simp only [pow_zero, Finset.univ_eq_empty, Finset.prod_empty, mul_one, one_mul]
    rfl
  | succ n ih =>
    have hw : Fin.snoc (Fin.init w) (w (Fin.last n)) = w := Fin.snoc_init_self w
    have he := realJetFourier_append K f (⟨⟨n, by omega⟩, Fin.init w⟩ : JetIndex2 K)
      (w (Fin.last n)) (by change n < K; omega) k
    change realJetFourier K f ⟨⟨n + 1, by omega⟩, Fin.snoc (Fin.init w) (w (Fin.last n))⟩ k = _ at he
    rw [hw] at he
    rw [he, norm_mul, complexFrequencyMultiplier_norm, ih (by omega) (Fin.init w),
      Fin.prod_univ_castSucc, pow_succ]
    simp only [Fin.init]
    ring

theorem frequencyPower_eq_word_sum (n : ℕ) (k : Frequency) :
    (∑ i : Fin 2, |(k i : ℝ)|) ^ n =
      ∑ w : DerivativeWord2 n, ∏ j : Fin n, |(k (w j) : ℝ)| := by
  have hh := Fintype.prod_sum (fun (_ : Fin n) (i : Fin 2) => |(k i : ℝ)|)
  simpa only [Finset.prod_const, Finset.card_fin] using hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Literal pointwise source estimates control the all-time uniformly local norm. -/

theorem weak_unitCube_volume : volume AVenhance.unitCube = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem cell_source_ulNorm_le_pointwise {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : ℝ → Vec 2 → E) (hf : Measurable (Function.uncurry f))
    (C : ℝ) (hb : ∀ t z, ‖f t z‖ ≤ C) :
    cellUlNorm Set.univ f ≤ ENNReal.ofReal C := by
  apply AVRegularity.CycleEvolution.cellUlNorm_le_uniform_cellL2Norm
  intro t
  have hm : Measurable (f t) := hf.comp (measurable_const.prodMk measurable_id)
  have he := eLpNorm_le_of_ae_bound (p := 2)
    (μ := volume.restrict AVenhance.unitCube) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (hb t))
  simpa only [cellL2Norm, Measure.restrict_apply_univ, weak_unitCube_volume,
    ENNReal.one_rpow, one_mul] using he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

/-! Literal geometry of the appended weak family and its common physical output origin. -/

open Providers.GenSem ChainGeometry

theorem weak_appendChild_geom (D : OCData) (ch : RealChain) (hl : ch.WellSlotted)
    (slot : ℤ) (t : ℝ) (z : Vec 2) :
    (ch.appendChild D slot t z).geom D =
      D.childGeom ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) slot)
        ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot
            (D.slotAnchor (ch.ctxLevel + 1) slot) t z,
          z + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) slot) t z⟩
        (ch.geom D) := by
  simpa only [RealChain.appendChild, RealChain.ctxLevel, RealChain.lastLevel, RealChain.slot,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (geom_append_child D ch.baseLevel ch.slots ch.base ch.children hl slot
      ⟨D.eps ch.ctxLevel • D.relDisp ch.ctxLevel ch.slot
          (D.slotAnchor (ch.ctxLevel + 1) slot) t z,
        z + D.relDisp ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) slot) t z⟩)

theorem weak_childGeom_output_origin (D : OCData) (hζ : IsFastProfile D.ζ)
    (g : ChainGeom) (hg : IsFlowGeom g) (m : ℕ) (slot : ℤ) (a t : ℝ) (z : Vec 2) :
    let δ := D.relDisp m slot a t z
    let child := D.childGeom m slot a ⟨D.eps m • δ, z + δ⟩ g
    child.1 t child.2.1 child.2.2 = g.1 t g.2.1 g.2.2 := by
  dsimp only [OCData.childGeom]
  rw [hg.inv]
  have harg : (D.eps m)⁻¹ • (g.2.1 + D.eps m • D.relDisp m slot a t z) +
      (z + D.relDisp m slot a t z -
        (D.eps m)⁻¹ • (g.2.1 + D.eps m • D.relDisp m slot a t z)) =
      z + D.relDisp m slot a t z := by abel
  rw [harg, relDisp_add_relDisp]
  have hzero : D.relDisp m slot a t z + D.relDisp m slot t a z = 0 := by
    rw [relDisp_add D hζ, relDisp_self]
  rw [add_assoc, ← smul_add, hzero, smul_zero, add_zero]

/-- The actual appended family meets its parent at the physical output time. -/
theorem weak_appendChild_output_origin (D : OCData) (hζ : IsFastProfile D.ζ)
    (ch : RealChain) (hl : ch.WellSlotted) (slot : ℤ) (t : ℝ) (z : Vec 2) :
    ((ch.appendChild D slot t z).geom D).1 t ((ch.appendChild D slot t z).geom D).2.1
        ((ch.appendChild D slot t z).geom D).2.2 =
      (ch.geom D).1 t (ch.geom D).2.1 (ch.geom D).2.2 := by
  rw [weak_appendChild_geom D ch hl]
  exact weak_childGeom_output_origin D hζ (ch.geom D) (isFlowGeom_geom D hζ ch)
    ch.ctxLevel ch.slot (D.slotAnchor (ch.ctxLevel + 1) slot) t z

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Literal child charts as normalized differences of the parent chart. -/

theorem childGeom_centered_chart_factorization (D : OCData) (k : ℕ) (slot : ℤ)
    (anchor : ℝ) (g : ChainGeom) (hg : ChainGeometry.InvLaw g) (c : ChainChild)
    (ρ θ : ℝ) (he : D.eps k ≠ 0) (hscale : D.eps k = ρ * θ)
    (C H : Vec 2) (hc : c.center = D.eps k • C) (u : ℝ) :
    let child := D.childGeom k slot anchor c g
    let R := (D.eps k)⁻¹ • childCenterReturn g anchor c (D.eps k • H)
    let B := θ • (C + D.relDisp k slot u anchor c.phase)
    let V := R + D.relDisp k slot u anchor (c.phase + R) -
      D.relDisp k slot u anchor c.phase
    centeredGeometryChart child (D.eps k) u H =
      θ⁻¹ • (centeredGeometryChart g ρ u (B + θ • V) -
        centeredGeometryChart g ρ u B) := by
  dsimp only
  let R := (D.eps k)⁻¹ • childCenterReturn g anchor c (D.eps k • H)
  have hR : childCenterReturn g anchor c (D.eps k • H) = D.eps k • R := by
    dsimp only [R]
    rw [smul_smul, mul_inv_cancel₀ he, one_smul]
  have hanchor : (D.childGeom k slot anchor c g).2.2 = anchor := rfl
  conv_lhs => unfold centeredGeometryChart
  rw [hanchor, childGeom_centered_flow_formula D k slot anchor g hg c u (D.eps k • H)]
  change (D.eps k)⁻¹ •
    (g.1 u (g.2.1 + c.center + childCenterReturn g anchor c (D.eps k • H) +
      D.eps k • D.relDisp k slot u anchor (c.phase + R)) g.2.2 -
     g.1 u (g.2.1 + c.center + D.eps k • D.relDisp k slot u anchor c.phase) g.2.2) =
    θ⁻¹ • (centeredGeometryChart g ρ u
      (θ • (C + D.relDisp k slot u anchor c.phase) +
        θ • (R + D.relDisp k slot u anchor (c.phase + R) -
          D.relDisp k slot u anchor c.phase)) -
      centeredGeometryChart g ρ u (θ • (C + D.relDisp k slot u anchor c.phase)))
  rw [hc, hR]
  have h₀ : g.2.1 + D.eps k • C + D.eps k • D.relDisp k slot u anchor c.phase =
      g.2.1 + ρ • (θ • (C + D.relDisp k slot u anchor c.phase)) := by
    rw [hscale]
    simp only [smul_add, smul_smul]
    abel
  have h₁ : g.2.1 + D.eps k • C + D.eps k • R +
      D.eps k • D.relDisp k slot u anchor (c.phase + R) =
      g.2.1 + ρ • (θ • (C + D.relDisp k slot u anchor c.phase) +
        θ • (R + D.relDisp k slot u anchor (c.phase + R) -
          D.relDisp k slot u anchor c.phase)) := by
    rw [hscale]
    simp only [smul_add, smul_sub, smul_smul]
    abel
  rw [h₀, h₁, hscale]
  exact centeredGeometryChart_scale_difference g ρ θ u _ _

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Filter Topology
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Joint measurability of slow or fast jets, including moving evaluation points. -/

variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace S]

theorem finite_realParameterWordJet_measurable_variable (f : S → Vec 2 → E) (n : ℕ) :
    (∀ s, ContDiff ℝ (n : ℕ∞) (f s)) → Measurable (Function.uncurry f) →
    ∀ (w : Fin n → Vec 2) (Y : S → Vec 2), Measurable Y →
    Measurable (fun s => realParameterWordJet (f s) n w (Y s)) := by
  induction n with
  | zero =>
      intro _ hm w Y hY
      simpa only [realParameterWordJet, iteratedFDeriv_zero_apply, Function.comp_def, Function.uncurry_def, id_eq] using
        hm.comp (measurable_id.prodMk hY)
  | succ n ih =>
      intro hf hm w Y hY
      have hsmall (s : S) : ContDiff ℝ (n : ℕ∞) (f s) :=
        (hf s).of_le (by exact_mod_cast (show n ≤ n + 1 by omega))
      obtain ⟨u, w, rfl⟩ := Fin.exists_cons w
      let h : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
      have hseq : Tendsto h atTop (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
        exact Filter.Eventually.of_forall fun k => by
          change h k ≠ 0
          dsimp only [h]
          positivity
      apply measurable_of_tendsto_metrizable
        (f := fun k s => (h k)⁻¹ • (realParameterWordJet (f s) n w (Y s + h k • u) -
          realParameterWordJet (f s) n w (Y s)))
      · intro k
        exact ((ih hsmall hm w (fun s => Y s + h k • u) (hY.add measurable_const)).sub
          (ih hsmall hm w Y hY)).const_smul _
      · apply tendsto_pi_nhds.mpr
        intro s
        have hL := finite_realParameterWordJet_hasFDerivAt (f s) n (hf s) w (Y s)
        have hline : HasDerivAt (fun a : ℝ => Y s + a • u) u 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (Y s)
        have hd := hL.comp_hasDerivAt_of_eq 0 hline (by simp)
        have ht := hd.tendsto_slope_zero.comp hseq
        simpa only [Function.comp_def, zero_add, zero_smul, add_zero,
          realParameterWordJet_derivative_cons] using ht

theorem finite_realParameterWordJet_measurable_joint (f : S → Vec 2 → E) (n : ℕ)
    (hf : ∀ s, ContDiff ℝ (n : ℕ∞) (f s)) (hm : Measurable (Function.uncurry f))
    (w : Fin n → Vec 2) :
    Measurable (fun a : S × Vec 2 => realParameterWordJet (f a.1) n w a.2) := by
  apply finite_realParameterWordJet_measurable_variable (fun a : S × Vec 2 => f a.1) n
    (fun a => hf a.1) _ w Prod.snd measurable_snd
  exact hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Actual entrywise matrix jets in the time-space metric supremum norm. -/

def matrixParameterJet (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℕ × ℕ) (Y : Vec 2) (t : ℝ) (_z : Vec 2) (i j : Fin 2) : ℝ :=
  realParameterCanonicalJet (fun X => G t X i j) p Y

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Birth-normalized center slices and native wavelength ratios satisfy the scale-step premises. -/

theorem native_weak_chart_scale_step (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (A : RealChain) (hchildren : A.children = []) (n : ℕ) :
    D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n) ≠ 0 ∧
    |D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)| ≤ 1 ∧
    |D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)| ≤ 1 ∧
    D.eps (A.ctxLevel + n) ≠ 0 ∧
    D.eps (A.ctxLevel + n) = D.eps (A.baseLevel + n) *
      (D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)) ∧
    D.eps (A.baseLevel + n + 1) = D.eps (A.baseLevel + n) *
      (D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)) ∧
    D.eps (A.baseLevel + (n + 1)) = D.eps (A.ctxLevel + n) := by
  have hΛ₁ : 1 ≤ D.Λ := le_trans (by norm_num : 1 ≤ (128 : ℕ)) hΛ
  have ha : 0 < D.eps (A.baseLevel + n) := Construction.Stream.ocEpsilon_pos hΛ₁
  have hb : 0 < D.eps (A.baseLevel + n + 1) := Construction.Stream.ocEpsilon_pos hΛ₁
  have he : A.ctxLevel + n = A.baseLevel + n + 1 := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hchildren, List.length_nil]
    omega
  have hr : |D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)| ≤ 1 := by
    rw [abs_of_pos (div_pos hb ha), div_le_one ha]
    exact EntryScales.epsilon_antitone hq hΛ (by omega)
  have hm : D.eps (A.baseLevel + n + 1) = D.eps (A.baseLevel + n) *
      (D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)) := by
    rw [mul_div_cancel₀ _ ha.ne']
  rw [he]
  exact ⟨(div_pos hb ha).ne', hr, hr, hb.ne', hm, hm, by congr 1⟩

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Two extra weak derivatives control the weighted square-summable Fourier array. -/

theorem realJetFourier_weight_bound (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) (k : Frequency) :
    latticeWeight k * ‖realJetFourier K f a k‖ ≤
      ‖realJetFourier K f a k‖ +
      ‖realJetFourier K f (appendJetIndex K a 0 (by omega)) k‖ +
      ‖realJetFourier K f (appendJetIndex K a 1 (by omega)) k‖ +
      ‖realJetFourier K f (appendJetIndex K (appendJetIndex K a 0 (by omega)) 1
        (by dsimp only [appendJetIndex]; omega)) k‖ := by
  let a0 := appendJetIndex K a 0 (by omega)
  let a1 := appendJetIndex K a 1 (by omega)
  have h0 := realJetFourier_append_norm K f a 0 (by omega) k
  have h1 := realJetFourier_append_norm K f a 1 (by omega) k
  have h01 := realJetFourier_append_norm K f a0 1 (by dsimp only [a0, appendJetIndex]; omega) k
  have hm := (mul_le_mul_of_nonneg_left h0 (abs_nonneg (k 1 : ℝ))).trans h01
  dsimp only [latticeWeight]
  nlinarith only [h0, h1, hm]

theorem realJetFourier_weight_memLp (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) :
    Memℓp (fun k : Frequency => latticeWeight k • realJetFourier K f a k) 2 := by
  let a0 := appendJetIndex K a 0 (by omega)
  let a1 := appendJetIndex K a 1 (by omega)
  let a01 := appendJetIndex K a0 1 (by dsimp only [a0, appendJetIndex]; omega)
  have hh := (((realJetFourier K f a).property.norm.add
    (realJetFourier K f a0).property.norm).add (realJetFourier K f a1).property.norm).add
      (realJetFourier K f a01).property.norm
  apply hh.mono
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k)]
  exact realJetFourier_weight_bound K f a ha k

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A scheduled zero child supplies an admissible anchor for the enlarged reference chart. -/

def weakZeroChildAnchor (A : RealChain) (slot : ℤ) : RealChain :=
  {A with slots := A.slots ++ [slot], children := A.children ++ [⟨0, 0⟩]}

theorem weakZeroChildAnchor_admissible (D : OCData) (hΛ : 1 ≤ D.Λ)
    (bw : ℝ) (hbw : 0 < bw) (j₀ i : ℕ) (p slot : ℤ)
    (A : RealChain) (hA : IsAdmissibleChain D bw j₀ i p A)
    (hslot : Odd slot) (hs : IsScheduledIn D i slot p) :
    IsAdmissibleChain D bw j₀ (i + 1) slot (weakZeroChildAnchor A slot) := by
  apply weak_carrier_append_child D bw 2 j₀ i p slot A hA hslot hs ⟨0, 0⟩
  simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero]
  exact mul_pos (by positivity) (Construction.Stream.ocEpsilon_pos hΛ)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization Set
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Window metric estimates supply all-time slow norm jets after time clamping. -/

def clampedParameterMetric {P : Type*} (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (a b : ℝ) (t : ℝ) (Y : P) : Matrix (Fin 2) (Fin 2) ℝ :=
  G (max a (min b t)) Y

theorem metric_clamp_mem (a b : ℝ) (hab : a ≤ b) (t : ℝ) :
    max a (min b t) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The transported array at zero slow displacement retains the full independent parameter regularity. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_transported_coefficient_zero_contDiff
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (Dγ n : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → P → Vec 2)
    (hB : ∀ d I a, ContDiff ℝ (n : ℕ∞) (fun Y => B d I Y a))
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    ContDiff ℝ (n : ℕ∞) (fun Y : P =>
      transportedCoeff (K Y) Dγ (fun d I => B d I Y) r A 0 a) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun Y : P => (Y, (0 : Vec 2))) :=
    contDiff_id.prodMk contDiff_const
  unfold transportedCoeff
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro I _
  apply ContDiff.sum
  intro i _
  exact ((((hK a i).comp hmap).of_le (by simp)).mul (hB d I i)).mul
    (((transitionT_independent_slow_smooth K hK (List.ofFn I) (List.ofFn A)).comp hmap).of_le (by simp))

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Parent-normalized centers use a unit center factor in the mixed chart step. -/

theorem native_weak_coarse_chart_scale_step (D : OCData) (hq : 1 < D.q)
    (hΛ : 128 ≤ D.Λ) (A : RealChain) (hchildren : A.children = []) (n : ℕ) :
    D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n) ≠ 0 ∧
    |D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)| ≤ 1 ∧
    |(1 : ℝ)| ≤ 1 ∧
    D.eps (A.ctxLevel + n) ≠ 0 ∧
    D.eps (A.ctxLevel + n) = D.eps (A.baseLevel + n) *
      (D.eps (A.baseLevel + n + 1) / D.eps (A.baseLevel + n)) ∧
    D.eps (A.baseLevel + n) = D.eps (A.baseLevel + n) * 1 ∧
    D.eps (A.baseLevel + (n + 1)) = D.eps (A.ctxLevel + n) := by
  obtain ⟨hθ, hθ₁, _, hε, he, _, hn⟩ :=
    native_weak_chart_scale_step D hq hΛ A hchildren n
  exact ⟨hθ, hθ₁, by norm_num, hε, he, (mul_one _).symm, hn⟩

end AVRegularity.EntryWeakProofs
end

section
open scoped ENNReal
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Every weak jet with two remaining derivatives has an absolutely summable Fourier array. -/

theorem realJetFourier_norm_summable (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K)
    (ha : a.1.val + 2 ≤ K) : Summable (fun k : Frequency => ‖realJetFourier K f a k‖) := by
  let A : lp (fun _ : Frequency => ℂ) 2 :=
    ⟨fun k => latticeWeight k • realJetFourier K f a k, realJetFourier_weight_memLp K f a ha⟩
  let B : lp (fun _ : Frequency => ℂ) 2 :=
    ⟨fun k => (1 / latticeWeight k : ℂ), latticeReciprocal_memLp⟩
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal :=
    ENNReal.HolderConjugate.toReal (by norm_num)
  have hh := lp.summable_mul hpq A B
  apply hh.congr
  intro k
  change ‖latticeWeight k • realJetFourier K f a k‖ * ‖(1 / latticeWeight k : ℂ)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k), norm_div,
    norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (latticeWeight_pos k)]
  field_simp [ne_of_gt (latticeWeight_pos k)]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The actual weak transfer's coupled slow and fast offsets leave its child flow fixed. -/

theorem weak_recenter_metadata (D : OCData) (A : RealChain) (h : Vec 2) :
    (A.recenter D h).baseLevel = A.baseLevel ∧ (A.recenter D h).slots = A.slots ∧
      (A.recenter D h).children.length = A.children.length := by
  rcases List.eq_nil_or_concat A.children with hc | ⟨cs, c, hc⟩
  · simp [RealChain.recenter, hc]
  · rw [List.concat_eq_append] at hc
    simp [RealChain.recenter, hc]

theorem weak_appendChild_recenter_flow (D : OCData) (A : RealChain) (hl : A.WellSlotted)
    (slot : ℤ) (t : ℝ) (z h : Vec 2) (he : D.eps A.ctxLevel ≠ 0) :
    (((A.recenter D h).appendChild D slot t (z + (D.eps A.ctxLevel)⁻¹ • h)).geom D).1 =
      ((A.appendChild D slot t z).geom D).1 := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  have hl' : (A.recenter D h).WellSlotted := by
    change (A.recenter D h).slots.length = (A.recenter D h).children.length + 1
    rw [hs, hc]
    exact hl
  have hctx : (A.recenter D h).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have hslot : (A.recenter D h).slot = A.slot := by simp only [RealChain.slot, hs]
  rw [weak_appendChild_geom D (A.recenter D h) hl', hctx, hslot,
    geom_recenter D A hl h, weak_appendChild_geom D A hl]
  exact weak_childGeom_phase_shift_flow D A.ctxLevel A.slot
    (D.slotAnchor (A.ctxLevel + 1) slot) t (A.geom D) z h he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs

/-! Window ellipticity is preserved by the all-time constant-in-fast-space metric extension. -/

variable {P : Type*}

theorem clampedParameterMetric_isCellMetric
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) (hab : a ≤ b)
    (hm : ∀ X i j, Measurable (fun t => G t X i j))
    (hsy : ∀ t ∈ Icc a b, ∀ X, (G t X).IsSymm)
    (he : ∀ t ∈ Icc a b, ∀ X : P, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t X i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (X : P) : IsCellMetric (fun t _ => clampedParameterMetric G a b t X) := by
  have hc : Measurable (fun p : ℝ × Vec 2 => max a (min b p.1)) :=
    (measurable_const.max (measurable_const.min measurable_fst))
  refine ⟨?_, (fun _ _ _ => rfl), ?_, ?_⟩
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (hm X i j).comp hc
  · intro t z
    exact hsy _ (metric_clamp_mem a b hab t) X
  · intro t z ξ
    obtain ⟨hl, hu⟩ := he _ (metric_clamp_mem a b hab t) X ξ
    have hn : 0 ≤ ∑ i : Fin 2, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have heq : (∑ i, ∑ j, ξ i * clampedParameterMetric G a b t X i j * ξ j) =
        ∑ i, ∑ j, G (max a (min b t)) X i j * ξ i * ξ j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [clampedParameterMetric]
      ring
    rw [heq]
    exact ⟨(mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hn).trans hl,
      hu.trans (mul_le_mul_of_nonneg_right (by norm_num : (5 / 4 : ℝ) ≤ 2) hn)⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Actual measurable metric derivatives provide finite jet and quotient budgets. -/

structure ParameterMetricReserve (H : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) where
  regular : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j)
  measurable : ∀ Y i j, Measurable (fun t => G t Y i j)
  metric : ∀ Y, IsCellMetric (fun t _ => G t Y)
  budget : ℕ → ℝ
  budget_nonneg : ∀ n, 0 ≤ budget n
  derivative_bound : ∀ n, n ≤ H → ∀ t Y i j,
    ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ budget n

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Smooth periodic fast fields have genuine ordered torus Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def smoothPeriodicRawJet (K : ℕ) (f : Vec 2 → E) : RawJet2 K E :=
  fun a => orderedDerivative a.2 f

theorem smooth_vector_weak_coordinate {f : Vec 2 → E} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (e : E) :
    HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e ((fderiv ℝ f x) (basisVec i))) := by
  let A := InnerProductSpace.toDual ℝ E e
  have h := HasWeakPartialDerivOn.of_contDiff (A.contDiff.comp hf) (i := i) (U := Set.univ)
  have hd (x : Vec 2) : (fderiv ℝ (A ∘ f) x) (basisVec i) =
      inner ℝ e ((fderiv ℝ f x) (basisVec i)) := by
    rw [fderiv_comp x A.differentiableAt (hf.differentiable (by norm_num) x), A.fderiv]
    rfl
  simp_rw [hd] at h
  exact h

theorem smoothPeriodicRawJet_hasWeakJet (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    HasOrderedWeakJetOn Set.univ (smoothPeriodicRawJet K f) := by
  intro j w i e
  have hs : ContDiff ℝ 1 (orderedDerivative w f) :=
    ChartTransport.contDiff_orderedDerivative w (hf.of_le (by simp))
  have he := smooth_vector_weak_coordinate hs i e
  have hn : orderedDerivative (Fin.snoc w i) f =
      fun x => (fderiv ℝ (orderedDerivative w f) x) (basisVec i) := by
    rw [orderedDerivative_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (orderedDerivative w f x))
    (fun x => inner ℝ e (orderedDerivative (Fin.snoc w i) f x))
  rw [hn]
  exact he

variable [MeasurableSpace E] [BorelSpace E]

def smoothPeriodicHk (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2
      (volume.restrict AVenhance.unitCube)) : TorusHk K E :=
  (show TorusHkFunction K E from ⟨smoothPeriodicRawJet K f,
    (fun a => ChartTransport.isZ2Periodic_orderedDerivative a.2 hp), hmem,
    smoothPeriodicRawJet_hasWeakJet K hf⟩).toHk

theorem smoothPeriodicHk_jet_ae (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2
      (volume.restrict AVenhance.unitCube)) (a : JetIndex2 K) :
    (smoothPeriodicHk K f hf hp hmem).val a =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative a.2 f :=
  torusJetToL2_ae _ _ a

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
namespace AVRegularity.EntryWeakProofs

/-! Summable uniform derivative majorants for the spatial Fourier series. -/

def realFourierMajorant (K : ℕ) (f : TorusHk K ℝ) (n : ℕ) (k : Frequency) : ℝ :=
  ‖realJetFourier K f (valueIndex2 K) k‖ * (2 * Real.pi) ^ n *
    (∑ i : Fin 2, |(k i : ℝ)|) ^ n

theorem realFourierMajorant_summable (K : ℕ) (f : TorusHk K ℝ) (n : ℕ) (hn : n + 2 ≤ K) :
    Summable (realFourierMajorant K f n) := by
  have hh : Summable (fun k : Frequency => ∑ w : DerivativeWord2 n,
      ‖realJetFourier K f ⟨⟨n, by omega⟩, w⟩ k‖) := by
    apply summable_sum
    intro w _
    exact realJetFourier_norm_summable K f _ (by change n + 2 ≤ K; exact hn)
  apply hh.congr
  intro k
  simp_rw [realJetFourier_word_norm K f n (by omega)]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← frequencyPower_eq_word_sum]
  dsimp only [realFourierMajorant]
  ring

def realFourierMode (K : ℕ) (f : TorusHk K ℝ) (k : Frequency) : Vec 2 → ℂ :=
  fun x => realJetFourier K f (valueIndex2 K) k • AVenhance.Infra.Torus.torusCharacter (-k) x

theorem realFourierMode_contDiff (K : ℕ) (f : TorusHk K ℝ) (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (realFourierMode K f k) :=
  contDiff_const.mul ((AVenhance.Infra.Torus.torusCharacter_contDiff (-k)).of_le (by simp))

theorem realFourierMode_derivative_bound (K : ℕ) (f : TorusHk K ℝ) (n : ℕ)
    (k : Frequency) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (realFourierMode K f k) x‖ ≤ realFourierMajorant K f n k := by
  have hcd : ContDiffAt ℝ (n : ℕ∞) (AVenhance.Infra.Torus.torusCharacter (-k)) x :=
    ((AVenhance.Infra.Torus.torusCharacter_contDiff (-k)).of_le (by simp)).contDiffAt
  change ‖iteratedFDeriv ℝ n
    (realJetFourier K f (valueIndex2 K) k • AVenhance.Infra.Torus.torusCharacter (-k)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (x := x) (i := n) hcd, norm_smul]
  exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_torusCharacter_le k n x)
    (norm_nonneg _)).trans_eq (by dsimp only [realFourierMajorant]; ring)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Recentered appended families have a fixed-parent reference with translated child center. -/

theorem childGeom_parent_center_translate (D : OCData) (k : ℕ) (pk : ℤ)
    (a : ℝ) (g : ChainGeom) (c : ChainChild) (h : Vec 2) :
    D.childGeom k pk a c (g.1, g.2.1 + h, g.2.2) =
      D.childGeom k pk a ⟨h + c.center, c.phase⟩ g := by
  simp only [OCData.childGeom, add_assoc]

theorem weak_appendChild_recenter_reference_geom (D : OCData) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (z h : Vec 2) :
    (((A.recenter D h).appendChild D slot t z).geom D) =
      D.childGeom A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot)
        ⟨h + D.eps A.ctxLevel • D.relDisp A.ctxLevel A.slot
            (D.slotAnchor (A.ctxLevel + 1) slot) t z,
          z + D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t z⟩
        (A.geom D) := by
  obtain ⟨hb, hs, hc⟩ := weak_recenter_metadata D A h
  have hl' : (A.recenter D h).WellSlotted := by
    change (A.recenter D h).slots.length = (A.recenter D h).children.length + 1
    rw [hs, hc]
    exact hl
  have hctx : (A.recenter D h).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have hslot : (A.recenter D h).slot = A.slot := by
    simp only [RealChain.slot, hs]
  rw [weak_appendChild_geom D (A.recenter D h) hl', hctx, hslot,
    geom_recenter D A hl h, childGeom_parent_center_translate]

/-! A cutoff blend with the identity preserves the genuine strong metric interval. -/

theorem convex_metric_ellipticity (A : Matrix (Fin 2) (Fin 2) ℝ) (χ : ℝ)
    (hχ₀ : 0 ≤ χ) (hχ₁ : χ ≤ 1) (ξ : Vec 2)
    (hl : (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j)
    (hu : (∑ i, ∑ j, A i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j ∧
    (∑ i, ∑ j, (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j) ≤
      (5 / 4) * ∑ i, ξ i ^ 2 := by
  have hI : (∑ i, ∑ j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ i * ξ j) = ∑ i, ξ i ^ 2 := by
    simp [Matrix.one_apply, pow_two]
  have hp i j : (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j =
      χ * (A i j * ξ i * ξ j) + (1 - χ) * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ i * ξ j) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have he : (∑ i, ∑ j, (χ • A + (1 - χ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ i * ξ j) =
      χ * (∑ i, ∑ j, A i j * ξ i * ξ j) + (1 - χ) * ∑ i, ξ i ^ 2 := by
    simp_rw [hp]
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hI]
  rw [he]
  have hQ : 0 ≤ ∑ i : Fin 2, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb₀ := mul_le_mul_of_nonneg_left hl hχ₀
  have hb₁ := mul_le_mul_of_nonneg_left hu hχ₀
  have hr : 0 ≤ (1 - χ) * ∑ i, ξ i ^ 2 := mul_nonneg (sub_nonneg.mpr hχ₁) hQ
  constructor <;> nlinarith only [hb₀, hb₁, hr]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Smooth periodic fast fields have genuine ordered torus Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem finite_smoothPeriodicRawJet_hasWeakJet (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) :
    HasOrderedWeakJetOn Set.univ (smoothPeriodicRawJet K f) := by
  intro j w i e
  have hs : ContDiff ℝ 1 (orderedDerivative w f) :=
    ChartTransport.contDiff_orderedDerivative w
      (hf.of_le (by exact_mod_cast (show 1 + j.val ≤ K by omega)))
  have he := smooth_vector_weak_coordinate hs i e
  have hn : orderedDerivative (Fin.snoc w i) f =
      fun x => (fderiv ℝ (orderedDerivative w f) x) (basisVec i) := by
    rw [orderedDerivative_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (orderedDerivative w f x))
    (fun x => inner ℝ e (orderedDerivative (Fin.snoc w i) f x))
  rw [hn]
  exact he

variable [MeasurableSpace E] [BorelSpace E]

def finiteSmoothPeriodicHk (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2
      (volume.restrict AVenhance.unitCube)) : TorusHk K E :=
  (show TorusHkFunction K E from ⟨smoothPeriodicRawJet K f,
    (fun a => ChartTransport.isZ2Periodic_orderedDerivative a.2 hp), hmem,
    finite_smoothPeriodicRawJet_hasWeakJet K hf⟩).toHk

theorem finiteSmoothPeriodicHk_jet_ae (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2
      (volume.restrict AVenhance.unitCube)) (a : JetIndex2 K) :
    (finiteSmoothPeriodicHk K f hf hp hmem).val a =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative a.2 f :=
  torusJetToL2_ae _ _ a

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVenhance.Infra.Heat
open AVenhance.Infra.Torus
namespace AVRegularity.EntryWeakProofs

/-! A finite-regularity classical Fourier representative from two reserved weak derivatives. -/

def realFourierLift (K : ℕ) (f : TorusHk K ℝ) : Vec 2 → ℂ :=
  fun x => ∑' k : Frequency, realFourierMode K f k x

theorem realFourierLift_contDiff (K r : ℕ) (hr : r + 2 ≤ K) (f : TorusHk K ℝ) :
    ContDiff ℝ (r : ℕ∞) (realFourierLift K f) := by
  apply contDiff_tsum (𝕜 := ℝ) (E := Vec 2) (F := ℂ)
    (f := realFourierMode K f) (v := realFourierMajorant K f) (N := (r : ℕ∞))
  · intro k
    exact (realFourierMode_contDiff K f k).of_le (by simp)
  · intro n hn
    have hn' : n ≤ r := by exact_mod_cast hn
    exact realFourierMajorant_summable K f n (by omega)
  · intro n k x _
    exact realFourierMode_derivative_bound K f n k x

theorem realFourierLift_periodic (K : ℕ) (f : TorusHk K ℝ) :
    AVenhance.IsZ2Periodic (realFourierLift K f) := by
  intro n x
  apply tsum_congr
  intro k
  dsimp only [realFourierMode]
  exact congrArg (fun z : ℂ => realJetFourier K f (valueIndex2 K) k • z)
    (torusCharacter_periodic (-k) n x)

def realClassicalLift (K : ℕ) (f : TorusHk K ℝ) : Vec 2 → ℝ :=
  fun x => (realFourierLift K f x).re

theorem realClassicalLift_contDiff (K r : ℕ) (hr : r + 2 ≤ K) (f : TorusHk K ℝ) :
    ContDiff ℝ (r : ℕ∞) (realClassicalLift K f) :=
  Complex.reCLM.contDiff.comp (realFourierLift_contDiff K r hr f)

theorem realClassicalLift_periodic (K : ℕ) (f : TorusHk K ℝ) :
    AVenhance.IsZ2Periodic (realClassicalLift K f) := by
  intro n x
  exact congrArg Complex.re (realFourierLift_periodic K f n x)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Piola lowering is measurable in parameters with only spatial smoothness. -/

variable {T : Type*} [MeasurableSpace T]

theorem transitionT_parameter_measurable
    (K : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ y i j, Measurable (fun t => K t y i j))
    (hKs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => K t y i j))
    (I A : List (Fin 2)) (y : Vec 2) : Measurable (fun t => transitionT (K t) I A y) := by
  induction I generalizing A y with
  | nil => cases A <;> exact measurable_const
  | cons i I ih =>
    have hd (A : List (Fin 2)) (b : Fin 2) :
        Measurable (fun t => fderiv ℝ (transitionT (K t) I A) y (basisVec b)) :=
      fderiv_apply_parameter_measurable (fun t x => transitionT (K t) I A x)
        (fun x => ih A x)
        (fun t => (CycleJointProofs.transitionT_spatial_smooth (K t) (hKs t) I A).differentiable (by simp))
        y (basisVec b)
    have hs : Measurable (fun t => ∑ b : Fin 2,
        K t y b i * fderiv ℝ (transitionT (K t) I A) y (basisVec b)) :=
      Finset.measurable_sum _ (fun b _ => (hK y b i).mul (hd A b))
    cases A with
    | nil => simpa only [transitionT, add_zero] using hs
    | cons a A =>
      have hprod : Measurable (fun t => K t y a i * transitionT (K t) I A y) :=
        (hK y a i).mul (ih A y)
      change Measurable (fun t =>
        (∑ b : Fin 2, K t y b i * fderiv ℝ (transitionT (K t) I (a :: A)) y (basisVec b)) +
          K t y a i * transitionT (K t) I A y)
      exact hs.add hprod

theorem transportedCoeff_parameter_measurable
    (K : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ y i j, Measurable (fun t => K t y i j))
    (hKs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => K t y i j))
    (Dγ : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → T → Vec 2)
    (hB : ∀ d I i, Measurable (fun t => B d I t i))
    (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2) (a : Fin 2) :
    Measurable (fun t => transportedCoeff (K t) Dγ (fun d I => B d I t) r A y a) := by
  unfold transportedCoeff
  apply Finset.measurable_sum
  intro d _
  apply Finset.measurable_sum
  intro I _
  apply Finset.measurable_sum
  intro i _
  exact ((hK y a i).mul (hB d I i)).mul
    (transitionT_parameter_measurable K hK hKs (List.ofFn I) (List.ofFn A) y)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The appended center in parent coordinates has a contractive child-to-parent ratio. -/

theorem weak_appendChild_recenter_coarse_reference_geom (D : OCData) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (z X : Vec 2)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    (((A.recenter D (ρ • X)).appendChild D slot t z).geom D) =
      D.childGeom A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot)
        ⟨ρ • (X + (D.eps A.ctxLevel / ρ) •
            D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t z),
          z + D.relDisp A.ctxLevel A.slot (D.slotAnchor (A.ctxLevel + 1) slot) t z⟩
        (A.geom D) := by
  rw [weak_appendChild_recenter_reference_geom D A hl slot t z (ρ • X)]
  have he : ρ * (D.eps A.ctxLevel / ρ) = D.eps A.ctxLevel := by
    rw [mul_div_cancel₀ _ hρ]
  simp only [smul_add, smul_smul, he]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Genuine parameter jets for scalar and vector sources in the uniformly local norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sourceParameterJet (f : ℝ → Vec 2 → Vec 2 → E) (p : ℕ × ℕ)
    (Y : Vec 2) (t : ℝ) (z : Vec 2) : E :=
  realParameterCanonicalJet (f t z) p Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Equivalent parent geometries yield equivalent actual appended reference geometries. -/

theorem weak_appendChild_recenter_reference_geometry_congr (D : OCData)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (hctx : A.ctxLevel = B.ctxLevel) (hslot : A.slot = B.slot) (hgeom : A.geom D = B.geom D)
    (ρ : ℝ) (hρ : ρ ≠ 0) (slot : ℤ) (t : ℝ) (z X Y : Vec 2) (hXY : X = Y) :
    (((A.recenter D (ρ • X)).appendChild D slot t z).geom D) =
      (((B.recenter D (ρ • Y)).appendChild D slot t z).geom D) := by
  rw [weak_appendChild_recenter_coarse_reference_geom D A hA slot t z X ρ hρ,
    weak_appendChild_recenter_coarse_reference_geom D B hB slot t z Y ρ hρ,
    hctx, hslot, hgeom, hXY]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The literal initial identity extends native coefficient families without imposing equations outside their carrier. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentIdentityLiftCoeff : LiftCoeff ι (fun _ => ℝ) :=
  fun m _ _ _ _ v u => if m = 0 then blockIdentityEntry (fun _ : ι => ℝ) v u else 0

theorem independentIdentityLiftCoeff_apply (f : ℝ → Vec 2 → ι → ℝ) (t : ℝ) (X z : Vec 2) :
    liftApply 0 (independentIdentityLiftCoeff (ι := ι)) f t X z = f t X := by
  funext v
  simp [liftApply, independentIdentityLiftCoeff, blockIdentityEntry_apply, orderedDerivative]

omit [Fintype ι] in
theorem independentIdentityLiftCoeff_above_order (m : ℕ) (hm : 0 < m) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentIdentityLiftCoeff m α t X z v u = 0 := by
  simp only [independentIdentityLiftCoeff, ite_eq_right (Nat.ne_of_gt hm)]

omit [Fintype ι] in
theorem independentIdentityLiftCoeff_perm (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    independentIdentityLiftCoeff (ι := ι) m (α ∘ σ) = independentIdentityLiftCoeff m α := rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Genuine slow differentiation preserves literal fast periodicity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sourceParameterJet_periodic (f : ℝ → Vec 2 → Vec 2 → E)
    (hp : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (p : ℕ × ℕ) (Y : Vec 2) (t : ℝ) :
    AVenhance.IsZ2Periodic (sourceParameterJet f p Y t) := by
  intro k z
  have he : f t (z + fun i => (k i : ℝ)) = f t z := by
    funext X
    exact hp t X k z
  change realParameterCanonicalJet (f t (z + fun i => (k i : ℝ))) p Y =
    realParameterCanonicalJet (f t z) p Y
  rw [he]

end AVRegularity.EntryWeakProofs
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativeGluedDissipationEnergyPrice
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
public import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent

section
section
/-! Actual native coefficient families glue with one fixed component matrix and no pulse-count loss. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift FastJets
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_gradient_factorial_spatial_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (P₀ : ℕ)
    (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r + 1 ≤ P₀) (hrQ : r + 1 ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (chart j τ))
    (hJ : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (chart j τ) (P₀ + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 → ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (label j τ))
    (hJlabel : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      ChartTransport.JetBound (label j τ) (r + 1) C (liftLength D G.level))
    (hw : ∀ j ∈ kset, 0 ≤ ϖ j τ) (hs : ∑ j ∈ kset, ϖ j τ ≤ 1)
    (hinv : ∀ j ∈ kset, ϖ j τ ≠ 0 → ∀ Y, chart j τ (label j τ Y) = Y)
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (v : CompIn G.comps) :
    let Kmax := ∑ j ∈ Finset.range (r + 1),
      ∑ n ∈ Finset.range N, nativeChartTransportConstant C (P₀ + N) (n + 1) (j + 1)
    let Mout := fun v u => ∑ hh ∈ Finset.range (H + 1),
      nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u
    let Aout := fun v u => (if v = u then 1 else 0) + Kmax * Mout v u
    let Cinput := ((P₀ + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (P₀ + N + 1), if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2
    let Z := ∑ u, ENNReal.ofReal (massConjugatedMatrix π Aout v u * (π u)⁻¹) *
      (ENNReal.ofReal Cinput * classicalGradFactorialSq (liftLength D G.level) (P₀ + N - 1) (fun X => a τ X u))
    ENNReal.ofReal ν * (ENNReal.ofReal (π v)⁻¹ * classicalGradFactorialSq rs r (fun Y =>
      gluedLift kset ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a τ Y v)) ≤
      (∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        (2 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (B * (1 + Kmax *
          (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
            ∑ hh ∈ Finset.range (H + 1), S ^ hh)))) * Z := by
  intro Kmax Mout Aout Cinput Z
  rw [weighted_classical_gradient_energy_eq ((slotLifts ⟨1, by decide⟩).setting.mass_pos v) hν.le]
  let Cbudget : ℕ → ℝ≥0∞ := fun _ => ENNReal.ofReal (B * (1 + Kmax *
    (nativeLiftScalarBudget P₀ (max k (L + 2)) Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh)))
  apply gradient_factorial_word_energy_sum_le r _ Cbudget Z
  intro j hj w
  have hKprice : (∑ n ∈ Finset.range N,
      nativeChartTransportConstant C (P₀ + N) (n + 1) (j + 1)) ≤ Kmax :=
    Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun j : ℕ => ∑ n ∈ Finset.range N,
        nativeChartTransportConstant C (P₀ + N) (n + 1) (j + 1))
      (fun _ _ => Finset.sum_nonneg fun _ _ => nativeChartTransportConstant_nonneg hC _ _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have hb := nativeStageLiftFamily_glued_dissipation_spatial_energy_le_of_price_le slotLifts hS P₀ hreserve
    (j + 1) (by omega) (by omega) (by omega) kset hodd ϖ c εc τ hc hεc hεc1 a ha chart label
    hC hchart hJ hrs hrse heρ hν hB hνB hprice
    (fun l hl hw => (hlabel l hl hw).of_le (by exact_mod_cast Nat.add_le_add_right hj 1))
    (fun l hl hw p hp hpj => hJlabel l hl hw p hp (hpj.trans (Nat.add_le_add_right hj 1)))
    hw hs w hinv ht v Kmax hKprice
  simpa only [Nat.add_sub_cancel] using hb

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual native glued values and dissipation control the component-sup strong energy at one source order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_strong_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hS : 0 ≤ S) (r : ℕ)
    (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (I : Set ℝ) (hI : MeasurableSet I) (kset : ℝ → Finset ℤ)
    (hodd : ∀ t ∈ I, ∀ j ∈ kset t, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ∀ t ∈ I, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (chart j t))
    (hJ : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (chart j t) (r + 1 + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (label j t))
    (hJlabel : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (label j t) (r + 1) C (liftLength D G.level))
    (hw : ∀ t ∈ I, ∀ j ∈ kset t, 0 ≤ ϖ j t)
    (hs : ∀ t ∈ I, ∑ j ∈ kset t, ϖ j t ≤ 1)
    (hinv : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 → ∀ Y, chart j t (label j t Y) = Y)
    (htime : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      c⁻¹ * t ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (hmeas : ∀ v, AEMeasurable (fun t => ENNReal.ofReal B * (ENNReal.ofReal (π v)⁻¹ *
      classicalGradFactorialSq (liftLength D G.level) (r + N) (fun x => a t x v)))
        (volume.restrict I)) :
    let C₀ := nativeLiftScalarBudget r (max k (L + 2)) Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh
    let C₁base := nativeLiftScalarBudget (r + 1) (max k (L + 2)) Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh
    let Kmax := ∑ j ∈ Finset.range (r + 1),
      ∑ n ∈ Finset.range N, nativeChartTransportConstant C (r + 1 + N) (n + 1) (j + 1)
    let C₁ := 1 + Kmax * C₁base
    let Cinput₀ := ((r + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (r + N + 1), 2 ^ j * (j.factorial : ℝ) ^ 2
    let Cinput₁ := ((r + 1 + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (r + 1 + N + 1), if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2
    let Vprice := ∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ j * ENNReal.ofReal
        ((∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (r + N) n j) ^ 2 * C₀)
    let Gprice := ∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal C₁
    classicalStrongEnergy rs ν π I r (fun t =>
      gluedLift (kset t) ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a t) ≤
      ((Vprice * ENNReal.ofReal Cinput₀) * ENNReal.ofReal C₀ +
        (Gprice * ENNReal.ofReal Cinput₁) * ENNReal.ofReal C₁) ^ (1 / 2 : ℝ) *
        classicalStrongEnergy (liftLength D G.level) B π I (r + N) a := by
  classical
  intro C₀ C₁base Kmax C₁ Cinput₀ Cinput₁ Vprice Gprice
  let slotLift := slotLifts ⟨1, by decide⟩
  let M (P : ℕ) : CompIn G.comps → CompIn G.comps → ℝ := fun v u =>
    ∑ hh ∈ Finset.range (H + 1), nativeLiftScalarBudget P (max k (L + 2)) Dm H N CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π (recordMajorant π G.fam)) hh v u
  have hM₀ : HasRealSchurBudget (massConjugatedMatrix π (M r)) C₀ :=
    nativeSlotLift_height_matrix_schur_budget slotLift hS r
  have hM₁ : HasRealSchurBudget (massConjugatedMatrix π (M (r + 1))) C₁base :=
    nativeSlotLift_height_matrix_schur_budget slotLift hS (r + 1)
  have hKmax : 0 ≤ Kmax := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    nativeChartTransportConstant_nonneg hC _ _ _
  let A₁ := fun v u => (if v = u then 1 else 0) + Kmax * M (r + 1) v u
  have hA₁ : HasRealSchurBudget (massConjugatedMatrix π A₁) C₁ :=
    mass_conjugated_identity_add_schur_budget π slotLift.setting.mass_pos (M (r + 1)) hM₁ hKmax
  apply classicalStrongEnergy_le_of_real_schur_bounds rs ν (liftLength D G.level) B π I r
    (r + N) _ a (massConjugatedMatrix π (M r)) (massConjugatedMatrix π A₁) C₀ C₁
    (Vprice * ENNReal.ofReal Cinput₀) (Gprice * ENNReal.ofReal Cinput₁) hM₀ hA₁ hmeas
  · intro v t ht
    have hb := nativeStageLiftFamily_glued_factorial_spatial_energy_le slotLifts hS r
      (fun slot => by have := hreserve slot; omega) r le_rfl ((Nat.le_succ r).trans hrQ)
      (kset t) (hodd t ht) ϖ c εc t hc hεc hεc1 a
      ((ha t ht).of_le (by exact_mod_cast Nat.add_le_add_right (Nat.le_succ r) N)) chart label
      hC (fun j hj hw => (hchart t ht j hj hw).of_le
        (by exact_mod_cast Nat.add_le_add_right (Nat.le_succ r) N))
      (fun j hj hw p hp hpj => hJ t ht j hj hw p hp (hpj.trans (Nat.add_le_add_right (Nat.le_succ r) N)))
      hrs hrse heρ
      (fun j hj hw => (hlabel t ht j hj hw).of_le (by exact_mod_cast Nat.le_succ r))
      (fun j hj hw p hp hpj => hJlabel t ht j hj hw p hp (hpj.trans (Nat.le_succ r)))
      (hw t ht) (hs t ht) (hinv t ht) (htime t ht) v
    apply hb.trans_eq
    simpa only [one_mul] using factored_matrix_energy_eq
      (fun u => massConjugatedMatrix π (M r) v u) (hM₀.nonneg v) π 1 Vprice
      (ENNReal.ofReal Cinput₀) (fun u => classicalFactorialSq (liftLength D G.level) (r + N)
        (fun x => a t x u))
  · intro v
    filter_upwards [ae_restrict_mem hI] with t ht
    have hb := nativeStageLiftFamily_glued_gradient_factorial_spatial_energy_le slotLifts hS (r + 1)
      hreserve r le_rfl hrQ (kset t) (hodd t ht) ϖ c εc t hc hεc hεc1 a (ha t ht) chart label
      hC (hchart t ht) (hJ t ht) hrs hrse heρ hν hB hνB hprice (hlabel t ht) (hJlabel t ht)
      (hw t ht) (hs t ht) (hinv t ht) (htime t ht) v
    have horder : r + 1 + N - 1 = r + N := by omega
    simp only [horder] at hb
    have hfactor := finite_order_price_factor (Finset.range (r + 1))
      (fun j => (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * (2 : ℝ≥0∞) ^ (j + 1)) hB.le C₁
    change _ = ENNReal.ofReal B * Gprice at hfactor
    rw [hfactor] at hb
    apply hb.trans_eq
    exact factored_matrix_energy_eq (fun u => massConjugatedMatrix π A₁ v u) (hA₁.nonneg v)
      π (ENNReal.ofReal B) Gprice (ENNReal.ofReal Cinput₁)
      (fun u => classicalGradFactorialSq (liftLength D G.level) (r + N) (fun x => a t x u))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The complete native lift price depends only on pre-data orders and scalar budgets. -/
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

def nativeLiftStrongEnergyPrice (r Q Dm H N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (S C : ℝ) : ℝ≥0∞ :=
  let C₀  := nativeLiftScalarBudget r Q Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh
  let C₁base := nativeLiftScalarBudget (r + 1) Q Dm H N CG Cw Cj *
      ∑ hh ∈ Finset.range (H + 1), S ^ hh
  let Kmax := ∑ j ∈ Finset.range (r + 1),
      ∑ n ∈ Finset.range N, nativeChartTransportConstant C (r + 1 + N) (n + 1) (j + 1)
  let C₁ := 1 + Kmax * C₁base
  let Cinput₀ := ((r + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (r + N + 1), 2 ^ j * (j.factorial : ℝ) ^ 2
  let Cinput₁ := ((r + 1 + N + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (r + 1 + N + 1), if j = 0 then 0 else 2 ^ j * ((j - 1).factorial : ℝ) ^ 2
  let Vprice := ∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ j * ENNReal.ofReal
        ((∑ n ∈ Finset.range (N + 1), nativeChartTransportConstant C (r + N) n j) ^ 2 * C₀)
  let Gprice := ∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal C₁
  (Vprice * ENNReal.ofReal Cinput₀) * ENNReal.ofReal C₀ +
    (Gprice * ENNReal.ofReal Cinput₁) * ENNReal.ofReal C₁

theorem nativeLiftStrongEnergyPrice_ne_top (r Q Dm H N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (S C : ℝ) :
    nativeLiftStrongEnergyPrice r Q Dm H N CG Cw Cj S C ≠ ∞ := by
  unfold nativeLiftStrongEnergyPrice
  dsimp only
  exact finite_factorial_strong_price_ne_top r _ _ _ _ _ _

theorem nativeLiftStrongEnergyPrice_real_constant (r Q Dm H N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (S C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (nativeLiftStrongEnergyPrice r Q Dm H N CG Cw Cj S C) ^ (1 / 2 : ℝ) = ENNReal.ofReal B :=
  finite_energy_price_real_bound _ (nativeLiftStrongEnergyPrice_ne_top r Q Dm H N CG Cw Cj S C)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual native glued values and dissipation control the component-sup strong energy at one source order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_strong_energy_uniform_budget_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar) (r : ℕ)
    (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (I : Set ℝ) (hI : MeasurableSet I) (kset : ℝ → Finset ℤ)
    (hodd : ∀ t ∈ I, ∀ j ∈ kset t, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ∀ t ∈ I, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (chart j t))
    (hJ : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (chart j t) (r + 1 + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (label j t))
    (hJlabel : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (label j t) (r + 1) C (liftLength D G.level))
    (hw : ∀ t ∈ I, ∀ j ∈ kset t, 0 ≤ ϖ j t)
    (hs : ∀ t ∈ I, ∑ j ∈ kset t, ϖ j t ≤ 1)
    (hinv : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 → ∀ Y, chart j t (label j t Y) = Y)
    (htime : ∀ t ∈ I, ∀ j ∈ kset t, ϖ j t ≠ 0 →
      c⁻¹ * t ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (hmeas : ∀ v, AEMeasurable (fun t => ENNReal.ofReal B * (ENNReal.ofReal (π v)⁻¹ *
      classicalGradFactorialSq (liftLength D G.level) (r + N) (fun x => a t x v)))
        (volume.restrict I)) :
    classicalStrongEnergy rs ν π I r (fun t =>
      gluedLift (kset t) ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
        chart label a t) ≤
      (nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * classicalStrongEnergy (liftLength D G.level) B π I (r + N) a := by
  have hb := nativeStageLiftFamily_glued_strong_energy_le
    (fun slot => (slotLifts slot).raiseBudget hSSbar) hSbar r hreserve hrQ
    I hI kset hodd ϖ c εc hc hεc hεc1 a ha chart label hC hchart hJ
    hrs hrse heρ hν hB hνB hprice hlabel hJlabel hw hs hinv htime hmeas
  simpa only [nativeStageLiftFamily_raiseBudget, nativeLiftStrongEnergyPrice] using hb

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual native glued values and dissipation control the component-sup strong energy at one source order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Lift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_sobolev_strong_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar) (r : ℕ)
    (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (t₀ t₁ : ℝ) (kset : ℝ → Finset ℤ)
    (hodd : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc : ℝ) (hc : c ≠ 0) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ∀ t ∈ (Set.Icc t₀ t₁), ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    {C : ℝ} (hC : 1 ≤ C)
    (hchart : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (chart j t))
    (hJ : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (chart j t) (r + 1 + N) C (liftLength D G.level))
    {rs e : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ liftLength D G.level)
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) (hνB : ν ≤ B)
    (hprice : εc = (e / Real.sqrt ν * Real.sqrt B) / liftLength D G.level)
    (hlabel : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (label j t))
    (hJlabel : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 →
      ChartTransport.JetBound (label j t) (r + 1) C (liftLength D G.level))
    (hw : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, 0 ≤ ϖ j t)
    (hs : ∀ t ∈ (Set.Icc t₀ t₁), ∑ j ∈ kset t, ϖ j t ≤ 1)
    (hinv : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 → ∀ Y, chart j t (label j t Y) = Y)
    (htime : ∀ t ∈ (Set.Icc t₀ t₁), ∀ j ∈ kset t, ϖ j t ≠ 0 →
      c⁻¹ * t ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
    (Z : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N) (hr v.1.root))
    (Zw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 1) (hr v.1.root))
    (hZ : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, IsClassicalRep (Z v t) (fun x => a t x v) (r + N))
    (hZw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁),
      IsClassicalRep (Zw v t) (fun x => a t x v) (r + N + 1))
    (hmeas : ∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc t₀ t₁)))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hU : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, IsClassicalRep (U v t)
      (fun x => (gluedLift (kset t) ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
          chart label a t) x v) r)
    (hUw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc t₀ t₁), IsClassicalRep (Uw v t)
      (fun x => (gluedLift (kset t) ϖ c (liftLength D G.level) e εc N H (nativeStageLiftFamily slotLifts)
          chart label a t) x v) (r + 1)) :
    strongEnergy rs ν π t₀ t₁ U Uw ≤
      (nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * strongEnergy (liftLength D G.level) B π t₀ t₁ Z Zw := by
  have hinput : ∀ v, AEMeasurable (fun t => ENNReal.ofReal B * (ENNReal.ofReal (π v)⁻¹ *
      classicalGradFactorialSq (liftLength D G.level) (r + N) (fun x => a t x v)))
      (volume.restrict (Set.Icc t₀ t₁)) := fun v => aemeasurable_const.mul
        (aemeasurable_const.mul (classicalGradFactorialSq_aemeasurable
          (liftLength D G.level) _ (Zw v) (fun t x => a t x v) (hmeas v) (hZw v)))
  rw [classicalRep_strong_energy_eq_ae rs ν t₀ t₁ π U Uw _ hU hUw,
    classicalRep_strong_energy_eq_ae (liftLength D G.level) B t₀ t₁ π Z Zw a hZ hZw]
  exact nativeStageLiftFamily_glued_strong_energy_uniform_budget_le slotLifts Sbar hSbar hSSbar
    r hreserve hrQ (Set.Icc t₀ t₁) measurableSet_Icc kset hodd ϖ c εc hc hεc hεc1 a ha
    chart label hC hchart hJ hrs hrse heρ hν hB hνB hprice hlabel hJlabel hw hs hinv htime hinput

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Actual native glued fields have compatible Sobolev carriers with their full classical jets. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem nativeStageLiftFamily_glued_classical_carrier
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r + 1 ≤ P₀) (hrQ : r + 1 ≤ max k (L + 2))
    (kset : Finset ℤ) (hodd : ∀ j ∈ kset, Odd j) (ϖ : ℤ → ℝ → ℝ)
    (c εc τ : ℝ) (hc : c ≠ 0)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (ha : ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a τ)) (haper : IsZ2Periodic (a τ))
    (ht : ∀ j ∈ kset, ϖ j τ ≠ 0 →
      c⁻¹ * τ ∈ Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    let F := gluedLift kset ϖ c (liftLength D G.level) (D.eps G.level) εc N H
      (nativeStageLiftFamily slotLifts)
      (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
      (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a τ
    ∃ (u : ∀ v : CompIn G.comps, TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, TorusHk (r + 1) (hr v.1.root)),
      (∀ v, IsClassicalRep (u v) (fun x => F x v) r) ∧
      (∀ v, IsClassicalRep (w v) (fun x => F x v) (r + 1)) ∧
      ∀ v, truncateTorusHk (Nat.le_succ r) (w v) = u v := by
  intro F
  have hreg (v : CompIn G.comps) : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => F x v) := by
    apply nativeStageLiftFamily_glued_contDiff slotLifts P₀ hreserve (r + 1) hrP hrQ
      kset hodd ϖ c (D.eps G.level) εc τ hc a ha _ _ _ _ ht v
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) τ
        (D.slotAnchor G.level j)).of_le (by simp)
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level j) τ).of_le (by simp)
  have hper : IsZ2Periodic F := nativeStageLiftFamily_glued_periodic slotLifts hi htorus
    kset hodd ϖ c εc τ hc a haper ht
  let w (v : CompIn G.comps) := classicalHilbertHk (r + 1) (fun x => F x v) (hreg v)
    (fun p x => congrFun (hper p x) v)
  have hw (v : CompIn G.comps) : IsClassicalRep (w v) (fun x => F x v) (r + 1) :=
    classicalHilbertHk_rep (r + 1) (fun x => F x v) (hreg v) (fun p x => congrFun (hper p x) v)
  refine ⟨fun v => truncateTorusHk (Nat.le_succ r) (w v), w, ?_, hw, fun _ => rfl⟩
  intro v
  exact classicalRep_truncate (Nat.le_succ r) le_rfl (w v) (fun x => F x v)
    (classicalRep_order_mono (w v) (fun x => F x v) (hw v) (Nat.le_succ r))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Construct the actual native lift coefficients with constants chosen before the stage and data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

theorem uniform_native_slot_lifts {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N K k L : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∃ (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (m₀ : ℕ), 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ slot : OddSlot, Nonempty (NativeSlotLift G slot (G.mass law) H N K k L CG Cw Cj S) := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := uniform_native_lift_analytic_certificates hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λs, hΛs, hs⟩ := native_lift_scale_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λa Λs, by omega, ?_⟩
  intro Λ hΛ bw hb Dm H N K k L hDm hN
  let qs := K + 4 * (H + 1) * (N + Dm) ^ 2
  let qf := max k (L + 2) + H * Dm + 2 * N + 2 * Dm
  obtain ⟨CG, Cw, _hCG, _hCw, ma, hma, hanalytic⟩ := ha Λ (by omega) qs
  obtain ⟨ms, hms, hscale⟩ := hs Λ (by omega)
  obtain ⟨B, _hB, hsource⟩ := stage_native_lift_source_exists_envelope bw hb qs qf
  let Cj : ℕ → ℕ → ℝ := fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * B (r + q)
  refine ⟨CG, Cw, Cj, max ma ms, by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hm hmM hj hdepth hreserve hreserve2 hlength slot
  have hΛ128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hi : 1 ≤ G.level := by omega
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have ⟨hnat, _, _, _, hpar, hcert, _, _⟩ := hG
  have ⟨hρ, hcell, hlam⟩ := hscale D hDα hDq hDΛ hDζ hband G.level (by omega) (by omega)
  let ρ := liftLength D G.level
  let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
  let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
    (G.fam.fiber slot (G.actual slot))
  have hA := hanalytic (CompIn G.comps) (fun v => hr v.1.root) Dm D
    hDα hDq hDΛ hDζ hseq hband G.level (by omega) hmM slot.1 slot.2 ρ hρ.le
    (G.fam.fiber slot (G.actual slot))
  let Ksrc := Dm
  have hKD : Ksrc ≤ Dm := le_rfl
  have h2K : 2 ≤ Ksrc := hDm
  have hz' : ∀ v u d, Ksrc < d.1 → Q.edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hres := effective_lift_reserves_le K k L H N Dm Ksrc hKD
  have hsource' := hsource hr D Dm j₀ G law P seedK freshK φ₀ hφ₀ M kI tA tB S θK
    hG hi hj hE hqD hΛ128 hζD hband hreserve hreserve2 hlength slot
    (ρ / D.eps (G.level - 1)) (div_nonneg hρ.le hE.le) (fun _ => 1) (Or.inl rfl)
  have hsourceQ : IsScaledJetEnvelope (G.mass law) Q.edge (Set.Icc a b)
      (ρ / D.eps (G.level - 1)) Cj qs qf (recordMajorant (G.mass law) G.fam) S := by
    simpa only [Q, familyLiftData, a, b, Cj, one_pow, div_one] using hsource'
  have hsetting := native_lift_setting_of_certificates G kI M hcert hpar hnat hi hj hb
    hΛ1 hζD hband hreserve hreserve2 slot ρ hρ hcell hlam (G.mass law)
    (fun v => Buffer.birth_compMass_pos hqD hΛ128 law v.1) H N K k L Ksrc hN h2K hKD
    CG Cw Cj (recordMajorant (G.mass law) G.fam) S hdepth hz' hA.2.1
    (fun r hr => hA.1 r (hr.trans hres.1)) (fun r _ => hA.2.2 r)
    (scaledEnvelope_order_mono hres.1 hres.2 hsourceQ)
  obtain ⟨Cc, hrestricted, hambient⟩ := effective_window_lift_exists_with_restricted hsetting hz'
  exact ⟨{
    cap := Ksrc
    cap_le := hKD
    cap_ge := h2K
    empty := hz'
    setting := hsetting
    coeff := Cc
    restricted := hrestricted
    ambient := hambient
  }⟩

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
section
/-! Construct the native slot lifts for both energy weights, with constants chosen before the
stage, data and marker. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

theorem uniform_native_weighted_slot_lifts {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N K k L : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∃ (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (m₀ : ℕ), 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    ∀ slot : OddSlot, Nonempty (NativeSlotLift G slot (fun v => G.mass law v / w v ^ 2) H N K k L CG Cw Cj S) := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := uniform_native_lift_analytic_certificates hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λs, hΛs, hs⟩ := native_lift_scale_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λa Λs, by omega, ?_⟩
  intro Λ hΛ bw hb Dm H N K k L hDm hN
  let qs := K + 4 * (H + 1) * (N + Dm) ^ 2
  let qf := max k (L + 2) + H * Dm + 2 * N + 2 * Dm
  obtain ⟨CG, Cw, _hCG, _hCw, ma, hma, hanalytic⟩ := ha Λ (by omega) qs
  obtain ⟨ms, hms, hscale⟩ := hs Λ (by omega)
  obtain ⟨B, _hB, hsource⟩ := stage_native_lift_source_exists_envelope bw hb qs qf
  let Cj : ℕ → ℕ → ℝ := fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * B (r + q)
  refine ⟨CG, Cw, Cj, max ma ms, by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hm hmM hj hdepth hreserve hreserve2 hlength w hw slot
  have hΛ128 : 128 ≤ D.Λ := by rw [hDΛ]; omega
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hwpos (v : CompIn G.comps) : 0 < w v := by
    rcases hw with rfl | rfl
    · exact zero_lt_one
    · exact Buffer.birth_compMarker_pos (by rw [hDq]; exact hq.1) hΛ128 law v.1
  have hπ (v : CompIn G.comps) : 0 < G.mass law v / w v ^ 2 :=
    div_pos (Buffer.birth_compMass_pos (by rw [hDq]; exact hq.1) hΛ128 law v.1)
      (sq_pos_of_pos (hwpos v))
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hi : 1 ≤ G.level := by omega
  have hE : 0 < D.eps (G.level - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have ⟨hnat, _, _, _, hpar, hcert, _, _⟩ := hG
  have ⟨hρ, hcell, hlam⟩ := hscale D hDα hDq hDΛ hDζ hband G.level (by omega) (by omega)
  let ρ := liftLength D G.level
  let a := D.slotStart G.level slot.1 / D.cellScaleSq G.level
  let b := (((slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  let Q := familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
    (G.fam.fiber slot (G.actual slot))
  have hA := hanalytic (CompIn G.comps) (fun v => hr v.1.root) Dm D
    hDα hDq hDΛ hDζ hseq hband G.level (by omega) hmM slot.1 slot.2 ρ hρ.le
    (G.fam.fiber slot (G.actual slot))
  let Ksrc := Dm
  have hKD : Ksrc ≤ Dm := le_rfl
  have h2K : 2 ≤ Ksrc := hDm
  have hz' : ∀ v u d, Ksrc < d.1 → Q.edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hres := effective_lift_reserves_le K k L H N Dm Ksrc hKD
  have hsource' := hsource hr D Dm j₀ G law P seedK freshK φ₀ hφ₀ M kI tA tB S θK
    hG hi hj hE hqD hΛ128 hζD hband hreserve hreserve2 hlength slot
    (ρ / D.eps (G.level - 1)) (div_nonneg hρ.le hE.le) w hw
  have hsourceQ : IsScaledJetEnvelope (fun v => G.mass law v / w v ^ 2) Q.edge (Set.Icc a b)
      (ρ / D.eps (G.level - 1)) Cj qs qf (recordMajorant (fun v => G.mass law v / w v ^ 2) G.fam) S := by
    simpa only [Q, familyLiftData, a, b, Cj] using hsource'
  have hsetting := native_lift_setting_of_certificates G kI M hcert hpar hnat hi hj hb
    hΛ1 hζD hband hreserve hreserve2 slot ρ hρ hcell hlam (fun v => G.mass law v / w v ^ 2)
    hπ H N K k L Ksrc hN h2K hKD
    CG Cw Cj (recordMajorant (fun v => G.mass law v / w v ^ 2) G.fam) S hdepth hz' hA.2.1
    (fun r hr => hA.1 r (hr.trans hres.1)) (fun r _ => hA.2.2 r)
    (scaledEnvelope_order_mono hres.1 hres.2 hsourceQ)
  obtain ⟨Cc, hrestricted, hambient⟩ := effective_window_lift_exists_with_restricted hsetting hz'
  exact ⟨{
    cap := Ksrc
    cap_le := hKD
    cap_ge := h2K
    empty := hz'
    setting := hsetting
    coeff := Cc
    restricted := hrestricted
    ambient := hambient
  }⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Prepared classical covariance data produce the actual native lifted field and its gradient carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_exists_of_prepared_classical_data
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r + 1 ≤ P₀) (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (hX : sX ≤ K + 2) (hZ : sZ ≤ max (k + 1) (L + 2))
    (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hprepared : ∀ v, ∀ t ∈ Set.Icc tp tf,
      IsCovImage (covPolyP (covPrimitive D G.level t) p)
        (succReadout G.level (D.eps (G.level - 1)) η Naux (fun v' => Y v' t) v) (PZ v t) ∧
      IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p))
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) :
    ∃ (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root)),
      IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y
        (nativeStageLiftFamily slotLifts) PZ a u w := by
  classical
  let F (t : ℝ) := gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
    (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level) (liftLength D G.level)
    (D.eps G.level) (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level) N H (nativeStageLiftFamily slotLifts)
    (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
    (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a t
  have hc : 0 < D.cellScaleSq G.level := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband _
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have hex (t : ℝ) : ∃ (u : ∀ v : CompIn G.comps, TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, TorusHk (r + 1) (hr v.1.root)),
      t ∈ Set.Icc tp tf → (∀ v, IsClassicalRep (u v) (fun x => F t x v) r) ∧
        (∀ v, IsClassicalRep (w v) (fun x => F t x v) (r + 1)) ∧
        ∀ v, truncateTorusHk (Nat.le_succ r) (w v) = u v := by
    by_cases ht : t ∈ Set.Icc tp tf
    · have haper : IsZ2Periodic (a t) := by
        intro q x
        funext v
        exact (hprepared v t ht).2.2.2.1 q x
      have hb := nativeStageLiftFamily_glued_classical_carrier slotLifts hi htorus P₀ hreserve
        r hrP hrQ (ocObsPulses D.α D.q D.Λ G.level t t)
        (fun j hj => (Finset.mem_filter.mp hj).2.1)
        (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level)
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
        t hc.ne' a (ha t ht) haper (by
          intro j _ hj
          have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
          rw [inv_mul_eq_div]
          exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
            div_le_div_of_nonneg_right htw.2 hc.le⟩)
      obtain ⟨u, w, hu, hw, htr⟩ := hb
      exact ⟨u, w, fun _ => ⟨hu, hw, htr⟩⟩
    · exact ⟨0, 0, fun ht' => False.elim (ht ht')⟩
  choose u w hrep using hex
  refine ⟨fun v t => u t v, fun v t => w t v, ⟨⟨?_, hprepared, ?_⟩, ?_⟩⟩
  · intro j hj
    exact nativeStageLiftFamily_sequence slotLifts sX sZ hX hZ j hj
  · intro v t ht
    exact classicalRep_value_ae (u t v) (fun x => F t x v) ((hrep t ht).1 v)
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hrep t ht).2.2 v

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Arbitrary actual lifted carriers have the classical jets of the constructed native field. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_classical_reps
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r + 1 ≤ P₀) (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) :
    let F := fun t => gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
      (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level) (liftLength D G.level)
      (D.eps G.level) (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
        liftLength D G.level) N H (nativeStageLiftFamily slotLifts)
      (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
      (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a t
    (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (u v t) (fun x => F t x v) r) ∧
    ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsClassicalRep (w v t) (fun x => F t x v) (r + 1) := by
  intro F
  classical
  have hc : 0 < D.cellScaleSq G.level := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband _
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have haper (t : ℝ) (ht : t ∈ Set.Icc tp tf) : IsZ2Periodic (a t) := by
    intro q x
    funext v
    exact (hfield.1.2.1 v t ht).2.2.2.1 q x
  have hcell (t : ℝ) (j : ℤ) (hj : ocCutoff D.α D.q D.Λ G.level j t ≠ 0) :
      (D.cellScaleSq G.level)⁻¹ * t ∈
        Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
          ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  have hper (t : ℝ) (ht : t ∈ Set.Icc tp tf) : IsZ2Periodic (F t) :=
    nativeStageLiftFamily_glued_periodic slotLifts hi htorus _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ hc.ne' a (haper t ht)
      (fun j _ hj => hcell t j hj)
  have hreg (t : ℝ) (ht : t ∈ Set.Icc tp tf) (v : CompIn G.comps) :
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => F t x v) := by
    apply nativeStageLiftFamily_glued_contDiff slotLifts P₀ hreserve (r + 1) hrP hrQ _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ _ hc.ne' a (ha t ht) _ _ _ _
      (fun j _ hj => hcell t j hj) v
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
        (D.slotAnchor G.level j)).of_le (by simp)
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level j) t).of_le (by simp)
  have hval := native_liftedField_value_eq_constructed slotLifts hΛ hζ hband p Naux sX sZ η tp tf
    Y CcT PZ a u hfield.1
  constructor
  · intro v t ht
    exact classicalRep_of_smooth_periodic_value_ae (u v t) (fun x => F t x v)
      ((hreg t ht v).of_le (by exact_mod_cast Nat.le_succ r))
      (fun q x => congrFun (hper t ht q x) v) (hval v t ht)
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc, hfield.2 v] with t ht hcompat
    exact classicalRep_of_compatible_smooth_value (u v t) (w v t) (fun x => F t x v)
      (hreg t ht v) (fun q x => congrFun (hper t ht q x) v) (hval v t ht) hcompat

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Higher retained values supply all prepared data for existence of the actual native lift. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_exists_of_higher_retained_values
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (hX : sX ≤ K + 2) (hZ : sZ ≤ max (k + 1) (L + 2))
    (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (hk : r + N + 2 * p ≤ Naux)
    (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root))
    (heq : ∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)) :
    ∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root)),
      IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w := by
  obtain ⟨PZ, a, hprepared, ha⟩ := higher_readout_covariance_input_exists D G.level p Naux
    (Naux + 3) (r + N + 1) (by omega) (liftedField_higher_regularity_reserve hk)
    η tp tf hΛ hζ Y Yhi heq
  have ha' : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t) := by
    intro t _
    simpa only [Nat.add_assoc, Nat.add_comm 1 N] using ha t
  obtain ⟨u, w, hw⟩ := native_liftedFieldW_exists_of_prepared_classical_data slotLifts
    hi hΛ hζ hband htorus (r + 1) hreserve r le_rfl hrQ p Naux sX sZ hX hZ
    η tp tf Y PZ a hprepared ha'
  exact ⟨nativeStageLiftFamily slotLifts, PZ, a, u, w, hw⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Arbitrary actual lifted carriers have the classical jets of the constructed native field. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_strong_energy_le
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    (Z : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N) (hr v.1.root))
    (Zw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 1) (hr v.1.root))
    (hZ : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Z v t) (fun x => a t x v) (r + N))
    (hZw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsClassicalRep (Zw v t) (fun x => a t x v) (r + N + 1))
    (hmeas : ∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc tp tf))) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      (nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * strongEnergy (liftLength D G.level) (D.κ (G.level - 1)) π tp tf Z Zw := by
  classical
  have hrep := native_liftedFieldW_classical_reps slotLifts hi hΛ hζ hband htorus
    (r + 1) hreserve r le_rfl hrQ p Naux sX sZ η tp tf Y CcT PZ a u w hfield ha
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have he : 0 < D.eps G.level := Construction.Stream.ocEpsilon_pos hΛ
  have hodd : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t, Odd j :=
    fun _ _ _ hj => (Finset.mem_filter.mp hj).2.1
  have hprice : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) =
      D.eps G.level / Real.sqrt (D.κ G.level) * Real.sqrt (D.κ (G.level - 1)) := by
    rw [ocDStar, Real.sqrt_div hB.le]
    change D.eps G.level * (Real.sqrt (D.κ (G.level - 1)) / Real.sqrt (D.κ G.level)) = _
    ring
  have heρ : D.eps G.level ≤ liftLength D G.level := by
    apply cell_scale_le_lift_radius he.le hν hνB hρ
    exact hcell
  apply nativeStageLiftFamily_glued_sobolev_strong_energy_le slotLifts Sbar hSbar hSSbar r
    hreserve hrQ tp tf (fun t => ocObsPulses D.α D.q D.Λ G.level t t) hodd
    (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level)
    (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
    hc.ne' (div_nonneg (by rw [hprice]; positivity) hρ.le) hcell a ha
    (fun j t y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
    (fun j t y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t) hC
    (fun t _ j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
      (D.slotAnchor G.level j)).of_le (by simp))
    (fun t ht j hj hw => (hflow t ht j hj hw).1) hrs hrse heρ hν hB hνB
    (congrArg (fun x => x / liftLength D G.level) hprice)
    (fun t _ j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level j) t).of_le (by simp))
    (fun t ht j hj hw d hd hle => (hflow t ht j hj hw).2 d hd (hle.trans (by omega)))
    (fun _ _ _ _ => Real.smoothTransition.nonneg _)
    (fun t ht => Providers.CascadeInvariants.sum_ocCutoff_le_one hτ _ (hodd t ht) t)
    (fun t _ j _ _ y => (CycleReference.streamFlowHomeomorph (D.hΦ (G.level - 1)) t
      (D.slotAnchor G.level j)).right_inv y) ?_ Z Zw hZ hZw hmeas u w hrep.1 hrep.2
  intro t _ j _ hj
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Uniform existence of the actual lift with constants chosen before the stage and fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

theorem uniform_native_lift_existence_of_higher_values {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N r sX sZ : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ (Gr : GenStage D hr Dm bw j₀) (p Naux : ℕ), r + N + 2 * p ≤ Naux →
    ∀ (η tp tf : ℝ)
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)) →
    ∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
      (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root)),
      IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w := by
  classical
  obtain ⟨Λ₀, hΛ₀, hpack⟩ := uniform_native_weighted_slot_lifts hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hb Dm H N r sX sZ hDm hN
  let K := max sX (r + 1 + N + Dm)
  let k := max (r + 1) sZ
  obtain ⟨CG, Cw, Cj, m₀, hm₀, hp⟩ := hpack Λ hΛ bw hb Dm H N K k sZ hDm hN
  refine ⟨m₀, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hm hmM hj hdepth hreserve hreserve2 hlength
    Gr p Naux hk η tp tf Y Yhi heq
  have htorus := hG.isTorusCompatible
  have hp' := hp hr D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hm hmM hj hdepth hreserve hreserve2 hlength (fun _ => 1) (Or.inl rfl)
  let slotLifts := fun slot => Classical.choice (hp' slot)
  have hres (slot : OddSlot) : r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2 := by
    have hc := (slotLifts slot).cap_le
    have hK : r + 1 + N + Dm ≤ K := Nat.le_max_right _ _
    omega
  exact native_liftedFieldW_exists_of_higher_retained_values slotLifts (by omega)
    (by rw [hDΛ]; omega) (by rw [hDζ]; exact hζ) hband htorus r hres
    (by have hh := Nat.le_max_left (r + 1) sZ; omega)
    p Naux sX sZ (by have hh := Nat.le_max_left sX (r + 1 + N + Dm); omega)
    (by omega) η tp tf Y hk Yhi heq

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Arbitrary actual lifted carriers have the classical jets of the constructed native field. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

theorem native_liftedFieldW_covariance_strong_energy_le
    {Gr : GenStage D hr Dm bw j₀}
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (η tp tf : ℝ)
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hfield : IsLiftedFieldW G Gr G.level p Naux N H sX sZ η tp tf Y CcT PZ a u w)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    (Z : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N) (hr v.1.root))
    (Zw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 1) (hr v.1.root))
    (hZ : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Z v t) (fun x => a t x v) (r + N))
    (hZw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsClassicalRep (Zw v t) (fun x => a t x v) (r + N + 1))
    (hmeas : ∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc tp tf)))
    {cr Ccov : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (hCcov : 0 ≤ Ccov)
    (z : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 2 * p) (hr v.1.root))
    (zw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 2 * p + 1) (hr v.1.root))
    (hzw : ∀ v, MemLp (zw v) 2 (volume.restrict (Set.Icc tp tf)))
    (hcov : ∀ v, ∀ t ∈ Set.Icc tp tf,
      IsCovImage (covPolyP (covPrimitive D G.level t) p) (z v t) (Z v t))
    (hcovw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsCovImage (covPolyP (covPrimitive D G.level t) p) (zw v t) (Zw v t))
    (hcost : ∀ t ∈ Set.Icc tp tf,
      CycleComparison.Coarse.covPolyConst
        (CycleComparison.Coarse.fbCovConst (liftLength D G.level)
          (covPrimitive D G.level t) (r + N + 2 * p)) p ≤ Ccov) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      ((nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * ENNReal.ofReal (Ccov * (cr⁻¹) ^ (r + N + 2 * p))) *
          strongEnergy (cr * liftLength D G.level) (D.κ (G.level - 1)) π tp tf z zw := by
  have hnative := native_liftedFieldW_strong_energy_le slotLifts hi hΛ hζ hband htorus
    r hreserve hrQ p Naux sX sZ η tp tf Y CcT PZ a u w hfield ha Sbar hSbar hSSbar
    hC hrs hrse hρ hν hB hνB hcell hflow Z Zw hZ hZw hmeas
  have hcovEnergy := covImage_strongEnergy_enhanced_radius_le hρ hcr hcr1
    (fun t => covPrimitive D G.level t) (D.κ (G.level - 1)) tp tf Ccov hCcov π
    (slotLifts ⟨1, by decide⟩).setting.mass_pos Z Zw z zw hzw hcov hcovw hcost
  apply hnative.trans
  simpa only [mul_assoc] using mul_le_mul' (le_refl
    ((nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
      (1 / 2 : ℝ))) hcovEnergy

end AVRegularity.Construction.Preservation.FullLift
end
end
end

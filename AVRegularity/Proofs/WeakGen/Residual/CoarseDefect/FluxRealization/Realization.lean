-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxJets
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Jets
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The existence of the coarse flux of the window** (statement).

`WeakCoarseFluxExistsStatement plan kOf`: for every passage `M < i ≤ M + J_w` of an instance, there
is a class `Fc` of order `k` with `CdFcRealizes` (minus the `AD`-flux of the frontier readout
`cdFrontier`). Time measurability is not part of it (generic tools give a
strongly measurable version afterwards).

The hypotheses are those of `WeakFrontierFluxStatement` minus the two menu inequalities and
the output, plus `WeakPassageCommonOK plan` (the coefficient floor: the stage coefficients are
`C^n` and periodic for every `n`, `weakPassage_coeffRegular`). The orders are
`k + Dc - 1 ≤ kOf R` (a derivative of order `d - 1 ≤ Dc - 1` of the frontier field, `C^{kOf R + 1}`,
must be `C^k`) and `kOf R + 3 ≤ K_w + m`, exactly as in `WeakFrontierFluxStatement`.

Special cases: `R_w = 0` or no letter component: `cdAD = 0`, `Fc = 0`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- **The coarse flux exists.** -/
def WeakCoarseFluxExistsStatement (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  WeakPassageCommonOK plan →
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (_hm : m ≤ weakEntryMmax R)
    (hk : k + 1 + Dc ≤ R.Kw + m) (_hkOf : k + Dc - 1 ≤ kOf R)
    (_hkOf3 : kOf R + 3 ≤ R.Kw + m),
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
      (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw) (_h : WeakComparisonInput r i)
      (v₀ : CompIn (c.stage i).comps),
    (∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
        r.Ur (i - 1) v t) →
    ∃ Fc : (∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
      CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
        (cdAD c Dc i v₀) Fc
end

/-! **The coarse flux of the window exists** (proofs).

`weakCoarseFluxExists`: the classical flux `x ↦ -∑_d ∑_α AD_d(t, x)(e_α) ∂^α F(t, x)` of the
classical frontier field `F = weakFrontierField (h.aU t)` is `C^k` and periodic at every time of
the window (the stage coefficients are `C^n` for every `n`: `weakPassage_coeffRegular`; `F` is
`C^{kOf R + 1}`: `weakCoarseFamilyRep`), its class is `finiteSmoothPeriodicHk`, and its value jet is
the stated one by `frontierJetsStep`. -/

section
/-- The classical flux of a frontier field `F`: `-∑_d ∑_α AD_d(x)(e_α) ∂^α F(x)`. -/
def coarseFluxFun {Dc : ℕ}
    (AD : ∀ d : Finset.Icc 2 Dc, Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (F : Vec 2 → ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => ℝ) :=
  -(WithLp.toLp 2 fun j : Fin 2 =>
    ∑ d : Finset.Icc 2 Dc, ∑ α : DerivativeWord2 (d.1 - 1),
      (AD d x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) • orderedDerivative α F x)

theorem coarseFluxFun_contDiff {Dc k : ℕ}
    (AD : ∀ d : Finset.Icc 2 Dc, Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (F : Vec 2 → ℝ) (hAD : ∀ d, ContDiff ℝ (k : ℕ) (AD d))
    (hF : ∀ d : Finset.Icc 2 Dc, ContDiff ℝ ((k + (d.1 - 1) : ℕ) : ℕ) F) :
    ContDiff ℝ (k : ℕ) (coarseFluxFun AD F) := by
  unfold coarseFluxFun
  refine ContDiff.neg ?_
  refine (contDiff_piLp 2).2 fun j => ?_
  dsimp only
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro α _
  have h1 : ContDiff ℝ (k : ℕ) (fun x => AD d x (WithLp.toLp 2 (Pi.single α (1 : ℝ)))) :=
    (hAD d).clm_apply contDiff_const
  have h2 : ContDiff ℝ (k : ℕ) (fun x => AD d x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) :=
    (contDiff_piLp (𝕜 := ℝ) (p := 2)).1 h1 j
  exact h2.smul (AVRegularity.ChartTransport.contDiff_orderedDerivative α (hF d))

theorem coarseFluxFun_periodic {Dc : ℕ}
    (AD : ∀ d : Finset.Icc 2 Dc, Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (F : Vec 2 → ℝ) (hAD : ∀ d, IsZ2Periodic (AD d)) (hF : IsZ2Periodic F) :
    IsZ2Periodic (coarseFluxFun AD F) := by
  intro n x
  unfold coarseFluxFun
  congr 1
  congr 1
  funext j
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
  rw [hAD d n x, AVRegularity.ChartTransport.isZ2Periodic_orderedDerivative α hF n x]


open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem cdAD_regular {c : WeakPassageInstance plan R} (hreg : (weakPassageRawSetting (plan := plan) (R := R) c).CoeffRegular) (Dc i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (n : ℕ) (t : ℝ) :
    ContDiff ℝ (n : ℕ) (cdAD c Dc i v₀ d t) ∧ IsZ2Periodic (cdAD c Dc i v₀ d t) := by
  have hM : c.M ≤ i - 1 := by omega
  have hJ : i - 1 < c.M + A.Jw := by omega
  have hfun : cdAD c Dc i v₀ d t = fun x => ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
    if h : v₀.1 ∈ (c.stage (i - 1)).comps ∧
        succComp i v₀.1 [WordLetter.eddy n] ∈ (c.stage (i - 1)).comps then
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨succComp i v₀.1 [WordLetter.eddy n], h.2⟩ ⟨v₀.1, h.1⟩,
        (c.D.eps (i - 1) ^ A.η₀) •
          (c.stage (i - 1)).physCoeff ⟨succComp i v₀.1 [WordLetter.eddy n], h.2⟩ ⟨v₀.1, h.1⟩ γ
            d.1 t x
    else 0 := by
    funext x
    simp [cdAD]
  rw [hfun]
  constructor
  · apply ContDiff.sum
    intro m _
    split_ifs with h
    · apply ContDiff.sum
      intro γ _
      exact ((hreg (i - 1) hM hJ _ _ γ n d.1 0 0).2.1 t).const_smul _
    · exact contDiff_const
  · intro z x
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun γ _ => ?_
      rw [(hreg (i - 1) hM hJ _ _ γ 0 d.1 0 0).2.2.1 t z x]
    · rfl


theorem frontierField_contDiff_periodic {c : WeakPassageInstance plan R} (i kk : ℕ)
    (g : CompIn (c.stage (i - 1)).comps → Vec 2 → ℝ)
    (hg : ∀ v', ContDiff ℝ (kk : ℕ) (g v')) (hp : ∀ v', IsZ2Periodic (g v'))
    (v : CompIn (c.stage i).comps) :
    ContDiff ℝ (kk : ℕ) (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) g v) ∧
      IsZ2Periodic (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) g v) := by
  constructor
  · unfold weakFrontierField
    apply ContDiff.sum
    intro v' _
    split_ifs
    · exact contDiff_const.mul (hg v')
    · exact contDiff_const
  · intro n x
    unfold weakFrontierField
    refine Finset.sum_congr rfl fun v' _ => ?_
    split_ifs
    · rw [hp v' n x]
    · rfl

/-- **The coarse flux exists.** -/
theorem weakCoarseFluxExists (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : WeakCoarseFluxExistsStatement plan kOf := by
  classical
  intro hcommon B A R Dc m k hDc hm hk hkOf hkOf3 c r Uhi Whi hpass i hi hit h v₀ htrunc
  have hkOf' : k + Dc - 1 ≤ kOf R := hkOf
  have hreg := weakPassage_coeffRegular hcommon c
  have hrep := weakCoarseFamilyRep plan kOf R m hm hkOf3 c r Uhi i hi hit h htrunc
  have hjets := frontierJetsStep plan kOf R Dc m k hm hk hkOf hkOf3 c r Uhi i hi hit h htrunc
  have hF : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ContDiff ℝ ((kOf R + 1 : ℕ) : ℕ) (weakFrontierField i A.Rw A.η₀ (c.stage i)
        (c.stage (i - 1)) (h.aU t) v) ∧ IsZ2Periodic (weakFrontierField i A.Rw A.η₀ (c.stage i)
        (c.stage (i - 1)) (h.aU t) v) := fun v t ht =>
    frontierField_contDiff_periodic i (kOf R + 1) _ (fun v' => (hrep v' t ht).2.1)
      (fun v' => (hrep v' t ht).2.2.1) v
  have hcd : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ContDiff ℝ (k : ℕ) (coarseFluxFun (fun d => cdAD c Dc i v₀ d t)
        (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v)) := by
    intro v t ht
    refine coarseFluxFun_contDiff _ _ (fun d => (cdAD_regular hreg Dc i hi hit v₀ d k t).1)
      (fun d => (hF v t ht).1.of_le ?_)
    have := d.2
    simp only [Finset.mem_Icc] at this
    exact_mod_cast (by omega : k + (d.1 - 1) ≤ kOf R + 1)
  have hper : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      IsZ2Periodic (coarseFluxFun (fun d => cdAD c Dc i v₀ d t)
        (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v)) :=
    fun v t ht => coarseFluxFun_periodic _ _
      (fun d => (cdAD_regular hreg Dc i hi hit v₀ d 0 t).2) (hF v t ht).2
  refine ⟨fun v t => if ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀) then
    AVRegularity.CycleWords.finiteSmoothPeriodicHk k _ (hcd v t ht) (hper v t ht) else 0, ?_⟩
  intro v t ht
  simp only [ht, ↓reduceDIte]
  have hj := TorusHkFunction.toHk_toFunction_ae
    (⟨AVRegularity.CycleWords.smoothPlaneRawJet k (coarseFluxFun (fun d => cdAD c Dc i v₀ d t)
        (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v)),
      AVRegularity.CycleWords.smoothPlaneRawJet_periodicWeak_finite k (hcd v t ht) (hper v t ht)⟩ :
      TorusHkFunction k (PiLp 2 (fun _ : Fin 2 => ℝ))) (valueIndex2 k)
  have h0 : ∀ g : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ),
      AVRegularity.CycleWords.smoothPlaneRawJet k g (valueIndex2 k) = g := fun g =>
    AVRegularity.orderedDerivative_zero g _
  have hall := ae_all_iff.2 fun d : Finset.Icc 2 Dc => ae_all_iff.2 fun α : DerivativeWord2 (d.1 - 1) =>
    hjets v t ht (d.1 - 1) (by have := d.2; simp only [Finset.mem_Icc] at this; omega) α
  filter_upwards [hj, hall] with x hx hx2
  refine hx.trans ?_
  rw [h0]
  unfold coarseFluxFun
  congr 1
  congr 1
  funext j
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
  rw [hx2 d α]
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

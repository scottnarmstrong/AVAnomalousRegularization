-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Finite.WeakPositive.NativeFacts
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Finite.Lift.PositivePhysicalIdentity
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Finite.WeakLift.RepresentationAdapters
import AVRegularity.Finite.WeakPositive.NativeAdapter
import AVRegularity.Readout.OperatorMap

/-! The weak represented-lift estimate at the entry carrier (1,400). All analytic inputs
are proved elsewhere; this exposes the carrier through the finite packing and iteration. -/

@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev MeasureTheory
open scoped Classical ENNReal
namespace AVRegularity.Finite.Assembly

/-- The weak-lift statement at carrier (1,400); the statement is unchanged. -/
def WeakLiftRepStatementAt : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cw : ℝ, 0 ≤ Cw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw 1 400 j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (Gw : GenStage D ScalarH Dm bw j₀) (lawW : BirthLaw) (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0
        stage →
      IsWeakEncoding Nw Jw η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => Jw * Rw) stage CcR W →
    ∀ (t : ℝ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (rT : Representation (CompSpace Gw.comps)),
      IsRepresentationAt (D.eps M) (Lr + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize s (Lr + 3) (D.eps M) rT


/-- Fixed-carrier weak lift from any stage of the stack, spending exactly the
remaining passage orders; the uniform step constant is chosen before m and all data. -/
def WeakLiftRepFromStatementAt : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cstep : ℝ, 0 ≤ Cstep ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw 1 400 j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0
        stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => Jw * Rw) stage CcR W →
    ∀ (m : ℕ), M ≤ m → m ≤ M + Jw →
    ∀ (t : ℝ) (g : CompIn (stage m).comps → Vec 2 → ℝ)
      (rT : Representation (CompSpace (stage m).comps)),
      IsRepresentationAt (D.eps m) (3 + (M + Jw - m) * Nw) rT →
      rT.value = compField (fun v => weakMass D Nw Jw η₀ v.1) (fun x v => g v x) →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W m t g y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal (Cstep ^ (M + Jw - m)) *
          representedSize s (3 + (M + Jw - m) * Nw) (D.eps m) rT


end AVRegularity.Finite.Assembly
namespace AVRegularity.Finite.WeakLift
open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs WeakEntryProofs

/-- The readout bound needs no carrier or lift-order threshold. -/
private theorem weak_fixed_readout_stack {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (s : ℝ) (M J N R Lr sX sZ : ℕ) (η σ : ℝ) (hN : 1 ≤ N) (hJ : 1 ≤ J)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hη : 0 ≤ η) (PW : ProvParams)
    (stage : ℕ → GenStage D ScalarH Dm bw j₀)
    (hc : IsWeakConstruction D PW (⟨N, R, sX, sZ, η, M + J⟩ : WeakMenu)
      M J (D.termRW σ M) 0 stage)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)) :
    WeakReadoutStackStatement s M J N Lr η (weakStoredWordBudget N R ^ J : ℕ) stage CcR (J * R) := by
  intro i hi hit
  apply weak_readoutCLM_norm_le_card D N J i η _ hN hJ hq hΛ hη
  · exact_mod_cast weakConstruction_card_le PW _ M J 0 _ stage hc i (by omega) hit
  · exact_mod_cast weakConstruction_card_le PW _ M J 0 _ stage hc (i - 1) (by omega) (by omega)
  · exact Nat.cast_nonneg _

/-- Use the actual positive chart bound and the literal zero-degree identity at one stack. -/
private theorem weak_fixed_correction_stack {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (s : ℝ) (M J N R Lr sX sZ : ℕ) (η Ct Cr : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hs : s < 1) (hCt : 0 ≤ Ct) (_hCr : 0 ≤ Cr)
    (P : WeakPositiveParameters N (J * R) (Lr + 3))
    (stage : ℕ → GenStage D ScalarH Dm bw j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (hl : ∀ i, M < i → i ≤ M + J → IsWeakReadoutLifts i N (J * R) sX sZ (stage i) (CcR i))
    (hf : ∀ i, M < i → i ≤ M + J → WeakPositiveGeometry P i (stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
        (fun v => weakMass D N J η v.1) slot))
    (hread : WeakReadoutStackStatement s M J N Lr η Cr stage CcR (J * R))
    (hchart : ∀ (D : OCData) (Dm j₀ : ℕ) (bw : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
      (π : CompIn G.comps → ℝ), (∀ v, 0 < π v) → WeakPositiveGeometry P i G →
      ∀ (A : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot)
        (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
        (∀ slot, WeakPositiveGraded (A slot)) →
        (∀ slot, WeakPositiveIdentified (A slot) (Cc slot.1)) →
      ∀ Cpath : ℝ, 0 ≤ Cpath →
        (∀ slot, HasRealSchurBudget (massConjugatedMatrix π (fun v u =>
          ∑ hh ∈ Finset.range (J * R + 1), weakPositiveMatrix (A slot) hh v u)) Cpath) →
      ∀ K, K ≤ Lr + 3 → ∀ t f (r : Representation (CompSpace G.comps)),
        IsRepresentationAt (D.eps (i - 1)) (K + N) r →
        r.value = compField π (fun x v => f v x) →
      let corr := compField π (fun x v => weakGluedLift i N (J * R) G (positiveLiftCoefficients Cc) t f v x)
      ContDiff ℝ (K : ℕ) corr ∧ IsZ2Periodic corr ∧
      RawProfileJetBound (D.eps i) K s corr (ENNReal.ofReal (Ct * Cpath) *
        ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) *
        representedSize s (K + N) (D.eps (i - 1)) r)) :
    WeakCorrectionStackStatement s M J N Lr η
      ((profileJetCount (Lr + 3) : ℝ) * (Ct * weakPositivePathCost P * Cr)) stage CcR (J * R) := by
  intro i hi hit K hK t g r hr hv
  obtain ⟨hgeo, ⟨A⟩⟩ := hf i hi hit
  let π := fun v : CompIn (stage i).comps => weakMass D N J η v.1
  let Rout := readoutCLM i (D.eps (i - 1)) η π
    (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
  let f := weakReadoutStep i η (stage i) (stage (i - 1)) g
  have hpath : 0 ≤ weakPositivePathCost P := mul_nonneg
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
    (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
  have hmapped := Readout.representation_map_isRepresentationAt r Rout hr
  have hmv : (r.map Rout).value = compField π (fun x v => f v x) := by
    rw [Readout.representation_map_value]
    funext x
    rw [hv]
    exact weak_readout_normalized D N J i η hN hJ hgeo.q_gt hgeo.Λ_ge g x
  obtain ⟨hcd, hper, hraw⟩ := hchart D Dm j₀ bw i (stage i) π (A ⟨1, by decide⟩).setting.mass_pos
    hgeo A (CcR i)
    (fun slot => weak_positive_graded_recurrence N (J * R) (Lr + 3) P D Dm j₀ bw i (stage i) π
      slot (D.eps (i - 1)) (A slot))
    (fun slot => weak_positive_support_identification N (J * R) (Lr + 3) P D Dm j₀ bw i
      (stage i) π slot (D.eps (i - 1)) (A slot) sX sZ (CcR i slot.1) (hl i hi hit slot.1 slot.2))
    (weakPositivePathCost P) hpath
    (fun slot => weak_positive_weighted_path_sums N (J * R) (Lr + 3) P D Dm j₀ bw i (stage i) π
      slot (D.eps (i - 1)) (A slot)) K hK t f (r.map Rout) hmapped hmv
  have hsize : representedSize s (K + N) (D.eps (i - 1)) (r.map Rout) ≤
      ENNReal.ofReal Cr * representedSize s (K + N) (D.eps (i - 1)) r :=
    (Readout.representedSize_map_le r Rout hr).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (hread i hi hit)) le_rfl)
  have he : 0 < D.eps i := (A ⟨1, by decide⟩).setting.e_pos
  have hE : 0 < D.eps (i - 1) := (A ⟨1, by decide⟩).setting.E_pos
  have heE : D.eps i ≤ D.eps (i - 1) :=
    Applications.eps_antitone hgeo.q_gt hgeo.Λ_ge (by omega)
  have hgain : ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (positive_scale_gain _ _ s he heE hs)
  have hcost : ENNReal.ofReal (Ct * weakPositivePathCost P) *
      ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) *
      representedSize s (K + N) (D.eps (i - 1)) (r.map Rout) ≤
      ENNReal.ofReal (Ct * weakPositivePathCost P * Cr) *
        representedSize s (K + N) (D.eps (i - 1)) r := by
    calc
      _ ≤ ENNReal.ofReal (Ct * weakPositivePathCost P) * 1 *
          (ENNReal.ofReal Cr * representedSize s (K + N) (D.eps (i - 1)) r) :=
        mul_le_mul' (mul_le_mul' le_rfl hgain) hsize
      _ = _ := by rw [ENNReal.ofReal_mul (mul_nonneg hCt hpath), mul_one]; ac_rfl
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hcorr : compField π (fun x v => weakGluedLift i N (J * R) (stage i) (CcR i) t f v x) -
      (fun x => Rout (r.value x)) =
      compField π (fun x v => weakGluedLift i N (J * R) (stage i)
        (positiveLiftCoefficients (CcR i)) t f v x) := by
    funext x
    have hrx := congrFun hv x
    change compField _ _ x - Rout (r.value x) = _
    rw [hrx, weak_readout_normalized D N J i η hN hJ hgeo.q_gt hgeo.Λ_ge g x]
    apply PiLp.ext
    intro v
    change (Real.sqrt (π v))⁻¹ * weakGluedLift i N (J * R) (stage i) (CcR i) t f v x -
      (Real.sqrt (π v))⁻¹ * f v x =
      (Real.sqrt (π v))⁻¹ * weakGluedLift i N (J * R) (stage i)
        (positiveLiftCoefficients (CcR i)) t f v x
    rw [← mul_sub, weak_glued_positive_difference i N (J * R) sX sZ (stage i) (CcR i)
      hΛ hgeo.fast hgeo.band (hl i hi hit)]
  refine ⟨hcorr.symm ▸ hcd, hcorr.symm ▸ hper, ?_⟩
  rw [hcorr]
  have hraw' : RawProfileJetBound (D.eps i) K s _
      (ENNReal.ofReal (Ct * weakPositivePathCost P * Cr) *
        representedSize s (K + N) (D.eps (i - 1)) r) :=
    ⟨hraw.1.trans hcost, fun α hα => (hraw.2 α hα).trans hcost⟩
  have hp := profile_jet_packing (D.eps i) s K (Lr + 3) _ _ he hK hraw'
  exact hp.trans_eq (by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    ac_rfl)

/-- The finite weak-lift representation at the fixed entry carrier (1,400). -/
theorem weak_lift_rep_at : Assembly.WeakLiftRepStatementAt := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hfactory⟩ := weak_plateau_parent_setting_at α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨0, 0, ?_⟩
  intro sX sZ _hsX _hsZ
  obtain ⟨P, _hcap, _hslow, _hfast, hf⟩ := hfactory Λ hΛ bw hbw hbw1 J N R η σ
    hJ hN hη hη1 hσ hσ1 Lr hLr sX sZ
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  obtain ⟨Ct, hCt, hchart⟩ := weak_positive_derivative_chart_of_pointwise_and_regularity
    weak_positive_pointwise_chart weak_positive_chart_regularity N (J * R) (Lr + 3) P s hs₀ hs
  let Cr : ℝ := (weakStoredWordBudget N R ^ J : ℕ)
  have hCr : 0 ≤ Cr := Nat.cast_nonneg _
  have hpath : 0 ≤ weakPositivePathCost P := mul_nonneg
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
    (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
  let Ccorr := (profileJetCount (Lr + 3) : ℝ) * (Ct * weakPositivePathCost P * Cr)
  have hCc : 0 ≤ Ccorr := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCt hpath) hCr)
  let Cstep := Cr + Ccorr
  have hCstep : 0 ≤ Cstep := add_nonneg hCr hCc
  refine ⟨Cstep ^ J, pow_nonneg hCstep _, ?_⟩
  intro j₀ hcarrier
  obtain ⟨Mf, hMf⟩ := hf j₀ hcarrier
  refine ⟨max 1 Mf, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage Gw lawW ιw CcR W
    hconstruction hencoding hlifts hchain t g rT hrT hvalue
  have hε (i : ℕ) : 0 < D.eps i := by
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDΛ]
    exact Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)
  have h128 : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ₀.trans hΛ
  have hread := weak_fixed_readout_stack s M J N R Lr sX sZ η σ hN hJ
    (hDq.symm ▸ hq.1) h128 hη.le PW stage hconstruction CcR
  have hcorr := weak_fixed_correction_stack s M J N R Lr sX sZ η Ct Cr hN hJ hs hCt hCr P
    stage CcR hlifts (fun i hi hit => hMf M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm
      PW Dm stage hconstruction i hi hit) hread hchart
  have hsteps := weak_stack_passage_of_readout_correction s M J N Lr η Cr Ccorr stage CcR (J * R)
    weak_passage_append hs hCr hCc hε (fun i hi _ =>
      Applications.eps_antitone (hDq.symm ▸ hq.1) h128 (by omega)) hread hcorr
  obtain ⟨hreindex, hvalreindex, hsize⟩ := weak_encoding_representation hencoding (Lr + 3)
    g rT hrT hvalue (s := s)
  obtain ⟨rW, hrW, hreadout, hbound⟩ := weak_lift_iteration s M J N Lr (J * R) η Cstep hLr
    hCstep hε stage CcR W hconstruction.2.1 hchain hsteps t (fun v y => g y (ιw v))
    (rT.map (compReindex ιw.symm)) hreindex hvalreindex
  exact ⟨rW, hrW, hreadout, hbound.trans (mul_le_mul' le_rfl hsize)⟩

/-- The same uniform step constant works from every start level of the actual stack. -/
theorem weak_lift_rep_from_at : Assembly.WeakLiftRepFromStatementAt := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hfactory⟩ := weak_plateau_parent_setting_at α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨0, 0, ?_⟩
  intro sX sZ _hsX _hsZ
  obtain ⟨P, _hcap, _hslow, _hfast, hf⟩ := hfactory Λ hΛ bw hbw hbw1 J N R η σ
    hJ hN hη hη1 hσ hσ1 Lr hLr sX sZ
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  obtain ⟨Ct, hCt, hchart⟩ := weak_positive_derivative_chart_of_pointwise_and_regularity
    weak_positive_pointwise_chart weak_positive_chart_regularity N (J * R) (Lr + 3) P s hs₀ hs
  let Cr : ℝ := (weakStoredWordBudget N R ^ J : ℕ)
  have hCr : 0 ≤ Cr := Nat.cast_nonneg _
  have hpath : 0 ≤ weakPositivePathCost P := mul_nonneg
    (zero_le_one.trans (nativeLiftScalarBudget_ge_one _ _ _ _ _ _ _ _))
    (Finset.sum_nonneg fun _ _ => pow_nonneg P.S_nonneg _)
  let Ccorr := (profileJetCount (Lr + 3) : ℝ) * (Ct * weakPositivePathCost P * Cr)
  have hCc : 0 ≤ Ccorr := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCt hpath) hCr)
  let Cstep := Cr + Ccorr
  have hCstep : 0 ≤ Cstep := add_nonneg hCr hCc
  refine ⟨Cstep, hCstep, ?_⟩
  intro j₀ hcarrier
  obtain ⟨Mf, hMf⟩ := hf j₀ hcarrier
  refine ⟨max 1 Mf, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR W
    hconstruction hlifts hchain m hm hmt t g rT hrT hvalue
  have hε (i : ℕ) : 0 < D.eps i := by
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDΛ]
    exact Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)
  have h128 : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ₀.trans hΛ
  have hread := weak_fixed_readout_stack s M J N R Lr sX sZ η σ hN hJ
    (hDq.symm ▸ hq.1) h128 hη.le PW stage hconstruction CcR
  have hcorr := weak_fixed_correction_stack s M J N R Lr sX sZ η Ct Cr hN hJ hs hCt hCr P
    stage CcR hlifts (fun i hi hit => hMf M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm
      PW Dm stage hconstruction i hi hit) hread hchart
  have hsteps := weak_stack_passage_of_readout_correction s M J N Lr η Cr Ccorr stage CcR (J * R)
    weak_passage_append hs hCr hCc hε (fun i hi _ =>
      Applications.eps_antitone (hDq.symm ▸ hq.1) h128 (by omega)) hread hcorr
  have horder : (M + J - m) * N ≤ Lr :=
    (Nat.mul_le_mul_right N (by omega : M + J - m ≤ J)).trans hLr
  simpa only [Nat.add_comm] using
    weak_lift_iteration_from s M J N Lr (J * R) η Cstep hLr hCstep hε stage CcR W
      hconstruction.2.1 hchain hsteps m hm hmt ((M + J - m) * N) horder le_rfl t g rT
      (by simpa only [Nat.add_comm] using hrT) hvalue

end AVRegularity.Finite.WeakLift

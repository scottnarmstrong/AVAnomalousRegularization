-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.WeakEddyMeanArrayProduction
public import AVRegularity.EntryWeak.UniformWeakStageStepGeometry
import AVRegularity.Construction.EntryScales.TerminalCore
import Mathlib.Algebra.Order.Star.Real

section
section
/-! The common inherited producer respects geometry across different actual context charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N h sZ n m : ℕ}
  {BG BV B C : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakStageInheritedMean_cross_reference_geometry
    (S : IndependentWeakStageFluxProduction G minBase cap Hstage B)
    (c c' : WeakStageProductionContext D bw j₀ G.level minBase cap) (π : StagePath G h)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (hKD : K ≤ Dm)
    (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (ψ : Vec (2 + 4 * c'.chain.1.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates c.chain.1.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (hψ : ∀ Y, ‖independentFreshCarrierCoordinates c'.chain.1.children.length Y‖ < 1 / 4 →
      ψ =ᶠ[𝓝 Y] fun _ => 1)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (word : DerivativeWord2 m)
    (E : ∀ r : Fin (cap + 1), IndependentInheritedMeanNaturalOutput (Fin (h + 1)) (4 * r.val)
      H K N h 1 sZ h n m word BG BV B C)
    (x : IndependentInheritedMeanInput (Fin (h + 1)) (4 * c.chain.1.children.length)
      H K N h 1 sZ BG BV B)
    (y : IndependentInheritedMeanInput (Fin (h + 1)) (4 * c'.chain.1.children.length)
      H K N h 1 sZ BG BV B)
    (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (hy : WeakStageInheritedPrimitiveRealization S c' π hKD ψ Cc y)
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (out inp : Fin (h + 1)) (t : ℝ) (z : Vec 2) :
    (E ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩).field x out inp t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      (E ⟨c'.chain.1.children.length, Nat.lt_succ_of_le c'.depth_bound⟩).field y out inp t z
        (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  let Y := independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P
  let Z := independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q
  let V : Set (Vec 2) := {W | ‖W + X‖ < 1 / 8}
  have hV : IsOpen V := isOpen_lt (continuous_id.add continuous_const).norm continuous_const
  have hzeroV : (0 : Vec 2) ∈ V := by simpa only [V, Set.mem_ofPred_eq, zero_add] using hX
  have hcarrier (r : ℕ) (W : Vec (4 * r))
      (hW : ∀ j, ‖independentFreshChildProjection j false W‖ ≤ 3 / 16) :
      ‖independentFreshCarrierCoordinates r (independentIntrinsicParameterPacking (4 * r) X W)‖ < 1 / 4 := by
    apply lt_of_le_of_lt (independentFreshCarrierCoordinates_norm_le_of_bounds r _ (3 / 16)
      (by norm_num) ?_ ?_) (by norm_num)
    · simpa only [independentIntrinsicParameterPacking_stored] using hW
    · rw [independentIntrinsicParameterPacking_slow]
      exact hX.le.trans (by norm_num)
  have ha : x.primitive.a = y.primitive.a := by
    rw [hx.left, hy.left, hslot]
  have hb : x.primitive.b = y.primitive.b := by
    rw [hx.right, hy.right, hslot]
  have hv : x.primitive.v = y.primitive.v := by rw [hx.drift, hy.drift, hslot]
  have hM : x.primitive.M = y.primitive.M := hx.matrix.trans hy.matrix.symm
  have hedge : x.primitive.edge = y.primitive.edge := by
    rw [hx.edge, hy.edge,
      ← weakStageCommonPathEdges_of_nonempty G π c.slot ⟨c.chain⟩,
      ← weakStageCommonPathEdges_of_nonempty G π c'.slot ⟨c'.chain⟩, hslot]
  have hg := hgeom
  rw [actualIndependentCoarseParameterChain_eq_fresh D c.chain.1 c.chain.2.2.2.1,
    actualIndependentCoarseParameterChain_eq_fresh D c'.chain.1 c'.chain.2.2.2.1] at hg
  obtain ⟨W, hW, hzeroW, hmetric⟩ := independentFreshExtendedMetric_equalDepth_geometry_germ
    c.chain.1.children.length c'.chain.1.children.length hdepth D G.level
    (independentFreshBaseChain c.chain.1) (independentFreshBaseChain c'.chain.1)
    (independentFreshBaseChain_wellSlotted _) (independentFreshBaseChain_wellSlotted _)
    (fun j => realChainSlotSeq c.chain.1 (j + 1)) (fun j => realChainSlotSeq c'.chain.1 (j + 1))
    (independentFreshCoarseBirthLength D c.chain.1) (independentFreshCoarseBirthLength D c'.chain.1)
    (D.eps (G.level - 1)) x.primitive.a x.primitive.b Y Z
    (by simpa only [Y, Z, independentIntrinsicParameterPacking_stored] using hg)
    (by simp only [Y, Z, independentIntrinsicParameterPacking_slow]) χ ψ
    (hχ Y (hcarrier _ P hP)) (hψ Z (hcarrier _ Q hQ))
  have hGx := hx.metric
  change x.primitive.G = clampedParameterMetric
    (cutoffParameterMetric χ (independentFreshNativeMetric D c.chain.1.ctxLevel
      (independentFreshBaseChain c.chain.1) (fun j => realChainSlotSeq c.chain.1 (j + 1))
      (independentFreshCoarseBirthLength D c.chain.1) (D.eps (G.level - 1))))
    x.primitive.a x.primitive.b at hGx
  rw [c.chain.2.1] at hGx
  have hGy := hy.metric
  change y.primitive.G = clampedParameterMetric
    (cutoffParameterMetric ψ (independentFreshNativeMetric D c'.chain.1.ctxLevel
      (independentFreshBaseChain c'.chain.1) (fun j => realChainSlotSeq c'.chain.1 (j + 1))
      (independentFreshCoarseBirthLength D c'.chain.1) (D.eps (G.level - 1))))
    y.primitive.a y.primitive.b at hGy
  rw [c'.chain.2.1, ← ha, ← hb] at hGy
  have he : IndependentLiftHeterogeneousSliceEq x.primitive y.primitive (W ∩ V) Y Z := by
    refine ⟨ha, hb, hv, hM, hedge, ?_, ?_⟩
    · intro i j tt A hA _zz
      rw [hGx, hGy]
      exact hmetric i j tt A hA.1
    · intro v u e γ hγ α tt A hA zz
      rw [hx.edge] at hγ
      rw [hx.fields, hy.fields]
      change independentPathTemplateField (S.pathIncomingField π c) v u
        ⟨e.val, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp e.property).1,
          (Finset.mem_Icc.mp e.property).2.trans hKD⟩⟩ γ α tt zz
          (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length) A + Y) = _
      rw [independentIntrinsicParameterPacking_add_slow, independentIntrinsicParameterPacking_add_slow]
      exact S.pathTemplateField_geometry π c c' hslot hdepth v u
        ⟨e.val, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp e.property).1,
          (Finset.mem_Icc.mp e.property).2.trans hKD⟩⟩ γ
        (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩) hγ α P Q hP hQ hgeom (A + X) hA.2 tt zz
  have hmean := independentInheritedMean_equalDepth_cross E
    ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩
    ⟨c'.chain.1.children.length, Nat.lt_succ_of_le c'.depth_bound⟩ hdepth x y
    (W ∩ V) Y Z (hW.inter hV) ⟨hzeroW, hzeroV⟩ he out inp
  simpa only [map_zero, zero_add] using hmean t 0 ⟨hzeroW, hzeroV⟩ z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Coherent actual inherited flux production includes its literal native source readout. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_inherited_flux_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H K N R sZ : ℕ) (hNK : N ≤ K) (hK₁ : 1 ≤ K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧
      ∃ E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV B, ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ) (hKD : K ≤ Dm), ∀ bw j₀ (G : GenStage D (fun _ => ℝ) Dm bw j₀),
      D.term < G.level → G.maxOrderBound K → ∀ minBase Hstage, M₀ ≤ minBase →
      weakInheritedPrimitiveMenuOrder H K N R + K + 1 ≤ Hstage →
      ∀ S : IndependentWeakStageFluxProduction G minBase J Hstage B,
      ∀ c : WeakStageProductionContext D bw j₀ G.level minBase J,
      ∀ h (π : StagePath G h) (hh : h ∈ Finset.Icc 1 R) sX,
      ∀ Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ),
      (∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
        IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
          (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
            (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
          (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
          ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          N h (Cc c.slot.1 A)) →
      ∃ x : IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
          (weakInheritedPrimitiveMenuOrder H K N R) K N h 1 sZ BG BV B,
        WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc x ∧
        ∀ (n : ℕ) (hn : n ∈ Finset.Icc 2 K) (d : ℕ) (hd : d ∈ Finset.Icc 2 n)
          (word : DerivativeWord2 (d - 1)),
        let j := IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n d
          c.depth_bound hh hn hd word
        ∃ Q : IndependentParameterSourceReserve H (E.physicalField j x D G.level),
          (∀ r ≤ H, Q.budget r ≤
            finiteMatrixPower (weightedPathMatrix h (stagePathStoredWeight G π)) h (Fin.last h) 0 *
              (D.κ D.term * D.eps G.level ^ (n - 2) *
                D.eps (G.level - 1) ^ ((d : ℝ) - (n : ℝ)) * E.budget)) ∧
          (∀ δ ∈ independentFreshPhaseTranslations c.chain.1.children.length,
            IndependentSourceTranslationInvariant δ (E.physicalField j x D G.level)) ∧
          ∀ Y : Vec (2 + 4 * c.chain.1.children.length),
          ∀ hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw
            (D.eps (G.level - 1)) j₀ G.level c.slot.1,
          ∀ t : ℝ, (D.cellScaleSq G.level)⁻¹ * t ∈ Icc x.primitive.a x.primitive.b → ∀ z : Vec 2,
          fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
            (familyLiftData D G.level c.slot.1 (c.atParameter Y hY).1 (D.eps (G.level - 1))
              (pathEdges G π c.slot (c.atParameter Y hY)))
            (Cc c.slot.1 (c.atParameter Y hY).1) n t) d word
            (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) =
          E.physicalField j x D G.level t z Y := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, E, M₀, hM₀, hprod⟩ :=
    uniform_weak_stage_inherited_mean_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J H K N R sZ hNK hK₁ B hB
  refine ⟨χ, BG, BV, hχ, hBG, hBV, E, M₀, hM₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK minBase Hstage
    hbase hH S c h π hh sX Cc hCc
  obtain ⟨x, ha, hb, hU, hG, hv, he, hf, hM, hc, hphase, hmean⟩ :=
    hprod D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK
      minBase Hstage hbase hH S c h π hh sX Cc hCc
  have hx : WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc x :=
    ⟨ha, hb, hU, hG, hv, he, hf, hM, hc, hphase⟩
  refine ⟨x, hx, ?_⟩
  intro n hn d hd word
  obtain ⟨Q, hQ, hperiod⟩ := hmean n hn d hd word
  refine ⟨Q, hQ, hperiod, ?_⟩
  intro Y hY t ht z
  let j := IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n d
    c.depth_bound hh hn hd word
  let x' := weakInheritedPrimitiveMenuInput x (Finset.mem_Icc.mp hh).2
  have hx' : WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc x' :=
    hx.restrictRegularity _ (weakInheritedPrimitiveMenuOrder_entry H K N R h (Finset.mem_Icc.mp hh).2)
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hq' : 1 < D.q := by rw [hDq]; exact hq.1
  have hYx : Y ∈ x'.primitive.U := by rw [hx'.carrier]; exact hY
  have hcopy := weakStageInheritedMean_full_native_copy S c π hKD hK
    (χ c.chain.1.children.length) (hχ c.chain.1.children.length).2.2.1 Cc word
    (E.output j) x' hx' hq' hΛ' hζ' hband hweak hNK (zero_le_one.trans hBG) hBV hB
    hK₁ (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    (Nat.ne_of_gt (Finset.mem_Icc.mp hh).1) (Finset.mem_Icc.mp hd).2
    (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hd).1) sX hCc Y hYx hY t ht
  exact hcopy

end AVRegularity.EntryWeakProofs
end
end

section
/-! One coherent inherited mean family supplies every bounded actual chart of a stage. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N R sZ h : ℕ}
  {BG BV B : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

structure WeakInheritedStageMeanFamily
    (S : IndependentWeakStageFluxProduction G minBase cap Hstage B)
    (π : StagePath G h) (hKD : K ≤ Dm) (hh : h ∈ Finset.Icc 1 R)
    (E : IndependentWeakInheritedMeanProducer cap H K N R sZ BG BV B)
    (χ : ∀ r, Vec (2 + 4 * r) → ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) where
  datum : ∀ c : WeakStageProductionContext D bw j₀ G.level minBase cap,
    IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
      (weakInheritedPrimitiveMenuOrder H K N R) K N h 1 sZ BG BV B
  realization : ∀ c, WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc (datum c)

namespace WeakInheritedStageMeanFamily
variable {S : IndependentWeakStageFluxProduction G minBase cap Hstage B} {π : StagePath G h}
  {hKD : K ≤ Dm} {hh : h ∈ Finset.Icc 1 R}
  {E : IndependentWeakInheritedMeanProducer cap H K N R sZ BG BV B}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

def array (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (n : Finset.Icc 2 K) (d : ℕ) (word : DerivativeWord2 (d - 1)) :=
  weakInheritedPhysicalArray E ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩
    ⟨h, hh⟩ n (F.datum c) D G.level d word

theorem production (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (P : ProvParams) (ht : G.HasTags P) (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (n : Finset.Icc 2 K) (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (F.array c n d word),
      (∀ k ≤ H, Q.budget k ≤ (π.provList.map (fun y => (y.2.2.tags P).witness)).prod *
        (D.κ D.term * D.eps G.level ^ (n.val - 2) *
          D.eps (G.level - 1) ^ ((d : ℝ) - (n.val : ℝ)) * E.budget)) ∧
      (∀ δ ∈ independentFreshPhaseTranslations c.chain.1.children.length,
        IndependentSourceTranslationInvariant δ (F.array c n d word)) := by
  obtain ⟨Q, hQ, hphase⟩ := weakInheritedPhysicalArray_production E
    ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩ ⟨h, hh⟩ n (F.datum c) D G.level hκ hε d word
  refine ⟨Q, ?_, ?_⟩
  · intro k hk
    have hb := hQ k hk
    rw [(F.realization c).matrix] at hb
    have he := stagePathStoredMatrix_endpoint G P ht π
    change finiteMatrixPower (weightedPathMatrix h (stagePathStoredWeight G π)) h (Fin.last h) 0 = _ at he
    rw [he] at hb
    exact hb
  · intro δ hδ t z Y
    exact hphase δ (by rw [(F.realization c).phase]; exact hδ) t z Y

theorem geometry (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (c c' : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (n : Finset.Icc 2 K) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8) (t : ℝ) (z : Vec 2) :
    F.array c n d word t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
      F.array c' n d word t z (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  by_cases hd : d ∈ Finset.Icc 2 n.val
  · have he (cc : WeakStageProductionContext D bw j₀ G.level minBase cap) :
        F.array cc n d word = E.physicalField
          (IndependentWeakInheritedMeanIndex.ofOrders cc.chain.1.children.length h n.val d
            cc.depth_bound hh n.property hd word) (F.datum cc) D G.level := by
      unfold array weakInheritedPhysicalArray
      exact dite_eq_left hd
    rw [he c, he c']
    let x := weakInheritedPrimitiveMenuInput (F.datum c) (Finset.mem_Icc.mp hh).2
    let y := weakInheritedPrimitiveMenuInput (F.datum c') (Finset.mem_Icc.mp hh).2
    have hx : WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc x :=
      (F.realization c).restrictRegularity _
        (weakInheritedPrimitiveMenuOrder_entry H K N R h (Finset.mem_Icc.mp hh).2)
    have hy : WeakStageInheritedPrimitiveRealization S c' π hKD (χ c'.chain.1.children.length) Cc y :=
      (F.realization c').restrictRegularity _
        (weakInheritedPrimitiveMenuOrder_entry H K N R h (Finset.mem_Icc.mp hh).2)
    have hmean := weakStageInheritedMean_cross_reference_geometry (H := H) (N := N) (sZ := sZ)
      (n := n.val) (BG := BG) (BV := BV) (C := E.budget) S c c' π hslot hdepth hKD
      (χ c.chain.1.children.length) (χ c'.chain.1.children.length) (hχ _) (hχ _) Cc word
      (fun r => E.output ⟨r, ⟨h, hh⟩, n, ⟨d, hd⟩, word⟩) x y hx hy P Q hP hQ hgeom X hX
      (Fin.last h) 0 ((D.cellScaleSq G.level)⁻¹ * t) 0
    exact congrArg (fun w : Vec 2 =>
      -(D.κ D.term * D.eps G.level ^ (n.val - 2) *
        D.eps (G.level - 1) ^ ((d : ℝ) - (n.val : ℝ))) • w) hmean
  · have he (cc : WeakStageProductionContext D bw j₀ G.level minBase cap) :
        F.array cc n d word = fun _ _ _ => 0 := by
      unfold array weakInheritedPhysicalArray
      exact dite_eq_right hd
    rw [he c, he c']


end WeakInheritedStageMeanFamily
end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The coherent inherited array reads the original localized path histories. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N R sZ h : ℕ}
  {BG BV B : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}
  {S : IndependentWeakStageFluxProduction G minBase cap Hstage B} {π : StagePath G h}
  {hKD : K ≤ Dm} {hh : h ∈ Finset.Icc 1 R}
  {E : IndependentWeakInheritedMeanProducer cap H K N R sZ BG BV B}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

theorem native_copy (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (hK : G.maxOrderBound K)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < G.level)
    (hNK : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B) (hK₁ : 1 ≤ K)
    (sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A : RealChain,
      ∀ hA : IsAdmissibleChain D bw j₀ G.level p.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level p.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level p.1 A (D.eps (G.level - 1)) (pathEdges G π p ⟨A, hA⟩))
        sX sZ (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N h (Cc p.1 A))
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (n : Finset.Icc 2 K) (d : ℕ) (hd : d ∈ Finset.Icc 2 n.val)
    (word : DerivativeWord2 (d - 1))
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw
      (D.eps (G.level - 1)) j₀ G.level c.slot.1)
    (t : ℝ) (ht : (D.cellScaleSq G.level)⁻¹ * t ∈
      Icc (F.datum c).primitive.a (F.datum c).primitive.b) (z : Vec 2) :
    fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
      (familyLiftData D G.level c.slot.1 (c.atParameter Y hY).1 (D.eps (G.level - 1))
        (pathEdges G π c.slot (c.atParameter Y hY)))
      (Cc c.slot.1 (c.atParameter Y hY).1) n.val t) d word
      (D.eps (G.level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) =
      F.array c n d word t z Y := by
  let x := weakInheritedPrimitiveMenuInput (F.datum c) (Finset.mem_Icc.mp hh).2
  have hx : WeakStageInheritedPrimitiveRealization S c π hKD (χ c.chain.1.children.length) Cc x :=
    (F.realization c).restrictRegularity _
      (weakInheritedPrimitiveMenuOrder_entry H K N R h (Finset.mem_Icc.mp hh).2)
  have hYx : Y ∈ x.primitive.U := by rw [hx.carrier]; exact hY
  have hcopy := weakStageInheritedMean_full_native_copy S c π hKD hK
    (χ c.chain.1.children.length) (hχ _) Cc word
    (E.output (IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n.val d
      c.depth_bound hh n.property hd word)) x hx hq hΛ hζ hband hweak hNK hBG hBV hB hK₁
    (Finset.mem_Icc.mp n.property).1 (Finset.mem_Icc.mp n.property).2
    (Nat.ne_of_gt (Finset.mem_Icc.mp hh).1) (Finset.mem_Icc.mp hd).2
    (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hd).1)
    sX (hCc c.slot) Y hYx hY t ht
  have he : F.array c n d word = E.physicalField
      (IndependentWeakInheritedMeanIndex.ofOrders c.chain.1.children.length h n.val d
        c.depth_bound hh n.property hd word) (F.datum c) D G.level := by
    unfold array weakInheritedPhysicalArray
    exact dite_eq_left hd
  rw [he]
  exact hcopy

end AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
end
end

section
/-! The coherent inherited array reads the original localized path histories. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N R sZ h : ℕ}
  {BG BV B : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}
  {S : IndependentWeakStageFluxProduction G minBase cap Hstage B} {π : StagePath G h}
  {hKD : K ≤ Dm} {hh : h ∈ Finset.Icc 1 R}
  {E : IndependentWeakInheritedMeanProducer cap H K N R sZ BG BV B}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

theorem native_anchor_copy (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (hK : G.maxOrderBound K)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < G.level)
    (hNK : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B) (hK₁ : 1 ≤ K)
    (hbw : bw ≤ 1 / 10000) (sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A : RealChain,
      ∀ hA : IsAdmissibleChain D bw j₀ G.level p.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level p.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level p.1 A (D.eps (G.level - 1)) (pathEdges G π p ⟨A, hA⟩))
        sX sZ (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N h (Cc p.1 A))
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (n : Finset.Icc 2 K) (d : ℕ) (hd : d ∈ Finset.Icc 2 n.val)
    (word : DerivativeWord2 (d - 1))
    (t : ℝ) (ht : (D.cellScaleSq G.level)⁻¹ * t ∈
      Icc (F.datum c).primitive.a (F.datum c).primitive.b) (z : Vec 2) :
    fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
      (familyLiftData D G.level c.slot.1 c.chain.1 (D.eps (G.level - 1))
        (pathEdges G π c.slot c.chain))
      (Cc c.slot.1 c.chain.1) n.val t) d word
      0 =
      F.array c n d word t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0
          (independentFreshCoarseChainPacking D c.chain.1)) := by
  let Y := independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0
    (independentFreshCoarseChainPacking D c.chain.1)
  have hY := actualIndependentCoarseProductionCarrier_native_anchor D hq hΛ hζ c.chain.1 bw
    (D.eps (G.level - 1)) hbw j₀ G.level c.slot.1 c.chain.2
  have hctx : c.atParameter Y hY = c.chain := by
    apply Subtype.ext
    change actualIndependentCoarseParameterChain D c.chain.1
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y) = c.chain.1
    rw [independentIntrinsicParameterPacking_stored]
    exact actualIndependentCoarseParameterChain_native D (by omega) c.chain.1 c.chain.2.2.2.1
  have hc := F.native_copy hK hχ hq hΛ hζ hband hweak hNK hBG hBV hB hK₁ sX hCc
    c n d hd word Y hY t ht z
  rw [hctx] at hc
  simpa only [Y, independentIntrinsicParameterPacking_slow, smul_zero] using hc

end AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
end
end

section
/-! Coherent actual inherited flux production includes its literal native source readout. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_inherited_mean_family (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H K N R sZ : ℕ) (hNK : N ≤ K) (hK₁ : 1 ≤ K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧
      ∃ E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV B, ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ) (hKD : K ≤ Dm), ∀ bw j₀ (G : GenStage D (fun _ => ℝ) Dm bw j₀),
      D.term < G.level → G.maxOrderBound K → ∀ minBase Hstage, M₀ ≤ minBase →
      weakInheritedPrimitiveMenuOrder H K N R + K + 1 ≤ Hstage →
      ∀ S : IndependentWeakStageFluxProduction G minBase J Hstage B,
      ∀ h (π : StagePath G h) (hh : h ∈ Finset.Icc 1 R) sX,
      ∀ Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ),
      (∀ p : OddSlot, ∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level p.1 A,
        IsLiftSequenceOn (ladderOmega D bw j₀ G.level p.1 A (D.eps (G.level - 1)))
          (familyLiftData D G.level p.1 A (D.eps (G.level - 1))
            (pathEdges G π p ⟨A, hA⟩)) sX sZ
          (D.slotStart G.level p.1 / D.cellScaleSq G.level)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          N h (Cc p.1 A)) →
      Nonempty (WeakInheritedStageMeanFamily S π hKD hh E χ Cc) := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, E, M₀, hM₀, hprod⟩ :=
    uniform_weak_stage_inherited_flux_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J H K N R sZ hNK hK₁ B hB
  refine ⟨χ, BG, BV, hχ, hBG, hBV, E, M₀, hM₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK minBase Hstage
    hbase hH S h π hh sX Cc hCc
  have hp (c : WeakStageProductionContext D bw j₀ G.level minBase J) :=
    hprod D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK
      minBase Hstage hbase hH S c h π hh sX Cc (hCc c.slot)
  exact ⟨⟨(fun c => Classical.choose (hp c)),
    fun c => (Classical.choose_spec (hp c)).1⟩⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The coherent inherited array reads the original localized path histories. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage H K N R sZ h : ℕ}
  {BG BV B : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}
  {S : IndependentWeakStageFluxProduction G minBase cap Hstage B} {π : StagePath G h}
  {hKD : K ≤ Dm} {hh : h ∈ Finset.Icc 1 R}
  {E : IndependentWeakInheritedMeanProducer cap H K N R sZ BG BV B}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

theorem toMeanArrayProduction (F : WeakInheritedStageMeanFamily S π hKD hh E χ Cc)
    (P : ProvParams) (ht : G.HasTags P)
    (hK : G.maxOrderBound K)
    (hχ : ∀ r Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 →
      χ r =ᶠ[𝓝 Y] fun _ => 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < G.level)
    (hNK : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B) (hK₁ : 1 ≤ K)
    (hbw : bw ≤ 1 / 10000) (sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A : RealChain,
      ∀ hA : IsAdmissibleChain D bw j₀ G.level p.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level p.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level p.1 A (D.eps (G.level - 1)) (pathEdges G π p ⟨A, hA⟩))
        sX sZ (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N h (Cc p.1 A))
    (n : Finset.Icc 2 K) :
    Nonempty (IndependentWeakMeanArrayProduction D bw j₀ G.level minBase cap H n.val
      ((π.provList.map (fun y => (y.2.2.tags P).witness)).prod) E.budget
      (fun p A d word t => fluxCoeff (pathMeanFlux D G.level (D.eps (G.level - 1))
        (familyLiftData D G.level p.1 A.1 (D.eps (G.level - 1)) (pathEdges G π p A))
        (Cc p.1 A.1) n.val t) d word 0)) := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ hband D.term).le
  have hp c d word := F.production P ht hκ (fun _ => Construction.Stream.ocEpsilon_pos hΛ₁) c n d word
  choose Q hQ hphase using hp
  refine ⟨{ field := fun c => F.array c n
            reserve := Q
            budget := hQ
            phase := hphase
            geometry := ?_
            native_copy := ?_ }⟩
  · intro c c' hslot hdepth d word W Z hW hZ hgeom X hX t z
    exact F.geometry hχ c c' hslot hdepth n d word W Z hW hZ hgeom X hX t z
  · intro c d word hd hdn t htime z
    have htime' : (D.cellScaleSq G.level)⁻¹ * t ∈
        Icc (F.datum c).primitive.a (F.datum c).primitive.b := by
      rw [(F.realization c).left, (F.realization c).right]
      exact htime
    exact (F.native_anchor_copy hK hχ hq hΛ hζ hband hweak hNK hBG hBV hB hK₁ hbw sX hCc
      c n d (Finset.mem_Icc.mpr ⟨hd, hdn⟩) word t htime' z).symm

end AVRegularity.EntryWeakProofs.WeakInheritedStageMeanFamily
end
end
end

section
section
/-! A genuine weak passage produces its successor uniformly before the flow data are chosen. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_successor_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (bw : ℝ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (cap H K N R sZ : ℕ) (hNK : N ≤ K) (hK₁ : 1 ≤ K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Bout : ℝ, 1 ≤ Bout ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ), K ≤ Dm → ∀ j₀ (G G' : GenStage D (fun _ => ℝ) Dm bw j₀),
      ∀ (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ),
      Mn.N = N → Mn.sZ = sZ → N + Din ≤ K →
      IsWeakPassage D P Mn rW Din G G' → G.HasTags P → G'.HasTags P →
      G.maxOrderBound K → G'.maxOrderBound K →
      (∀ h (_π : StagePath G h), h ≤ R) →
      ∀ minBase Hstage, M₀ ≤ minBase → weakInheritedPrimitiveMenuOrder H K N R + K + 1 ≤ Hstage →
      IndependentWeakStageFluxProduction G minBase (cap + 1) Hstage B →
      Nonempty (IndependentWeakStageFluxProduction G' minBase cap H Bout) := by
  obtain ⟨χi, BGi, BVi, hχi, hBGi, hBVi, Ei, Mi, hMi, hi⟩ :=
    uniform_weak_stage_inherited_mean_family α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ
      (cap + 1) H K N R sZ hNK hK₁ B hB
  obtain ⟨χe, BGe, BVe, hχe, _hBGe, _hBVe, Ee, Me, hMe, he⟩ :=
    uniform_weak_stage_eddy_mean_family α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ (cap + 1) H N sZ
  obtain ⟨Mg, hMg, hg⟩ := uniform_weak_stage_step_geometry
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw hbw cap (H + K)
  let Bmean := Ei.budget + Ee.budget + 1
  have hEi := Ei.budget_nonneg
  have hEe := Ee.budget_nonneg
  have hBmean : 0 ≤ Bmean := by dsimp only [Bmean]; positivity
  let C := weakStageTransferJetMenu cap (H + K)
  have hC : 0 ≤ C := (weakStageTransferJetMenu_one_le cap (H + K)).trans' (by norm_num)
  let Bout := weakPiolaProductionMenuBudget H (H + K) K C
    (H.factorial * Bmean * (1 + (2 * Real.pi) ^ (H + 1)) ^ H)
  have hBout : 1 ≤ Bout := weakPiolaProductionMenuBudget_one_le _ _ _ _ _ hC
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hBmean) (pow_nonneg (by positivity) _))
  let M₀ := Mi + Me + Mg
  have hi₀ : Mi ≤ M₀ := by dsimp only [M₀]; omega
  have he₀ : Me ≤ M₀ := by dsimp only [M₀]; omega
  have hg₀ : Mg ≤ M₀ := by dsimp only [M₀]; omega
  refine ⟨Bout, hBout, M₀, hMi.trans hi₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD j₀ G G' P Mn rW Din
    hN hsZ hDin hp htG htG' hKG hKG' hpath minBase Hstage hbase hH S
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hq' : 1 < D.q := by rw [hDq]; exact hq.1
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ' hband D.term).le
  have hε : ∀ i, 0 < D.eps i := fun _ => Construction.Stream.ocEpsilon_pos hΛ₁
  have hlevel : Mg ≤ G'.level := by have := hp.1; have := hp.2.1; omega
  have geo := hg D hDα hDq hDΛ hDζ hstream j₀ G'.level minBase hlevel (hg₀.trans hbase)
  have hsrc v u γ := weakPassage_produced_source_means hΛ₁ hζ' hband P Mn rW Din hp htG' htG
    (minBase := minBase) (cap := cap) (H := H) (B := Bmean)
    (by
      intro src Cc Cc0 hv hCc hCc0
      cases src with
      | inherited w h π n =>
        have hh : h ∈ Finset.Icc 1 R := Finset.mem_Icc.mpr ⟨hv.2.1, hpath h π⟩
        have hCc' : (WeakSource.inherited w h π n).IsLiftFamily Mn.sX sZ N
            (D.eps (G.level - 1)) Cc := by simpa only [hN, hsZ] using hCc
        have hlift (p : OddSlot) (A : RealChain) (hA : IsAdmissibleChain D bw j₀ G.level p.1 A) := hCc' p.1 A ⟨hA, p.2⟩
        obtain ⟨F⟩ := hi D (hi₀.trans hterm) hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G
          hp.1 hKG minBase Hstage (hi₀.trans hbase) hH S h π hh Mn.sX Cc hlift
        have hn : n ∈ Finset.Icc 2 K := Finset.mem_Icc.mpr ⟨hv.2.2.1, hv.2.2.2.trans (by rw [hN]; exact hDin)⟩
        obtain ⟨M⟩ := F.toMeanArrayProduction P htG hKG (fun r Y hY => (hχi r).2.2.1 Y hY)
          hq' hΛ' hζ' hband hp.1 hNK ((show (0 : ℝ) ≤ 1 by norm_num).trans hBGi) hBVi hB hK₁ hbw₁ Mn.sX hlift ⟨n, hn⟩
        let A := weakInheritedMeanArray_sourceReadout w h π n Cc Cc0 M
        exact ⟨A.enlargeBudget (weakSourceMeanWeight_nonneg P htG (.inherited w h π n)) hκ hε
          Bmean (by dsimp only [Bmean]; linarith [Ee.budget_nonneg])⟩
      | eddy v w n =>
        have hz (p : OddSlot) (A : RealChain) (hA : IsAdmissibleChain D bw j₀ G.level p.1 A) := hCc0 p.1 A p.2 hA
        have hz' : ∀ p : OddSlot, ∀ A, IsAdmissibleChain D bw j₀ G.level p.1 A →
            IsLiftSequence (familyLiftData (Dm := Dm) D G.level p.1 A (D.eps (G.level - 1))
              (fun _ _ _ => [])) Mn.sX sZ (D.slotStart G.level p.1 / D.cellScaleSq G.level)
              ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
              N 0 (Cc0 p.1 A) := by simpa only [hN, hsZ] using hz
        obtain ⟨F⟩ := he D (he₀.trans hterm) hDα hDq hDΛ hDζ hstream hband bw j₀ G.level minBase
          (he₀.trans hbase) hp.1 Dm Mn.sX Cc0 hz'
        have hn : n ∈ Finset.Icc 2 (N + 1) := by rw [hN] at hv; exact Finset.mem_Icc.mpr ⟨hv.2.2.1, hv.2.2.2⟩
        obtain ⟨M⟩ := F.toMeanArrayProduction (fun r Y hY => (hχe r).2.2.1 Y hY)
          hq' hΛ' hζ' hbw₁ hband hp.1 Dm Mn.sX hz' ⟨n, hn⟩
        let A := weakEddyMeanArray_sourceReadout v w n Cc Cc0 M
        exact ⟨A.enlargeBudget (sq_nonneg _) hκ hε Bmean
          (by dsimp only [Bmean]; linarith [Ei.budget_nonneg])⟩) v u γ
  let src v u γ := Classical.choice (hsrc v u γ)
  exact independentWeakStageFluxProduction_of_producedMeans hq' hΛ' hζ' hband hbw hbw₁
    hBmean hC hKG' le_rfl geo src

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite backward assembly constructs every reserve from the empty root with constants before data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_backward_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (bw : ℝ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (length cap H K N R sZ : ℕ) (hNK : N ≤ K) (hK₁ : 1 ≤ K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ), K ≤ Dm → ∀ j₀ (stage : ℕ → GenStage D (fun _ => ℝ) Dm bw j₀),
      ∀ (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ → ℕ), Mn.N = N → Mn.sZ = sZ →
      (∀ i, i < length → N + Din i ≤ K) →
      (∀ i, i < length → IsWeakPassage D P Mn rW (Din i) (stage (i + 1)) (stage i)) →
      (∀ i, i ≤ length → (stage i).HasTags P) →
      (∀ i, i ≤ length → (stage i).maxOrderBound K) →
      (∀ i, i ≤ length → ∀ h (_π : StagePath (stage i) h), h ≤ R) →
      ∀ top r, IsWeakRoot top r (stage length) →
      ∀ minBase, M₀ ≤ minBase →
      Nonempty (IndependentWeakStageFluxProduction (stage 0) minBase cap H B) := by
  induction length generalizing cap H with
  | zero =>
      refine ⟨1, le_rfl, 2, le_rfl, ?_⟩
      intro D _ _ _ _ _ _ _ Dm _ j₀ stage P Mn rW Din _ _ _ _ _ _ _ top r hroot minBase _
      exact independentWeakStageFluxProduction_root (stage 0) top r hroot minBase cap H 1
  | succ length ih =>
      let Hfine := weakInheritedPrimitiveMenuOrder H K N R + K + 1
      obtain ⟨Bfine, hBfine, Mf, hMf, hf⟩ := ih (cap + 1) Hfine
      obtain ⟨B, hB, Ms, hMs, hs⟩ := uniform_weak_stage_successor_production
        α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw hbw hbw₁ cap H K N R sZ hNK hK₁
        Bfine ((show (0 : ℝ) ≤ 1 by norm_num).trans hBfine)
      let M₀ := Mf + Ms
      have hMf₀ : Mf ≤ M₀ := by dsimp only [M₀]; omega
      have hMs₀ : Ms ≤ M₀ := by dsimp only [M₀]; omega
      refine ⟨B, hB, M₀, hMf.trans hMf₀, ?_⟩
      intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD j₀ stage P Mn rW Din
        hN hsZ hDin hp ht hK hpath top r hroot minBase hbase
      obtain ⟨S⟩ := hf D (hMf₀.trans hterm) hDα hDq hDΛ hDζ hstream hband Dm hKD j₀
        (fun i => stage (i + 1)) P Mn rW (fun i => Din (i + 1)) hN hsZ
        (fun i hi => hDin (i + 1) (by omega))
        (fun i hi => hp (i + 1) (by omega))
        (fun i hi => ht (i + 1) (by omega))
        (fun i hi => hK (i + 1) (by omega))
        (fun i hi => hpath (i + 1) (by omega)) top r hroot minBase (hMf₀.trans hbase)
      exact hs D (hMs₀.trans hterm) hDα hDq hDΛ hDζ hstream hband Dm hKD j₀
        (stage 1) (stage 0) P Mn rW (Din 0) hN hsZ (hDin 0 (by omega))
        (hp 0 (by omega)) (ht 1 (by omega)) (ht 0 (by omega))
        (hK 1 (by omega)) (hK 0 (by omega)) (hpath 1 (by omega)) minBase Hfine
        (hMs₀.trans hbase) le_rfl S

end AVRegularity.EntryWeakProofs
end
end

section
/-! One finite common budget produces all actual output stages of every supplied weak menu. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_construction_flux_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (bw : ℝ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (J N Rw sZ H : ℕ) (hJ : 1 ≤ J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ), 1 + J * N ≤ Dm → ∀ j₀ (stage : ℕ → GenStage D (fun _ => ℝ) Dm bw j₀),
      ∀ (P : ProvParams) (Mn : WeakMenu) (M r : ℕ) (rW : ℝ),
      Mn.N = N → Mn.R = Rw → Mn.sZ = sZ →
      IsWeakConstruction D P Mn M J rW r stage →
      ∀ minBase, M₀ ≤ minBase → ∀ i, M ≤ i → i ≤ M + J →
      Nonempty (IndependentWeakStageFluxProduction (stage i) minBase 0 H B) := by
  let K := 1 + J * N
  have hNK : N ≤ K := by
    have hm := Nat.mul_le_mul_right N hJ
    simpa only [one_mul] using hm.trans (Nat.le_add_left _ _)
  have hex (j : Fin (J + 1)) := uniform_weak_stage_backward_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw hbw hbw₁ j.val 0 H K N (J * Rw) sZ hNK
    (by dsimp only [K]; omega)
  choose Bs hBs Ms hMs prod using hex
  let B := ∑ j : Fin (J + 1), Bs j
  let M₀ := ∑ j : Fin (J + 1), Ms j
  have hBj (j : Fin (J + 1)) : Bs j ≤ B :=
    Finset.single_le_sum (fun k _ => (show (0 : ℝ) ≤ 1 by norm_num).trans (hBs k)) (Finset.mem_univ j)
  have hMj (j : Fin (J + 1)) : Ms j ≤ M₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine ⟨B, (hBs 0).trans (hBj 0), M₀, (hMs 0).trans (hMj 0), ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD j₀ stage P Mn M r rW hN hR hsZ hc minBase hbase i hi hit
  let j : Fin (J + 1) := ⟨M + J - i, by omega⟩
  have hh (k : ℕ) (hk : k < j.val) :
      N + (1 + (M + J - (i + k + 1)) * Mn.N) ≤ K := by
    have hm := Nat.mul_le_mul_right N (show M + J - (i + k + 1) + 1 ≤ J by dsimp only [j] at hk; omega)
    rw [Nat.add_mul, one_mul] at hm
    rw [hN]
    dsimp only [K]
    omega
  have htop : i + j.val = M + J := by dsimp only [j]; omega
  obtain ⟨S⟩ := prod j D ((hMj j).trans hterm) hDα hDq hDΛ hDζ hstream hband Dm hKD j₀
    (fun k => stage (i + k)) P Mn rW (fun k => 1 + (M + J - (i + k + 1)) * Mn.N)
    hN hsZ hh
    (fun k hk => by
      have hp := (hc.2.2 (i + k + 1) (by omega) (by dsimp only [j] at hk; omega)).1
      have he : i + k + 1 - 1 = i + k := by omega
      rw [he] at hp
      simpa only [Nat.add_assoc] using hp)
    (fun k hk => weakConstruction_stage_hasTags P Mn M J r rW hc (i + k) (by omega)
      (by dsimp only [j] at hk; omega))
    (fun k hk => by
      have hb := weakConstruction_stage_maxOrderBound P Mn M J r rW hc (i + k) (by omega)
        (by dsimp only [j] at hk; omega)
      simpa only [hN] using hb)
    (fun k hk h π => by
      have hb := weakConstruction_path_length_bound P Mn M J r rW stage hc (i + k) (by omega)
        (by dsimp only [j] at hk; omega) h π
      simpa only [hR] using hb)
    (M + J) r (by simpa only [htop] using hc.2.1) minBase ((hMj j).trans hbase)
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ' hband D.term).le
  simpa only [Nat.add_zero] using
    (show Nonempty (IndependentWeakStageFluxProduction (stage (i + 0)) minBase 0 H B) from
      ⟨S.enlargeBudget hκ (fun _ => Construction.Stream.ocEpsilon_pos hΛ₁) B (hBj j)⟩)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine production and physical assembly give the universal-menu dimensional coefficient bound. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_physical_coefficient_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (bw : ℝ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (J N Rw sZ Ks : ℕ) (hJ : 1 ≤ J) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ), 1 + J * N ≤ Dm → ∀ j₀ (stage : ℕ → GenStage D (fun _ => ℝ) Dm bw j₀),
      ∀ (P : ProvParams) (M sX r : ℕ) (η rW : ℝ), D.term = M →
      IsWeakConstruction D P (⟨N, Rw, sX, sZ, η, M + J⟩ : WeakMenu) M J rW r stage →
      ∀ i, M ≤ i → i < M + J →
      ∀ (v u : CompIn (stage i).comps) (γ : (stage i).fam.Γ v u) (d k : ℕ),
      2 ≤ d → d ≤ ((stage i).fam.identity v u γ).maxOrder → k ≤ Ks → ∀ t₀ t₁ : ℝ,
      coefficientSeminorm (D.eps i) k t₀ t₁ ((stage i).physCoeff v u γ d) ≤
        ENNReal.ofReal (CK * ((stage i).fam.identity v u γ).record.size * D.κ M *
          D.eps (i + 1) ^ (((stage i).fam.identity v u γ).maxOrder - 2) *
          D.eps i ^ ((d : ℝ) - (((stage i).fam.identity v u γ).maxOrder : ℝ))) := by
  obtain ⟨B, hB, Mb, hMb, hprod⟩ := uniform_weak_construction_flux_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw hbw hbw₁ J N Rw sZ Ks hJ
  obtain ⟨Ma, hMa, hanchor⟩ := weak_anchor_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ
  let K := 1 + J * N
  let C := weakBaseChartJetBudget (Ks + K + 1)
  have hC : 1 ≤ C := weakBaseChartJetBudget_ge_one _
  let Cmat := positiveJetCompositionBudget (Ks + K) C
  have hCmat : 1 ≤ Cmat := positiveJetCompositionBudget_ge_one _ _ hC
  let Bsource := Ks.factorial * B * C ^ Ks
  have hBs : 0 ≤ Bsource := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hB))
    (pow_nonneg (zero_le_one.trans hC) _)
  let price := weakPhysicalPiolaMenuPrice Ks K (Ks + K) Cmat Bsource
  have hprice : 0 ≤ price := zero_le_one.trans
    (weakPhysicalPiolaMenuPrice_one_le _ _ _ _ _ (zero_le_one.trans hCmat) hBs)
  let CK := ((Ks + 1 : ℕ) * (2 : ℝ) ^ Ks) * price
  let M₀ := Mb + Ma + 2
  refine ⟨CK, mul_nonneg (by positivity) hprice, M₀, ?_, ?_⟩
  · dsimp only [M₀]; omega
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD j₀ stage P M sX r η rW hDM hc
    i hi hit v u γ d k hd hdn hk t₀ t₁
  let Mn : WeakMenu := ⟨N, Rw, sX, sZ, η, M + J⟩
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hq' : 1 < D.q := by rw [hDq]; exact hq.1
  have hε : ∀ j, 0 < D.eps j := fun _ => Construction.Stream.ocEpsilon_pos hΛ₁
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ' hband D.term).le
  have hl := weakConstruction_level P Mn M J r rW stage hc i hi (Nat.le_of_lt hit)
  have hnatural := weakConstruction_output_natural P Mn M J r rW stage hc i hi hit
  have htags := weakConstruction_stage_hasTags P Mn M J r rW hc i hi (Nat.le_of_lt hit)
  have horder := weakConstruction_stage_maxOrderBound P Mn M J r rW hc i hi (Nat.le_of_lt hit)
  have hp := (hc.2.2 (i + 1) (by omega) (by omega)).1
  rw [Nat.add_sub_cancel] at hp
  have hMbterm : Mb ≤ D.term := by dsimp only [M₀] at hterm; omega
  have hMbbase : Mb ≤ D.term - 1 := by dsimp only [M₀] at hterm; omega
  obtain ⟨S⟩ := hprod D hMbterm hDα hDq hDΛ hDζ hstream hband Dm hKD j₀ stage P Mn M r rW
    rfl rfl rfl hc (D.term - 1) hMbbase i hi (Nat.le_of_lt hit)
  have hbase : D.term - 1 ≤ (stage i).level - 1 := by rw [hl, hDM]; omega
  have hsmall : ocTauPP D.α D.q D.Λ (stage i).level ≤
      2 ^ (-25 : ℤ) * (ocA D.α D.q D.Λ ((stage i).level - 1))⁻¹ := by
    rw [hl, hDα, hDq, hDΛ]
    exact (hanchor i (by dsimp only [M₀] at hterm; omega)).1
  have hscale : D.eps (stage i).level ≤ D.eps ((stage i).level - 1) :=
    EntryScales.epsilon_antitone hq' hΛ' (Nat.sub_le _ _)
  have hchart (t : ℝ) (p : OddSlot) (ht : t ∈ ((stage i).fam.piece p).output) j (hj : 1 ≤ j) (hjN : j ≤ Ks + K + 1) inverse y :=
    weak_natural_piece_chart_jets D s (by rw [hDα]; exact hα₀) (by rw [hDα]; exact hα₁)
      hs₀ (by rw [hDα]; exact hs₁) (by rw [hDα, hDq]; exact hq) hΛ' hζ'
      (by rw [hDα, hDq, hDΛ, hDζ]; exact hstream) (M + J) (stage i).level
      (by rw [hl]; dsimp only [M₀] at hterm; omega) p.1 ((stage i).fam.piece p)
      (hnatural.1 p) hsmall hscale t ht (Ks + K + 1) j hj hjN inverse y
  let dim := ((stage i).fam.identity v u γ).record.size *
    (D.κ D.term * D.eps ((stage i).level + 1) ^ (((stage i).fam.identity v u γ).maxOrder - 2) *
      D.eps (stage i).level ^ ((d : ℝ) - (((stage i).fam.identity v u γ).maxOrder : ℝ)))
  have hdim : 0 ≤ dim := mul_nonneg ((stage i).fam.identity v u γ).record.size_nonneg
    (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _)) (Real.rpow_pos_of_pos (hε _) _).le)
  have hs := weak_constituentPhysical_uniform_coefficientSeminorm (stage i).fam
    (D.kap (stage i).level) (D.eps (stage i).level) (D.eps ((stage i).level - 1)) (stage i).actual
    v u γ d Ks k hk (D.eps (stage i).level) (dim * price) (hε _) (mul_nonneg hdim hprice)
    (fun t p _ => S.physical_piece_contDiff hq' hΛ' hζ' hband hbw₁ (zero_le_one.trans hB)
      P Mn rW _ hp htags (M + J) hnatural hbase v u γ d hd Ks le_rfl t p)
    (fun t p ht j hj y => S.physical_piece_jet_le hq' hΛ' hζ' hband hbw₁ (zero_le_one.trans hB)
      P Mn rW _ hp htags (M + J) hnatural hbase K horder Ks le_rfl C hC v u γ d hd hdn t p
      (fun j hj hjN y => hchart t p ht j hj hjN false y)
      (fun j hj hjN y => hchart t p ht j hj hjN true y) j hj y) t₀ t₁
  calc
    _ = coefficientSeminorm (D.eps (stage i).level) k t₀ t₁ ((stage i).physCoeff v u γ d) := by rw [hl]
    _ ≤ ENNReal.ofReal (((Ks + 1 : ℕ) * (2 : ℝ) ^ Ks) * (dim * price)) := hs
    _ = _ := by
      congr 1
      dsimp only [CK, dim]
      rw [congrArg D.eps hl, congrArg (fun j => D.eps (j + 1)) hl, hDM]
      ring

end AVRegularity.EntryWeakProofs
end
end
end

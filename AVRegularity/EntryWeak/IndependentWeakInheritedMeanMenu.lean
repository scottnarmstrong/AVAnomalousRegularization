-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.IndependentActualCoarseEddyCopy
public import AVRegularity.EntryWeak.WeakStageSampledReferenceField
import AVRegularity.Proofs.GenSem.ChainMetric

section
section
/-! Uniform actual Eddy production uses one coherent choice across all primitive reference charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_coherent_eddy_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H N sZ : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z →
          χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧
      ∃ E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0,
      ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      M ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → ∀ hdepth : A.children.length ≤ J, D.term < A.ctxLevel →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps A.lastLevel → ∀ Dm sX,
      ∀ Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ),
      (∀ B, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot B →
        IsLiftSequence (familyLiftData (Dm := Dm) D A.ctxLevel A.slot B ρ (fun _ _ _ => [])) sX sZ
          (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
          N 0 (Cc B)) →
      ∃ x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * A.children.length)
          H N N 0 0 sZ BG BV 0,
        x.response = D.weakPe A.ctxLevel ∧
        x.data.primitive.a = D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel ∧
        x.data.primitive.b =
          (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel ∧
        x.data.primitive.U = actualIndependentCoarseNativeCarrier D A bw ∧
        x.data.primitive.G = actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length)
          x.data.primitive.a x.data.primitive.b ∧
        x.data.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot ∧
        x.data.primitive.edge = (fun _ _ _ => []) ∧
        x.data.primitive.M = (fun _ _ => 0) ∧
        x.data.primitive.Cc = independentCarrierCoefficientExtension
          (actualIndependentCoarseStoredCarrier D A bw)
          (fun P => Cc (actualIndependentCoarseParameterChain D A P)) ∧
        x.data.translations = independentFreshPhaseTranslations A.children.length ∧
        ∀ n hn hnN m hm β,
          ∃ Q : IndependentParameterSourceReserve H
            (E.field ⟨A.children.length, Nat.lt_succ_of_le hdepth⟩ x n hn hnN m hm β 0 0),
            (∀ j ≤ H, Q.budget j ≤ D.weakPe A.ctxLevel ^ 2 * E.budget) ∧
            (∀ t ∈ Icc x.data.primitive.a x.data.primitive.b,
              ∀ Y ∈ actualIndependentCoarseNativeCarrier D A bw, ∀ z k,
              E.field ⟨A.children.length, Nat.lt_succ_of_le hdepth⟩ x n hn hnN m hm β 0 0 t z Y k =
                fieldCellMean (fun w =>
                  ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot t w k •
                    Cc (actualIndependentCoarseParameterChain D A
                      (independentStoredParameterProjection (4 * A.children.length) Y))
                      0 n m β t (independentIntrinsicSlowProjection (4 * A.children.length) Y) w 0 0 1)) ∧
            (∀ δ ∈ independentFreshPhaseTranslations A.children.length,
              IndependentSourceTranslationInvariant δ
                (E.field ⟨A.children.length, Nat.lt_succ_of_le hdepth⟩ x n hn hnN m hm β 0 0)) := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, M, hM, hprod⟩ :=
    uniform_actual_independent_coarse_positive_datum_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J H N sZ
  let E := independentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0
    le_rfl (zero_le_one.trans hBG) hBV le_rfl
  refine ⟨χ, BG, BV, hχ, hBG, hBV, E, M, hM, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband A hbase hdepth hweak bw j₀ hA
    ρ hρ hρle Dm sX Cc hc
  obtain ⟨x, hresponse, ha, hb, hU, hG, hv, he, hmatrix, hCc, hphase⟩ :=
    hprod D hterm hDα hDq hDΛ hDζ hstream hband A hbase hdepth hweak bw j₀ hA
      ρ hρ hρle Dm sX Cc hc
  refine ⟨x, hresponse, ha, hb, hU, hG, hv, he, hmatrix, hCc, hphase, ?_⟩
  intro n hn hnN m hm β
  obtain ⟨Q, hQ, hcopy, hperiod⟩ := independent_actual_coarse_eddy_copy
    J H N sZ BG BV E D A bw hdepth Cc x hresponse ha hb hU hv hCc hphase n hn hnN m hm β
  refine ⟨Q, hQ, ?_, hperiod⟩
  simpa only [ha, hb] using hcopy

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite calibration identifies the produced inherited mean field with its literal native array. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H T D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteMeanFluxCoefficient_reconstructed_copy
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S (H + D + 2) B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hT : H ≤ T) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (m : ℕ) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) (out inp : ι) (k : Fin 2) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    independentMeanFluxCoefficientSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
      1 S.G S.v (independentFiniteLiftFields S P) hh n m α lam out inp k t z Y =
      positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k m α t
        (independentIntrinsicSlowProjection d Y) z out inp 1 := by
  dsimp only
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
  let C := positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k
  have hsym (β : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) : C m (β ∘ σ) = C m β := by
    exact positiveMeanFluxCoefficient_intrinsic_perm Q (independentFiniteNativeCoefficients S P Y)
      hh n k m (independentFiniteNativeCoefficients_perm S P Y hh (n - 1) m) β σ
  have htest (p : Fin (m + 1) × Fin (n - 1 + 1)) :
      fieldCellMean (fun z => independentLiftFluxSource S.edge S.edgeField
        (independentIntrinsicSlowEmbedding d)
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) 1 S.G S.v
        (independentFiniteLiftFields S P) hh n out inp k t z Y) =
      normalizedLiftTestField C (n - 1)
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) inp out 1 t
        (independentIntrinsicSlowProjection d Y) z := by
    rw [independentFiniteLiftFluxMean_reconstructed_copy S P hB hD hT hBG hBV hBE hh n hn hhpos]
    exact (independentFiniteNativeMeanFlux_normalized_apply S P hB hD (by omega) Y hh n hn hhpos
      (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) inp k t
      (independentIntrinsicSlowProjection d Y) z out).symm
  unfold independentMeanFluxCoefficientSource
  simp_rw [htest]
  exact liftCalibration_synthesis (n - 1) m hm C lam hlam hsym α t
    (independentIntrinsicSlowProjection d Y) z out inp 1

end AVRegularity.EntryWeakProofs
end
end

section
/-! The original localized family has its literal scaled physical mean coefficient array. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {dP T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteOriginalMeanFlux_scaled_fluxCoeff
    (S : IndependentLiftPrimitiveData ι dP T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + dP)) (hY : Y ∈ S.U)
    (hD : 1 ≤ D) (hbase : D ≤ base) (hh n : ℕ) (hhh : hh ≤ R) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (d : ℕ) (hd : d - 1 ≤ n - 1) (α : DerivativeWord2 (d - 1))
    (a ρ : ℝ) (hρ : ρ ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc S.a S.b) (y : Vec 2)
    (hpoint : ρ⁻¹ • y = independentIntrinsicSlowProjection dP Y) (v u : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding dP X + independentIntrinsicSliceOffset dP Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y)⟩
    fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q
      (S.Cc (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single u (f (ρ • X)))
        hh n t (ρ⁻¹ • W) z k) v) d α y =
      fun k => (a * ρ ^ (d - 1)) *
        positiveMeanFluxCoefficient Q (S.Cc (independentStoredParameterProjection dP Y)) hh n k
          (d - 1) α t (ρ⁻¹ • y) 0 v u 1 := by
  dsimp only
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding dP X + independentIntrinsicSliceOffset dP Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y)⟩
  let f : Vec 2 → ι → ℝ := fun X => Pi.single u (∏ j : Fin (d - 1), (ρ • X - y) (α j))
  have he : f = fun X => ρ ^ (d - 1) • Providers.GenSem.monoField u (ρ⁻¹ • y) α X := by
    funext X
    dsimp only [f]
    rw [scaled_word_monomial (d - 1) α ρ hρ y X]
    simp only [Providers.GenSem.monoField, ← Pi.single_smul, smul_eq_mul]
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [he]
    exact (Providers.GenSem.contDiff_monoField u (ρ⁻¹ • y) α).const_smul _
  funext k
  unfold fluxCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  have hmean := independentFiniteOriginalMeanFlux_smooth_apply S P hB hD hbase Y hY
    hh n hhh hn hhpos f hf k t ht 0 v
  change ((d - 1).factorial : ℝ)⁻¹ * (a * fieldCellMean
    (fun z => liftFluxX Q (S.Cc (independentStoredParameterProjection dP Y)) (fun _ => f)
      hh n t (ρ⁻¹ • y) z k) v) = _
  rw [hpoint] at he
  rw [hpoint, ← hmean, he, scalarLiftApply_coarse_smul _ _ _
    (Providers.GenSem.contDiff_monoField u (independentIntrinsicSlowProjection dP Y) α),
    Providers.GenSem.liftApply_monoField hd]
  · have hfact : (((d - 1).factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 1)
    field_simp
  · intro σ β
    exact positiveMeanFluxCoefficient_intrinsic_perm Q (S.Cc (independentStoredParameterProjection dP Y)) hh n k
      (d - 1) (S.symmetric (independentStoredParameterProjection dP Y) hh hhh (n - 1) (d - 1)) β σ

end AVRegularity.EntryWeakProofs
end
end

section
/-! Localized actual histories read the produced physical mean array through their genuine native primitive copies. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {dP T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentPhysicalMeanFlux_native_copy_on
    (S : IndependentLiftPrimitiveData ι dP T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + dP)) (hY : Y ∈ S.U)
    (V : Set (Vec dP)) (c : Vec dP → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hCc : S.Cc = independentCarrierCoefficientExtension V c)
    (hP : independentStoredParameterProjection dP Y ∈ V)
    (Ω : Set (Vec 2)) (Q : LiftOperatorData ι (fun _ => ℝ) D) (sX sZ : ℕ)
    (hc : IsLiftSequenceOn Ω Q sX sZ S.a S.b N R (c (independentStoredParameterProjection dP Y)))
    (hη : Q.η = 1) (hv : Q.v = S.v)
    (hD : 1 ≤ D) (hbase : D ≤ base) (hh n : ℕ) (hhh : hh ≤ R)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (d : ℕ) (hd : d - 1 ≤ n - 1) (α : DerivativeWord2 (d - 1))
    (a ρ : ℝ) (hρ : ρ ≠ 0) (t : ℝ) (ht : t ∈ Icc S.a S.b) (y : Vec 2)
    (hpoint : ρ⁻¹ • y = independentIntrinsicSlowProjection dP Y)
    (hG : Q.G t (independentIntrinsicSlowProjection dP Y) = S.G t Y)
    (he : SlowOpenEdgeEq (independentIntrinsicSliceCarrier dP S.U Y) t Q.edge
      (independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y))) (v u : ι) :
    let Q' : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding dP X + independentIntrinsicSliceOffset dP Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y)⟩
    fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q
      (c (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single u (f (ρ • X)))
        hh n t (ρ⁻¹ • W) z k) v) d α y =
      fun k => (a * ρ ^ (d - 1)) *
        positiveMeanFluxCoefficient Q' (S.Cc (independentStoredParameterProjection dP Y)) hh n k
          (d - 1) α t (ρ⁻¹ • y) 0 v u 1 := by
  dsimp only
  let Q' : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding dP X + independentIntrinsicSliceOffset dP Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y)⟩
  have hcopy : fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q
        (c (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single u (f (ρ • X)))
          hh n t (ρ⁻¹ • W) z k) v) d α y =
      fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q'
        (S.Cc (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single u (f (ρ • X)))
          hh n t (ρ⁻¹ • W) z k) v) d α y := by
    unfold fluxCoeff
    apply congrArg (fun F : Vec 2 => ((d - 1).factorial : ℝ)⁻¹ • F)
    funext k
    apply congrArg (fun r : ℝ => a * r)
    apply congrArg (fun F : Vec 2 → ι → ℝ => fieldCellMean F v)
    funext z
    rw [hpoint]
    apply liftFluxX_primitive_point_congr
      (independentIntrinsicSliceCarrier_isOpen dP S.U S.open_carrier Y) Q Q' hη hv _ _ _
      hh n hn t he _ _ (independentIntrinsicSliceCarrier_base dP S.U Y hY) _ z k
    · intro p q hpq m _hm β X _hX w v u
      rw [hCc]
      symm
      exact independentCarrierCoefficientExtension_copy_on V c _ hP Ω Q hc p
        (by rcases hpq with hp | ⟨rfl, _⟩ <;> omega) q m β t ht X w v u
    · change Q.G t (independentIntrinsicSlowProjection dP Y) = S.G t
        (independentIntrinsicSlowEmbedding dP (independentIntrinsicSlowProjection dP Y) +
          independentIntrinsicSliceOffset dP Y)
      rw [independentIntrinsicSliceOffset_base]
      exact hG
  exact hcopy.trans (independentFiniteOriginalMeanFlux_scaled_fluxCoeff S P hB Y hY
    hD hbase hh n hhh hn hhpos d hd α a ρ hρ t ht y hpoint v u)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual positive-response primitive metadata, without extra coefficient assumptions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}

structure WeakStageEddyPrimitiveRealization
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * c.chain.1.children.length)
      H N N 0 0 sZ BG BV 0) : Prop where
  response : x.response = D.weakPe level
  left : x.data.primitive.a = D.slotStart level c.slot.1 / D.cellScaleSq level
  right : x.data.primitive.b =
    (((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level
  carrier : x.data.primitive.U = actualIndependentCoarseNativeCarrier D c.chain.1 bw
  metric : x.data.primitive.G = actualIndependentCoarseScaledExtendedMetric D c.chain.1
    (D.eps (level - 1)) χ x.data.primitive.a x.data.primitive.b
  drift : x.data.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ level (D.kap level) c.slot.1
  edge : x.data.primitive.edge = fun _ _ _ => []
  matrix : x.data.primitive.M = fun _ _ => 0
  coefficients : x.data.primitive.Cc = independentCarrierCoefficientExtension
    (actualIndependentCoarseStoredCarrier D c.chain.1 bw)
    (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P))
  phase : x.data.translations = independentFreshPhaseTranslations c.chain.1.children.length

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The literal Eddy flux reads the coherently produced mean with its exact dimensional factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem weakData_eddyFlux_produced_coefficient (J H N sZ : ℕ) (BG BV : ℝ)
    (E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (hm : D.term < A.ctxLevel) (hslot : Odd A.slot) (bw : ℝ) (hdepth : A.children.length ≤ J)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * A.children.length)
      H N N 0 0 sZ BG BV 0)
    (hresponse : x.response = D.weakPe A.ctxLevel)
    (ha : x.data.primitive.a = D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
    (hb : x.data.primitive.b =
      (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
    (hU : x.data.primitive.U = actualIndependentCoarseNativeCarrier D A bw)
    (hv : x.data.primitive.v =
      ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot)
    (hCc : x.data.primitive.Cc = independentCarrierCoefficientExtension
      (actualIndependentCoarseStoredCarrier D A bw)
      (fun P => Cc (actualIndependentCoarseParameterChain D A P)))
    (hphase : x.data.translations = independentFreshPhaseTranslations A.children.length)
    (n d : ℕ) (hn : 2 ≤ n) (hnN : n - 1 ≤ N) (hd : 1 ≤ d) (hdn : d ≤ n)
    (β : DerivativeWord2 (d - 1)) (Y : Vec (2 + 4 * A.children.length))
    (hY : Y ∈ actualIndependentCoarseNativeCarrier D A bw)
    (ρ : ℝ) (hρ : 0 < ρ) (y : Vec 2)
    (hy : ρ⁻¹ • y = independentIntrinsicSlowProjection (4 * A.children.length) Y)
    (Dm sX : ℕ) (t : ℝ) (ht : (D.cellScaleSq A.ctxLevel)⁻¹ * t ∈ Icc
      (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
      ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel))
    (hseq : IsLiftSequence (familyLiftData (Dm := Dm) D A.ctxLevel A.slot
      (actualIndependentCoarseParameterChain D A
        (independentStoredParameterProjection (4 * A.children.length) Y)) ρ (fun _ _ _ => []))
      sX sZ (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
      ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
      N 0 (Cc (actualIndependentCoarseParameterChain D A
        (independentStoredParameterProjection (4 * A.children.length) Y)))) :
    fluxCoeff (weakEddyFlux D A.ctxLevel ρ
      (familyLiftData (Dm := Dm) D A.ctxLevel A.slot
        (actualIndependentCoarseParameterChain D A
          (independentStoredParameterProjection (4 * A.children.length) Y)) ρ (fun _ _ _ => []))
      (Cc (actualIndependentCoarseParameterChain D A
        (independentStoredParameterProjection (4 * A.children.length) Y))) n t) d β y =
      -(D.κ D.term * D.eps A.ctxLevel ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) •
        E.field ⟨A.children.length, Nat.lt_succ_of_le hdepth⟩ x (n - 1) (by omega)
          hnN (d - 1) (by omega) β 0 0 ((D.cellScaleSq A.ctxLevel)⁻¹ * t) 0 Y := by
  obtain ⟨_, _, hcopy, _⟩ := independent_actual_coarse_eddy_copy J H N sZ BG BV E D A bw
    hdepth Cc x hresponse ha hb hU hv hCc hphase (n - 1) (by omega) hnN (d - 1) (by omega) β
  rw [actualWeakEddyFlux_fluxCoeff D hΛ hζ hband A.ctxLevel hm A.slot hslot
    _ ρ hρ (fun _ _ _ => []) sX sZ N 0 _ _ _ hseq n d hn hd hdn β t ht y]
  funext k
  change -(D.κ D.term * D.eps A.ctxLevel ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) * _ = _
  rw [hy, ← hcopy ((D.cellScaleSq A.ctxLevel)⁻¹ * t) ht Y hY 0 k]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! Coherent positive-response arrays for all bounded actual charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}

structure WeakEddyStageMeanFamily
    (E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0)
    (χ : ∀ r, Vec (2 + 4 * r) → ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) where
  datum : ∀ c : WeakStageProductionContext D bw j₀ level minBase cap,
    IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * c.chain.1.children.length) H N N 0 0 sZ BG BV 0
  realization : ∀ c, WeakStageEddyPrimitiveRealization c (χ c.chain.1.children.length) Cc (datum c)

namespace WeakEddyStageMeanFamily
variable {E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

def array (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (n : Finset.Icc 2 (N + 1)) (d : ℕ) (word : DerivativeWord2 (d - 1)) :=
  weakEddyPhysicalArray E ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩ n
    (F.datum c) D level d word

theorem production (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (n : Finset.Icc 2 (N + 1)) (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (F.array c n d word),
      (∀ k ≤ H, Q.budget k ≤ D.weakPe level ^ 2 *
        (D.κ D.term * D.eps level ^ (n.val - 2) *
          D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)) * E.budget)) ∧
      (∀ δ ∈ independentFreshPhaseTranslations c.chain.1.children.length,
        IndependentSourceTranslationInvariant δ (F.array c n d word)) := by
  obtain ⟨Q, hQ, hphase⟩ := weakEddyPhysicalArray_production E
    ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩ n (F.datum c) D level hκ hε
    (F.realization c).response d word
  refine ⟨Q, hQ, ?_⟩
  intro δ hδ
  exact hphase δ (by rw [(F.realization c).phase]; exact hδ)

end WeakEddyStageMeanFamily
end AVRegularity.EntryWeakProofs
end
end

section
/-! Uniform actual Eddy production uses one coherent choice across all primitive reference charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_eddy_mean_family (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H N sZ : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z →
          χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧
      ∃ E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0,
      ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      M ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ bw j₀ level minBase, M ≤ minBase → D.term < level → ∀ Dm sX,
      ∀ Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ),
      (∀ p : OddSlot, ∀ A, IsAdmissibleChain D bw j₀ level p.1 A →
        IsLiftSequence (familyLiftData (Dm := Dm) D level p.1 A (D.eps (level - 1))
          (fun _ _ _ => [])) sX sZ (D.slotStart level p.1 / D.cellScaleSq level)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)
          N 0 (Cc p.1 A)) →
      Nonempty (WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
        (level := level) (minBase := minBase) E χ Cc) := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, E, M, hM, hprod⟩ :=
    uniform_actual_independent_coarse_coherent_eddy_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J H N sZ
  refine ⟨χ, BG, BV, hχ, hBG, hBV, E, M, hM, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband bw j₀ level minBase hbase hweak Dm sX Cc hc
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hp (c : WeakStageProductionContext D bw j₀ level minBase J) :
      ∃ x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * c.chain.1.children.length)
        H N N 0 0 sZ BG BV 0,
        WeakStageEddyPrimitiveRealization c (χ c.chain.1.children.length) Cc x := by
    let A := c.chain.1
    have hctx : A.ctxLevel = level := c.chain.2.1
    have hslot : A.slot = c.slot.1 := c.chain.2.2.2.2.1
    have hA : IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A := by
      rw [hctx, hslot]
      exact c.chain.2
    have hlast : A.lastLevel = level - 1 := by
      change A.lastLevel + 1 = level at hctx
      omega
    have hCc : ∀ B, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot B →
        IsLiftSequence (familyLiftData (Dm := Dm) D A.ctxLevel A.slot B (D.eps (level - 1))
          (fun _ _ _ => [])) sX sZ (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
          N 0 (Cc c.slot.1 B) := by
      simpa only [hctx, hslot] using hc c.slot
    obtain ⟨x, hresponse, ha, hb, hU, hG, hv, he, hmatrix, hCc', hphase, _hmean⟩ :=
      hprod D hterm hDα hDq hDΛ hDζ hstream hband A (hbase.trans c.base_bound)
        c.depth_bound (by rw [hctx]; exact hweak) bw j₀ hA (D.eps (level - 1))
        (Construction.Stream.ocEpsilon_pos hΛ₁) (by rw [hlast]) Dm sX (Cc c.slot.1) hCc
    refine ⟨x, ?_⟩
    exact ⟨by simpa only [hctx] using hresponse,
      by simpa only [hctx, hslot] using ha,
      by simpa only [hctx, hslot] using hb,
      hU, hG, by simpa only [hctx, hslot] using hv, he, hmatrix, hCc', hphase⟩
  exact ⟨⟨(fun c => Classical.choose (hp c)), fun c => Classical.choose_spec (hp c)⟩⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual Eddy array copies the original zero-edge mean flux. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}
  {E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem native_copy (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < level)
    (Dm sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A, IsAdmissibleChain D bw j₀ level p.1 A →
      IsLiftSequence (familyLiftData (Dm := Dm) D level p.1 A (D.eps (level - 1))
        (fun _ _ _ => [])) sX sZ (D.slotStart level p.1 / D.cellScaleSq level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)
        N 0 (Cc p.1 A))
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (n : Finset.Icc 2 (N + 1)) (d : ℕ) (hd : d ∈ Finset.Icc 2 n.val)
    (word : DerivativeWord2 (d - 1)) (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw
      (D.eps (level - 1)) j₀ level c.slot.1)
    (t : ℝ) (ht : (D.cellScaleSq level)⁻¹ * t ∈ Icc
      (D.slotStart level c.slot.1 / D.cellScaleSq level)
      ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)) (z : Vec 2) :
    fluxCoeff (weakEddyFlux D level (D.eps (level - 1))
      (familyLiftData (Dm := Dm) D level c.slot.1 (c.atParameter Y hY).1
        (D.eps (level - 1)) (fun _ _ _ => []))
      (Cc c.slot.1 (c.atParameter Y hY).1) n.val t) d word
      (D.eps (level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) =
      F.array c n d word t z Y := by
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hx := F.realization c
  have ha : (F.datum c).data.primitive.a =
      D.slotStart c.chain.1.ctxLevel c.chain.1.slot / D.cellScaleSq c.chain.1.ctxLevel := by
    simpa only [hctx, hslot] using hx.left
  have hb : (F.datum c).data.primitive.b =
      (((c.chain.1.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ c.chain.1.ctxLevel) /
        D.cellScaleSq c.chain.1.ctxLevel := by
    simpa only [hctx, hslot] using hx.right
  have hv : (F.datum c).data.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ
      c.chain.1.ctxLevel (D.kap c.chain.1.ctxLevel) c.chain.1.slot := by
    simpa only [hctx, hslot] using hx.drift
  have hr : (F.datum c).response = D.weakPe c.chain.1.ctxLevel := by
    simpa only [hctx] using hx.response
  have hseq : IsLiftSequence (familyLiftData (Dm := Dm) D c.chain.1.ctxLevel c.chain.1.slot
      (c.atParameter Y hY).1 (D.eps (level - 1)) (fun _ _ _ => [])) sX sZ
      (D.slotStart c.chain.1.ctxLevel c.chain.1.slot / D.cellScaleSq c.chain.1.ctxLevel)
      ((((c.chain.1.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ c.chain.1.ctxLevel) /
        D.cellScaleSq c.chain.1.ctxLevel) N 0 (Cc c.slot.1 (c.atParameter Y hY).1) := by
    simpa only [hctx, hslot] using hCc c.slot (c.atParameter Y hY).1 (c.atParameter Y hY).2
  have htime : (D.cellScaleSq c.chain.1.ctxLevel)⁻¹ * t ∈ Icc
      (D.slotStart c.chain.1.ctxLevel c.chain.1.slot / D.cellScaleSq c.chain.1.ctxLevel)
      ((((c.chain.1.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ c.chain.1.ctxLevel) /
        D.cellScaleSq c.chain.1.ctxLevel) := by
    simpa only [hctx, hslot] using ht
  have hcopy := weakData_eddyFlux_produced_coefficient cap H N sZ BG BV E D hΛ hζ hband
    c.chain.1 (by rw [hctx]; exact hweak) (by rw [hslot]; exact c.slot.property)
    bw c.depth_bound (Cc c.slot.1) (F.datum c) hr ha hb hx.carrier hv hx.coefficients hx.phase
    n.val d (Finset.mem_Icc.mp n.property).1 (by have := (Finset.mem_Icc.mp n.property).2; omega)
    (by have := (Finset.mem_Icc.mp hd).1; omega) (Finset.mem_Icc.mp hd).2 word Y hY.1.1
    (D.eps (level - 1)) (Construction.Stream.ocEpsilon_pos hΛ) _
    (inv_smul_smul₀ (Construction.Stream.ocEpsilon_pos hΛ).ne' _) Dm sX t htime hseq
  simp only [hctx, hslot] at hcopy
  have he : F.array c n d word =
      independentProducedFluxSource
        (D.κ D.term * D.eps level ^ (n.val - 2) *
          D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)))
        (fun tt => (D.cellScaleSq level)⁻¹ * tt)
        (fun tt _ W => E.field ⟨c.chain.1.children.length, Nat.lt_succ_of_le c.depth_bound⟩
          (F.datum c) (n.val - 1) (by have := (Finset.mem_Icc.mp n.property).1; omega)
          (by have := (Finset.mem_Icc.mp n.property).2; omega) (d - 1)
          (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) word 0 0 tt 0 W) := by
    unfold array weakEddyPhysicalArray
    exact dite_eq_left hd
  rw [he]
  exact hcopy

end AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
end
end

section
/-! The actual Eddy array copies the original zero-edge mean flux. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap H N sZ : ℕ} {BG BV : ℝ}
  {E : IndependentPositiveEddyDepthProducer (Fin 1) cap H N N 0 0 sZ BG BV 0}
  {χ : ∀ r, Vec (2 + 4 * r) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

theorem native_anchor_copy (F : WeakEddyStageMeanFamily (D := D) (bw := bw) (j₀ := j₀)
    (level := level) (minBase := minBase) E χ Cc)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hbw : bw ≤ 1 / 10000)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hweak : D.term < level)
    (Dm sX : ℕ)
    (hCc : ∀ p : OddSlot, ∀ A, IsAdmissibleChain D bw j₀ level p.1 A →
      IsLiftSequence (familyLiftData (Dm := Dm) D level p.1 A (D.eps (level - 1))
        (fun _ _ _ => [])) sX sZ (D.slotStart level p.1 / D.cellScaleSq level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)
        N 0 (Cc p.1 A))
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (n : Finset.Icc 2 (N + 1)) (d : ℕ) (hd : d ∈ Finset.Icc 2 n.val)
    (word : DerivativeWord2 (d - 1))
    (t : ℝ) (ht : (D.cellScaleSq level)⁻¹ * t ∈ Icc
      (D.slotStart level c.slot.1 / D.cellScaleSq level)
      ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ level) / D.cellScaleSq level)) (z : Vec 2) :
    fluxCoeff (weakEddyFlux D level (D.eps (level - 1))
      (familyLiftData (Dm := Dm) D level c.slot.1 c.chain.1
        (D.eps (level - 1)) (fun _ _ _ => []))
      (Cc c.slot.1 c.chain.1) n.val t) d word
      0 =
      F.array c n d word t z
        (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0
          (independentFreshCoarseChainPacking D c.chain.1)) := by
  let Y := independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0
    (independentFreshCoarseChainPacking D c.chain.1)
  have hY := actualIndependentCoarseProductionCarrier_native_anchor D hq hΛ hζ c.chain.1 bw
    (D.eps (level - 1)) hbw j₀ level c.slot.1 c.chain.2
  have hctx : c.atParameter Y hY = c.chain := by
    apply Subtype.ext
    change actualIndependentCoarseParameterChain D c.chain.1
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y) = c.chain.1
    rw [independentIntrinsicParameterPacking_stored]
    exact actualIndependentCoarseParameterChain_native D (by omega) c.chain.1 c.chain.2.2.2.1
  have hc := F.native_copy (by omega) hζ hband hweak Dm sX hCc c n d hd word Y hY t ht z
  rw [hctx] at hc
  simpa only [Y, independentIntrinsicParameterPacking_slow, smul_zero] using hc

end AVRegularity.EntryWeakProofs.WeakEddyStageMeanFamily
end
end

section
/-! Coherent inherited means retain native copies, weighted reserves and open-slice naturality. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentInheritedCrossNativeMeanProduction (d H D N R count qs hh n m : ℕ)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (hND : N ≤ D) (hD : 1 ≤ D) (hn : 2 ≤ n) (hhh : hh ≤ R) (hhpos : hh ≠ 0) (hm : m ≤ n - 1)
    (BG BV BE : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ f :
      IndependentLiftNaturalPrimitiveDatum ι d
        (independentLiftPrimitiveTopOrder (H + D + 2) D N R) D N R count qs BG BV BE →
      ι → ι → ℝ → Vec 2 → Vec (2 + d) → Vec 2,
      (∀ x out inp, ∃ Qf : IndependentParameterSourceReserve H (f x out inp),
        (∀ r ≤ H, Qf.budget r ≤ finiteMatrixPower x.primitive.M hh out inp * C) ∧
        (∀ t ∈ Icc x.primitive.a x.primitive.b, ∀ Y ∈ x.primitive.U, ∀ z k,
          let Q : LiftOperatorData ι (fun _ => ℝ) D :=
            ⟨1, fun t X => x.primitive.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
              x.primitive.v, independentConstituentEdgeSlice x.primitive.edge x.primitive.edgeField x.primitive.edges
                (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
          f x out inp t z Y k = positiveMeanFluxCoefficient Q
            (x.primitive.Cc (independentStoredParameterProjection d Y)) hh n k m α t
            (independentIntrinsicSlowProjection d Y) z out inp 1) ∧
        (∀ δ ∈ x.translations, IndependentSourceTranslationInvariant δ (f x out inp))) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z → ∀ out inp,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (f x out inp) (f y out inp) := by
  obtain ⟨B, hB, P, hprod, hPCross⟩ := independentInheritedCrossMeanUniformProduction (ι := ι)
    d H D N R count qs hh n m α lam hND hn hhpos BG BV BE hBG hBV hBE
  let C := max 1 (2 * independentMeanFluxCoefficientCost (2 + d) H D n m count α lam 1 BG BV BE B)
  let X := IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder (H + D + 2) D N R) D N R count qs BG BV BE
  let f := fun (x : X) (out inp : ι) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) (k : Fin 2) => independentMeanFluxCoefficientSource
    x.primitive.edge x.primitive.edgeField (independentIntrinsicSlowEmbedding d) 1
    x.primitive.G x.primitive.v (independentFiniteLiftFields x.primitive (P x))
    hh n m α lam out inp k t z Y
  refine ⟨C, zero_le_one.trans (le_max_left _ _), f, ?_, ?_⟩
  · intro x out inp
    let S := x.primitive
    obtain ⟨Qf, hQf⟩ := (hprod x).2 out inp
    refine ⟨Qf, ?_, ?_, ?_⟩
    · intro r hr
      exact (hQf r hr).trans (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh out inp))
    · intro t ht Y hY z k
      have hT : H ≤ independentLiftPrimitiveTopOrder (H + D + 2) D N R :=
        (Nat.le_add_right H (D + 2)).trans
          (independentLiftPrimitiveTopOrder_base_le (H + D + 2) D N R)
      exact (independentFiniteMeanFluxCoefficient_reconstructed_copy S (P x) hB hD hT hBG hBV hBE
        hh n hn hhpos m hm α lam hlam t z Y out inp k).trans
        (congrArg (fun c : ℝ →L[ℝ] ℝ => c 1)
          (independentFiniteNativeMeanCoefficient_copy S (P x) Y hY hh n hhh (by omega) hhpos
            k m hm α t ht z out inp))
    · intro δ hδ t z Y
      funext k
      exact independentMeanFluxCoefficientSource_translation_invariant δ S.edge S.edgeField
        (independentIntrinsicSlowEmbedding d) 1 S.G S.v (independentFiniteLiftFields S (P x))
        (fun t Y i j => congrFun (congrFun (x.metric_translation δ hδ t Y) i) j)
        (x.edge_translation δ hδ) ((hprod x).1 δ hδ) hh n m α lam out inp k t z Y
  · intro x y U Y Z hU hzero he out inp t V hV z
    funext k
    dsimp only [f]
    rw [← he.edge, ← he.drift]
    have Qc p q (l : Fin (q + 1)) (β : DerivativeWord2 l.val) v u :
        IndependentParameterSourceReserve (D + 1)
          (fun t z W => independentFiniteLiftFields x.primitive (P x) p q l.val β t z W v u) :=
      (independentFiniteLiftFields_reserve x.primitive (P x) hB p q l.val β v u).choose.restrictOrder
        (D + 1) (by omega)
    have Qe p q (l : Fin (q + 1)) (β : DerivativeWord2 l.val) v u :
        IndependentParameterSourceReserve (D + 1)
          (fun t z W => independentFiniteLiftFields y.primitive (P y) p q l.val β t z W v u) :=
      (independentFiniteLiftFields_reserve y.primitive (P y) hB p q l.val β v u).choose.restrictOrder
        (D + 1) (by omega)
    exact independentMeanFluxCoefficientSource_slow_slice_congr x.primitive.edge
      x.primitive.edgeField y.primitive.edgeField (independentIntrinsicSlowEmbedding d)
      (independentIntrinsicSlowEmbedding_norm_le d) Y Z 1 x.primitive.G y.primitive.G x.primitive.v
      _ _ Qc Qe hU he.metric he.edge_fields (hPCross x y U Y Z hU hzero he)
      hh n m α lam out inp k t V hV z

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Finite inherited menus share one price before every native primitive datum. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

abbrev IndependentInheritedMeanInput (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count qs : ℕ) (BG BV BE : ℝ) :=
  IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder (H + D + 2) D N R) D N R count qs BG BV BE

structure IndependentInheritedMeanNaturalOutput (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count qs hh n m : ℕ) (α : DerivativeWord2 m) (BG BV BE C : ℝ) where
  field : IndependentInheritedMeanInput ι d H D N R count qs BG BV BE →
    ι → ι → ℝ → Vec 2 → Vec (2 + d) → Vec 2
  production : ∀ x out inp, ∃ Q : IndependentParameterSourceReserve H (field x out inp),
    (∀ r ≤ H, Q.budget r ≤ finiteMatrixPower x.primitive.M hh out inp * C) ∧
    (∀ t ∈ Icc x.primitive.a x.primitive.b, ∀ Y ∈ x.primitive.U, ∀ z k,
      let Q : LiftOperatorData ι (fun _ => ℝ) D :=
        ⟨1, fun t X => x.primitive.G t
          (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
          x.primitive.v, independentConstituentEdgeSlice x.primitive.edge x.primitive.edgeField
            x.primitive.edges (independentIntrinsicSlowEmbedding d)
              (independentIntrinsicSliceOffset d Y)⟩
      field x out inp t z Y k = positiveMeanFluxCoefficient Q
        (x.primitive.Cc (independentStoredParameterProjection d Y)) hh n k m α t
        (independentIntrinsicSlowProjection d Y) z out inp 1) ∧
    (∀ δ ∈ x.translations, IndependentSourceTranslationInvariant δ (field x out inp))
  cross : ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
    IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z → ∀ out inp,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
        (field x out inp) (field y out inp)

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite source menu shares one coherent mean budget while retaining each original path grade. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem independentInheritedVariableGradeMenuProduction
    {I : Type*} [Fintype I] (ι : I → Type*)
    [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
    (d : I → ℕ) (H D N count qs : ℕ) (hh n m : I → ℕ)
    (α : ∀ j, DerivativeWord2 (m j))
    (hND : N ≤ D) (hD : 1 ≤ D) (hn : ∀ j, 2 ≤ n j)
    (hhpos : ∀ j, hh j ≠ 0) (hm : ∀ j, m j ≤ n j - 1)
    (BG BV BE : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      Nonempty (IndependentInheritedMeanNaturalOutput (ι j) (d j) H D N (hh j) count qs
        (hh j) (n j) (m j) (α j) BG BV BE C) := by
  classical
  have hprice j := independentInheritedCrossNativeMeanProduction (ι := ι j)
    (d j) H D N (hh j) count qs (hh j) (n j) (m j) (α j) 1 one_ne_zero
    hND hD (hn j) le_rfl (hhpos j) (hm j) BG BV BE hBG hBV hBE
  choose C hC f hprod hcross using hprice
  let B := independentFiniteStepBudget C
  refine ⟨B, zero_le_one.trans (independentFiniteStepBudget_one_le C hC), ?_⟩
  intro j
  refine ⟨{ field := f j, production := ?_, cross := hcross j }⟩
  intro x out inp
  obtain ⟨Q, hQ, hcopy, hphase⟩ := hprod j x out inp
  refine ⟨Q, ?_, hcopy, hphase⟩
  intro r hr
  exact (hQ r hr).trans (mul_le_mul_of_nonneg_left
    (independentFiniteStepBudget_entry_le C hC j)
    (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg (hh j) out inp))

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Cross-chart naturality compares equal-depth charts without transporting their stored coordinate types. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {p q O D N R count : ℕ} {BG BV BE : ℝ}

structure IndependentLiftHeterogeneousSliceEq
    (S : IndependentLiftPrimitiveData ι p O D N R count BG BV BE)
    (T : IndependentLiftPrimitiveData ι q O D N R count BG BV BE)
    (U : Set (Vec 2)) (Y : Vec (2 + p)) (Z : Vec (2 + q)) : Prop where
  left : S.a = T.a
  right : S.b = T.b
  drift : S.v = T.v
  matrix : S.M = T.M
  edge : S.edge = T.edge
  metric : ∀ i j t X, X ∈ U → ∀ _z : Vec 2,
    S.G t (independentIntrinsicSlowEmbedding p X + Y) i j =
      T.G t (independentIntrinsicSlowEmbedding q X + Z) i j
  fields : ∀ v u d γ, γ ∈ S.edge v u d → ∀ word t X, X ∈ U → ∀ z,
    S.edgeField v u d γ word t z (independentIntrinsicSlowEmbedding p X + Y) =
      T.edgeField v u d γ word t z (independentIntrinsicSlowEmbedding q X + Z)

theorem IndependentLiftHeterogeneousSliceEq.sameDimension
    {S T : IndependentLiftPrimitiveData ι p O D N R count BG BV BE}
    {U : Set (Vec 2)} {Y Z : Vec (2 + p)}
    (he : IndependentLiftHeterogeneousSliceEq S T U Y Z) :
    IndependentLiftPrimitiveSlowSliceEq S T U Y Z :=
  ⟨he.left, he.right, he.drift, he.matrix, he.edge, he.metric, he.fields⟩

theorem independentInheritedMean_equalDepth_cross
    {J H K L h qs n m : ℕ} {word : DerivativeWord2 m} {C : ℝ}
    (E : ∀ r : Fin (J + 1), IndependentInheritedMeanNaturalOutput ι (4 * r.val)
      H K L h 1 qs h n m word BG BV BE C)
    (r s : Fin (J + 1)) (hrs : r.val = s.val)
    (x : IndependentInheritedMeanInput ι (4 * r.val) H K L h 1 qs BG BV BE)
    (y : IndependentInheritedMeanInput ι (4 * s.val) H K L h 1 qs BG BV BE)
    (U : Set (Vec 2)) (Y : Vec (2 + 4 * r.val)) (Z : Vec (2 + 4 * s.val))
    (hU : IsOpen U) (hzero : (0 : Vec 2) ∈ U)
    (he : IndependentLiftHeterogeneousSliceEq x.primitive y.primitive U Y Z)
    (out inp : ι) :
    ∀ t X, X ∈ U → ∀ z,
      (E r).field x out inp t z (independentIntrinsicSlowEmbedding (4 * r.val) X + Y) =
        (E s).field y out inp t z (independentIntrinsicSlowEmbedding (4 * s.val) X + Z) := by
  have hrs' : r = s := Fin.ext hrs
  subst s
  exact (E r).cross x y U Y Z hU hzero he.sameDimension out inp

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual finite weak menu chooses its inherited mean producers before any data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

abbrev IndependentWeakInheritedMeanIndex (J R K : ℕ) :=
  Σ _r : Fin (J + 1), Σ _h : Finset.Icc 1 R, Σ n : Finset.Icc 2 K,
    Σ d : Finset.Icc 2 n.val, DerivativeWord2 (d.val - 1)

namespace IndependentWeakInheritedMeanIndex
variable {J R K : ℕ}
def depth (j : IndependentWeakInheritedMeanIndex J R K) : ℕ := j.1.val
def grade (j : IndependentWeakInheritedMeanIndex J R K) : ℕ := j.2.1.val
def degree (j : IndependentWeakInheritedMeanIndex J R K) : ℕ := j.2.2.1.val
def testedOrder (j : IndependentWeakInheritedMeanIndex J R K) : ℕ := j.2.2.2.1.val
def word (j : IndependentWeakInheritedMeanIndex J R K) : DerivativeWord2 (j.testedOrder - 1) := j.2.2.2.2
end IndependentWeakInheritedMeanIndex

theorem independentWeakInheritedMeanMenuProduction (J H K N R sZ : ℕ)
    (hNK : N ≤ K) (hK : 1 ≤ K)
    (BG BV BE : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : IndependentWeakInheritedMeanIndex J R K,
      Nonempty (IndependentInheritedMeanNaturalOutput (Fin (j.grade + 1)) (4 * j.depth)
        H K N j.grade 1 sZ j.grade j.degree (j.testedOrder - 1) j.word BG BV BE C) := by
  classical
  apply independentInheritedVariableGradeMenuProduction
    (fun j : IndependentWeakInheritedMeanIndex J R K => Fin (j.grade + 1))
    (fun j => 4 * j.depth) H K N 1 sZ
    IndependentWeakInheritedMeanIndex.grade IndependentWeakInheritedMeanIndex.degree
    (fun j => j.testedOrder - 1) IndependentWeakInheritedMeanIndex.word hNK hK
  · intro j
    exact (Finset.mem_Icc.mp j.2.2.1.property).1
  · intro j
    have hh := (Finset.mem_Icc.mp j.2.1.property).1
    exact Nat.ne_of_gt hh
  · intro j
    exact Nat.sub_le_sub_right (Finset.mem_Icc.mp j.2.2.2.1.property).2 1
  · exact hBG
  · exact hBV
  · exact hBE

end AVRegularity.EntryWeakProofs
end
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.ActualIndependentCoarseEmptySliceData
import AVRegularity.EntryWeak.MolecularUlFluxNormBound

section
section
/-! The produced open metric carrier and literal coefficient extension transfer original family inverses without global boundary smoothness. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem actualIndependentCoarseCarrierInverse_transfer_on (D : OCData) (hΛ : 1 ≤ D.Λ) (A : RealChain)
    (bw ρ a b : ℝ) (j₀ : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ A.ctxLevel slot A) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (sX sZ N R hh n : ℕ) (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Y : Vec (2 + 4 * A.children.length)) (hY : Y ∈ actualIndependentCoarseLiftCarrier D A bw ρ j₀ A.ctxLevel slot)
    (hc : IsLiftSequenceOn (ladderOmega D bw j₀ A.ctxLevel slot
      (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) ρ)
      (actualIndependentCoarseSliceLiftData D A ρ slot edge Y)
      sX sZ a b N R (c (independentStoredParameterProjection (4 * A.children.length) Y)))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsCellFieldInverse
      (fun t => Matrix.of ((actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y).G t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y)))
      (actualIndependentCoarseSliceLiftData D A ρ slot edge Y).v sZ a b 0
      (fun t z => liftCellSource (actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y)
        (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f) hh n t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z)
      (fun t z => liftApply n (actualIndependentCoarseCarrierCoefficients D A bw c Y hh n) (fun _ => f) t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z) := by
  let Q := actualIndependentCoarseSliceLiftData D A ρ slot edge Y
  let U := independentIntrinsicSliceCarrier (4 * A.children.length) (actualIndependentCoarseLiftCarrier D A bw ρ j₀ A.ctxLevel slot) Y
  have hU : IsOpen U := independentIntrinsicSliceCarrier_isOpen _ _
    (actualIndependentCoarseLiftCarrier_isOpen D hΛ A bw ρ j₀ A.ctxLevel slot hA) Y
  have hbase : independentIntrinsicSlowProjection (4 * A.children.length) Y ∈ U :=
    independentIntrinsicSliceCarrier_base _ _ Y hY
  have hi := independentCarrierCoefficientExtension_inverse_on (actualIndependentCoarseStoredCarrier D A bw) c
    (independentStoredParameterProjection (4 * A.children.length) Y) hY.1.1
    (ladderOmega D bw j₀ A.ctxLevel slot
      (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) ρ)
    Q hc hh n hhh hn hnN f hf
    (independentIntrinsicSlowProjection (4 * A.children.length) Y) hY.2
  let G := (actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y).G
  have hG : ∀ t ∈ Icc a b, ∀ X ∈ U, Q.G t X = G t X := by
    intro t ht X hX
    have he := actualIndependentCoarseScaledExtendedMetric_lift_carrier_copy D A bw ρ a b t j₀ A.ctxLevel slot χ hχ ht
      (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
        independentIntrinsicSliceOffset (4 * A.children.length) Y) hX
    exact (actualIndependentCoarseScaledMetric_slice D A hA.2.2.1 ρ slot edge Y t X).symm.trans he.symm
  exact local_lift_inverse_metric_carrier_replacement hU Q G a b hG sZ hh n
    (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f)
    (independentIntrinsicSlowProjection (4 * A.children.length) Y) hbase hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine predecessor data identify the symmetric array with the literal physical slow-flux mean. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem positiveMeanFluxCoefficient_literal_apply
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (hD : 1 ≤ D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : Fin 2) (t : ℝ) (Y z : Vec 2) (v : ι)
    (hG : ∀ i j, ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G t Y i j))
    (hv : Continuous (Q.v t))
    (hΦ : GoodField 1 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 1 (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t))
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun y => Cc hh (n - 1) m α t Y y v u))
    (hsource : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hgood : ∀ q, GoodField D (liftApply q (Cc (hh - 1) q) (fun _ => f) t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k) (fun _ => f) t Y z v =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t Y z k) v := by
  let F := fun z => (Real.sqrt Q.η * Q.v t z k) •
    liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z
  let T := fun z => ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
    sourceFluxCoefficientArray Q.edge Q.η t
      (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t) k j Y z
  have hF : Continuous F :=
    (continuous_const.mul ((continuous_apply k).comp hv)).smul (hΦ.continuous_slice Y)
  have hT : Continuous T := continuous_finsetSum _ (fun j _ =>
    (sourceFluxCoefficientArray_good Q.edge hD Q.η t _ (hgood (n - 1 - j)) hΓ k j).continuous_slice Y)
  have he (y : Vec 2) : T y v =
      ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t) k j v Y y := by
    dsimp only [T]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hjD : j ≤ D - 1 := by have := Finset.mem_range.mp hj; omega
    have hb := Weighted.isBoxSmooth_of_joint_contDiff j ((D - 1) - j) _
      ((hgood (n - 1 - j)).mono (by omega)).1
    exact congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _ k j hb v) Y) y
  rw [positiveMeanFluxCoefficient_intrinsic_apply Q Cc hh n f hf k t Y z v
    ((continuous_apply k).comp hv) hc
    hsource (fun v u d γ hγ α => Weighted.isBoxSmooth_of_joint_contDiff 0 0 _
      ((contDiff_pi.mp (hΓ v u d γ hγ α).1 k).of_le (by norm_num)))]
  have hmean := congrFun (liftFluxX_cell_mean_intrinsic Q hD Cc hh n hn hhpos
    (fun _ => f) t Y k hG hv hΦ hΨ hgood hΓ) v
  simp_rw [← he]
  change fieldCellMean (fun y => F y v) - Real.sqrt Q.η •
    fieldCellMean (fun y => T y v) = _
  rw [fieldCellMean_pi_apply F hF v, fieldCellMean_pi_apply T hT v]
  exact hmean.symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! Functional production families retain coherent choices across primitive input data at one
rank. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

abbrev IndependentLiftRankProductionFamily (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d base D N R count qs r : ℕ) (BG BV BE C : ℝ) :=
  ∀ x : IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE,
    ∀ hh n, hh ≤ R → n ≤ N → ambientRecurrenceRank N hh n = r →
    ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d)
        (liftProductionOrder base D N R hh n) n x.primitive.a x.primitive.b x.primitive.U
        (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower x.primitive.M hh v u) C

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d base D N R count qs r : ℕ} {BG BV BE C : ℝ}

def IndependentLiftRankProductionFamily.IsNatural
    (Q : IndependentLiftRankProductionFamily ι d base D N R count qs r BG BV BE C) : Prop :=
  ∀ x hh n hhh hn hr m hm α v u δ,
    δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x hh n hhh hn hr m hm α v u).field

def IndependentLiftRankProductionFamily.IsCrossNatural
    (Q : IndependentLiftRankProductionFamily ι d base D N R count qs r BG BV BE C) : Prop :=
  ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
    IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
    ∀ hh n hhh hn hr m hm α v u t z,
      (Q x hh n hhh hn hr m hm α v u).field t z Y =
      (Q y hh n hhh hn hr m hm α v u).field t z Z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced incoming edge germs and the actual metric extension preserve the native inverse. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem actualIndependentCoarseCarrierInverse_edge_transfer_on (D : OCData) (hΛ : 1 ≤ D.Λ) (A : RealChain)
    (bw ρ a b : ℝ) (j₀ : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ A.ctxLevel slot A)
    (edge edge' : ConstituentEdges Dm (fun _ : ι => ℝ))
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (sX sZ N R hh n : ℕ) (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Y : Vec (2 + 4 * A.children.length)) (hY : Y ∈ actualIndependentCoarseLiftCarrier D A bw ρ j₀ A.ctxLevel slot)
    (U : Set (Vec 2)) (hU : IsOpen U)
    (hbase : independentIntrinsicSlowProjection (4 * A.children.length) Y ∈ U)
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq U t
      (actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y).edge edge')
    (hc : IsLiftSequenceOn (ladderOmega D bw j₀ A.ctxLevel slot
      (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) ρ)
      (actualIndependentCoarseSliceLiftData D A ρ slot edge Y)
      sX sZ a b N R (c (independentStoredParameterProjection (4 * A.children.length) Y)))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let Q := actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y
    IsCellFieldInverse
      (fun t => Matrix.of (Q.G t (independentIntrinsicSlowProjection (4 * A.children.length) Y)))
      Q.v sZ a b 0
      (fun t z => liftCellSource {Q with edge := edge'} (actualIndependentCoarseCarrierCoefficients D A bw c Y)
        (fun _ => f) hh n t (independentIntrinsicSlowProjection (4 * A.children.length) Y) z)
      (fun t z => liftApply n (actualIndependentCoarseCarrierCoefficients D A bw c Y hh n) (fun _ => f) t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z) := by
  let Q := actualIndependentCoarseExtendedSliceLiftData D A ρ slot edge χ a b Y
  have hi := actualIndependentCoarseCarrierInverse_transfer_on D hΛ A bw ρ a b j₀ slot hA edge χ hχ c
    sX sZ N R hh n hhh hn hnN Y hY hc f hf
  exact local_lift_inverse_edge_replacement hU Q edge' a b sZ hh n
    (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f)
    (independentIntrinsicSlowProjection (4 * A.children.length) Y) hbase he hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Original actual eddy lifts supply the precise unit-contrast native inverse used by coefficient production. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem actualIndependentCoarseEmptyCarrierInverse (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (hA : A.WellSlotted) (hweak : D.term < A.ctxLevel) (bw ρ a b : ℝ) (slot : ℤ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (sX sZ N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Y : Vec (2 + 4 * A.children.length)) (hY : Y ∈ actualIndependentCoarseNativeCarrier D A bw)
    (hc : IsLiftSequence (actualIndependentCoarseSliceLiftData (Dm := Dm) D A ρ slot (fun _ _ _ => []) Y)
      sX sZ a b N 0 (c (independentStoredParameterProjection (4 * A.children.length) Y)))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsCellFieldInverse (fun t => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y)
      (ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) slot) sZ a b 0
      (fun t z => liftCellSource
        (⟨1, (fun t X => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t
          (independentIntrinsicSlowEmbedding (4 * A.children.length) X + independentIntrinsicSliceOffset (4 * A.children.length) Y)),
          ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) slot,
          (fun _ _ _ => [])⟩ : LiftOperatorData ι (fun _ => ℝ) Dm)
        (actualIndependentCoarseCarrierCoefficients D A bw c Y) (fun _ => f) 0 n t
          (independentIntrinsicSlowProjection (4 * A.children.length) Y) z)
      (fun t z => liftApply n (actualIndependentCoarseCarrierCoefficients D A bw c Y 0 n) (fun _ => f) t
        (independentIntrinsicSlowProjection (4 * A.children.length) Y) z) := by
  have hi := actualIndependentCoarseCarrierInverse_transfer D A hA bw ρ a b slot (fun _ _ _ => []) χ hχ
    c sX sZ N 0 0 n le_rfl hn hnN Y hY hc f hf
  rw [actualIndependentCoarseExtendedEmptySliceData_eq D hΛ hζ hband A hweak ρ slot χ a b Y] at hi
  have hmat : (fun t => Matrix.of (actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y)) =
      (fun t => actualIndependentCoarseScaledExtendedMetric D A ρ χ a b t Y) := by
    funext t i j
    rfl
  simpa only [independentIntrinsicSliceOffset_base, hmat, actualIndependentCoarseSliceLiftData,
    familyLiftData] using hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual path histories and their literal means use the fixed weak menu cap. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem restrict_familyLiftData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hKD : K ≤ Dm) (level : ℕ) (slot : ℤ) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) :
    restrictLiftData K hKD (familyLiftData D level slot A ρ edge) =
      familyLiftData D level slot A ρ (restrictConstituentEdges K hKD edge) := rfl

theorem weakPath_isLiftSequenceOn_effective_order (G : GenStage D hr Dm bw j₀)
    (K : ℕ) (hKD : K ≤ Dm) (hK : G.maxOrderBound K) {h : ℕ} (π : StagePath G h)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p) (ρ : ℝ)
    (Ω : Set (Vec 2)) (sX sZ N R : ℕ) (hNK : N ≤ K) (a b : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : IsLiftSequenceOn Ω (familyLiftData D G.level p.1 c.1 ρ (pathEdges G π p c))
      sX sZ a b N R Cc) :
    IsLiftSequenceOn Ω
      (familyLiftData D G.level p.1 c.1 ρ (restrictConstituentEdges K hKD (pathEdges G π p c)))
      sX sZ a b N R Cc := by
  have hh := isLiftSequenceOn_restrict_effective_order Ω K hKD
    (familyLiftData D G.level p.1 c.1 ρ (pathEdges G π p c))
    (weakFamilyPathEdges_nil_above_stage_order G K hK π p c ρ)
    sX sZ N R hNK a b Cc hc
  rw [restrict_familyLiftData] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! The physical path flux uses the fixed weak menu when its tested degree is retained. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem liftFluxX_restrict_effective_order (K : ℕ) (hKD : K ≤ Dm)
    (Q : LiftOperatorData ι h Dm) (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : n ≤ K) (t : ℝ) :
    liftFluxX Q Cc f hh n t = liftFluxX (restrictLiftData K hKD Q) Cc f hh n t := by
  unfold liftFluxX
  simp only [restrictLiftData, Nat.min_eq_right (hn.trans hKD), Nat.min_eq_right hn]
  simp_rw [sourceFlux_restrict_effective_order K hKD Q.edge hz]

theorem pathMeanFlux_restrict_effective_order (D : OCData) (m : ℕ) (ρ : ℝ)
    (K : ℕ) (hKD : K ≤ Dm) {hh : ℕ}
    (Q : LiftOperatorData (Fin (hh + 1)) (fun _ => ℝ) Dm)
    (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff (Fin (hh + 1)) (fun _ => ℝ))
    (n : ℕ) (hn : n ≤ K) (t : ℝ) :
    pathMeanFlux D m ρ Q Cc n t = pathMeanFlux D m ρ (restrictLiftData K hKD Q) Cc n t := by
  unfold pathMeanFlux
  simp_rw [liftFluxX_restrict_effective_order K hKD Q hz Cc _ hh n hn]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {bw : ℝ} {j₀ : ℕ}

theorem weakPath_pathMeanFlux_effective_order (G : GenStage D hr Dm bw j₀)
    (K : ℕ) (hKD : K ≤ Dm) (hK : G.maxOrderBound K) {hh : ℕ} (π : StagePath G hh)
    (p : OddSlot) (c : StageCtx D bw j₀ G.level p) (ρ : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (hh + 1)) (fun _ => ℝ))
    (n : ℕ) (hn : n ≤ K) (t : ℝ) :
    pathMeanFlux D G.level ρ (familyLiftData D G.level p.1 c.1 ρ (pathEdges G π p c)) Cc n t =
      pathMeanFlux D G.level ρ
        (familyLiftData D G.level p.1 c.1 ρ (restrictConstituentEdges K hKD (pathEdges G π p c))) Cc n t := by
  have he := pathMeanFlux_restrict_effective_order D G.level ρ K hKD
    (familyLiftData D G.level p.1 c.1 ρ (pathEdges G π p c))
    (weakFamilyPathEdges_nil_above_stage_order G K hK π p c ρ) Cc n hn t
  rw [restrict_familyLiftData] at he
  exact he

end AVRegularity.EntryWeakProofs
end
end

section
/-! One rank step consumes genuine earlier productions at its actual production order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

structure IndependentLiftNaturalProductionStepDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d base D N R count qs hh n : ℕ) (BG BV BE B : ℝ) where
  data : IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE
  earlier : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d)
      (4 * liftProductionOrder base D N R hh n + 2 * D + 7) q
      data.primitive.a data.primitive.b data.primitive.U
      (fun Y => data.primitive.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower data.primitive.M p v u) B
  earlier_translation : ∀ δ ∈ data.translations, ∀ p q hpq m hm α v u,
    IndependentSourceTranslationInvariant δ (earlier p q hpq m hm α v u).field

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d base D N R count qs hh n : ℕ} {BG BV BE B : ℝ}

def IndependentLiftNaturalProductionStepDatum.restrict
    (x : IndependentLiftNaturalProductionStepDatum ι d base D N R count qs hh n BG BV BE B) :
    IndependentLiftNaturalPredecessorDatum ι d
      (4 * liftProductionOrder base D N R hh n + 5) D N R count hh n qs BG BV BE B := by
  let k := liftProductionOrder base D N R hh n
  have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
    have ho := liftProductionOrder_le_initial base D N R hh n
    dsimp only [independentLiftPrimitiveTopOrder, k]
    omega
  exact
    { primitive := x.data.primitive.monoOrder (4 * k + 5) horder
      fastOrder := x.data.fastOrder
      earlier := fun p q hpq m hm α v u =>
        (x.earlier p q hpq m hm α v u).monoOrder (4 * k + 5 + 2 * D + 2) (by dsimp only [k]; omega)
      translations := x.data.translations
      metric_translation := x.data.metric_translation
      edge_translation := x.data.edge_translation
      earlier_translation := x.earlier_translation }

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine metric and pulse production supply every actual full-family molecular production
before coefficient recursion. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_molecular_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H K : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      M ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J → D.term < A.ctxLevel →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps A.lastLevel →
      let a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
      let b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
      let G := actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length) a b
      let v := ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot
      ∃ Q : IndependentParameterMetricReserve K G,
      ∃ Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : Vec (2 + 4 * A.children.length)) => v t z i),
      ∃ Mdata : Vec (2 + 4 * A.children.length) → MolecularData,
        (∀ n ≤ K, Q.budget n ≤ BG) ∧ (∀ i n, n ≤ H → (Qv i).budget n ≤ BV) ∧
        (∀ i n, (Qv i).budget n ≤ D.weakPe A.ctxLevel * BV) ∧
        D.weakPe A.ctxLevel ≤ 1 ∧
        (∀ Y, (Mdata Y).G = fun t => G t Y) ∧ (∀ Y, (Mdata Y).v = v) ∧
        (∀ Y, dataCoefficients (Mdata Y) = ⟨(fun t _ => G t Y), (Mdata Y).v, 0, 0⟩) ∧
        (∀ Y n, n ≤ H → Nonempty (MolecularFiniteDriftBudget (Mdata Y) n)) := by
  obtain ⟨χ, BG, hχ, hBG, M₀, hM₀, hmetric⟩ := uniform_actual_independent_coarse_scaled_metric_reserve_production
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J K
  obtain ⟨M₁, hpulse⟩ := uniform_actual_weak_pulse_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ H
  refine ⟨χ, BG, pulseFastDerivativeConstant H, hχ, hBG, pulseFastDerivativeConstant_nonneg H,
    max M₀ M₁, hM₀.trans (le_max_left _ _), ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hseq hband A hbase hdepth hweak bw j₀ hA ρ hρ hρle
  dsimp only
  let a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
  let b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
  let G := actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length) a b
  let v := ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hν : 0 < D.kap A.ctxLevel := weakData_kap_pos D hΛ₁ hζ' hband _
  have hp : Odd A.slot := by
    have hh := realChainSlotSeq_odd D A hA A.children.length le_rfl
    rw [realChainSlotSeq_last A hA.2.2.1] at hh
    exact hh
  have hband' : IsOCBandChain α q Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ] using hband
  have hsmall := hpulse D ((le_max_right _ _).trans hterm) hDα hDq hDΛ hband' A.ctxLevel hweak
  obtain ⟨Q, hQ, he⟩ := hmetric D hDα hDq hDΛ hDζ hseq hband A
    ((le_max_left _ _).trans hbase) hdepth bw j₀ hA ρ hρ hρle
  obtain ⟨Mdata, hG, hv, hc, hbud⟩ := independentParameterMetric_pulse_molecular_production H K Q
    (fun t Y ξ => (he t Y ξ).1) hΛ₁ hν hζ' hp hsmall.2
  refine ⟨Q, (fun i => independentPulseEntrySourceReserve H hΛ₁ hν hζ' hp i),
    Mdata, hQ, ?_, ?_, hsmall.1, hG, hv, hc, hbud⟩
  · intro i n _
    exact independentPulseEntrySourceReserve_budget_bound H hΛ₁ hν hζ' hp hsmall.1 i n
  · intro i n
    exact independentPulseEntrySourceReserve_response_budget H hΛ₁ hν hζ' hp i n

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Actual native inverses produce the next full-parameter coefficient production before all
primitive data. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftPredecessorCoefficientProduction (d k D N R count hh n qs m : ℕ)
    (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n)
    (α : DerivativeWord2 m) (out inp : ι) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : IndependentLiftPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B,
      Nonempty (IndependentScalarCoefficientProduction (2 + d) k n x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α out inp
        (finiteMatrixPower x.primitive.M hh out inp) C) := by
  let X := IndependentLiftPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B
  let A := fun p : Fin (m + 1) × Fin (n + 1) =>
    (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let src := fun (x : X) p t z Y out =>
    independentLiftPredecessorSource x.primitive x.earlier (A p) out inp t z Y
  let g := fun (x : X) p => independentTimeWindowSource (Ioc x.primitive.a x.primitive.b) (src x p)
  have hprod (x : X) p := independentLiftPredecessorSource_production x.primitive x.earlier
    (A p) out inp hn hnD hBG hBV hBE hB
  choose Q hQ using hprod
  let Qg := fun (x : X) p => ((Q x p).timeWindow (Ioc x.primitive.a x.primitive.b)
    measurableSet_Ioc).congrSource (show independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
      (independentLiftPredecessorSource x.primitive x.earlier (A p) out inp) =
      (fun t z Y => g x p t z Y out) by
        funext t z Y
        by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
        · simp only [g, src, independentTimeWindowSource, ite_eq_left ht]
        · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply])
  let BS := independentCalibratedCellSourcePrice (2 + d) (4 * k + 5) D hh n m count BG BV BE B
  have hBS : 0 ≤ BS := independentCalibratedCellSourcePrice_nonneg _ _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB
  have hQg (x : X) p r (hr : r ≤ 4 * k + 5) :
      (Qg x p).budget r ≤ finiteMatrixPower x.primitive.M hh out inp * BS := by
    dsimp only [Qg]
    rw [IndependentParameterSourceReserve.congrSource_budget,
      IndependentParameterSourceReserve.timeWindow_budget]
    exact (hQ x p r hr).trans (mul_le_mul_of_nonneg_left
      (independentLiftCellProductionCost_le_calibrated _ _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB p)
      (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh out inp))
  have hg (x : X) p t (ht : t ≤ x.primitive.a) z Y : g x p t z Y out = 0 := by
    rw [show g x p t z Y = 0 from independent_time_window_Ioc_past_zero
      (fun t z Y => (src x p t z Y : ι → ℝ)) x.primitive.a x.primitive.b t ht z Y]
    rfl
  have hmean (x : X) p t Y : fieldCellMean (fun z => g x p t z Y out) = 0 := by
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simp only [g, independentTimeWindowSource, ite_eq_left ht]
      exact independentLiftPredecessorSource_mean_zero x.primitive x.earlier (A p) out inp hn hnD t Y
    · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply, fieldCellMean_zero]
  have hactual (x : X) p Y (hY : Y ∈ x.primitive.U) :
      IsCellFieldInverse (x.primitive.molecular Y).G (x.primitive.molecular Y).v qs x.primitive.a x.primitive.b 0
        (fun t z => g x p t z Y)
        (fun t z => (Real.exp (((1 : ℝ) • A p) (independentIntrinsicSlowProjection d Y)))⁻¹ •
          liftApply n (x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
            (fun _ Z => Real.exp (((1 : ℝ) • A p) Z) • (Pi.single inp (1 : ℝ) : ι → ℝ))
            t (independentIntrinsicSlowProjection d Y) z) := by
    have hi := independentLiftPredecessorSource_actual_inverse x.primitive x.earlier (by omega)
      (by omega) hhh hn hnN hnD (A p) inp Y hY
    rw [x.fastOrder] at hi
    simpa only [one_smul] using hi
  exact family_variable_window_independent_coefficient_productions_exist (A := X)
    (fun x => x.primitive.window) k (k + 4) k n m hm (by omega) (by omega) le_rfl (by omega)
    out inp (fun x => x.primitive.metric) Qg (fun _ => BG) (fun _ => BS)
    (fun _ => hBG) (fun _ => hBS) (fun x => x.primitive.metric_bound)
    (fun x => finiteMatrixPower x.primitive.M hh out inp)
    (fun x => finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh out inp) hQg
    (fun x => x.primitive.molecular) (fun x => x.primitive.molecular_coefficients)
    (fun x => x.primitive.v) (fun x => x.primitive.drift) (fun x => x.primitive.molecular_drift)
    (fun x => x.primitive.molecular_budget) hg hmean qs
    (fun x Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
    (fun _ => independentIntrinsicSlowProjection d) (fun x => x.primitive.U)
    (fun x Y β σ => x.primitive.symmetric _ hh hhh n m β σ) α 1 one_ne_zero hactual

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual native inverses produce the next full-parameter coefficient production before all
primitive data. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCrossNaturalPredecessorCoefficientProduction (d k D N R count hh n qs m : ℕ)
    (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n)
    (α : DerivativeWord2 m) (out inp : ι) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x :
      IndependentLiftNaturalPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k n x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α out inp
        (finiteMatrixPower x.primitive.M hh out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x x' Y Z,
        finiteMatrixPower x.primitive.M hh out inp = finiteMatrixPower x'.primitive.M hh out inp →
        x.primitive.a = x'.primitive.a → x.primitive.b = x'.primitive.b →
        x.primitive.v = x'.primitive.v →
        (∀ t, x.primitive.G t Y = x'.primitive.G t Z) →
        (∀ p : Fin (m + 1) × Fin (n + 1), ∀ t z,
          independentLiftPredecessorSource x.primitive x.earlier
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) out inp t z Y =
          independentLiftPredecessorSource x'.primitive x'.earlier
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) out inp t z Z) →
        ∀ t z, (Q x).field t z Y = (Q x').field t z Z := by
  let X := IndependentLiftNaturalPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B
  let A := fun p : Fin (m + 1) × Fin (n + 1) =>
    (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let src := fun (x : X) p t z Y out =>
    independentLiftPredecessorSource x.primitive x.earlier (A p) out inp t z Y
  let g := fun (x : X) p => independentTimeWindowSource (Ioc x.primitive.a x.primitive.b) (src x p)
  have hprod (x : X) p := independentLiftPredecessorSource_production x.primitive x.earlier
    (A p) out inp hn hnD hBG hBV hBE hB
  choose Q hQ using hprod
  let Qg := fun (x : X) p => ((Q x p).timeWindow (Ioc x.primitive.a x.primitive.b)
    measurableSet_Ioc).congrSource (show independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
      (independentLiftPredecessorSource x.primitive x.earlier (A p) out inp) =
      (fun t z Y => g x p t z Y out) by
        funext t z Y
        by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
        · simp only [g, src, independentTimeWindowSource, ite_eq_left ht]
        · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply])
  let BS := independentCalibratedCellSourcePrice (2 + d) (4 * k + 5) D hh n m count BG BV BE B
  have hBS : 0 ≤ BS := independentCalibratedCellSourcePrice_nonneg _ _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB
  have hQg (x : X) p r (hr : r ≤ 4 * k + 5) :
      (Qg x p).budget r ≤ finiteMatrixPower x.primitive.M hh out inp * BS := by
    dsimp only [Qg]
    rw [IndependentParameterSourceReserve.congrSource_budget,
      IndependentParameterSourceReserve.timeWindow_budget]
    exact (hQ x p r hr).trans (mul_le_mul_of_nonneg_left
      (independentLiftCellProductionCost_le_calibrated _ _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB p)
      (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh out inp))
  have hg (x : X) p t (ht : t ≤ x.primitive.a) z Y : g x p t z Y out = 0 := by
    rw [show g x p t z Y = 0 from independent_time_window_Ioc_past_zero
      (fun t z Y => (src x p t z Y : ι → ℝ)) x.primitive.a x.primitive.b t ht z Y]
    rfl
  have hmean (x : X) p t Y : fieldCellMean (fun z => g x p t z Y out) = 0 := by
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simp only [g, independentTimeWindowSource, ite_eq_left ht]
      exact independentLiftPredecessorSource_mean_zero x.primitive x.earlier (A p) out inp hn hnD t Y
    · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply, fieldCellMean_zero]
  have hactual (x : X) p Y (hY : Y ∈ x.primitive.U) :
      IsCellFieldInverse (x.primitive.molecular Y).G (x.primitive.molecular Y).v qs x.primitive.a x.primitive.b 0
        (fun t z => g x p t z Y)
        (fun t z => (Real.exp (((1 : ℝ) • A p) (independentIntrinsicSlowProjection d Y)))⁻¹ •
          liftApply n (x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
            (fun _ Z => Real.exp (((1 : ℝ) • A p) Z) • (Pi.single inp (1 : ℝ) : ι → ℝ))
            t (independentIntrinsicSlowProjection d Y) z) := by
    have hi := independentLiftPredecessorSource_actual_inverse x.primitive x.earlier (by omega)
      (by omega) hhh hn hnN hnD (A p) inp Y hY
    rw [x.fastOrder] at hi
    simpa only [one_smul] using hi
  let Rel : X → Vec (2 + d) → Vec (2 + d) → Prop := fun x Y Z =>
    ∃ δ ∈ x.translations, Y = Z + δ
  have hGR (x : X) (Y Z : Vec (2 + d)) (hYZ : Rel x Y Z) (t : ℝ) :
      x.primitive.G t Y = x.primitive.G t Z := by
    obtain ⟨δ, hδ, rfl⟩ := hYZ
    exact x.metric_translation δ hδ t Z
  have hgR (x : X) (p : Fin (m + 1) × Fin (n + 1)) (Y Z : Vec (2 + d))
      (hYZ : Rel x Y Z) (t : ℝ) (z : Vec 2) : g x p t z Y out = g x p t z Z out := by
    obtain ⟨δ, hδ, rfl⟩ := hYZ
    have hc := independentLiftPredecessorFields_translation_invariant x.primitive x.earlier δ
      (x.earlier_translation δ hδ)
    have hs := independentLiftCoefficientCellSource_translation_invariant δ x.primitive.edge
      x.primitive.edgeField (independentIntrinsicSlowEmbedding d) (A p) 1 x.primitive.G x.primitive.v
      (independentLiftPredecessorFields x.primitive x.earlier)
      (fun t Y i j => congrFun (congrFun (x.metric_translation δ hδ t Y) i) j)
      (x.edge_translation δ hδ) hc hh n out inp t z Z
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simpa only [g, src, independentTimeWindowSource, ite_eq_left ht,
        independentLiftPredecessorSource] using hs
    · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply]
  obtain ⟨C, hC, Qprod, hnat, hcross⟩ := family_variable_window_cross_natural_independent_coefficient_productions_exist (A := X)
    (fun x => x.primitive.window) k (k + 4) k n m hm (by omega) (by omega) le_rfl (by omega)
    out inp (fun x => x.primitive.metric) Qg (fun _ => BG) (fun _ => BS)
    (fun _ => hBG) (fun _ => hBS) (fun x => x.primitive.metric_bound)
    (fun x => finiteMatrixPower x.primitive.M hh out inp)
    (fun x => finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh out inp) hQg
    (fun x => x.primitive.molecular) (fun x => x.primitive.molecular_coefficients)
    (fun x => x.primitive.v) (fun x => x.primitive.drift) (fun x => x.primitive.molecular_drift)
    (fun x => x.primitive.molecular_budget) hg hmean Rel hGR hgR qs
    (fun x Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
    (fun _ => independentIntrinsicSlowProjection d) (fun x => x.primitive.U)
    (fun x Y β σ => x.primitive.symmetric _ hh hhh n m β σ) α 1 one_ne_zero hactual

  refine ⟨C, hC, Qprod, ?_, ?_⟩
  · intro x δ hδ t z Y
    exact hnat x t (Y + δ) Y ⟨δ, hδ, rfl⟩ z
  · intro x x' Y Z hθ ha hb hvEq hG hs
    apply hcross x x' Y Z hθ ha hb hvEq hG
    intro p t z
    have hwindow : Ioc x.primitive.a x.primitive.b = Ioc x'.primitive.a x'.primitive.b := by
      rw [ha, hb]
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · have ht' : t ∈ Ioc x'.primitive.a x'.primitive.b := hwindow ▸ ht
      simpa only [g, src, independentTimeWindowSource, ite_eq_left ht, ite_eq_left ht', A]
        using hs p t z
    · have ht' : t ∉ Ioc x'.primitive.a x'.primitive.b := hwindow ▸ ht
      simp only [g, independentTimeWindowSource, ite_eq_right ht, ite_eq_right ht', Pi.zero_apply]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual native inverses produce the next full-parameter coefficient production before all
primitive data. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCrossNaturalPredecessorGermProduction (d k D N R count hh n qs m : ℕ)
    (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n)
    (α : DerivativeWord2 m) (out inp : ι) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x :
      IndependentLiftNaturalPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k n x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α out inp
        (finiteMatrixPower x.primitive.M hh out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
        (∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ l β v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (fun t z W => independentLiftPredecessorFields x.primitive x.earlier p q l β t z W v u)
            (fun t z W => independentLiftPredecessorFields y.primitive y.earlier p q l β t z W v u)) →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  obtain ⟨C, hC, Q, hnat, hcross⟩ := independentLiftCrossNaturalPredecessorCoefficientProduction
    d k D N R count hh n qs m hhh hn hnN hnD hm α out inp BG BV BE B hBG hBV hBE hB
  refine ⟨C, hC, Q, hnat, ?_⟩
  intro x y U Y Z hU hzero he hc t z
  refine hcross x y Y Z ?_ ?_ ?_ ?_ ?_ ?_ t z
  · rw [he.matrix]
  · exact he.window_left
  · exact he.window_right
  · exact he.drift
  · intro r
    ext i j
    simpa only [map_zero, zero_add] using he.metric i j r 0 hzero (0 : Vec 2)
  · intro p r w
    have hs := independentLiftPredecessorSource_slow_slice_congr
      x.toIndependentLiftPredecessorDatum y.toIndependentLiftPredecessorDatum
      Y Z hU he hc ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) hn hnD out inp r 0 hzero w
    simpa only [map_zero, zero_add] using hs

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual independent inverse step consumes genuine earlier productions at the geometric
reserve orders. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftPrimitivePredecessorProduction (d base D N R count qs hh n m : ℕ)
    (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hND : N ≤ D) (hm : m ≤ n)
    (α : DerivativeWord2 m) (out inp : ι) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ S : IndependentLiftPrimitiveData ι d
      (independentLiftPrimitiveTopOrder base D N R) D N R count BG BV BE,
      S.sZ = qs → ∀ _P : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ l, l ≤ q →
        ∀ β : DerivativeWord2 l, ∀ v u,
        IndependentScalarCoefficientProduction (2 + d)
          (4 * liftProductionOrder base D N R hh n + 2 * D + 7) q S.a S.b S.U
          (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
          (independentIntrinsicSlowProjection d) l β v u (finiteMatrixPower S.M p v u) B,
      Nonempty (IndependentScalarCoefficientProduction (2 + d)
        (liftProductionOrder base D N R hh n) n S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α out inp (finiteMatrixPower S.M hh out inp) C) := by
  let k := liftProductionOrder base D N R hh n
  obtain ⟨C, hC, hprod⟩ := independentLiftPredecessorCoefficientProduction d k D N R count hh n qs m
    hhh hn hnN (hnN.trans hND) hm α out inp BG BV BE B hBG hBV hBE hB
  refine ⟨1 + C, le_add_of_nonneg_right hC, ?_⟩
  intro S hqs P
  have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
    have ho := liftProductionOrder_le_initial base D N R hh n
    dsimp only [independentLiftPrimitiveTopOrder, k]
    omega
  let T := S.monoOrder (4 * k + 5) horder
  let x : IndependentLiftPredecessorDatum ι d (4 * k + 5) D N R count hh n qs BG BV BE B :=
    ⟨T, hqs, by
      have he : 4 * k + 5 + 2 * D + 2 = 4 * liftProductionOrder base D N R hh n + 2 * D + 7 := by
        dsimp only [k]
        omega
      rw [he]
      exact P⟩
  obtain ⟨Q⟩ := hprod x
  exact ⟨Q.enlargeBudget (1 + C) (le_add_of_nonneg_left zero_le_one)
    (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh out inp)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite index menu fixes one common inverse-step price before native data are chosen. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

abbrev IndependentLiftPositiveIndex (ι : Type*) (R N : ℕ) :=
  Σ _hh : Fin (R + 1), Σ n : {n : Fin (N + 1) // 1 ≤ n.val},
    Σ m : Fin (n.val.val + 1), DerivativeWord2 m.val × ι × ι

def independentFiniteStepBudget {I : Type*} [Fintype I] (C : I → ℝ) : ℝ := 1 + ∑ i, C i

theorem independentFiniteStepBudget_one_le {I : Type*} [Fintype I] (C : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) : 1 ≤ independentFiniteStepBudget C :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i)

theorem independentFiniteStepBudget_entry_le {I : Type*} [Fintype I] (C : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) (i : I) : C i ≤ independentFiniteStepBudget C :=
  (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Strong finite-rank induction produces true independent coefficient reserves for every native datum. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftRankProduction (d base D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (r : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ S : IndependentLiftPrimitiveData ι d
      (independentLiftPrimitiveTopOrder base D N R) D N R count BG BV BE,
      S.sZ = qs → ∀ hh n, hh ≤ R → n ≤ N → ambientRecurrenceRank N hh n = r →
      ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      Nonempty (IndependentScalarCoefficientProduction (2 + d)
        (liftProductionOrder base D N R hh n) n S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C) := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    choose C hC hprod using fun p : Fin r => ih p.val p.isLt
    let B := finitePriorRankBudget r C
    have hBC : 1 ≤ B := finitePriorRankBudget_one_le r C (fun p => zero_le_one.trans (hC p))
    let I := IndependentLiftPositiveIndex ι R N
    have hstep (i : I) := independentLiftPrimitivePredecessorProduction d base D N R count qs
      i.1.val i.2.1.val.val i.2.2.1.val (by have := i.1.isLt; omega) i.2.1.property
      (by have := i.2.1.val.isLt; omega) hND (by have := i.2.2.1.isLt; omega)
      i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 BG BV BE B hBG hBV hBE (zero_le_one.trans hBC)
    choose A hA hstepProd using hstep
    let K := independentFiniteStepBudget A
    have hK : 1 ≤ K := independentFiniteStepBudget_one_le A (fun i => zero_le_one.trans (hA i))
    refine ⟨K, hK, ?_⟩
    intro S hqs hh n hhh hnN hr m hm α v u
    by_cases hn0 : n = 0
    · subst n
      exact S.zero_degree_production _ hh m hhh hm α v u K hK
    · have hn : 1 ≤ n := by omega
      have earlier : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ l, l ≤ q →
          ∀ β : DerivativeWord2 l, ∀ v u,
          Nonempty (IndependentScalarCoefficientProduction (2 + d)
            (4 * liftProductionOrder base D N R hh n + 2 * D + 7) q S.a S.b S.U
            (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
            (independentIntrinsicSlowProjection d) l β v u (finiteMatrixPower S.M p v u) B) := by
        intro p q hpq l hl β v u
        have hpR : p ≤ R := by rcases hpq with h | ⟨rfl, _⟩ <;> omega
        by_cases hq : q ≤ N
        · have hprior : ambientRecurrenceRank N p q < r := by
            rw [← hr]
            rcases hpq with hp | ⟨rfl, hqn⟩
            · exact ambientRecurrenceRank_height N hh n p q hp hq
            · exact ambientRecurrenceRank_composition N p n p q le_rfl hnN hqn
          let j : Fin r := ⟨ambientRecurrenceRank N p q, hprior⟩
          obtain ⟨Q⟩ := hprod j S hqs p q hpR hq rfl l hl β v u
          have ho := liftProductionOrder_predecessor_room base D N R hh n p q hhh hnN hq hpq
          exact ⟨(Q.monoOrder _ ho).enlargeBudget B
            (priorRankBudget_le_common r C (fun j => zero_le_one.trans (hC j)) j)
            (finiteMatrixPower_nonneg S.M S.matrix_nonneg p v u)⟩
        · exact S.above_degree_production _ p q l hpR (by omega) β v u B (zero_le_one.trans hBC)
      let P := fun p q hpq l hl β v u => Classical.choice (earlier p q hpq l hl β v u)
      let i : I := ⟨⟨hh, by omega⟩, ⟨⟨n, by omega⟩, hn⟩, ⟨m, by change m < n + 1; omega⟩, α, v, u⟩
      obtain ⟨Q⟩ := hstepProd i S hqs P
      exact ⟨Q.enlargeBudget K
        (independentFiniteStepBudget_entry_le A (fun i => zero_le_one.trans (hA i)) i)
        (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! One finite menu price covers every produced native coefficient at the requested full parameter reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftFiniteProduction (d base D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ S : IndependentLiftPrimitiveData ι d
      (independentLiftPrimitiveTopOrder base D N R) D N R count BG BV BE,
      S.sZ = qs → ∀ hh n, hh ≤ R → n ≤ N →
      ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      Nonempty (IndependentScalarCoefficientProduction (2 + d) base n S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C) := by
  choose C hC hprod using fun r : Fin (liftProductionRankMax N R + 1) =>
    independentLiftRankProduction (ι := ι) d base D N R count qs BG BV BE hND hBG hBV hBE r.val
  let B := finitePriorRankBudget (liftProductionRankMax N R + 1) C
  have hB : 1 ≤ B := finitePriorRankBudget_one_le _ C (fun r => zero_le_one.trans (hC r))
  refine ⟨B, hB, ?_⟩
  intro S hqs hh n hhh hn m hm α v u
  let r : Fin (liftProductionRankMax N R + 1) :=
    ⟨ambientRecurrenceRank N hh n, Nat.lt_succ_of_le (liftProductionRank_le N R hh n hhh hn)⟩
  obtain ⟨Q⟩ := hprod r S hqs hh n hhh hn rfl m hm α v u
  have ho : base ≤ liftProductionOrder base D N R hh n := by
    exact (Nat.le_succ base).trans
      (weakJointRecurrenceReserve_base (4 * (D + 4)) base (liftProductionRankMax N R)
        (ambientRecurrenceRank N hh n) (by omega))
  exact ⟨(Q.monoOrder base ho).enlargeBudget B
    (priorRankBudget_le_common _ C (fun r => zero_le_one.trans (hC r)) r)
    (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! A uniform actual rank step retains cross-family equality and the phase reserve. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCrossNaturalStepCoefficientProduction (d base D N R count qs hh n m : ℕ)
    (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hND : N ≤ D) (hm : m ≤ n)
    (α : DerivativeWord2 m) (out inp : ι) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x :
      IndependentLiftNaturalProductionStepDatum ι d base D N R count qs hh n BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d)
        (liftProductionOrder base D N R hh n) n x.data.primitive.a x.data.primitive.b
        x.data.primitive.U
        (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α out inp
        (finiteMatrixPower x.data.primitive.M hh out inp) C,
      (∀ x δ, δ ∈ x.data.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        (∀ p q hpq l hl β v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.earlier p q hpq l hl β v u).field (y.earlier p q hpq l hl β v u).field) →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  let k := liftProductionOrder base D N R hh n
  obtain ⟨C, hC, Qcore, hnat, hcross⟩ := independentLiftCrossNaturalPredecessorGermProduction
    d k D N R count hh n qs m hhh hn hnN (hnN.trans hND) hm α out inp
    BG BV BE B hBG hBV hBE hB
  let Q := fun x : IndependentLiftNaturalProductionStepDatum ι d base D N R count qs hh n BG BV BE B =>
    (Qcore x.restrict).enlargeBudget (1 + C) (le_add_of_nonneg_left zero_le_one)
      (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg hh out inp)
  refine ⟨1 + C, le_add_of_nonneg_right hC, Q, ?_, ?_⟩
  · intro x δ hδ
    exact hnat x.restrict δ hδ
  · intro x y U Y Z hU hzero he hc t z
    have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
      have ho := liftProductionOrder_le_initial base D N R hh n
      dsimp only [independentLiftPrimitiveTopOrder, k]
      omega
    have hre : IndependentLiftPrimitiveSlowSliceEq x.restrict.primitive y.restrict.primitive U Y Z :=
      he.monoOrder (4 * k + 5) horder
    apply hcross x.restrict y.restrict U Y Z hU hzero hre ?_ t z
    intro p q hpq l β v u
    exact independentLiftPredecessorFields_slow_slice_congr
      x.restrict.toIndependentLiftPredecessorDatum y.restrict.toIndependentLiftPredecessorDatum Y Z
      (fun p q hpq l hl β v u => hc p q hpq l hl β v u) p q hpq l β v u

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full native menu reconstructs literal finite coefficient fields with global initial and cutoff clauses. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ}

abbrev IndependentLiftMenuProductions (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (base : ℕ) (B : ℝ) :=
  ∀ hh n, hh ≤ R → n ≤ N → ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) base n S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) B

def independentFiniteLiftFields (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) (v u : ι) : ℝ :=
  if hhh : hh ≤ R then
    if hn : n ≤ N then
      if n = 0 then
        if hh = 0 ∧ m = 0 then if v = u then 1 else 0 else 0
      else independentCoefficientProductionFields (P hh n hhh hn) m α t z Y v u
    else 0
  else 0

theorem independentFiniteLiftFields_positive_zero_degree
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh : ℕ) (hhh : hh ≠ 0)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) (v u : ι) :
    independentFiniteLiftFields S P hh 0 m α t z Y v u = 0 := by
  by_cases hR : hh ≤ R
  · simp only [independentFiniteLiftFields, dite_eq_left hR, dite_eq_left (Nat.zero_le N),
      ite_true, ite_eq_right (show ¬ (hh = 0 ∧ m = 0) from fun h => hhh h.1)]
  · simp only [independentFiniteLiftFields, dite_eq_right hR]

theorem independentFiniteLiftFields_above_degree
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh n m : ℕ) (hn : N < n)
    (α : DerivativeWord2 m) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) (v u : ι) :
    independentFiniteLiftFields S P hh n m α t z Y v u = 0 := by
  by_cases hR : hh ≤ R
  · simp only [independentFiniteLiftFields, dite_eq_left hR, dite_eq_right (Nat.not_le.mpr hn)]
  · simp only [independentFiniteLiftFields, dite_eq_right hR]

theorem independentFiniteLiftFields_perm
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh n m : ℕ) (α : DerivativeWord2 m)
    (σ : Equiv.Perm (Fin m)) :
    independentFiniteLiftFields S P hh n m (α ∘ σ) = independentFiniteLiftFields S P hh n m α := by
  funext t z Y v u
  simp only [independentFiniteLiftFields, independentCoefficientProductionFields]
  rw [canonicalDerivativeWord_comp_perm α σ]

theorem independentFiniteLiftFields_translation_invariant
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (δ : Vec (2 + d))
    (hP : ∀ hh n hhh hn m hm α v u,
      IndependentSourceTranslationInvariant δ (P hh n hhh hn m hm α v u).field)
    (hh n m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IndependentSourceTranslationInvariant δ (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u) := by
  intro t z Y
  dsimp only [independentFiniteLiftFields]
  split
  · split
    · split
      · rfl
      · dsimp only [independentCoefficientProductionFields]
        split
        · exact hP _ _ _ _ _ _ _ _ _ t z Y
        · rfl
    · rfl
  · rfl

theorem independentFiniteLiftFields_copy_positive
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh n m : ℕ) (hhh : hh ≤ R) (hn : n ≤ N)
    (hn0 : n ≠ 0) (hm : m ≤ n) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc S.a S.b)
    (Y : Vec (2 + d)) (hY : Y ∈ S.U) (z : Vec 2) (v u : ι) :
    independentFiniteLiftFields S P hh n m α t z Y v u =
      S.Cc (independentStoredParameterProjection d Y) hh n m α t
        (independentIntrinsicSlowProjection d Y) z v u 1 := by
  simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn, ite_eq_right hn0]
  exact independentCoefficientProductionFields_copy (P hh n hhh hn) m hm
    (fun Y β σ => S.symmetric _ hh hhh n m β σ) α t ht Y hY z v u

theorem independentFiniteLiftFields_mean_zero
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hh n m : ℕ) (hnpos : 1 ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (Y : Vec (2 + d)) (v u : ι) :
    fieldCellMean (fun z => independentFiniteLiftFields S P hh n m α t z Y v u) = 0 := by
  by_cases hhh : hh ≤ R
  · by_cases hn : n ≤ N
    · have hn0 : n ≠ 0 := by omega
      simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn, ite_eq_right hn0]
      by_cases hm : m ≤ n
      · exact independentCoefficientProductionFields_mean_zero (P hh n hhh hn) hnpos m hm α t Y v u
      · simp only [independentCoefficientProductionFields, dite_eq_right hm, fieldCellMean_zero]
    · simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_right hn, fieldCellMean_zero]
  · simp only [independentFiniteLiftFields, dite_eq_right hhh, fieldCellMean_zero]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every reconstructed native coefficient is a full independent source with its literal matrix weight. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteLiftFields_reserve
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hh n m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    ∃ Q : IndependentParameterSourceReserve base
      (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u),
      ∀ j ≤ base, Q.budget j ≤ finiteMatrixPower S.M hh v u * B := by
  have hz (he : (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u) =
      fun _ _ _ => 0) :
      ∃ Q : IndependentParameterSourceReserve base
        (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u),
        ∀ j ≤ base, Q.budget j ≤ finiteMatrixPower S.M hh v u * B := by
    let Q : IndependentParameterSourceReserve base
      (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u) := (IndependentParameterSourceReserve.zero (P := Vec (2 + d)) (E := ℝ) base).congrSource he.symm
    refine ⟨Q, ?_⟩
    intro j hj
    dsimp only [Q]
    rw [IndependentParameterSourceReserve.congrSource_budget]
    change 0 ≤ finiteMatrixPower S.M hh v u * B
    exact mul_nonneg (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u) (zero_le_one.trans hB)
  by_cases hhh : hh ≤ R
  · by_cases hn : n ≤ N
    · by_cases hn0 : n = 0
      · by_cases h0 : hh = 0 ∧ m = 0
        · let Q : IndependentParameterSourceReserve base
            (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u) := (IndependentParameterSourceReserve.const (P := Vec (2 + d)) base
            (if v = u then (1 : ℝ) else 0)).congrSource (by
              funext t z Y
              simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn,
                ite_eq_left hn0, ite_eq_left h0])
          refine ⟨Q, ?_⟩
          intro j hj
          dsimp only [Q]
          rw [IndependentParameterSourceReserve.congrSource_budget]
          rw [h0.1]
          apply (constant_test_matrix_budget base S.M v u j).trans
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hB
            (finiteMatrixPower_nonneg S.M S.matrix_nonneg 0 v u)
        · apply hz
          funext t z Y
          simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn,
            ite_eq_left hn0, ite_eq_right h0]
      · by_cases hm : m ≤ n
        · let Q : IndependentParameterSourceReserve base
            (fun t z Y => independentFiniteLiftFields S P hh n m α t z Y v u) := (P hh n hhh hn m hm (canonicalDerivativeWord α) v u).reserve.congrSource (by
            funext t z Y
            simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn,
              ite_eq_right hn0, independentCoefficientProductionFields, dite_eq_left hm])
          refine ⟨Q, ?_⟩
          intro j hj
          dsimp only [Q]
          rw [IndependentParameterSourceReserve.congrSource_budget]
          exact (P hh n hhh hn m hm (canonicalDerivativeWord α) v u).bound j hj
        · apply hz
          funext t z Y
          simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_left hn,
            ite_eq_right hn0, independentCoefficientProductionFields, dite_eq_right hm]
    · apply hz
      funext t z Y
      simp only [independentFiniteLiftFields, dite_eq_left hhh, dite_eq_right hn]
  · apply hz
    funext t z Y
    simp only [independentFiniteLiftFields, dite_eq_right hhh]

end AVRegularity.EntryWeakProofs
end
end
end

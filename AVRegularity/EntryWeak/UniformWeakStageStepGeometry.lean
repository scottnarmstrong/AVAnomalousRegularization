-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentWeakInheritedMeanMenu
public import AVRegularity.EntryWeak.IndependentActualCoarseEddyCopy
import AVRegularity.Construction.EntryScales.TerminalCore

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! One finite reserve order supplies every actual inherited path grade. -/

def weakInheritedPrimitiveMenuOrder (H D N R : ℕ) : ℕ :=
  ∑ h : Fin (R + 1), independentLiftPrimitiveTopOrder (H + D + 2) D N h.val

theorem weakInheritedPrimitiveMenuOrder_entry (H D N R h : ℕ) (hh : h ≤ R) :
    independentLiftPrimitiveTopOrder (H + D + 2) D N h ≤ weakInheritedPrimitiveMenuOrder H D N R :=
  finiteNatMenu_entry_le_sum (fun h => independentLiftPrimitiveTopOrder (H + D + 2) D N h) R h hh

def weakInheritedPrimitiveMenuInput {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d H D N R h count qs : ℕ} {BG BV BE : ℝ}
    (x : IndependentLiftNaturalPrimitiveDatum ι d (weakInheritedPrimitiveMenuOrder H D N R)
      D N h count qs BG BV BE) (hh : h ≤ R) :
    IndependentInheritedMeanInput ι d H D N h count qs BG BV BE :=
  x.restrictRegularity _ (weakInheritedPrimitiveMenuOrder_entry H D N R h hh)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Coherent inherited producers consume one common primitive order throughout a stage. -/

namespace IndependentWeakInheritedMeanIndex
variable {J R K : ℕ}

def ofOrders (r h n d : ℕ) (hr : r ≤ J) (hh : h ∈ Finset.Icc 1 R)
    (hn : n ∈ Finset.Icc 2 K) (hd : d ∈ Finset.Icc 2 n)
    (word : DerivativeWord2 (d - 1)) : IndependentWeakInheritedMeanIndex J R K :=
  ⟨⟨r, Nat.lt_succ_of_le hr⟩, ⟨h, hh⟩, ⟨n, hn⟩, ⟨d, hd⟩, word⟩

theorem grade_le (j : IndependentWeakInheritedMeanIndex J R K) : j.grade ≤ R :=
  (Finset.mem_Icc.mp j.2.1.property).2

end IndependentWeakInheritedMeanIndex

structure IndependentWeakInheritedMeanProducer (J H K N R sZ : ℕ) (BG BV BE : ℝ) where
  budget : ℝ
  budget_nonneg : 0 ≤ budget
  output : ∀ j : IndependentWeakInheritedMeanIndex J R K,
    IndependentInheritedMeanNaturalOutput (Fin (j.grade + 1)) (4 * j.depth)
      H K N j.grade 1 sZ j.grade j.degree (j.testedOrder - 1) j.word BG BV BE budget

def independentWeakInheritedMeanProducer (J H K N R sZ : ℕ)
    (hNK : N ≤ K) (hK : 1 ≤ K) (BG BV BE : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE := Classical.choice (by
  obtain ⟨C, hC, hprod⟩ := independentWeakInheritedMeanMenuProduction
    J H K N R sZ hNK hK BG BV BE hBG hBV hBE
  exact ⟨⟨C, hC, fun j => Classical.choice (hprod j)⟩⟩)

namespace IndependentWeakInheritedMeanProducer
variable {J H K N R sZ : ℕ} {BG BV BE : ℝ}

abbrev Input (j : IndependentWeakInheritedMeanIndex J R K) :=
  IndependentLiftNaturalPrimitiveDatum (Fin (j.grade + 1)) (4 * j.depth)
    (weakInheritedPrimitiveMenuOrder H K N R) K N j.grade 1 sZ BG BV BE

def field (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE)
    (j : IndependentWeakInheritedMeanIndex J R K) (x : Input (sZ := sZ) (BG := BG) (BV := BV) (BE := BE) j) :=
  (E.output j).field (weakInheritedPrimitiveMenuInput x j.grade_le)

theorem production (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE)
    (j : IndependentWeakInheritedMeanIndex J R K) (x : Input (sZ := sZ) (BG := BG) (BV := BV) (BE := BE) j)
    (out inp : Fin (j.grade + 1)) :
    ∃ Q : IndependentParameterSourceReserve H (E.field j x out inp),
      (∀ r ≤ H, Q.budget r ≤ finiteMatrixPower x.primitive.M j.grade out inp * E.budget) ∧
      (∀ δ ∈ x.translations, IndependentSourceTranslationInvariant δ (E.field j x out inp)) := by
  obtain ⟨Q, hQ, _hcopy, hphase⟩ := (E.output j).production
    (weakInheritedPrimitiveMenuInput x j.grade_le) out inp
  exact ⟨Q, hQ, hphase⟩

theorem cross (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE)
    (j : IndependentWeakInheritedMeanIndex J R K)
    (x y : Input (sZ := sZ) (BG := BG) (BV := BV) (BE := BE) j)
    (U : Set (Vec 2)) (Y Z : Vec (2 + 4 * j.depth))
    (hU : IsOpen U) (hzero : (0 : Vec 2) ∈ U)
    (he : IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z)
    (out inp : Fin (j.grade + 1)) :
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding (4 * j.depth)) U Y Z
      (E.field j x out inp) (E.field j y out inp) := by
  apply (E.output j).cross _ _ U Y Z hU hzero _ out inp
  exact ⟨he.window_left, he.window_right, he.drift, he.matrix, he.edge, he.metric, he.edge_fields⟩

end IndependentWeakInheritedMeanProducer

end AVRegularity.EntryWeakProofs
end
end

section
section
/-! Positive-response means compare different charts of the same finite depth. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem independentEddy_equalDepth_cross
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J H K N R count qs : ℕ} {BG BV BE : ℝ}
    (E : IndependentPositiveEddyDepthProducer ι J H K N R count qs BG BV BE)
    (r s : Fin (J + 1)) (hrs : r.val = s.val)
    (x : IndependentPositiveNaturalPrimitiveDatum ι (4 * r.val) H K N R count qs BG BV BE)
    (y : IndependentPositiveNaturalPrimitiveDatum ι (4 * s.val) H K N R count qs BG BV BE)
    (U : Set (Vec 2)) (Y : Vec (2 + 4 * r.val)) (Z : Vec (2 + 4 * s.val))
    (hU : IsOpen U) (hzero : (0 : Vec 2) ∈ U) (hresponse : x.response = y.response)
    (he : IndependentLiftHeterogeneousSliceEq x.data.primitive y.data.primitive U Y Z)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ) (hm : m ≤ n)
    (word : DerivativeWord2 m) (out inp : ι) :
    ∀ t X, X ∈ U → ∀ z,
      E.field r x n hn hnN m hm word out inp t z
          (independentIntrinsicSlowEmbedding (4 * r.val) X + Y) =
        E.field s y n hn hnN m hm word out inp t z
          (independentIntrinsicSlowEmbedding (4 * s.val) X + Z) := by
  have hrs' : r = s := Fin.ext hrs
  subst s
  exact E.cross r x y U Y Z hU hzero hresponse he.sameDimension n hn hnN m hm word out inp

end AVRegularity.EntryWeakProofs
end
end

section
/-! Signed physical inherited fields retain the literal path witness and common-chart naturality. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
namespace IndependentWeakInheritedMeanProducer
variable {J H K N R sZ : ℕ} {BG BV BE : ℝ}

def physicalField (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE)
    (j : IndependentWeakInheritedMeanIndex J R K)
    (x : Input (H := H) (N := N) (sZ := sZ) (BG := BG) (BV := BV) (BE := BE) j)
    (D : OCData) (level : ℕ) : ℝ → Vec 2 → Vec (2 + 4 * j.depth) → Vec 2 :=
  independentProducedFluxSource
    (D.κ D.term * D.eps level ^ (j.degree - 2) *
      D.eps (level - 1) ^ ((j.testedOrder : ℝ) - (j.degree : ℝ)))
    (fun t => (D.cellScaleSq level)⁻¹ * t) (fun t _ Y => E.field j x (Fin.last j.grade) 0 t 0 Y)

theorem physicalField_production
    (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV BE)
    (j : IndependentWeakInheritedMeanIndex J R K)
    (x : Input (H := H) (N := N) (sZ := sZ) (BG := BG) (BV := BV) (BE := BE) j)
    (D : OCData) (level : ℕ) (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i) :
    ∃ Q : IndependentParameterSourceReserve H (E.physicalField j x D level),
      (∀ r ≤ H, Q.budget r ≤ finiteMatrixPower x.primitive.M j.grade (Fin.last j.grade) 0 *
        (D.κ D.term * D.eps level ^ (j.degree - 2) *
          D.eps (level - 1) ^ ((j.testedOrder : ℝ) - (j.degree : ℝ)) * E.budget)) ∧
      (∀ δ ∈ x.translations, IndependentSourceTranslationInvariant δ (E.physicalField j x D level)) := by
  obtain ⟨Q, hQ, hphase⟩ := E.production j x (Fin.last j.grade) 0
  let c := D.κ D.term * D.eps level ^ (j.degree - 2) *
    D.eps (level - 1) ^ ((j.testedOrder : ℝ) - (j.degree : ℝ))
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hκ (pow_nonneg (hε level).le _))
    (Real.rpow_pos_of_pos (hε _) _).le
  have hclock : Measurable (fun t : ℝ => (D.cellScaleSq level)⁻¹ * t) :=
    measurable_const.mul measurable_id
  refine ⟨independentProducedFluxReserve H c _ hclock _ (Q.freezeFast 0), ?_, ?_⟩
  · intro r hr
    exact independentProducedFluxReserve_budget H c hc _ hclock _ (Q.freezeFast 0) _ E.budget hQ r hr
  · intro δ hδ t z Y
    exact congrArg (fun v : Vec 2 => (-c) • v) (hphase δ hδ _ 0 Y)

end IndependentWeakInheritedMeanProducer
end AVRegularity.EntryWeakProofs
end
end

section
/-! The coherently produced inherited field is the coefficient of the actual localized physical mean flux. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {dP H D N R count qs hh n d : ℕ} {BG BV BE C : ℝ} {α : DerivativeWord2 (d - 1)}

theorem independentInheritedProducedPhysicalMean_copy_on
    (E : IndependentInheritedMeanNaturalOutput ι dP H D N R count qs hh n (d - 1) α BG BV BE C)
    (x : IndependentInheritedMeanInput ι dP H D N R count qs BG BV BE)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE)
    (Y : Vec (2 + dP)) (hY : Y ∈ x.primitive.U)
    (V : Set (Vec dP)) (c : Vec dP → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hCc : x.primitive.Cc = independentCarrierCoefficientExtension V c)
    (hP : independentStoredParameterProjection dP Y ∈ V)
    (Ω : Set (Vec 2)) (Q : LiftOperatorData ι (fun _ => ℝ) D) (sX sZ : ℕ)
    (hc : IsLiftSequenceOn Ω Q sX sZ x.primitive.a x.primitive.b N R
      (c (independentStoredParameterProjection dP Y)))
    (hη : Q.η = 1) (hv : Q.v = x.primitive.v)
    (hD : 1 ≤ D) (hhh : hh ≤ R) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (hd : d - 1 ≤ n - 1)
    (a ρ : ℝ) (hρ : ρ ≠ 0) (t : ℝ) (ht : t ∈ Icc x.primitive.a x.primitive.b) (y : Vec 2)
    (hpoint : ρ⁻¹ • y = independentIntrinsicSlowProjection dP Y)
    (hG : Q.G t (independentIntrinsicSlowProjection dP Y) = x.primitive.G t Y)
    (he : SlowOpenEdgeEq (independentIntrinsicSliceCarrier dP x.primitive.U Y) t Q.edge
      (independentConstituentEdgeSlice x.primitive.edge x.primitive.edgeField x.primitive.edges
        (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y))) (v u : ι) :
    fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q
      (c (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single u (f (ρ • X)))
        hh n t (ρ⁻¹ • W) z k) v) d α y =
      fun k => (a * ρ ^ (d - 1)) * E.field x v u t 0 Y k := by
  obtain ⟨B, hB, hprod⟩ := independentLiftFiniteProduction (ι := ι)
    dP (H + D + 2) D N R count qs BG BV BE hND hBG hBV hBE
  let P : IndependentLiftMenuProductions x.primitive (H + D + 2) B :=
    fun p q hp hq m hm β v u => (hprod x.primitive x.fastOrder p q hp hq m hm β v u).some
  have hcopy := independentPhysicalMeanFlux_native_copy_on x.primitive P hB Y hY
    V c hCc hP Ω Q sX sZ hc hη hv hD (by omega) hh n hhh hn hhpos d hd α a ρ hρ t ht y hpoint hG he v u
  obtain ⟨_Qf, _hQf, hfield, _hphase⟩ := E.production x v u
  refine hcopy.trans ?_
  funext k
  rw [hpoint]
  rw [hfield t ht Y hY 0 k]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The finite mean menu gives one complete source array; unused orders are zero. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {J H K N R sZ : ℕ} {BG BV B : ℝ}

def weakInheritedPhysicalArray
    (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV B)
    (r : Fin (J + 1)) (h : Finset.Icc 1 R) (n : Finset.Icc 2 K)
    (x : IndependentLiftNaturalPrimitiveDatum (Fin (h.val + 1)) (4 * r.val)
      (weakInheritedPrimitiveMenuOrder H K N R) K N h.val 1 sZ BG BV B)
    (D : OCData) (level d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * r.val) → Vec 2 :=
  if hd : d ∈ Finset.Icc 2 n.val then
    E.physicalField ⟨r, h, n, ⟨d, hd⟩, word⟩ x D level
  else fun _ _ _ => 0

theorem weakInheritedPhysicalArray_production
    (E : IndependentWeakInheritedMeanProducer J H K N R sZ BG BV B)
    (r : Fin (J + 1)) (h : Finset.Icc 1 R) (n : Finset.Icc 2 K)
    (x : IndependentLiftNaturalPrimitiveDatum (Fin (h.val + 1)) (4 * r.val)
      (weakInheritedPrimitiveMenuOrder H K N R) K N h.val 1 sZ BG BV B)
    (D : OCData) (level : ℕ) (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (weakInheritedPhysicalArray E r h n x D level d word),
      (∀ k ≤ H, Q.budget k ≤ finiteMatrixPower x.primitive.M h.val (Fin.last h.val) 0 *
        (D.κ D.term * D.eps level ^ (n.val - 2) *
          D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)) * E.budget)) ∧
      (∀ δ ∈ x.translations, IndependentSourceTranslationInvariant δ
        (weakInheritedPhysicalArray E r h n x D level d word)) := by
  by_cases hd : d ∈ Finset.Icc 2 n.val
  · have he : weakInheritedPhysicalArray E r h n x D level d word =
        E.physicalField ⟨r, h, n, ⟨d, hd⟩, word⟩ x D level := by
      unfold weakInheritedPhysicalArray
      exact dite_eq_left hd
    rw [he]
    exact E.physicalField_production ⟨r, h, n, ⟨d, hd⟩, word⟩ x D level hκ hε
  · have he : weakInheritedPhysicalArray E r h n x D level d word = fun _ _ _ => 0 := by
      unfold weakInheritedPhysicalArray
      exact dite_eq_right hd
    rw [he]
    refine ⟨IndependentParameterSourceReserve.zero H, ?_, fun _ _ _ _ _ => rfl⟩
    intro k _hk
    exact mul_nonneg (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg _ _ _)
      (mul_nonneg (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _))
        (Real.rpow_pos_of_pos (hε _) _).le) E.budget_nonneg)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual path mean reads its produced coefficient with the exact weak dimensional factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {dP H K N h qs n d : ℕ} {BG BV BE C : ℝ} {α : DerivativeWord2 (d - 1)}

theorem weakData_pathMeanFlux_produced_coefficient
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m : ℕ) (hm : D.term < m)
    (E : IndependentInheritedMeanNaturalOutput (Fin (h + 1)) dP H K N h 1 qs h n (d - 1) α BG BV BE C)
    (x : IndependentInheritedMeanInput (Fin (h + 1)) dP H K N h 1 qs BG BV BE)
    (hND : N ≤ K) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE)
    (Y : Vec (2 + dP)) (hY : Y ∈ x.primitive.U)
    (V : Set (Vec dP)) (c : Vec dP → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hCc : x.primitive.Cc = independentCarrierCoefficientExtension V c)
    (hP : independentStoredParameterProjection dP Y ∈ V)
    (Ω : Set (Vec 2)) (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) K) (sX sZ : ℕ)
    (hc : IsLiftSequenceOn Ω Q sX sZ x.primitive.a x.primitive.b N h
      (c (independentStoredParameterProjection dP Y)))
    (hη : Q.η = 1) (hv : Q.v = x.primitive.v)
    (hK : 1 ≤ K) (hn : 2 ≤ n) (hhpos : h ≠ 0) (hd : d - 1 ≤ n - 1)
    (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ)
    (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc x.primitive.a x.primitive.b) (y : Vec 2)
    (hpoint : ρ⁻¹ • y = independentIntrinsicSlowProjection dP Y)
    (hG : Q.G ((D.cellScaleSq m)⁻¹ * t) (independentIntrinsicSlowProjection dP Y) = x.primitive.G ((D.cellScaleSq m)⁻¹ * t) Y)
    (he : SlowOpenEdgeEq (independentIntrinsicSliceCarrier dP x.primitive.U Y) ((D.cellScaleSq m)⁻¹ * t) Q.edge
      (independentConstituentEdgeSlice x.primitive.edge x.primitive.edgeField x.primitive.edges
        (independentIntrinsicSlowEmbedding dP) (independentIntrinsicSliceOffset dP Y))) (hd₁ : 1 ≤ d) :
    fluxCoeff (pathMeanFlux D m ρ Q (c (independentStoredParameterProjection dP Y)) n t) d α y =
      -(D.κ D.term * D.eps m ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) •
        E.field x (Fin.last h) 0 ((D.cellScaleSq m)⁻¹ * t) 0 Y := by
  let a := -((D.cellScaleSq m)⁻¹ *
    (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ)
  have hc' := independentInheritedProducedPhysicalMean_copy_on E x hND hBG hBV hBE
    Y hY V c hCc hP Ω Q sX sZ hc hη hv hK le_rfl hn hhpos hd a ρ hρ.ne'
    ((D.cellScaleSq m)⁻¹ * t) ht y hpoint hG he (Fin.last h) 0
  have hscale : a * ρ ^ (d - 1) =
      -(D.κ D.term * D.eps m ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) := by
    dsimp only [a]
    rw [neg_mul, weakData_flux_dimensional_count D hΛ hζ hband m hm ρ hρ n d hn hd₁]
  rw [hscale] at hc'
  change fluxCoeff (fun f W k => a * fieldCellMean (fun z => liftFluxX Q
      (c (independentStoredParameterProjection dP Y)) (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X)))
        h n ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • W) z k) (Fin.last h)) d α y =
      fun k => -(D.κ D.term * D.eps m ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ))) *
        E.field x (Fin.last h) 0 ((D.cellScaleSq m)⁻¹ * t) 0 Y k
  exact hc' 

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced stage fields and the supplied original histories construct the actual inherited primitive. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_inherited_primitive_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J O K : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ) (hKD : K ≤ Dm), ∀ bw j₀ (G : GenStage D (fun _ => ℝ) Dm bw j₀),
      D.term < G.level → G.maxOrderBound K → ∀ minBase H (B : ℝ), M₀ ≤ minBase → 0 ≤ B →
      O + K + 1 ≤ H → ∀ S : IndependentWeakStageFluxProduction G minBase J H B,
      ∀ c : WeakStageProductionContext D bw j₀ G.level minBase J,
      ∀ h (π : StagePath G h) N sX sZ, N ≤ K →
      ∀ Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ),
      (∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
        IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
          (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
            (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
          (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
          ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          N h (Cc c.slot.1 A)) →
      ∃ x : IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
          O K N h 1 sZ BG BV B,
        x.primitive.a = D.slotStart G.level c.slot.1 / D.cellScaleSq G.level ∧
        x.primitive.b =
          (((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level ∧
        x.primitive.U = actualIndependentCoarseProductionCarrier D c.chain.1 bw
          (D.eps (G.level - 1)) j₀ G.level c.slot.1 ∧
        x.primitive.G = actualIndependentCoarseScaledExtendedMetric D c.chain.1 (D.eps (G.level - 1))
          (χ c.chain.1.children.length) x.primitive.a x.primitive.b ∧
        x.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ G.level (D.kap G.level) c.slot.1 ∧
        x.primitive.edge = restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)) ∧
        x.primitive.edgeField = restrictedIndependentEdgeField K hKD
          (independentPathTemplateField (S.pathIncomingField π c)) ∧
        x.primitive.M = weightedPathMatrix h (stagePathStoredWeight G π) ∧
        x.primitive.Cc = independentCarrierCoefficientExtension
          (actualIndependentCoarseStoredCarrier D c.chain.1 bw)
          (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P)) ∧
        x.translations = independentFreshPhaseTranslations c.chain.1.children.length := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, M₀, hM₀, hprod⟩ :=
    uniform_actual_independent_coarse_inherited_datum_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J O K
  refine ⟨χ, BG, BV, hχ, hBG, hBV, M₀, hM₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband Dm hKD bw j₀ G hweak hK minBase H B
    hbase hB hH S c h π N sX sZ hNK Cc hCc
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hq' : 1 < D.q := by rw [hDq]; exact hq.1
  let A := c.chain.1
  have hctx : A.ctxLevel = G.level := c.chain.2.1
  have hslot : A.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hA : IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A := by
    rw [hctx, hslot]
    exact c.chain.2
  have hlast : A.lastLevel = G.level - 1 := by
    change A.lastLevel + 1 = G.level at hctx
    omega
  let U := actualIndependentCoarseProductionCarrier D A bw (D.eps (G.level - 1)) j₀ G.level c.slot.1
  have hU : IsOpen U := actualIndependentCoarseProductionCarrier_isOpen D hΛ₁ A bw _ j₀ G.level c.slot.1 c.chain.2
  obtain ⟨Q, hQ, hnative⟩ := S.pathIncomingField_anchored_effective_production π hq' hΛ' hζ' hband
    hweak.le hB c (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩) K hKD (O + K + 1) hH
  have hmap : ∀ v u d γ, γ ∈ restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)) v u d → ‖γ.map‖ ≤ 1 := by
    intro v u d γ hγ
    exact pathEdges_maps_bound G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩) v u ⟨d.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ γ hγ
  have hcount : ∀ v u d, (restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)) v u d).length ≤ 1 := by
    intro v u d
    exact pathEdges_length_le_one G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩) v u _
  have hc := actualIndependentCoarsePath_isLiftSequenceOn_effective_order π c K hKD hK sX sZ N h hNK Cc hCc
  have hphase : ∀ δ ∈ independentFreshPhaseTranslations A.children.length,
      ∀ v u d γ, γ ∈ restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)) v u d → ∀ word,
      IndependentSourceTranslationInvariant δ (restrictedIndependentEdgeField K hKD
        (independentPathTemplateField (S.pathIncomingField π c)) v u d γ word) := by
    intro δ hδ v u d γ _hγ word
    exact S.pathIncomingField_translation π c δ hδ v u ⟨d.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ γ word
  have hUsub : U ⊆ actualIndependentCoarseLiftCarrier D A bw (D.eps (G.level - 1)) j₀ A.ctxLevel A.slot := by
    intro Y hY
    simpa only [hctx, hslot] using hY.1
  have hx := hprod D hterm hDα hDq hDΛ hDζ hstream hband A (hbase.trans c.base_bound)
    c.depth_bound (by rw [hctx]; exact hweak) bw j₀ hA (D.eps (G.level - 1))
    (Construction.Stream.ocEpsilon_pos hΛ₁) (by rw [hlast]) N h 1 sZ B (Fin (h + 1)) U hU hUsub sX
    (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D A P))
    (fun P => restrictConstituentEdges K hKD (actualIndependentCoarsePathEdges π c P))
    (restrictConstituentEdges K hKD (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩)))
    (restrictedIndependentEdgeField K hKD (independentPathTemplateField (S.pathIncomingField π c))) Q
    (weightedPathMatrix h (stagePathStoredWeight G π)) (stagePathStoredMatrix_nonneg G π) hQ hmap hcount
    (by simpa only [hctx, hslot] using hc)
    (by simpa only [actualIndependentCoarseExtendedSliceLiftData, actualIndependentCoarseSliceLiftData, hctx, hslot]
      using fun Y hY t _ht => hnative Y hY t) hphase
  simpa only [hctx, hslot] using hx

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual inherited primitive's geometry and labels, bundled for native readout. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap Hstage O K N h sZ : ℕ}
  {BG BV B : ℝ} {G : GenStage D (fun _ => ℝ) Dm bw j₀}

structure WeakStageInheritedPrimitiveRealization
    (S : IndependentWeakStageFluxProduction G minBase cap Hstage B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (π : StagePath G h) (hKD : K ≤ Dm) (χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (x : IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
      O K N h 1 sZ BG BV B) : Prop where
  left : x.primitive.a = D.slotStart G.level c.slot.1 / D.cellScaleSq G.level
  right : x.primitive.b =
    (((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level
  carrier : x.primitive.U = actualIndependentCoarseProductionCarrier D c.chain.1 bw
    (D.eps (G.level - 1)) j₀ G.level c.slot.1
  metric : x.primitive.G = actualIndependentCoarseScaledExtendedMetric D c.chain.1
    (D.eps (G.level - 1)) χ x.primitive.a x.primitive.b
  drift : x.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ G.level (D.kap G.level) c.slot.1
  edge : x.primitive.edge = restrictConstituentEdges K hKD
    (pathEdges G π c.slot (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩))
  fields : x.primitive.edgeField = restrictedIndependentEdgeField K hKD
    (independentPathTemplateField (S.pathIncomingField π c))
  matrix : x.primitive.M = weightedPathMatrix h (stagePathStoredWeight G π)
  coefficients : x.primitive.Cc = independentCarrierCoefficientExtension
    (actualIndependentCoarseStoredCarrier D c.chain.1 bw)
    (fun P => Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P))
  phase : x.translations = independentFreshPhaseTranslations c.chain.1.children.length

namespace WeakStageInheritedPrimitiveRealization
variable {S : IndependentWeakStageFluxProduction G minBase cap Hstage B}
  {c : WeakStageProductionContext D bw j₀ G.level minBase cap} {π : StagePath G h}
  {hKD : K ≤ Dm} {χ : Vec (2 + 4 * c.chain.1.children.length) → ℝ}
  {Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}
  {x : IndependentLiftNaturalPrimitiveDatum (Fin (h + 1)) (4 * c.chain.1.children.length)
    O K N h 1 sZ BG BV B}

theorem restrictRegularity (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (T : ℕ) (hT : T ≤ O) :
    WeakStageInheritedPrimitiveRealization S c π hKD χ Cc (x.restrictRegularity T hT) :=
  ⟨hx.left, hx.right, hx.carrier, hx.metric, hx.drift, hx.edge, hx.fields, hx.matrix,
    hx.coefficients, hx.phase⟩

theorem native_edges (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : D.term ≤ G.level) (hB : 0 ≤ B)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (hY : Y ∈ x.primitive.U) (t : ℝ) :
    SlowOpenEdgeEq (independentIntrinsicSliceCarrier (4 * c.chain.1.children.length) x.primitive.U Y) t
      (familyLiftData D G.level c.slot.1
        (actualIndependentCoarseParameterChain D c.chain.1
          (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))
        (D.eps (G.level - 1)) (restrictConstituentEdges K hKD
          (actualIndependentCoarsePathEdges π c
            (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)))).edge
      (independentConstituentEdgeSlice x.primitive.edge x.primitive.edgeField x.primitive.edges
        (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length))
        (independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y)) := by
  have hY' := hY
  rw [hx.carrier] at hY'
  obtain ⟨R₀, _hR₀, hcopy⟩ := S.pathIncomingField_anchored_effective_production
    π hq hΛ hζ hband hm hB c (weakStageCommonPathAnchor G c.slot ⟨c.chain⟩) K hKD Hstage le_rfl
  rw [independentConstituentEdgeSlice_congr _ _ _ _ x.primitive.edges R₀ hx.edge hx.fields,
    hx.carrier]
  exact hcopy Y hY' t

theorem native_metric (hx : WeakStageInheritedPrimitiveRealization S c π hKD χ Cc x)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates c.chain.1.children.length Y‖ < 1 / 4 →
      χ =ᶠ[𝓝 Y] fun _ => 1)
    (edge : ConstituentEdges K (fun _ : Fin (h + 1) => ℝ))
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (hY : Y ∈ x.primitive.U)
    (t : ℝ) (ht : t ∈ Icc x.primitive.a x.primitive.b) :
    (familyLiftData D G.level c.slot.1
      (actualIndependentCoarseParameterChain D c.chain.1
        (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))
      (D.eps (G.level - 1)) edge).G t
        (independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y) = x.primitive.G t Y := by
  have hY' := hY
  rw [hx.carrier] at hY'
  rw [hx.metric, actualIndependentCoarseScaledExtendedMetric_lift_carrier_copy
    D c.chain.1 bw (D.eps (G.level - 1)) _ _ t j₀ G.level c.slot.1 χ hχ ht Y hY'.1]
  have hs := actualIndependentCoarseScaledMetric_slice D c.chain.1 c.chain.2.2.2.1
    (D.eps (G.level - 1)) c.slot.1 edge Y t
    (independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y)
  rw [independentIntrinsicSliceOffset_base, c.chain.2.1] at hs
  exact hs.symm

end WeakStageInheritedPrimitiveRealization
end AVRegularity.EntryWeakProofs
end
end

section
/-! Uniform geometric controls for the actual weak successor construction. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

structure WeakStageStepGeometry (D : OCData) (bw : ℝ) (j₀ level minBase cap N : ℕ) (C : ℝ) : Prop where
  ratio : |D.eps level / D.eps (level - 1)| ≤ 1
  small : ∀ slot t, t ∈ weakStageCutoffWindow D (level + 1) slot →
    |D.slotAnchor (level + 1) slot - t| * ocA D.α D.q D.Λ level ≤ 1
  displacement : ∀ p, Odd p → ∀ slot t, t ∈ weakStageCutoffWindow D (level + 1) slot → ∀ z,
    ‖D.relDisp level p (D.slotAnchor (level + 1) slot) t z‖ ≤ 1 / 16
  append : ∀ (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot), IsScheduledIn D level slot.1 c.slot.1 →
    ∀ Y : Vec (2 + 4 * c.chain.1.children.length),
    Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (level - 1)) j₀ level c.slot.1 →
    ∀ t, t ∈ weakStageCutoffWindow D (level + 1) slot.1 → ∀ z,
    IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z)
  jets : ∀ (c : WeakStageProductionContext D bw j₀ level minBase cap) (slot : OddSlot),
    IsScheduledIn D level slot.1 c.slot.1 → ∀ t, t ∈ weakStageCutoffWindow D (level + 1) slot.1 →
    ∀ X : Vec 2 × Vec (2 + 4 * c.chain.1.children.length), ∀ a b j, j ≤ N →
    ‖iteratedFDeriv ℝ j (fun Z : (Vec 2 × Vec (2 + 4 * c.chain.1.children.length)) × Vec 2 =>
      independentFreshClampedTransferMatrix c.chain.1.children.length D
        (actualIndependentCoarseParameterChain D c.chain.1) level (D.eps (level - 1)) slot.1 t Z.1
        (D.eps level • Z.2) a b) (X, 0)‖ ≤ C

end AVRegularity.EntryWeakProofs
end
end

section
/-! All geometric controls for a weak successor follow from one data-independent terminal threshold. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_weak_stage_step_geometry (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hbw : 0 < bw) (cap N : ℕ) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ j₀ level minBase, M₀ ≤ level → M₀ ≤ minBase →
      WeakStageStepGeometry D bw j₀ level minBase cap N (weakStageTransferJetMenu cap N) := by
  obtain ⟨Mj, hMj, hjet⟩ := uniform_weak_stage_transfer_jet_menu
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ cap N
  obtain ⟨Ms, _hMs, hsmall⟩ := uniform_weak_transfer_shear_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ
  obtain ⟨Md, _hMd, hdisp⟩ := uniform_weak_reference_displacement_eventually_small
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ
  obtain ⟨Ma, _hMa, happend⟩ := uniform_weak_appendChild_eventually_in_carrier
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ bw 2 hbw (by norm_num)
  let M₀ := Mj + Ms + Md + Ma
  have hj : Mj ≤ M₀ := by dsimp only [M₀]; omega
  have hs : Ms ≤ M₀ := by dsimp only [M₀]; omega
  have hd : Md ≤ M₀ := by dsimp only [M₀]; omega
  have ha : Ma ≤ M₀ := by dsimp only [M₀]; omega
  refine ⟨M₀, hMj.trans hj, ?_⟩
  intro D hDα hDq hDΛ hDζ hstream j₀ level minBase hlevel hbase
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hq' : 1 < D.q := by rw [hDq]; exact hq.1
  have hε : ∀ i, 0 < D.eps i := fun _ => Construction.Stream.ocEpsilon_pos hΛ₁
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_of_pos (div_pos (hε level) (hε (level - 1)))]
    apply (div_le_iff₀ (hε (level - 1))).2
    rw [one_mul]
    exact EntryScales.epsilon_antitone hq' hΛ' (Nat.sub_le level 1)
  · intro slot t ht
    exact hsmall D hDα hDq hDΛ level ((hs.trans hlevel)) slot t ht
  · intro p hp slot t ht z
    exact hdisp D hDα hDq hDΛ hDζ level (hd.trans hlevel) p slot hp t ht z
  · intro c slot hsch Y hY t ht z
    exact happend D hDα hDq hDΛ hDζ level j₀ c.slot.1 slot.1 _ (ha.trans hlevel)
      hY.1.2 slot.2 hsch t ht z
  · intro c slot hsch t ht X a b k hk
    have hc : c.chain.1.ctxLevel = level := c.chain.2.1
    have hp : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
    have hA : IsAdmissibleChain D bw j₀ c.chain.1.ctxLevel c.chain.1.slot c.chain.1 := by
      rw [hc, hp]
      exact c.chain.2
    have hlast : c.chain.1.baseLevel + c.chain.1.children.length = level - 1 := by
      change c.chain.1.baseLevel + c.chain.1.children.length + 1 = level at hc
      omega
    have hh := hjet D hDα hDq hDΛ hDζ hstream c.chain.1 ((hj.trans hbase).trans c.base_bound)
      c.depth_bound bw j₀ hbw hA slot.1 slot.2 (by simpa only [hc, hp] using hsch) t
      (by rw [hc]; exact ht) X k hk a b
    simpa only [hc, hlast] using hh

end AVRegularity.EntryWeakProofs
end
end
end

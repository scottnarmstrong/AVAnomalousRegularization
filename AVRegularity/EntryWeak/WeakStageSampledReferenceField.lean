-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentPositiveCrossEddyProduction
public import AVRegularity.EntryWeak.MolecularUlFluxNormBound
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Full-family productions supply genuine native good and centered test fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

def independentFiniteNativeCoefficients_reserve
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + d)) (hh n m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    JointSourceReserve base (fun t z X => independentFiniteNativeCoefficients S P Y hh n m α t X z v u 1) :=
  ((independentFiniteLiftFields_reserve S P hB hh n m α v u).choose.affineSlice
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
    (independentIntrinsicSliceOffset d Y)).congrSource (by
      funext t z X
      simp only [independentFiniteNativeCoefficients, independentScalarCoefficientSlice,
        smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one])

theorem independentFiniteNativeTest_goodField
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + d)) (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (u : ι) (t : ℝ) :
    GoodField base (liftApply n (independentFiniteNativeCoefficients S P Y hh n)
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t) :=
  scalarLiftTest_goodField base n _ A u
    (fun m α v w => independentFiniteNativeCoefficients_reserve S P hB Y hh n m.val α v w) t

theorem independentFiniteNativeCoefficients_positive_grade_mean_zero
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d))
    (hh n : ℕ) (hhpos : hh ≠ 0) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (X : Vec 2) (v u : ι) (ξ : ℝ) :
    fieldCellMean (fun z => independentFiniteNativeCoefficients S P Y hh n m α t X z v u ξ) = 0 := by
  change fieldCellMean (fun z =>
    independentFiniteLiftFields S P hh n m α t z
      (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) v u • ξ) = 0
  by_cases hn : n = 0
  · subst n
    simp only [independentFiniteLiftFields_positive_zero_degree S P hh hhpos, zero_smul,
      fieldCellMean_zero]
  · simp only [smul_eq_mul, mul_comm _ ξ]
    change fieldCellMean (fun z => ξ • independentFiniteLiftFields S P hh n m α t z
      (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) v u) = 0
    rw [fieldCellMean_smul,
      independentFiniteLiftFields_mean_zero S P hh n m (by omega), smul_zero]

theorem independentFiniteNativeTest_positive_grade_centField
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + d)) (hh n : ℕ) (hhpos : hh ≠ 0)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (t : ℝ) :
    CoefField True base (liftApply n (independentFiniteNativeCoefficients S P Y hh n)
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t) :=
  scalarLiftTest_centField base n _ A u
    (fun m α v w => independentFiniteNativeCoefficients_reserve S P hB Y hh n m.val α v w)
    (fun m _ α t X v w ξ => independentFiniteNativeCoefficients_positive_grade_mean_zero
      S P Y hh n hhpos m α t X v w ξ) t

end AVRegularity.EntryWeakProofs
end
end

section
/-! Coherent positive Eddy means give vector reserves at the squared response. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossEddyVectorProduction (d H D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ f : ∀ _x : IndependentPositiveNaturalPrimitiveDatum ι d H D N R count qs BG BV BE,
      ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → DerivativeWord2 m → ι → ι →
      ℝ → Vec 2 → Vec (2 + d) → Vec 2,
      (∀ x n hn hnN m hm α out inp,
        ∃ Q : IndependentParameterSourceReserve H (f x n hn hnN m hm α out inp),
          (∀ r ≤ H, Q.budget r ≤ (x.response ^ 2 * finiteMatrixPower x.data.primitive.M 0 out inp) * C) ∧
          (∀ t ∈ Icc x.data.primitive.a x.data.primitive.b, ∀ Y ∈ x.data.primitive.U, ∀ z k,
            f x n hn hnN m hm α out inp t z Y k = fieldCellMean (fun w =>
              x.data.primitive.v t w k • x.data.primitive.Cc (independentStoredParameterProjection d Y)
                0 n m α t (independentIntrinsicSlowProjection d Y) w out inp 1)) ∧
          (∀ δ ∈ x.data.translations, IndependentSourceTranslationInvariant δ (f x n hn hnN m hm α out inp))) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ n hn hnN m hm α out inp,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (f x n hn hnN m hm α out inp) (f y n hn hnN m hm α out inp) := by
  obtain ⟨B, hB, scalar, hprod, hcross⟩ := independentPositiveCrossEddyProduction (ι := ι)
    d H D N R count qs BG BV BE hND hBG hBV hBE
  let f := fun x n hn hnN m hm α out inp t z Y k => scalar x n hn hnN m hm α out inp k t z Y
  refine ⟨2 * B, mul_nonneg (by norm_num) hB, f, ?_, ?_⟩
  · intro x n hn hnN m hm α out inp
    choose Q hQ hcopy hphase using fun k : Fin 2 => hprod x n hn hnN m hm α out inp k
    refine ⟨independentSourcePiReserve H _ Q, ?_, ?_, ?_⟩
    · intro r hr
      have hh := independentSourcePiReserve_uniform_budget H _ Q
        ((x.response ^ 2 * finiteMatrixPower x.data.primitive.M 0 out inp) * B) hQ r hr
      simp only [Fintype.card_fin, Nat.cast_ofNat] at hh
      exact hh.trans_eq (by ring)
    · intro t ht Y hY z k
      exact hcopy k t ht Y hY z
    · intro δ hδ t z Y
      funext k
      exact hphase k δ hδ t z Y
  · intro x y U Y Z hU hzero hresponse he n hn hnN m hm α out inp t V hV z
    funext k
    let U' : Set (Vec 2) := (fun W => W + V) ⁻¹' U
    have hU' : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
    have hz' : (0 : Vec 2) ∈ U' := by simpa only [U', Set.mem_preimage, zero_add] using hV
    exact hcross x y U'
      (independentIntrinsicSlowEmbedding d V + Y) (independentIntrinsicSlowEmbedding d V + Z)
      hU' hz' hresponse (he.recenter V) n hn hnN m hm α out inp k t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite depth price is chosen before every primitive family, retaining the coherent Eddy fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossEddyDepthProduction (J H D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ f : ∀ r : Fin (J + 1),
      IndependentPositiveNaturalPrimitiveDatum ι (4 * r.val) H D N R count qs BG BV BE →
      ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → DerivativeWord2 m → ι → ι →
      ℝ → Vec 2 → Vec (2 + 4 * r.val) → Vec 2,
      (∀ r x n hn hnN m hm α out inp,
        ∃ Q : IndependentParameterSourceReserve H (f r x n hn hnN m hm α out inp),
          (∀ j ≤ H, Q.budget j ≤ (x.response ^ 2 * finiteMatrixPower x.data.primitive.M 0 out inp) * C) ∧
          (∀ t ∈ Icc x.data.primitive.a x.data.primitive.b, ∀ Y ∈ x.data.primitive.U, ∀ z k,
            f r x n hn hnN m hm α out inp t z Y k = fieldCellMean (fun w =>
              x.data.primitive.v t w k • x.data.primitive.Cc
                (independentStoredParameterProjection (4 * r.val) Y)
                0 n m α t (independentIntrinsicSlowProjection (4 * r.val) Y) w out inp 1)) ∧
          (∀ δ ∈ x.data.translations,
            IndependentSourceTranslationInvariant δ (f r x n hn hnN m hm α out inp))) ∧
      ∀ r x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ n hn hnN m hm α out inp,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding (4 * r.val)) U Y Z
            (f r x n hn hnN m hm α out inp) (f r y n hn hnN m hm α out inp) := by
  classical
  have hprices (r : Fin (J + 1)) := independentPositiveCrossEddyVectorProduction (ι := ι)
    (4 * r.val) H D N R count qs BG BV BE hND hBG hBV hBE
  choose C hC f hprod hcross using hprices
  let B := independentFiniteStepBudget C
  have hB : 0 ≤ B := zero_le_one.trans (independentFiniteStepBudget_one_le C hC)
  refine ⟨B, hB, f, ?_, hcross⟩
  intro r x n hn hnN m hm α out inp
  obtain ⟨Q, hQ, hcopy, hphase⟩ := hprod r x n hn hnN m hm α out inp
  refine ⟨Q, ?_, hcopy, hphase⟩
  intro j hj
  exact (hQ j hj).trans (mul_le_mul_of_nonneg_left
    (independentFiniteStepBudget_entry_le C hC r)
    (mul_nonneg (sq_nonneg x.response)
      (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp)))

end AVRegularity.EntryWeakProofs
end
end

section
/-! A single Eddy producer retains its choices and cross-chart naturality throughout stage assembly. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

structure IndependentPositiveEddyDepthProducer (J H D N R count qs : ℕ) (BG BV BE : ℝ) where
  budget : ℝ
  budget_nonneg : 0 ≤ budget
  field : ∀ r : Fin (J + 1),
    IndependentPositiveNaturalPrimitiveDatum ι (4 * r.val) H D N R count qs BG BV BE →
    ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → DerivativeWord2 m → ι → ι →
    ℝ → Vec 2 → Vec (2 + 4 * r.val) → Vec 2
  production : ∀ r x n hn hnN m hm α out inp,
    ∃ Q : IndependentParameterSourceReserve H (field r x n hn hnN m hm α out inp),
      (∀ j ≤ H, Q.budget j ≤
        (x.response ^ 2 * finiteMatrixPower x.data.primitive.M 0 out inp) * budget) ∧
      (∀ t ∈ Icc x.data.primitive.a x.data.primitive.b, ∀ Y ∈ x.data.primitive.U, ∀ z k,
        field r x n hn hnN m hm α out inp t z Y k = fieldCellMean (fun w =>
          x.data.primitive.v t w k • x.data.primitive.Cc
            (independentStoredParameterProjection (4 * r.val) Y)
            0 n m α t (independentIntrinsicSlowProjection (4 * r.val) Y) w out inp 1)) ∧
      (∀ δ ∈ x.data.translations,
        IndependentSourceTranslationInvariant δ (field r x n hn hnN m hm α out inp))
  cross : ∀ r x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
    IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
    ∀ n hn hnN m hm α out inp,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding (4 * r.val)) U Y Z
        (field r x n hn hnN m hm α out inp) (field r y n hn hnN m hm α out inp)

noncomputable def independentPositiveEddyDepthProducer (J H D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    IndependentPositiveEddyDepthProducer ι J H D N R count qs BG BV BE := Classical.choice (by
  obtain ⟨C, hC, f, hprod, hcross⟩ := independentPositiveCrossEddyDepthProduction (ι := ι)
    J H D N R count qs BG BV BE hND hBG hBV hBE
  exact ⟨⟨C, hC, f, hprod, hcross⟩⟩)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine actual molecular data (`MolecularData`) and original empty-edge lift clauses construct
the eddy primitive datum. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualIndependentCoarseEmptyPrimitiveData (H Dm N : ℕ) (BG BV : ℝ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (bw : ℝ) (j₀ : ℕ) (hA : IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A)
    (hweak : D.term < A.ctxLevel) (ρ : ℝ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (sX sZ : ℕ)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hc : ∀ P ∈ actualIndependentCoarseStoredCarrier D A bw,
      IsLiftSequence (familyLiftData (Dm := Dm) D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
        (fun _ _ _ => [])) sX sZ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) N 0 (c P))
    (Q : IndependentParameterMetricReserve (H + Dm + 1)
      (actualIndependentCoarseScaledExtendedMetric D A ρ χ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)))
    (hQ : ∀ r ≤ H + Dm + 1, Q.budget r ≤ BG)
    (Qv : ∀ i, IndependentParameterSourceReserve (H + Dm)
      (fun t z (_ : Vec (2 + 4 * A.children.length)) =>
        ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot t z i))
    (hQv : ∀ i r, r ≤ H + Dm → (Qv i).budget r ≤ BV)
    (Mdata : Vec (2 + 4 * A.children.length) → MolecularData)
    (hMG : ∀ Y, (Mdata Y).G = fun t => actualIndependentCoarseScaledExtendedMetric D A ρ χ
      (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
      ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y)
    (hMv : ∀ Y, (Mdata Y).v = ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot)
    (hMC : ∀ Y, dataCoefficients (Mdata Y) =
      ⟨(fun t _ => actualIndependentCoarseScaledExtendedMetric D A ρ χ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y),
        (Mdata Y).v, 0, 0⟩)
    (V : ∀ Y K, K ≤ H → MolecularFiniteDriftBudget (Mdata Y) K) :
    IndependentLiftPrimitiveData ι (4 * A.children.length) H Dm N 0 0 BG BV 0 where
  a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
  b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
  window := weakData_lift_window_strict D hΛ hζ hband A.ctxLevel A.slot
  U := actualIndependentCoarseNativeCarrier D A bw
  open_carrier := actualIndependentCoarseNativeCarrier_isOpen D A bw
  G := actualIndependentCoarseScaledExtendedMetric D A ρ χ _ _
  v := ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot
  drift := normalizedPulseDrift_isCellDrift hΛ (weakData_kap_pos D hΛ hζ hband _) hζ (by
    have hp := realChainSlotSeq_odd D A hA A.children.length le_rfl
    rw [realChainSlotSeq_last A hA.2.2.1] at hp
    exact hp)
  edge := fun _ _ _ => []
  edgeField := fun _ _ _ _ _ _ _ _ => 0
  M := fun _ _ => 0
  matrix_nonneg := fun _ _ => le_rfl
  metric := Q.restrictOrder H (by omega)
  metric_bound r hr := hQ r (by omega)
  metric_entries := Q.entrySource
  metric_entries_bound i j r hr := hQ r hr
  drift_entries := Qv
  drift_bound := hQv
  edges _ _ _ _ hγ := (List.not_mem_nil hγ).elim
  edge_bound _ _ _ _ hγ := (List.not_mem_nil hγ).elim
  edge_maps _ _ _ _ hγ := (List.not_mem_nil hγ).elim
  edge_lengths := fun _ _ _ => le_rfl
  molecular := Mdata
  molecular_coefficients := hMC
  molecular_metric := hMG
  molecular_drift := hMv
  molecular_budget := V
  sZ := sZ
  Cc := independentCarrierCoefficientExtension (actualIndependentCoarseStoredCarrier D A bw) c
  initial P f _hf t _ht X z := independentCarrierCoefficientExtension_initial _ c P (fun _ => f) t X z
  positive_zero_degree _ hh hhh hhh0 := (by omega : False).elim
  above_degree P hh hhh n hn m α t X z v u := independentCarrierCoefficientExtension_above_degree
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (fun _ _ _ => [])) hc P hh n m hhh hn α t X z v u
  above_order P hh hhh n m hm α t X z v u := independentCarrierCoefficientExtension_above_order
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (fun _ _ _ => [])) hc P hh n m hhh hm α t X z v u
  symmetric P hh hhh n m α σ := independentCarrierCoefficientExtension_perm
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (fun _ _ _ => [])) hc P hh n m hhh α σ
  inverse hh hhh n hn hnN f hf Y hY := by
    have hh0 : hh = 0 := by omega
    subst hh
    have hi := actualIndependentCoarseEmptyCarrierInverse D hΛ hζ hband A hA.2.2.1 hweak bw ρ _ _ A.slot
      χ hχ c sX sZ N n hn hnN Y hY (hc _ hY.1) f hf
    simpa only [independentIntrinsicSliceOffset_base, actualIndependentCoarseCarrierCoefficients,
      independentConstituentEdgeSlice_empty, Matrix.of_apply] using hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal carrier flux copies and produced reserves identify the true native inherited mean. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H T D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteLiftFluxMean_reconstructed_copy
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S (H + D + 2) B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hT : H ≤ T) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (A : Vec 2 →L[ℝ] ℝ) (Y : Vec (2 + d)) (t : ℝ) (out inp : ι) (k : Fin 2) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    fieldCellMean (fun z => independentLiftFluxSource S.edge S.edgeField
      (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
      (independentFiniteLiftFields S P) hh n out inp k t z Y) =
      (Real.exp (A (independentIntrinsicSlowProjection d Y)))⁻¹ •
        fieldCellMean (fun z => liftFluxX Q (independentFiniteNativeCoefficients S P Y)
          (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) hh n t
          (independentIntrinsicSlowProjection d Y) z k) out := by
  dsimp only
  let F : Vec 2 → ι → ℝ := fun z out => independentLiftFluxSource S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
    (independentFiniteLiftFields S P) hh n out inp k t z Y
  have hF : Continuous F := by
    apply continuous_pi
    intro v
    obtain ⟨Qv, _⟩ := independentFiniteLiftFlux_reserve H S P hB le_rfl hT hBG hBV hBE
      hh n hn hhpos A v inp k
    exact ((Qv.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
  choose Qc hc using fun p q m β v u => independentFiniteLiftFields_reserve S P hB p q m β v u
  apply independentFluxMean_point_copy F _ _ hF ?_ out
  intro z v
  have he := independent_lift_coefficient_flux_source_slice H S.edge hD S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
    (independentIntrinsicSliceOffset d Y) A 1 S.G S.v (independentFiniteLiftFields S P)
    hh n hn hhpos v inp k (fun p q _ m β v u => Qc p q m.val β v u)
    (fun v u e γ hγ β => (S.edges v u e γ hγ β).restrictOrder (H + 1) (by omega))
    t z (independentIntrinsicSlowProjection d Y)
  rw [independentIntrinsicSliceOffset_base] at he
  exact he

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced incoming edge germs on an open subcarrier construct a genuine inherited primitive datum. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualIndependentCoarseInheritedPrimitiveDataRestricted (H Dm N R count : ℕ) (BG BV BE : ℝ)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (bw : ℝ) (j₀ : ℕ) (hA : IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A)
    (hweak : D.term < A.ctxLevel) (ρ : ℝ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ)
    (hχ : ∀ Y, ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1)
    (U : Set (Vec (2 + 4 * A.children.length))) (hUopen : IsOpen U)
    (hUsub : U ⊆ actualIndependentCoarseLiftCarrier D A bw ρ j₀ A.ctxLevel A.slot)
    (sX sZ : ℕ)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (nativeEdge : Vec (4 * A.children.length) → ConstituentEdges Dm (fun _ : ι => ℝ))
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (edgeField : ∀ (_v _u : ι) (e : Finset.Icc 2 Dm), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec (2 + 4 * A.children.length) → Vec 2)
    (Qe : ∀ v u e, ∀ γ ∈ edge v u e, ∀ β,
      IndependentParameterSourceReserve (H + Dm + 1) (edgeField v u e γ β))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u)
    (hQe : ∀ v u e γ hγ β r, r ≤ H + Dm + 1 →
      (Qe v u e γ hγ β).budget r ≤ M v u * BE)
    (hmap : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1)
    (hcount : ∀ v u e, (edge v u e).length ≤ count)
    (hc : ∀ P ∈ actualIndependentCoarseStoredCarrier D A bw,
      IsLiftSequenceOn (ladderOmega D bw j₀ A.ctxLevel A.slot
        (actualIndependentCoarseParameterChain D A P) ρ) (familyLiftData (Dm := Dm) D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
        (nativeEdge P)) sX sZ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) N R (c P))
    (he : ∀ Y ∈ U,
      ∀ t ∈ Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel),
      SlowOpenEdgeEq
        (independentIntrinsicSliceCarrier (4 * A.children.length)
          (U) Y) t
        (actualIndependentCoarseExtendedSliceLiftData D A ρ A.slot
          (nativeEdge (independentStoredParameterProjection (4 * A.children.length) Y)) χ
          (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) Y).edge
        (independentConstituentEdgeSlice edge edgeField Qe
          (independentIntrinsicSlowEmbedding (4 * A.children.length))
          (independentIntrinsicSliceOffset (4 * A.children.length) Y)))
    (Q : IndependentParameterMetricReserve (H + Dm + 1)
      (actualIndependentCoarseScaledExtendedMetric D A ρ χ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)))
    (hQ : ∀ r ≤ H + Dm + 1, Q.budget r ≤ BG)
    (Qv : ∀ i, IndependentParameterSourceReserve (H + Dm)
      (fun t z (_ : Vec (2 + 4 * A.children.length)) =>
        ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot t z i))
    (hQv : ∀ i r, r ≤ H + Dm → (Qv i).budget r ≤ BV)
    (Mdata : Vec (2 + 4 * A.children.length) → MolecularData)
    (hMG : ∀ Y, (Mdata Y).G = fun t => actualIndependentCoarseScaledExtendedMetric D A ρ χ
      (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
      ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y)
    (hMv : ∀ Y, (Mdata Y).v = ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot)
    (hMC : ∀ Y, dataCoefficients (Mdata Y) =
      ⟨(fun t _ => actualIndependentCoarseScaledExtendedMetric D A ρ χ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y),
        (Mdata Y).v, 0, 0⟩)
    (V : ∀ Y K, K ≤ H → MolecularFiniteDriftBudget (Mdata Y) K) :
    IndependentLiftPrimitiveData ι (4 * A.children.length) H Dm N R count BG BV BE where
  a := D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel
  b := (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel
  window := weakData_lift_window_strict D hΛ hζ hband A.ctxLevel A.slot
  U := U
  open_carrier := hUopen
  G := actualIndependentCoarseScaledExtendedMetric D A ρ χ _ _
  v := ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot
  drift := normalizedPulseDrift_isCellDrift hΛ (weakData_kap_pos D hΛ hζ hband _) hζ (by
    have hp := realChainSlotSeq_odd D A hA A.children.length le_rfl
    rw [realChainSlotSeq_last A hA.2.2.1] at hp
    exact hp)
  edge := edge
  edgeField := edgeField
  M := M
  matrix_nonneg := hM
  metric := Q.restrictOrder H (by omega)
  metric_bound r hr := hQ r (by omega)
  metric_entries := Q.entrySource
  metric_entries_bound i j r hr := hQ r hr
  drift_entries := Qv
  drift_bound := hQv
  edges := Qe
  edge_bound := hQe
  edge_maps := hmap
  edge_lengths := hcount
  molecular := Mdata
  molecular_coefficients := hMC
  molecular_metric := hMG
  molecular_drift := hMv
  molecular_budget := V
  sZ := sZ
  Cc := independentCarrierCoefficientExtension (actualIndependentCoarseStoredCarrier D A bw) c
  initial P f _hf t _ht X z := independentCarrierCoefficientExtension_initial _ c P (fun _ => f) t X z
  positive_zero_degree P hh hhh _hhhR m α t X z v u :=
    independentCarrierCoefficientExtension_positive_zero_degree _ c P hh hhh m α t X z v u
  above_degree P hh hhh n hn m α t X z v u := independentCarrierCoefficientExtension_above_degree_on
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (nativeEdge P))
    (fun P => ladderOmega D bw j₀ A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ)
    hc P hh n m hhh hn α t X z v u
  above_order P hh hhh n m hm α t X z v u := independentCarrierCoefficientExtension_above_order_on
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (nativeEdge P))
    (fun P => ladderOmega D bw j₀ A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ)
    hc P hh n m hhh hm α t X z v u
  symmetric P hh hhh n m α σ := independentCarrierCoefficientExtension_perm_on
    _ c (fun P => familyLiftData D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
      (nativeEdge P))
    (fun P => ladderOmega D bw j₀ A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ)
    hc P hh n m hhh α σ
  inverse hh hhh n hn hnN f hf Y hY := by
    have hY' := hUsub hY
    let V := independentIntrinsicSliceCarrier (4 * A.children.length) U Y
    have hV : IsOpen V := independentIntrinsicSliceCarrier_isOpen _ _ hUopen Y
    have hbase : independentIntrinsicSlowProjection (4 * A.children.length) Y ∈ V :=
      independentIntrinsicSliceCarrier_base _ _ Y hY
    have hi := actualIndependentCoarseCarrierInverse_edge_transfer_on D hΛ A bw ρ _ _ j₀ A.slot hA
      (nativeEdge (independentStoredParameterProjection (4 * A.children.length) Y))
      (independentConstituentEdgeSlice edge edgeField Qe
        (independentIntrinsicSlowEmbedding (4 * A.children.length))
        (independentIntrinsicSliceOffset (4 * A.children.length) Y))
      χ hχ c sX sZ N R hh n hhh hn hnN Y hY' V hV hbase (he Y hY) (hc _ hY'.1.1) f hf
    rw [actualIndependentCoarseExtendedWeakSliceData_eq D hΛ hζ hband A hweak ρ A.slot
      (nativeEdge (independentStoredParameterProjection (4 * A.children.length) Y)) χ _ _ Y] at hi
    have hmat : (fun t => Matrix.of (actualIndependentCoarseScaledExtendedMetric D A ρ χ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y)) =
        (fun t => actualIndependentCoarseScaledExtendedMetric D A ρ χ
          (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) t Y) := by
      funext t i j
      rfl
    simpa only [independentIntrinsicSliceOffset_base, actualIndependentCoarseCarrierCoefficients,
      actualIndependentCoarseSliceLiftData, familyLiftData, hmat] using hi

end AVRegularity.EntryWeakProofs
end
end

section
/-! Positive-response Eddy mean arrays retain their response square and exact physical dimensions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {J H N sZ : ℕ} {BG BV : ℝ}

def weakEddyPhysicalArray
    (E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0)
    (r : Fin (J + 1)) (n : Finset.Icc 2 (N + 1))
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * r.val) H N N 0 0 sZ BG BV 0)
    (D : OCData) (level d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * r.val) → Vec 2 :=
  if hd : d ∈ Finset.Icc 2 n.val then
    independentProducedFluxSource
      (D.κ D.term * D.eps level ^ (n.val - 2) *
        D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)))
      (fun t => (D.cellScaleSq level)⁻¹ * t)
      (fun t _ Y => E.field r x (n.val - 1) (by have := (Finset.mem_Icc.mp n.property).1; omega)
        (by have := (Finset.mem_Icc.mp n.property).2; omega) (d - 1)
        (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) word 0 0 t 0 Y)
  else fun _ _ _ => 0

theorem weakEddyPhysicalArray_production
    (E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0)
    (r : Fin (J + 1)) (n : Finset.Icc 2 (N + 1))
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * r.val) H N N 0 0 sZ BG BV 0)
    (D : OCData) (level : ℕ) (hκ : 0 ≤ D.κ D.term) (hε : ∀ i, 0 < D.eps i)
    (hresponse : x.response = D.weakPe level)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H (weakEddyPhysicalArray E r n x D level d word),
      (∀ k ≤ H, Q.budget k ≤ D.weakPe level ^ 2 *
        (D.κ D.term * D.eps level ^ (n.val - 2) *
          D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)) * E.budget)) ∧
      (∀ δ ∈ x.data.translations, IndependentSourceTranslationInvariant δ
        (weakEddyPhysicalArray E r n x D level d word)) := by
  by_cases hd : d ∈ Finset.Icc 2 n.val
  · have hn : 1 ≤ n.val - 1 := by have := (Finset.mem_Icc.mp n.property).1; omega
    have hnN : n.val - 1 ≤ N := by have := (Finset.mem_Icc.mp n.property).2; omega
    let f := E.field r x (n.val - 1) hn hnN (d - 1)
      (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) word 0 0
    have he : weakEddyPhysicalArray E r n x D level d word =
        independentProducedFluxSource
          (D.κ D.term * D.eps level ^ (n.val - 2) *
            D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ)))
          (fun t => (D.cellScaleSq level)⁻¹ * t) (fun t _ Y => f t 0 Y) := by
      unfold weakEddyPhysicalArray
      exact dite_eq_left hd
    rw [he]
    obtain ⟨Q, hQ, _hcopy, hphase⟩ := E.production r x (n.val - 1) hn hnN (d - 1)
      (Nat.sub_le_sub_right (Finset.mem_Icc.mp hd).2 1) word 0 0
    have hQ' : ∀ k ≤ H, Q.budget k ≤ D.weakPe level ^ 2 * E.budget := by
      simpa only [finiteMatrixPower_zero, ite_true, mul_one, hresponse] using hQ
    let c := D.κ D.term * D.eps level ^ (n.val - 2) *
      D.eps (level - 1) ^ ((d : ℝ) - (n.val : ℝ))
    have hc : 0 ≤ c := mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _))
      (Real.rpow_pos_of_pos (hε _) _).le
    have hclock : Measurable (fun t : ℝ => (D.cellScaleSq level)⁻¹ * t) :=
      measurable_const.mul measurable_id
    refine ⟨independentProducedFluxReserve H c _ hclock _ (Q.freezeFast 0), ?_, ?_⟩
    · intro k hk
      exact independentProducedFluxReserve_budget H c hc _ hclock _ (Q.freezeFast 0) _ E.budget hQ' k hk
    · intro δ hδ t z Y
      exact congrArg (fun w : Vec 2 => (-c) • w) (hphase δ hδ _ 0 Y)
  · have he : weakEddyPhysicalArray E r n x D level d word = fun _ _ _ => 0 := by
      unfold weakEddyPhysicalArray
      exact dite_eq_right hd
    rw [he]
    refine ⟨IndependentParameterSourceReserve.zero H, ?_, fun _ _ _ _ _ => rfl⟩
    intro k _hk
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hκ
      (pow_nonneg (hε _).le _)) (Real.rpow_pos_of_pos (hε _) _).le) E.budget_nonneg)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! One finite Piola price covers all source degrees and tested orders of a weak stage. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

def weakPiolaProductionMenuCost (H N : ℕ) (C B₀ : ℝ) (j : ℕ × ℕ) : ℝ :=
  10 * ∑ k : Fin (H + 1), independentPiolaDimensionlessPrice N j.1 k.val C B₀ j.2

def weakPiolaProductionMenuBudget (H N K : ℕ) (C B₀ : ℝ) : ℝ :=
  independentFiniteStepBudget (fun j : Fin (K + 1) × Fin (K + 1) =>
    weakPiolaProductionMenuCost H N C B₀ (j.1.val, j.2.val))

theorem weakPiolaProductionMenuCost_nonneg (H N : ℕ) (C B₀ : ℝ)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (j : ℕ × ℕ) :
    0 ≤ weakPiolaProductionMenuCost H N C B₀ j :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    independentPiolaDimensionlessPrice_nonneg _ _ _ _ _ _ hC hB₀)

theorem weakPiolaProductionMenuBudget_one_le (H N K : ℕ) (C B₀ : ℝ)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) : 1 ≤ weakPiolaProductionMenuBudget H N K C B₀ :=
  independentFiniteStepBudget_one_le _ (fun _ => weakPiolaProductionMenuCost_nonneg H N C B₀ hC hB₀ _)

theorem weakPiolaProductionMenuCost_le (H N K n r : ℕ) (C B₀ : ℝ)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) (hn : n ≤ K) (hr : r ≤ K) :
    weakPiolaProductionMenuCost H N C B₀ (n, r) ≤ weakPiolaProductionMenuBudget H N K C B₀ :=
  independentFiniteStepBudget_entry_le
    (fun j : Fin (K + 1) × Fin (K + 1) => weakPiolaProductionMenuCost H N C B₀ (j.1.val, j.2.val))
    (fun _ => weakPiolaProductionMenuCost_nonneg H N C B₀ hC hB₀ _)
    (⟨n, Nat.lt_succ_of_le hn⟩, ⟨r, Nat.lt_succ_of_le hr⟩)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Uniform molecular data turn produced incoming edge germs into actual inherited natural inputs. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_inherited_datum_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J O Dm : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z →
          χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧ ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ D : OCData,
      M₀ ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M₀ ≤ A.baseLevel → A.children.length ≤ J → D.term < A.ctxLevel →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps A.lastLevel →
      ∀ (N R count sZ : ℕ) (BE : ℝ),
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (U : Set (Vec (2 + 4 * A.children.length))) (_hUopen : IsOpen U)
    (_hUsub : U ⊆ actualIndependentCoarseLiftCarrier D A bw ρ j₀ A.ctxLevel A.slot)
    (sX : ℕ)
    (c : Vec (4 * A.children.length) → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (nativeEdge : Vec (4 * A.children.length) → ConstituentEdges Dm (fun _ : ι => ℝ))
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (edgeField : ∀ (_v _u : ι) (e : Finset.Icc 2 Dm), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec (2 + 4 * A.children.length) → Vec 2)
    (Qe : ∀ v u e, ∀ γ ∈ edge v u e, ∀ β,
      IndependentParameterSourceReserve (O + Dm + 1) (edgeField v u e γ β))
    (M : ι → ι → ℝ) (_hM : ∀ v u, 0 ≤ M v u)
    (_hQe : ∀ v u e γ hγ β r, r ≤ O + Dm + 1 →
      (Qe v u e γ hγ β).budget r ≤ M v u * BE)
    (_hmap : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1)
    (_hcount : ∀ v u e, (edge v u e).length ≤ count)
    (_hc : ∀ P ∈ actualIndependentCoarseStoredCarrier D A bw,
      IsLiftSequenceOn (ladderOmega D bw j₀ A.ctxLevel A.slot
        (actualIndependentCoarseParameterChain D A P) ρ) (familyLiftData (Dm := Dm) D A.ctxLevel A.slot (actualIndependentCoarseParameterChain D A P) ρ
        (nativeEdge P)) sX sZ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) N R (c P))
    (_he : ∀ Y ∈ U,
      ∀ t ∈ Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel),
      SlowOpenEdgeEq
        (independentIntrinsicSliceCarrier (4 * A.children.length)
          (U) Y) t
        (actualIndependentCoarseExtendedSliceLiftData D A ρ A.slot
          (nativeEdge (independentStoredParameterProjection (4 * A.children.length) Y)) (χ A.children.length)
          (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel) Y).edge
        (independentConstituentEdgeSlice edge edgeField Qe
          (independentIntrinsicSlowEmbedding (4 * A.children.length))
          (independentIntrinsicSliceOffset (4 * A.children.length) Y)))
    (_hphase : ∀ δ ∈ independentFreshPhaseTranslations A.children.length,
      ∀ v u e γ, γ ∈ edge v u e → ∀ β,
        IndependentSourceTranslationInvariant δ (edgeField v u e γ β)),
      ∃ x : IndependentLiftNaturalPrimitiveDatum ι (4 * A.children.length)
          O Dm N R count sZ BG BV BE,
        x.primitive.a = D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel ∧
        x.primitive.b =
          (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel ∧
        x.primitive.U = U ∧
        x.primitive.G = actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length)
          x.primitive.a x.primitive.b ∧
        x.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot ∧
        x.primitive.edge = edge ∧ x.primitive.edgeField = edgeField ∧ x.primitive.M = M ∧
        x.primitive.Cc = independentCarrierCoefficientExtension
          (actualIndependentCoarseStoredCarrier D A bw) c ∧
        x.translations = independentFreshPhaseTranslations A.children.length := by
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, M₀, hM₀, hmol⟩ :=
    uniform_actual_independent_coarse_molecular_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J (O + Dm) (O + Dm + 1)
  refine ⟨χ, BG, BV, hχ, hBG, hBV, M₀, hM₀, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hstream hband A hbase hdepth hweak bw j₀ hA
    ρ hρ hρle N R count sZ BE ι instFintype instDecidableEq U hUopen hUsub sX c nativeEdge edge edgeField Qe M hM hQe hmap hcount hc he hphase
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  obtain ⟨QM, Qv, Mdata, hQM, hQv, _hPeQv, _hPe1, hMG, hMv, hMC, hV⟩ :=
    hmol D hterm hDα hDq hDΛ hDζ hstream hband A hbase hdepth hweak bw j₀ hA ρ hρ hρle
  let S := actualIndependentCoarseInheritedPrimitiveDataRestricted O Dm N R count BG BV BE
    D hΛ₁ hζ' hband A bw j₀ hA hweak ρ (χ A.children.length) (hχ _).2.2.1
    U hUopen hUsub sX sZ c nativeEdge edge edgeField Qe M hM hQe hmap hcount hc he
    QM hQM Qv hQv Mdata hMG hMv hMC (fun Y K hK => (hV Y K (by omega)).some)
  let x : IndependentLiftNaturalPrimitiveDatum ι (4 * A.children.length)
      O Dm N R count sZ BG BV BE :=
    { primitive := S
      fastOrder := rfl
      translations := independentFreshPhaseTranslations A.children.length
      metric_translation := fun δ hδ t Y =>
        actualIndependentCoarseScaledExtendedMetric_phase_translation D hΛ₁ A bw j₀
          A.ctxLevel A.slot hA ρ _ _ t (χ A.children.length) (hχ _).2.2.2 δ hδ Y
      edge_translation := hphase }
  exact ⟨x, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual path data on the stored carrier retain the supplied original lift histories. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap : ℕ}
  {G : GenStage D hr Dm bw j₀} {h : ℕ}

def WeakStageProductionContext.atStoredParameter
    {level : ℕ} (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (P : Vec (4 * c.chain.1.children.length))
    (hP : P ∈ actualIndependentCoarseStoredCarrier D c.chain.1 bw) :
    StageCtx D bw j₀ level c.slot :=
  ⟨actualIndependentCoarseParameterChain D c.chain.1 P,
    (actualIndependentCoarseParameterChain_admissible_iff D c.chain.1 bw j₀ level c.slot.1
      c.chain.2 P).mpr hP⟩

open scoped Classical in
def actualIndependentCoarsePathEdges (π : StagePath G h)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (P : Vec (4 * c.chain.1.children.length)) : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ) :=
  if hP : P ∈ actualIndependentCoarseStoredCarrier D c.chain.1 bw then
    pathEdges G π c.slot (c.atStoredParameter P hP)
  else fun _ _ _ => []

theorem actualIndependentCoarsePathEdges_native (π : StagePath G h)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (P : Vec (4 * c.chain.1.children.length))
    (hP : P ∈ actualIndependentCoarseStoredCarrier D c.chain.1 bw) :
    actualIndependentCoarsePathEdges π c P = pathEdges G π c.slot (c.atStoredParameter P hP) := by
  simp only [actualIndependentCoarsePathEdges, dite_eq_left hP]

theorem actualIndependentCoarsePath_isLiftSequenceOn_effective_order
    (π : StagePath G h) (c : WeakStageProductionContext D bw j₀ G.level minBase cap)
    (K : ℕ) (hKD : K ≤ Dm) (hK : G.maxOrderBound K)
    (sX sZ N R : ℕ) (hNK : N ≤ K)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : ∀ A : RealChain, ∀ hA : IsAdmissibleChain D bw j₀ G.level c.slot.1 A,
      IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1 A (D.eps (G.level - 1)))
        (familyLiftData D G.level c.slot.1 A (D.eps (G.level - 1))
          (pathEdges G π c.slot ⟨A, hA⟩)) sX sZ
        (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
        ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
        N R (Cc c.slot.1 A))
    (P : Vec (4 * c.chain.1.children.length))
    (hP : P ∈ actualIndependentCoarseStoredCarrier D c.chain.1 bw) :
    IsLiftSequenceOn (ladderOmega D bw j₀ G.level c.slot.1
        (actualIndependentCoarseParameterChain D c.chain.1 P) (D.eps (G.level - 1)))
      (familyLiftData D G.level c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P)
        (D.eps (G.level - 1)) (restrictConstituentEdges K hKD (actualIndependentCoarsePathEdges π c P)))
      sX sZ (D.slotStart G.level c.slot.1 / D.cellScaleSq G.level)
      ((((c.slot.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
      N R (Cc c.slot.1 (actualIndependentCoarseParameterChain D c.chain.1 P)) := by
  rw [actualIndependentCoarsePathEdges_native π c P hP]
  exact weakPath_isLiftSequenceOn_effective_order G K hKD hK π c.slot
    (c.atStoredParameter P hP) (D.eps (G.level - 1)) _ sX sZ N R hNK _ _ _
    (hc _ (c.atStoredParameter P hP).2)

end AVRegularity.EntryWeakProofs
end
end

section
/-! A common path anchor labels all produced charts; original native histories still use their actual contexts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ minBase cap H : ℕ} {B : ℝ}
  {G : GenStage D hr Dm bw j₀} {h : ℕ}

def weakStageCommonPathAnchor (G : GenStage D hr Dm bw j₀) (p : OddSlot)
    (hc : Nonempty (StageCtx D bw j₀ G.level p)) : StageCtx D bw j₀ G.level p :=
  Classical.choice hc

open scoped Classical in
def weakStageCommonPathEdges (G : GenStage D hr Dm bw j₀) (π : StagePath G h) (p : OddSlot) :
    ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ) :=
  if hc : Nonempty (StageCtx D bw j₀ G.level p) then
    pathEdges G π p (weakStageCommonPathAnchor G p hc)
  else fun _ _ _ => []

theorem weakStageCommonPathEdges_of_nonempty (G : GenStage D hr Dm bw j₀) (π : StagePath G h)
    (p : OddSlot) (hc : Nonempty (StageCtx D bw j₀ G.level p)) :
    weakStageCommonPathEdges G π p = pathEdges G π p (weakStageCommonPathAnchor G p hc) := by
  simp only [weakStageCommonPathEdges, dite_eq_left hc]

theorem IndependentWeakStageFluxProduction.pathIncomingField_anchored_production
    (S : IndependentWeakStageFluxProduction G minBase cap H B) (π : StagePath G h)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : D.term ≤ G.level) (hB : 0 ≤ B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (anchor : StageCtx D bw j₀ G.level c.slot) :
    ∃ Q : ∀ v u d, ∀ γ ∈ pathEdges G π c.slot anchor v u d, ∀ word,
      IndependentParameterSourceReserve H
        (independentPathTemplateField (S.pathIncomingField π c) v u d γ word),
      ∀ v u d γ hγ word n, n ≤ H → (Q v u d γ hγ word).budget n ≤
        weightedPathMatrix h (stagePathStoredWeight G π) v u * B := by
  classical
  have hprod : ∀ (j : Fin h) (d : Finset.Icc 2 Dm),
      d.val ≤ (G.fam.identity _ _ (π.step j).2.2).maxOrder → ∀ word,
      ∃ Q : IndependentParameterSourceReserve H (S.pathIncomingField π c j d word),
        ∀ n ≤ H, Q.budget n ≤ (G.fam.identity _ _ (π.step j).2.2).record.size * B := by
    intro j d hd word
    exact S.incomingField_reserve hq hΛ hζ hband hm hB c _ _ (π.step j).2.2 d.val word
      (Finset.mem_Icc.mp d.property).1 hd
  choose Q hQ using hprod
  have hpath := independentPathTemplateField_reserve G π c.slot anchor
    (S.pathIncomingField π c) Q B hQ
  choose R hR using hpath
  exact ⟨R, hR⟩

theorem IndependentWeakStageFluxProduction.pathIncomingField_anchored_native_copy
    (S : IndependentWeakStageFluxProduction G minBase cap H B) (π : StagePath G h)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (anchor : StageCtx D bw j₀ G.level c.slot)
    (Q : ∀ v u d, ∀ γ ∈ pathEdges G π c.slot anchor v u d, ∀ word,
      IndependentParameterSourceReserve H
        (independentPathTemplateField (S.pathIncomingField π c) v u d γ word))
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
      j₀ G.level c.slot.1) (t : ℝ) :
    SlowOpenEdgeEq
      (independentIntrinsicSliceCarrier (4 * c.chain.1.children.length)
        (actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
          j₀ G.level c.slot.1) Y) t
      (familyLiftData D G.level c.slot.1 (c.atParameter Y hY).1 (D.eps (G.level - 1))
        (pathEdges G π c.slot (c.atParameter Y hY))).edge
      (independentConstituentEdgeSlice (pathEdges G π c.slot anchor)
        (independentPathTemplateField (S.pathIncomingField π c)) Q
        (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length))
        (independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y)) := by
  change SlowOpenEdgeEq _ t (liftEdges (D.cellScaleSq G.level)
    (D.eps (G.level - 1) / D.eps (G.level - 1)) (pathEdges G π c.slot (c.atParameter Y hY))) _
  rw [div_self (show D.eps (G.level - 1) ≠ 0 from (Construction.Stream.ocEpsilon_pos hΛ).ne')]
  apply independentPathTemplate_fixed_context_clock_copy G π c.slot anchor (c.atParameter Y hY)
    (S.pathIncomingField π c) Q (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length))
    (independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y) _ (D.cellScaleSq G.level) t
  intro j d hd word X hX z
  exact S.incomingField_slice_native_copy hΛ hζ hband c _ _ (π.step j).2.2 d.val word
    (Finset.mem_Icc.mp d.property).1 hd Y hY X hX t z

theorem IndependentWeakStageFluxProduction.pathIncomingField_anchored_effective_production
    (S : IndependentWeakStageFluxProduction G minBase cap H B) (π : StagePath G h)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hm : D.term ≤ G.level) (hB : 0 ≤ B)
    (c : WeakStageProductionContext D bw j₀ G.level minBase cap) (anchor : StageCtx D bw j₀ G.level c.slot)
    (K : ℕ) (hKD : K ≤ Dm) (T : ℕ) (hTH : T ≤ H) :
    ∃ R : ∀ v u d, ∀ γ ∈ restrictConstituentEdges K hKD (pathEdges G π c.slot anchor) v u d, ∀ word,
      IndependentParameterSourceReserve T
        (restrictedIndependentEdgeField K hKD
          (independentPathTemplateField (S.pathIncomingField π c)) v u d γ word),
      (∀ v u d γ hγ word n, n ≤ T → (R v u d γ hγ word).budget n ≤
        weightedPathMatrix h (stagePathStoredWeight G π) v u * B) ∧
      ∀ Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
        j₀ G.level c.slot.1, ∀ t,
      SlowOpenEdgeEq
        (independentIntrinsicSliceCarrier (4 * c.chain.1.children.length)
          (actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (G.level - 1))
            j₀ G.level c.slot.1) Y) t
        (familyLiftData D G.level c.slot.1
          (actualIndependentCoarseParameterChain D c.chain.1
            (independentStoredParameterProjection (4 * c.chain.1.children.length) Y))
          (D.eps (G.level - 1)) (restrictConstituentEdges K hKD
            (actualIndependentCoarsePathEdges π c
              (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)))).edge
        (independentConstituentEdgeSlice (restrictConstituentEdges K hKD (pathEdges G π c.slot anchor))
          (restrictedIndependentEdgeField K hKD (independentPathTemplateField (S.pathIncomingField π c))) R
          (independentIntrinsicSlowEmbedding (4 * c.chain.1.children.length))
          (independentIntrinsicSliceOffset (4 * c.chain.1.children.length) Y)) := by
  obtain ⟨Q, hQ⟩ := S.pathIncomingField_anchored_production π hq hΛ hζ hband hm hB c anchor
  let R : ∀ v u d, ∀ γ ∈ restrictConstituentEdges K hKD (pathEdges G π c.slot anchor) v u d, ∀ word,
      IndependentParameterSourceReserve T
        (restrictedIndependentEdgeField K hKD
          (independentPathTemplateField (S.pathIncomingField π c)) v u d γ word) :=
    fun v u d γ hγ word => (Q v u ⟨d.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ γ hγ word).restrictOrder T hTH
  refine ⟨R, ?_, ?_⟩
  · intro v u d γ hγ word n hn
    exact hQ v u ⟨d.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ γ hγ word n (hn.trans hTH)
  · intro Y hY t
    have hΛ₁ : 1 ≤ D.Λ := by omega
    have he := (S.pathIncomingField_anchored_native_copy π hΛ₁ hζ hband c anchor Q Y hY t).restrictOrder K hKD
    rw [independentConstituentEdgeSlice_restrict K hKD _ _ Q R] at he
    rw [actualIndependentCoarsePathEdges_native π c _ hY.1.1.1]
    exact he

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual admissible appended chains stay in the bounded history menu used for production. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

def weakStageAppendedNativeChain
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (slot : ℤ) (t : ℝ) (z : Vec 2) : RealChain :=
  ((actualIndependentCoarseParameterChain D c.chain.1
    (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)).recenter D
      (D.eps (level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y)).appendChild D slot t z

theorem weakStageAppendedNativeChain_base
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (slot : ℤ) (t : ℝ) (z : Vec 2) :
    (weakStageAppendedNativeChain c Y slot t z).baseLevel = c.chain.1.baseLevel := by
  unfold weakStageAppendedNativeChain
  change (RealChain.recenter D _ _).baseLevel = _
  exact (weak_recenter_metadata D _ _).1

theorem weakStageAppendedNativeChain_depth
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (slot : ℤ) (t : ℝ) (z : Vec 2) :
    (weakStageAppendedNativeChain c Y slot t z).children.length = c.chain.1.children.length + 1 := by
  unfold weakStageAppendedNativeChain RealChain.appendChild
  rw [List.length_append, List.length_singleton, (weak_recenter_metadata D _ _).2.2]
  simp only [actualIndependentCoarseParameterChain, List.length_ofFn]

def WeakStageProductionContext.appendNative
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (slot : OddSlot) (t : ℝ) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z)) :
    WeakStageProductionContext D bw j₀ (level + 1) minBase (cap + 1) where
  slot := slot
  chain := ⟨weakStageAppendedNativeChain c Y slot.1 t z, hA⟩
  base_bound := by rw [weakStageAppendedNativeChain_base]; exact c.base_bound
  depth_bound := by rw [weakStageAppendedNativeChain_depth]; exact Nat.add_le_add_right c.depth_bound 1

end AVRegularity.EntryWeakProofs
end
end

section
/-! Physical mean-flux symmetry depends only on the genuine predecessor symmetry. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem positiveMeanFluxCoefficient_intrinsic_perm
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hh n : ℕ) (k : Fin 2) (m : ℕ)
    (hs : ∀ β (σ : Equiv.Perm (Fin m)), Cc hh (n - 1) m (β ∘ σ) = Cc hh (n - 1) m β)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    positiveMeanFluxCoefficient Q Cc hh n k m (α ∘ σ) =
      positiveMeanFluxCoefficient Q Cc hh n k m α := by
  funext t X z v u
  unfold positiveMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_perm _ _ m hs α σ, sourceFluxMeanCoefficient_perm]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The sampled zero-child reference and the actual admissible appended chart have equal geometry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

theorem weakStageSampled_reference_geometry
    (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (t : ℝ) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z)) :
    let cf := c.zeroChild hΛ hbw slot hs
    let cn := c.appendNative Y slot t z hA
    (actualIndependentCoarseParameterChain D cf.chain.1
      (weakZeroChildParameterPacking c.chain.1 slot.1
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t (z, Y)))).geom D =
      (actualIndependentCoarseParameterChain D cn.chain.1
        (independentFreshCoarseChainPacking D cn.chain.1)).geom D := by
  dsimp only [WeakStageProductionContext.zeroChild, WeakStageProductionContext.appendNative]
  rw [actualIndependentCoarseParameterChain_native D hΛ _ hA.2.2.1]
  rw [actualZeroChildParameterChain_eq_reference D c.chain.1 c.chain.2.2.2.1]
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hg := weakZeroChildReferenceFamily_append_geometry D c.chain.1 c.chain.2.2.2.1 slot.1
    (D.eps (level - 1)) (Construction.Stream.ocEpsilon_pos hΛ).ne'
    (by rw [hctx]) t z Y
  simpa only [hctx, hslot, weakStageAppendedNativeChain] using hg

theorem weakStageSampled_reference_center_bound
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : ℤ) (ell : ℝ) (hell : |ell| ≤ 1)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (t : ℝ) (z : Vec 2)
    (hc : ∀ j, ‖independentFreshChildProjection j false
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)‖ ≤ 3 / 16)
    (hY : ‖independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y‖ ≤ 1 / 8)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot) t z‖ ≤ 1 / 16) :
    ∀ j, ‖independentFreshChildProjection j false
      (weakZeroChildParameterPacking c.chain.1 slot
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot ell t (z, Y)))‖ ≤
      3 / 16 := by
  apply independentFreshChildProjection_cast_bound
    (show c.chain.1.children.length + 1 = (weakZeroChildAnchor c.chain.1 slot).children.length by
      simp only [weakZeroChildAnchor, List.length_append, List.length_singleton]) _ (3 / 16)
  intro j
  have hb := independentFreshCoarseAppendPacking_carrier_bound c.chain.1.children.length
    D level c.slot.1 slot ell hell t z Y hc hY hδ
  have hj := independentFreshCarrierCoordinates_center_bound (c.chain.1.children.length + 1)
    (independentIntrinsicParameterPacking (4 * (c.chain.1.children.length + 1)) 0
      (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot ell t (z, Y))) j
  rw [independentIntrinsicParameterPacking_stored] at hj
  exact hj.trans hb

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reference-natural actual fields can be read at an admissible appended native anchor. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

theorem weakStageSampled_reference_field
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (F : ∀ c : WeakStageProductionContext D bw j₀ (level + 1) minBase (cap + 1),
      ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2)
    (hF : ∀ c c', c.slot = c'.slot → c.chain.1.children.length = c'.chain.1.children.length →
      ∀ (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length)),
      (∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16) →
      (∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16) →
      (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
        (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D → ∀ t z,
      F c t z (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) 0 P) =
        F c' t z (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) 0 Q))
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (t : ℝ) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z))
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (hc : ∀ j, ‖independentFreshChildProjection j false
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)‖ ≤ 3 / 16)
    (hY : ‖independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y‖ ≤ 1 / 8)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16)
    (tt : ℝ) (zz : Vec 2) :
    let cf := c.zeroChild (by omega : 1 ≤ D.Λ) hbw slot hs
    let cn := c.appendNative Y slot t z hA
    F cf tt zz (independentIntrinsicParameterPacking (4 * cf.chain.1.children.length) 0
      (weakZeroChildParameterPacking c.chain.1 slot.1
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t (z, Y)))) =
      F cn tt zz (independentIntrinsicParameterPacking (4 * cn.chain.1.children.length) 0
        (independentFreshCoarseChainPacking D cn.chain.1)) := by
  dsimp only
  refine hF (c.zeroChild (by omega) hbw slot hs) (c.appendNative Y slot t z hA) rfl ?_ _ _ ?_ ?_ ?_ tt zz
  · change (weakZeroChildAnchor c.chain.1 slot.1).children.length =
      (weakStageAppendedNativeChain c Y slot.1 t z).children.length
    rw [weakStageAppendedNativeChain_depth]
    simp only [weakZeroChildAnchor, List.length_append, List.length_singleton]
  · exact weakStageSampled_reference_center_bound c slot.1 _ hell Y t z hc hY hδ
  · intro j
    exact (independentFreshCoarseChainPacking_center_bound D hq hΛ _ bw hbw₁ j₀ (level + 1)
      slot.1 hA j).trans (by norm_num)
  · exact weakStageSampled_reference_geometry (by omega) hbw c slot hs Y t z hA

end AVRegularity.EntryWeakProofs
end
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFirstCrossResponseProduction

section
section
/-! Finite positive-response source prices, including the exceptional initial metric cancellation. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

def independentPositiveCellPrice (d K D n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (BG BV BE B : ℝ) : ℝ :=
  if n = 2 then
    (1 + ((d : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
      normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget 1 A * B)
  else
    (1 + ((d : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
      (normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget (n - 1) A * B) +
        normalizedCellB2UniformBudget K A 1 BG (finiteLiftSymbolBudget (n - 2) A * B)) +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal 0,
        independentLiftMeanCompositionCost d K j A B
          (independentLiftAProductionMenuCost (K + D) D n count A 1 BG BV BE B)

theorem independentPositiveCellPrice_nonneg (d K D n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentPositiveCellPrice d K D n count A BG BV BE B := by
  have htest q : 0 ≤ finiteLiftSymbolBudget q A * B := mul_nonneg (finiteLiftSymbolBudget_nonneg q A) hB
  have hcenter : 0 ≤ (1 + ((d : ℝ) + 1) ^ K * (K + 1 : ℕ)) := by positivity
  unfold independentPositiveCellPrice
  split
  · exact mul_nonneg hcenter (normalizedCellB1UniformBudget_nonneg _ _ _ _ _ _ hBG hBV (htest 1))
  · exact add_nonneg
      (mul_nonneg hcenter (add_nonneg
        (normalizedCellB1UniformBudget_nonneg _ _ _ _ _ _ hBG hBV (htest (n - 1)))
        (normalizedCellB2UniformBudget_nonneg _ _ _ _ _ hBG (htest (n - 2)))))
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ =>
        independentLiftMeanCompositionCost_nonneg d K j A B _ hB
          (independentLiftAProductionMenuCost_nonneg _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB))

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite common positive-response price precedes every actual family and calibration test. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

def independentPositiveCalibrationPrice (d K D n m count : ℕ) (BG BV BE B : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) × Fin (n + 1), independentPositiveCellPrice d K D n count
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) BG BV BE B

theorem independentPositiveCalibrationPrice_nonneg (d K D n m count : ℕ) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentPositiveCalibrationPrice d K D n m count BG BV BE B :=
  Finset.sum_nonneg fun _ _ => independentPositiveCellPrice_nonneg _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB

theorem independentPositiveCellPrice_le_calibrated (d K D n m count : ℕ) (BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (p : Fin (m + 1) × Fin (n + 1)) :
    independentPositiveCellPrice d K D n count
      ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) BG BV BE B ≤
      independentPositiveCalibrationPrice d K D n m count BG BV BE B := by
  unfold independentPositiveCalibrationPrice
  exact Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) =>
    independentPositiveCellPrice_nonneg d K D n count
      ((q.2 : ℝ) • coordinateSymbolDirection (q.1 : ℝ)) BG BV BE B hBG hBV hBE hB)
    (Finset.mem_univ p)

end AVRegularity.EntryWeakProofs
end
end

section
/-! All higher positive diagonal inverse sources share one response-linear finite price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositiveCellSource_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B)
    (hK : K ≤ H) (hbase : K + 2 * D + 2 ≤ base) (hn : 2 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) :
    ∃ Qs : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S
          (independentFinitePositivePredecessors S P Q hθ (zero_le_one.trans hB))) 0 n out inp),
      ∀ r ≤ K, Qs.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
        independentPositiveCellPrice (2 + d) K D n count A BG BV BE B := by
  by_cases hn2 : n = 2
  · subst n
    have hp := independentPositiveSecondSource_uniform_production S P Q hθ0 hθ hBG hBV
      (zero_le_one.trans hB) hK (by omega) hnN A out inp
    simpa only [independentPositiveCellPrice, ite_true] using hp
  · have hp := independentPositiveDiagonalCellSource_uniform_production S P Q hθ0 hθ hBG hBV hBE hB
      hK hbase (by omega) hnN hnD A out inp
    simpa only [independentPositiveCellPrice, ite_eq_right hn2] using hp

end AVRegularity.EntryWeakProofs
end
end

section
/-! First response production depends only on the primitive slow germ and its response. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentFirstCrossResponseGermProduction (d k D N R count qs m : ℕ)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (hm : m ≤ 1) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x : IndependentFirstResponseDatum ι d k D N R count qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k 1 x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  obtain ⟨C, hC, Q, hnat, hcross⟩ := independentFirstCrossResponseCoefficientProduction
    d k D N R count qs m hD hN hm α out inp BG BV BE B hBG hBV hB
  refine ⟨C, hC, Q, hnat, ?_⟩
  intro x y U Y Z _hU hzero hresponse he t z
  refine hcross x y Y Z ?_ he.window_left he.window_right he.drift ?_ ?_ t z
  · rw [hresponse, he.matrix]
  · intro r
    ext i j
    simpa only [map_zero, zero_add] using he.metric i j r 0 hzero (0 : Vec 2)
  · intro p r w
    rw [independentFirstLiftCellSource x.primitive x.productions,
      independentFirstLiftCellSource y.primitive y.productions, he.drift]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Joint finite-rank induction produces coherent full-parameter coefficient fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCrossNaturalRankProduction (d base D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (r : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : IndependentLiftRankProductionFamily ι d base D N R count qs r BG BV BE C,
      Q.IsNatural ∧ Q.IsCrossNatural := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    choose C hC Qprior hNatPrior hCrossPrior using fun p : Fin r => ih p.val p.isLt
    let B := finitePriorRankBudget r C
    have hBC : 1 ≤ B := finitePriorRankBudget_one_le r C (fun p => zero_le_one.trans (hC p))
    let I := IndependentLiftPositiveIndex ι R N
    have hstep (i : I) := independentLiftCrossNaturalStepCoefficientProduction d base D N R count qs
      i.1.val i.2.1.val.val i.2.2.1.val (by have := i.1.isLt; omega) i.2.1.property
      (by have := i.2.1.val.isLt; omega) hND (by have := i.2.2.1.isLt; omega)
      i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 BG BV BE B hBG hBV hBE (zero_le_one.trans hBC)
    choose A hA Qstep hNatStep hCrossStep using hstep
    let K := independentFiniteStepBudget A
    have hK : 1 ≤ K := independentFiniteStepBudget_one_le A (fun i => zero_le_one.trans (hA i))
    let X := IndependentLiftNaturalPrimitiveDatum ι d
      (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE
    have hindices : ∀ hh n (hhh : hh ≤ R) (hnN : n ≤ N)
        (hr : ambientRecurrenceRank N hh n = r) m (hm : m ≤ n) (α : DerivativeWord2 m) v u,
        ∃ Q : ∀ x : X, IndependentScalarCoefficientProduction (2 + d)
          (liftProductionOrder base D N R hh n) n x.primitive.a x.primitive.b x.primitive.U
          (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
          (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower x.primitive.M hh v u) K,
          (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
          ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
            IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
            ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
      intro hh n hhh hnN hr m hm α v u
      by_cases hn0 : n = 0
      · subst n
        choose Q hzNat hzFormula using fun x : X =>
          x.primitive.zero_degree_explicit_natural_production
            (liftProductionOrder base D N R hh 0) hh m hhh hm α v u K hK
        refine ⟨Q, (fun x δ _ => hzNat x δ), ?_⟩
        intro x y U Y Z _ _ _ t z
        rw [hzFormula x, hzFormula y]
      · have hn : 1 ≤ n := by omega
        have earlier : ∀ p q (hpq : p < hh ∨ (p = hh ∧ q < n)) l (hl : l ≤ q)
            (β : DerivativeWord2 l) v u,
            ∃ Q : ∀ x : X, IndependentScalarCoefficientProduction (2 + d)
              (4 * liftProductionOrder base D N R hh n + 2 * D + 7) q
              x.primitive.a x.primitive.b x.primitive.U
              (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) p q)
              (independentIntrinsicSlowProjection d) l β v u (finiteMatrixPower x.primitive.M p v u) B,
              (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
              ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
                IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
                ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
          intro p q hpq l hl β v u
          have hpR : p ≤ R := by rcases hpq with h | ⟨rfl, _⟩ <;> omega
          by_cases hq : q ≤ N
          · have hprior : ambientRecurrenceRank N p q < r := by
              rw [← hr]
              rcases hpq with hp | ⟨rfl, hqn⟩
              · exact ambientRecurrenceRank_height N hh n p q hp hq
              · exact ambientRecurrenceRank_composition N p n p q le_rfl hnN hqn
            let j : Fin r := ⟨ambientRecurrenceRank N p q, hprior⟩
            have ho := liftProductionOrder_predecessor_room base D N R hh n p q hhh hnN hq hpq
            let Q := fun x : X =>
              ((Qprior j) x p q hpR hq rfl l hl β v u).monoOrder _ ho |>.enlargeBudget B
                (priorRankBudget_le_common r C (fun j => zero_le_one.trans (hC j)) j)
                (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg p v u)
            refine ⟨Q, ?_, ?_⟩
            · intro x δ hδ
              exact hNatPrior j x p q hpR hq rfl l hl β v u δ hδ
            · intro x y U Y Z hU hzero he t z
              exact hCrossPrior j x y U Y Z hU hzero he p q hpR hq rfl l hl β v u t z
          · choose Q hzNat hzFormula using fun x : X =>
              x.primitive.above_degree_explicit_natural_production
                (4 * liftProductionOrder base D N R hh n + 2 * D + 7) p q l hpR (by omega) β v u
                B (zero_le_one.trans hBC)
            refine ⟨Q, (fun x δ _ => hzNat x δ), ?_⟩
            intro x y U Y Z _ _ _ t z
            rw [hzFormula x, hzFormula y]
        choose P hPNat hPCross using earlier
        let datum := fun x : X =>
          (⟨x, (fun p q hpq l hl β v u => P p q hpq l hl β v u x),
            (fun δ hδ p q hpq l hl β v u => hPNat p q hpq l hl β v u x δ hδ)⟩ :
            IndependentLiftNaturalProductionStepDatum ι d base D N R count qs hh n BG BV BE B)
        let i : I := ⟨⟨hh, by omega⟩, ⟨⟨n, by omega⟩, hn⟩,
          ⟨m, by change m < n + 1; omega⟩, α, v, u⟩
        let Q := fun x : X => (Qstep i (datum x)).enlargeBudget K
          (independentFiniteStepBudget_entry_le A (fun i => zero_le_one.trans (hA i)) i)
          (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh v u)
        refine ⟨Q, ?_, ?_⟩
        · intro x δ hδ
          exact hNatStep i (datum x) δ hδ
        · intro x y U Y Z hU hzero he t z
          apply hCrossStep i (datum x) (datum y) U Y Z hU hzero he ?_ t z
          intro p q hpq l hl β v u τ V hV w
          let U' : Set (Vec 2) := (fun W => W + V) ⁻¹' U
          have hU' : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
          have hz' : (0 : Vec 2) ∈ U' := by simpa only [U', Set.mem_preimage, zero_add] using hV
          exact hPCross p q hpq l hl β v u x y U'
            (independentIntrinsicSlowEmbedding d V + Y) (independentIntrinsicSlowEmbedding d V + Z)
            hU' hz' (he.recenter V) τ w
    choose Q hNat hCross using hindices
    refine ⟨K, hK, (fun x hh n hhh hn hr m hm α v u => Q hh n hhh hn hr m hm α v u x), ?_, ?_⟩
    · intro x hh n hhh hn hr m hm α v u δ hδ
      exact hNat hh n hhh hn hr m hm α v u x δ hδ
    · intro x y U Y Z hU hzero he hh n hhh hn hr m hm α v u t z
      exact hCross hh n hhh hn hr m hm α v u x y U Y Z hU hzero he t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Joint first-response production preserves primitive germ equality at the actual geometric order. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentFirstCrossResponseOrderProduction (d base D N R count qs m : ℕ)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (hm : m ≤ 1) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) (liftProductionOrder base D N R 0 1) 1 x.data.primitive.a x.data.primitive.b
        x.data.primitive.U (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.data.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.data.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  let k := liftProductionOrder base D N R 0 1
  have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
    have ho := liftProductionOrder_le_initial base D N R 0 1
    dsimp only [independentLiftPrimitiveTopOrder, k]
    omega
  let datum := fun x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B =>
    (⟨x.data.primitive.monoOrder (4 * k + 5) horder,
      (fun hh n hhh hn m hm α v u => (x.productions hh n hhh hn m hm α v u).monoOrder _ (by omega)),
      x.data.fastOrder, x.response, x.response_nonneg,
      (fun i r hr => x.drift_response i r (hr.trans horder)),
      x.data.translations, x.data.metric_translation⟩ :
      IndependentFirstResponseDatum ι d k D N R count qs BG BV BE B)
  obtain ⟨C, hC, Qcore, hnat, hcross⟩ := independentFirstCrossResponseGermProduction
    d k D N R count qs m hD hN hm α out inp BG BV BE B hBG hBV hB
  let Q := fun x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B =>
    (Qcore (datum x)).enlargeBudget (1 + C) (le_add_of_nonneg_left zero_le_one)
      (mul_nonneg x.response_nonneg
        (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp))
  refine ⟨1 + C, le_add_of_nonneg_right hC, Q, ?_, ?_⟩
  · intro x δ hδ
    exact hnat (datum x) δ hδ
  · intro x y U Y Z hU hzero hresponse he t z
    exact hcross (datum x) (datum y) U Y Z hU hzero hresponse
      (he.monoOrder (4 * k + 5) horder) t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite uniform price covers coherent coefficient productions at every requested rank. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCrossNaturalFiniteProduction (d base D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x : IndependentLiftNaturalPrimitiveDatum ι d
      (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE,
      ∀ hh n, hh ≤ R → n ≤ N → ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base n
        x.primitive.a x.primitive.b x.primitive.U
        (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) hh n)
        (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower x.primitive.M hh v u) C,
      (∀ x hh n hhh hn m hm α v u δ, δ ∈ x.translations →
        IndependentSourceTranslationInvariant δ (Q x hh n hhh hn m hm α v u).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
        ∀ hh n hhh hn m hm α v u t z,
          (Q x hh n hhh hn m hm α v u).field t z Y =
          (Q y hh n hhh hn m hm α v u).field t z Z := by
  choose C hC Qrank hNat hCross using fun r : Fin (liftProductionRankMax N R + 1) =>
    independentLiftCrossNaturalRankProduction (ι := ι) d base D N R count qs BG BV BE hND hBG hBV hBE r.val
  let B := finitePriorRankBudget (liftProductionRankMax N R + 1) C
  have hB : 1 ≤ B := finitePriorRankBudget_one_le _ C (fun r => zero_le_one.trans (hC r))
  let X := IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE
  let Q := fun (x : X) (hh n : ℕ) (hhh : hh ≤ R) (hn : n ≤ N) (m : ℕ) (hm : m ≤ n)
      (α : DerivativeWord2 m) (v u : ι) => by
    let r : Fin (liftProductionRankMax N R + 1) :=
      ⟨ambientRecurrenceRank N hh n, Nat.lt_succ_of_le (liftProductionRank_le N R hh n hhh hn)⟩
    have ho : base ≤ liftProductionOrder base D N R hh n := by
      exact (Nat.le_succ base).trans
        (weakJointRecurrenceReserve_base (4 * (D + 4)) base (liftProductionRankMax N R)
          (ambientRecurrenceRank N hh n) (by omega))
    exact ((Qrank r) x hh n hhh hn rfl m hm α v u).monoOrder base ho |>.enlargeBudget B
      (priorRankBudget_le_common _ C (fun r => zero_le_one.trans (hC r)) r)
      (finiteMatrixPower_nonneg x.primitive.M x.primitive.matrix_nonneg hh v u)
  refine ⟨B, hB, Q, ?_, ?_⟩
  · intro x hh n hhh hn m hm α v u δ hδ
    let r : Fin (liftProductionRankMax N R + 1) :=
      ⟨ambientRecurrenceRank N hh n, Nat.lt_succ_of_le (liftProductionRank_le N R hh n hhh hn)⟩
    exact hNat r x hh n hhh hn rfl m hm α v u δ hδ
  · intro x y U Y Z hU hzero he hh n hhh hn m hm α v u t z
    let r : Fin (liftProductionRankMax N R + 1) :=
      ⟨ambientRecurrenceRank N hh n, Nat.lt_succ_of_le (liftProductionRank_le N R hh n hhh hn)⟩
    exact hCross r x y U Y Z hU hzero he hh n hhh hn rfl m hm α v u t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! The first response menu is selected jointly across primitive data before its finite price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentFirstCrossResponseMenuProduction (d base D N R count qs : ℕ)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B,
      ∀ m, m ≤ 1 → ∀ α : DerivativeWord2 m, ∀ out inp,
      IndependentScalarCoefficientProduction (2 + d) (liftProductionOrder base D N R 0 1) 1
        x.data.primitive.a x.data.primitive.b x.data.primitive.U
        (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.data.primitive.M 0 out inp) C,
      (∀ x m hm α out inp δ, δ ∈ x.data.translations →
        IndependentSourceTranslationInvariant δ (Q x m hm α out inp).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ m hm α out inp t z, (Q x m hm α out inp).field t z Y = (Q y m hm α out inp).field t z Z := by
  classical
  let I := Σ m : Fin 2, DerivativeWord2 m.val × ι × ι
  have hprod (i : I) := independentFirstCrossResponseOrderProduction d base D N R count qs i.1.val
    hD hN (by have := i.1.isLt; omega) i.2.1 i.2.2.1 i.2.2.2 BG BV BE B hBG hBV hB
  choose C hC Qcore hnat hcross using hprod
  let K := independentFiniteStepBudget C
  have hK : 1 ≤ K := independentFiniteStepBudget_one_le C (fun i => zero_le_one.trans (hC i))
  let Q := fun (x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B)
    m (hm : m ≤ 1) (α : DerivativeWord2 m) out inp =>
      (Qcore (⟨⟨m, by omega⟩, α, out, inp⟩ : I) x).enlargeBudget K
        (independentFiniteStepBudget_entry_le C (fun i => zero_le_one.trans (hC i)) _)
        (mul_nonneg x.response_nonneg
          (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp))
  refine ⟨K, hK, Q, ?_, ?_⟩
  · intro x m hm α out inp δ hδ
    exact hnat _ x δ hδ
  · intro x y U Y Z hU hzero hresponse he m hm α out inp t z
    exact hcross _ x y U Y Z hU hzero hresponse he t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Primitive reserve room pays both the unscaled full native menu and the positive degree induction. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

def independentPositivePrimitiveTopOrder (base D N R : ℕ) : ℕ :=
  independentLiftPrimitiveTopOrder (independentLiftPrimitiveTopOrder base D N R + 2 * D + 2) D N R

theorem independentLiftPrimitiveTopOrder_base_le (base D N R : ℕ) :
    base ≤ independentLiftPrimitiveTopOrder base D N R := by
  have ho : base ≤ liftProductionOrder base D N R 0 0 :=
    (Nat.le_succ base).trans (weakJointRecurrenceReserve_base (4 * (D + 4)) base
      (liftProductionRankMax N R) (ambientRecurrenceRank N 0 0) (by omega))
  dsimp only [independentLiftPrimitiveTopOrder]
  omega

theorem independentPositivePrimitiveTopOrder_room (base D N R : ℕ) :
    independentLiftPrimitiveTopOrder base D N R ≤ independentPositivePrimitiveTopOrder base D N R := by
  let menu := independentLiftPrimitiveTopOrder base D N R + 2 * D + 2
  have ho : menu ≤ liftProductionOrder menu D N R 0 0 :=
    (Nat.le_succ menu).trans (weakJointRecurrenceReserve_base (4 * (D + 4)) menu
      (liftProductionRankMax N R) (ambientRecurrenceRank N 0 0) (by omega))
  change independentLiftPrimitiveTopOrder base D N R ≤ 4 * liftProductionOrder menu D N R 0 0 + 5
  dsimp only [menu] at ho ⊢
  omega

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Actual higher diagonal inverses produce response-linear coefficients from genuine positive predecessors. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossResponseCoefficientProduction (d k D N R count qs n m : ℕ)
    (hn : 2 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveResponseDatum ι d k D N R count n qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k n x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x x' Y Z,
        x.response * finiteMatrixPower x.primitive.M 0 out inp =
          x'.response * finiteMatrixPower x'.primitive.M 0 out inp →
        x.primitive.a = x'.primitive.a → x.primitive.b = x'.primitive.b →
        x.primitive.v = x'.primitive.v →
        (∀ t, x.primitive.G t Y = x'.primitive.G t Z) →
        (∀ p : Fin (m + 1) × Fin (n + 1), ∀ t z,
          independentLiftCoefficientCellSource x.primitive.edge x.primitive.edgeField
            (independentIntrinsicSlowEmbedding d)
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 x.primitive.G x.primitive.v
            (independentFiniteLiftFields x.primitive (independentFinitePositivePredecessors x.primitive x.productions x.earlier
              x.response_small (zero_le_one.trans hB))) 0 n out inp t z Y =
          independentLiftCoefficientCellSource x'.primitive.edge x'.primitive.edgeField
            (independentIntrinsicSlowEmbedding d)
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 x'.primitive.G x'.primitive.v
            (independentFiniteLiftFields x'.primitive (independentFinitePositivePredecessors x'.primitive x'.productions x'.earlier
              x'.response_small (zero_le_one.trans hB))) 0 n out inp t z Z) →
        ∀ t z, (Q x).field t z Y = (Q x').field t z Z := by
  let X := IndependentPositiveResponseDatum ι d k D N R count n qs BG BV BE B
  let A := fun p : Fin (m + 1) × Fin (n + 1) => (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let Pc := fun (x : X) => independentFinitePositivePredecessors x.primitive x.productions x.earlier
    x.response_small (zero_le_one.trans hB)
  let src := fun (x : X) p => independentLiftCoefficientCellSource x.primitive.edge
    x.primitive.edgeField (independentIntrinsicSlowEmbedding d) (A p) 1 x.primitive.G
    x.primitive.v (independentFiniteLiftFields x.primitive (Pc x)) 0 n
  let g := fun (x : X) p => independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
    (fun t z Y v => src x p v inp t z Y)
  have hprod (x : X) p := independentPositiveCellSource_uniform_production x.primitive x.productions
    x.earlier x.response_nonneg x.response_small hBG hBV hBE hB le_rfl le_rfl hn hnN hnD (A p) out inp
  choose Q hQ using hprod
  let Qg := fun (x : X) p => ((Q x p).timeWindow (Ioc x.primitive.a x.primitive.b)
    measurableSet_Ioc).congrSource (show independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
      (src x p out inp) = (fun t z Y => g x p t z Y out) by
        funext t z Y
        by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
        · simp only [g, independentTimeWindowSource, ite_eq_left ht]
        · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply])
  let BS := independentPositiveCalibrationPrice (2 + d) (4 * k + 5) D n m count BG BV BE B
  have hBS : 0 ≤ BS := independentPositiveCalibrationPrice_nonneg _ _ _ _ _ _ _ _ _ _ hBG hBV hBE (zero_le_one.trans hB)
  have hθ (x : X) : 0 ≤ x.response * finiteMatrixPower x.primitive.M 0 out inp :=
    mul_nonneg x.response_nonneg (finiteMatrixPower_nonneg _ x.primitive.matrix_nonneg _ _ _)
  have hQg (x : X) p r (hr : r ≤ 4 * k + 5) :
      (Qg x p).budget r ≤ (x.response * finiteMatrixPower x.primitive.M 0 out inp) * BS := by
    dsimp only [Qg]
    rw [IndependentParameterSourceReserve.congrSource_budget,
      IndependentParameterSourceReserve.timeWindow_budget]
    exact (hQ x p r hr).trans (mul_le_mul_of_nonneg_left
      (independentPositiveCellPrice_le_calibrated (2 + d) (4 * k + 5) D n m count BG BV BE B
        hBG hBV hBE (zero_le_one.trans hB) p) (hθ x))
  have hg (x : X) p t (ht : t ≤ x.primitive.a) z Y : g x p t z Y out = 0 := by
    rw [show g x p t z Y = 0 from independent_time_window_Ioc_past_zero
      (fun t z Y => (fun v => src x p v inp t z Y)) x.primitive.a x.primitive.b t ht z Y]
    rfl
  have hmean (x : X) p t Y : fieldCellMean (fun z => g x p t z Y out) = 0 := by
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simp only [g, independentTimeWindowSource, ite_eq_left ht]
      exact independentFiniteLiftSource_mean_zero x.primitive (Pc x) hB le_rfl
        (A p) out inp (by omega) hnD t Y
    · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply, fieldCellMean_zero]
  have hactual (x : X) p Y (hY : Y ∈ x.primitive.U) :
      IsCellFieldInverse (x.primitive.molecular Y).G (x.primitive.molecular Y).v qs x.primitive.a x.primitive.b 0
        (fun t z => g x p t z Y)
        (fun t z => (Real.exp (((1 : ℝ) • A p) (independentIntrinsicSlowProjection d Y)))⁻¹ •
          liftApply n (x.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
            (fun _ Z => Real.exp (((1 : ℝ) • A p) Z) • (Pi.single inp (1 : ℝ) : ι → ℝ))
            t (independentIntrinsicSlowProjection d Y) z) := by
    have hi := independentFiniteLiftSource_actual_inverse x.primitive (Pc x) hB le_rfl
      (by omega) (by omega) (Nat.zero_le R) (by omega) hnN hnD (A p) inp Y hY
    rw [x.fastOrder] at hi
    simpa only [g, src, one_smul] using hi
  let Rel : X → Vec (2 + d) → Vec (2 + d) → Prop := fun x Y Z => ∃ δ ∈ x.translations, Y = Z + δ
  have hGR (x : X) Y Z (hYZ : Rel x Y Z) t : x.primitive.G t Y = x.primitive.G t Z := by
    obtain ⟨δ, hδ, rfl⟩ := hYZ
    exact x.metric_translation δ hδ t Z
  have hgR (x : X) p Y Z (hYZ : Rel x Y Z) t z : g x p t z Y out = g x p t z Z out := by
    obtain ⟨δ, hδ, rfl⟩ := hYZ
    have hPc := independentFinitePositivePredecessors_translation_invariant x.primitive x.productions x.earlier
      x.response_small (zero_le_one.trans hB) δ (x.production_translation δ hδ) (x.earlier_translation δ hδ)
    have hc := independentFiniteLiftFields_translation_invariant x.primitive (Pc x) δ hPc
    have hs := independentLiftCoefficientCellSource_translation_invariant δ x.primitive.edge x.primitive.edgeField
      (independentIntrinsicSlowEmbedding d) (A p) 1 x.primitive.G x.primitive.v
      (independentFiniteLiftFields x.primitive (Pc x))
      (fun t Y i j => congrFun (congrFun (x.metric_translation δ hδ t Y) i) j)
      (x.edge_translation δ hδ) hc 0 n out inp t z Z
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simpa only [g, src, independentTimeWindowSource, ite_eq_left ht] using hs
    · simp only [g, independentTimeWindowSource, ite_eq_right ht]
  obtain ⟨C, hC, Qprod, hnat, hcross⟩ := family_variable_window_cross_natural_independent_coefficient_productions_exist (A := X)
    (fun x => x.primitive.window) k (k + 4) k n m hm (by omega) (by omega) le_rfl (by omega)
    out inp (fun x => x.primitive.metric) Qg (fun _ => BG) (fun _ => BS) (fun _ => hBG)
    (fun _ => hBS) (fun x => x.primitive.metric_bound)
    (fun x => x.response * finiteMatrixPower x.primitive.M 0 out inp) hθ hQg
    (fun x => x.primitive.molecular) (fun x => x.primitive.molecular_coefficients)
    (fun x => x.primitive.v) (fun x => x.primitive.drift) (fun x => x.primitive.molecular_drift)
    (fun x => x.primitive.molecular_budget) hg hmean Rel hGR hgR qs
    (fun x Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
    (fun _ => independentIntrinsicSlowProjection d) (fun x => x.primitive.U)
    (fun x Y β σ => x.primitive.symmetric _ 0 (Nat.zero_le R) n m β σ) α 1 one_ne_zero hactual
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
      simpa only [g, src, Pc, independentTimeWindowSource, ite_eq_left ht, ite_eq_left ht', A]
        using hs p t z
    · have ht' : t ∉ Ioc x'.primitive.a x'.primitive.b := hwindow ▸ ht
      simp only [g, independentTimeWindowSource, ite_eq_right ht, ite_eq_right ht', Pi.zero_apply]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Positive primitive input records only the genuine response bound on the drift. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

structure IndependentPositiveNaturalPrimitiveDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d base D N R count qs : ℕ) (BG BV BE : ℝ) where
  data : IndependentLiftNaturalPrimitiveDatum ι d
    (independentPositivePrimitiveTopOrder base D N R) D N R count qs BG BV BE
  response : ℝ
  response_nonneg : 0 ≤ response
  response_small : response ≤ 1
  drift_response : ∀ i r, r ≤ independentLiftPrimitiveTopOrder base D N R →
    (data.primitive.drift_entries i).budget r ≤ response * BV

end AVRegularity.EntryWeakProofs
end
end

section
/-! Response-linear native production retains equality on equivalent primitive and predecessor germs. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossResponseGermProduction (d k D N R count qs n m : ℕ)
    (hn : 2 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveResponseDatum ι d k D N R count n qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k n x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
        (∀ hh q hhh hq m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.productions hh q hhh hq m hm α v u).field
            (y.productions hh q hhh hq m hm α v u).field) →
        (∀ q hq hqn m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.earlier q hq hqn m hm α v u).field
            (y.earlier q hq hqn m hm α v u).field) →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  obtain ⟨C, hC, Q, hnat, hcross⟩ := independentPositiveCrossResponseCoefficientProduction
    d k D N R count qs n m hn hnN hnD hm α out inp BG BV BE B hBG hBV hBE hB
  refine ⟨C, hC, Q, hnat, ?_⟩
  intro x y U Y Z hU hzero hresponse he hp hq t z
  let Px := independentFinitePositivePredecessors x.primitive x.productions x.earlier
    x.response_small (zero_le_one.trans hB)
  let Py := independentFinitePositivePredecessors y.primitive y.productions y.earlier
    y.response_small (zero_le_one.trans hB)
  have hP hh q hhh hqN m hm α v u :
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
        (Px hh q hhh hqN m hm α v u).field (Py hh q hhh hqN m hm α v u).field := by
    dsimp only [Px, Py, independentFinitePositivePredecessors]
    split
    · rename_i ha
      obtain ⟨rfl, hpos, hqn⟩ := ha
      exact hq q hpos hqn m hm α v u
    · exact hp hh q hhh hqN m hm α v u
  have hfields := independentFiniteLiftFields_slow_slice_congr x.primitive y.primitive Px Py Y Z hP
  choose Qx _hx using fun hh q m (α : DerivativeWord2 m) v u =>
    independentFiniteLiftFields_reserve x.primitive Px hB hh q m α v u
  choose Qy _hy using fun hh q m (α : DerivativeWord2 m) v u =>
    independentFiniteLiftFields_reserve y.primitive Py hB hh q m α v u
  refine hcross x y Y Z ?_ he.window_left he.window_right he.drift ?_ ?_ t z
  · rw [hresponse, he.matrix]
  · intro r
    ext i j
    simpa only [map_zero, zero_add] using he.metric i j r 0 hzero (0 : Vec 2)
  · intro p r w
    have hs : IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
        (independentLiftCoefficientCellSource x.primitive.edge x.primitive.edgeField
          (independentIntrinsicSlowEmbedding d)
          ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 x.primitive.G x.primitive.v
          (independentFiniteLiftFields x.primitive Px) 0 n out inp)
        (independentLiftCoefficientCellSource y.primitive.edge y.primitive.edgeField
          (independentIntrinsicSlowEmbedding d)
          ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 y.primitive.G y.primitive.v
          (independentFiniteLiftFields y.primitive Py) 0 n out inp) := by
      rw [← he.edge, ← he.drift]
      apply independentLiftCoefficientCellSource_slow_slice_congr x.primitive.edge
        x.primitive.edgeField y.primitive.edgeField (independentIntrinsicSlowEmbedding d)
        (independentIntrinsicSlowEmbedding_norm_le d) Y Z _ 1 x.primitive.G y.primitive.G
        x.primitive.v _ _ 0 n (by omega) hnD out inp
      · intro i j
        exact (x.primitive.metric_entries i j).restrictOrder (D + 1) (by omega)
      · intro i j
        exact (y.primitive.metric_entries i j).restrictOrder (D + 1) (by omega)
      · intro i
        exact (x.primitive.drift_entries i).restrictOrder D (by omega)
      · intro hh q _hhq m α v u
        exact (Qx hh q m.val α v u).restrictOrder (2 * D + 2) (by omega)
      · intro hh q _hhq m α v u
        exact (Qy hh q m.val α v u).restrictOrder (2 * D + 2) (by omega)
      · intro v u e γ hγ α
        exact (x.primitive.edges v u e γ hγ α).restrictOrder (D + 1) (by omega)
      · intro v u e γ hγ α
        have hγ' : γ ∈ y.primitive.edge v u e := by rw [← he.edge]; exact hγ
        exact (y.primitive.edges v u e γ hγ' α).restrictOrder (D + 1) (by omega)
      · exact hU
      · exact he.metric
      · exact he.edge_fields
      · intro hh q _hhq m α v u
        exact hfields hh q m α v u
    simpa only [map_zero, zero_add, Px, Py] using hs r 0 hzero w

end AVRegularity.EntryWeakProofs
end
end

section
/-! Joint positive-response production fits the geometric degree induction without losing germ equality. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossResponseOrderProduction (d base D N R count qs n m : ℕ)
    (hn : 2 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D) (hm : m ≤ n) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveNaturalStepDatum ι d base D N R count qs n BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) (liftProductionOrder base D N R 0 n) n x.menu.data.primitive.a x.menu.data.primitive.b
        x.menu.data.primitive.U (fun Y => x.menu.data.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.menu.response * finiteMatrixPower x.menu.data.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.menu.data.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        x.menu.response = y.menu.response →
        IndependentLiftPrimitiveSlowSliceEq x.menu.data.primitive y.menu.data.primitive U Y Z →
        (∀ hh q hhh hq m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.menu.productions hh q hhh hq m hm α v u).field
            (y.menu.productions hh q hhh hq m hm α v u).field) →
        (∀ q hq hqn m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.earlier q hq hqn m hm α v u).field
            (y.earlier q hq hqn m hm α v u).field) →
        ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
  let k := liftProductionOrder base D N R 0 n
  obtain ⟨C, hC, Qcore, hnat, hcross⟩ := independentPositiveCrossResponseGermProduction
    d k D N R count qs n m hn hnN hnD hm α out inp BG BV BE B hBG hBV hBE hB
  let Q := fun x : IndependentPositiveNaturalStepDatum ι d base D N R count qs n BG BV BE B =>
    (Qcore x.restrict).enlargeBudget (1 + C) (le_add_of_nonneg_left zero_le_one)
      (mul_nonneg x.menu.response_nonneg
        (finiteMatrixPower_nonneg x.menu.data.primitive.M x.menu.data.primitive.matrix_nonneg 0 out inp))
  refine ⟨1 + C, le_add_of_nonneg_right hC, Q, ?_, ?_⟩
  · intro x δ hδ
    exact hnat x.restrict δ hδ
  · intro x y U Y Z hU hzero hresponse he hp hq t z
    have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
      have ho := liftProductionOrder_le_initial base D N R 0 n
      dsimp only [independentLiftPrimitiveTopOrder, k]
      omega
    exact hcross x.restrict y.restrict U Y Z hU hzero hresponse
      (he.monoOrder (4 * k + 5) horder) hp hq t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Joint degree induction preserves the positive response and equality of primitive and menu germs. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossDegreeProduction (d base D N R count qs : ℕ) (BG BV BE BP : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hBP : 1 ≤ BP) :
    ∀ n, 1 ≤ n → n ≤ N → ∃ C : ℝ, 1 ≤ C ∧
      ∃ Q : ∀ x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE BP,
      ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ out inp,
      IndependentScalarCoefficientProduction (2 + d) (liftProductionOrder base D N R 0 n) n
        x.data.primitive.a x.data.primitive.b x.data.primitive.U
        (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.data.primitive.M 0 out inp) C,
      (∀ x m hm α out inp δ, δ ∈ x.data.translations →
        IndependentSourceTranslationInvariant δ (Q x m hm α out inp).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        (∀ hh q hhh hq m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.productions hh q hhh hq m hm α v u).field
            (y.productions hh q hhh hq m hm α v u).field) →
        ∀ m hm α out inp t z, (Q x m hm α out inp).field t z Y = (Q y m hm α out inp).field t z Z := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnN
    by_cases hn1 : n = 1
    · subst n
      obtain ⟨C, hC, Q, hnat, hcross⟩ := independentFirstCrossResponseMenuProduction
        (ι := ι) d base D N R count qs (hnN.trans hND) hnN BG BV BE BP hBG hBV hBP
      refine ⟨C, hC, Q, hnat, ?_⟩
      intro x y U Y Z hU hzero hresponse he _hp
      exact hcross x y U Y Z hU hzero hresponse he
    · have hn2 : 2 ≤ n := by omega
      let X := IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE BP
      let J := {q : Fin n // 1 ≤ q.val}
      have hprior (q : J) := ih q.val.val q.val.isLt q.property (show q.val.val ≤ N by omega)
      choose C hC Qprior hNatPrior hCrossPrior using hprior
      let Bprior := independentFiniteStepBudget C
      have hBprior : 1 ≤ Bprior := independentFiniteStepBudget_one_le C (fun q => zero_le_one.trans (hC q))
      let B := BP + Bprior
      have hB : 1 ≤ B := hBP.trans (le_add_of_nonneg_right (zero_le_one.trans hBprior))
      have hBPB : BP ≤ B := le_add_of_nonneg_right (zero_le_one.trans hBprior)
      have hCB (q : J) : C q ≤ B :=
        (independentFiniteStepBudget_entry_le C (fun q => zero_le_one.trans (hC q)) q).trans
          (le_add_of_nonneg_left (zero_le_one.trans hBP))
      let menu := fun x : X =>
        (⟨x.data,
          (fun hh q hhh hq m hm α v u => (x.productions hh q hhh hq m hm α v u).enlargeBudget B hBPB
            (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg hh v u)),
          x.response, x.response_nonneg, x.response_small, x.drift_response,
          x.production_translation⟩ : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B)
      have earlier q (hq : 1 ≤ q) (hqn : q < n) l (hl : l ≤ q) (β : DerivativeWord2 l) v u :
          ∃ Q : ∀ x : X, IndependentScalarCoefficientProduction (2 + d)
            (4 * liftProductionOrder base D N R 0 n + 2 * D + 7) q
            x.data.primitive.a x.data.primitive.b x.data.primitive.U
            (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 q)
            (independentIntrinsicSlowProjection d) l β v u
            (x.response * finiteMatrixPower x.data.primitive.M 0 v u) B,
          (∀ x δ, δ ∈ x.data.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
          ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
            IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
            (∀ hh q hhh hq m hm α v u,
              IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
                (x.productions hh q hhh hq m hm α v u).field
                (y.productions hh q hhh hq m hm α v u).field) →
            ∀ t z, (Q x).field t z Y = (Q y).field t z Z := by
        let j : J := ⟨⟨q, hqn⟩, hq⟩
        have ho := liftProductionOrder_predecessor_room base D N R 0 n 0 q
          (Nat.zero_le R) hnN (by omega) (Or.inr ⟨rfl, hqn⟩)
        let Q := fun x : X => ((Qprior j x l hl β v u).monoOrder _ ho).enlargeBudget B (hCB j)
          (mul_nonneg x.response_nonneg
            (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 v u))
        refine ⟨Q, ?_, ?_⟩
        · intro x δ hδ
          exact hNatPrior j x l hl β v u δ hδ
        · intro x y U Y Z hU hzero hresponse he hp t z
          exact hCrossPrior j x y U Y Z hU hzero hresponse he hp l hl β v u t z
      choose P hPNat hPCross using earlier
      let datum := fun x : X =>
        (⟨menu x, (fun q hq hqn l hl β v u => P q hq hqn l hl β v u x),
          (fun δ hδ q hq hqn l hl β v u => hPNat q hq hqn l hl β v u x δ hδ)⟩ :
          IndependentPositiveNaturalStepDatum ι d base D N R count qs n BG BV BE B)
      let I := Σ m : Fin (n + 1), DerivativeWord2 m.val × ι × ι
      have hstep (i : I) := independentPositiveCrossResponseOrderProduction d base D N R count qs n i.1.val
        hn2 hnN (hnN.trans hND) (by have := i.1.isLt; omega) i.2.1 i.2.2.1 i.2.2.2
        BG BV BE B hBG hBV hBE hB
      choose A hA Qstep hNatStep hCrossStep using hstep
      let K := independentFiniteStepBudget A
      have hK : 1 ≤ K := independentFiniteStepBudget_one_le A (fun i => zero_le_one.trans (hA i))
      let Q := fun (x : X) m (hm : m ≤ n) (α : DerivativeWord2 m) out inp =>
        (Qstep (⟨⟨m, by omega⟩, α, out, inp⟩ : I) (datum x)).enlargeBudget K
          (independentFiniteStepBudget_entry_le A (fun i => zero_le_one.trans (hA i)) _)
          (mul_nonneg x.response_nonneg
            (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp))
      refine ⟨K, hK, Q, ?_, ?_⟩
      · intro x m hm α out inp δ hδ
        exact hNatStep _ (datum x) δ hδ
      · intro x y U Y Z hU hzero hresponse he hp m hm α out inp t z
        apply hCrossStep _ (datum x) (datum y) U Y Z hU hzero hresponse he hp ?_ t z
        intro q hq hqn l hl β v u τ V hV w
        let U' : Set (Vec 2) := (fun W => W + V) ⁻¹' U
        have hU' : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
        have hz' : (0 : Vec 2) ∈ U' := by simpa only [U', Set.mem_preimage, zero_add] using hV
        apply hPCross q hq hqn l hl β v u x y U'
          (independentIntrinsicSlowEmbedding d V + Y) (independentIntrinsicSlowEmbedding d V + Z)
          hU' hz' hresponse (he.recenter V) ?_ τ w
        intro hh q hhh hq m hm α v u
        exact (hp hh q hhh hq m hm α v u).recenter V

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite joint positive menu retains response-linear bounds and cross-family germ equality. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossFiniteProduction (d base D N R count qs : ℕ) (BG BV BE BP : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hBP : 1 ≤ BP) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ Q : ∀ x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE BP,
      ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ out inp,
      IndependentScalarCoefficientProduction (2 + d) base n
        x.data.primitive.a x.data.primitive.b x.data.primitive.U
        (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.data.primitive.M 0 out inp) C,
      (∀ x n hn hnN m hm α out inp δ, δ ∈ x.data.translations →
        IndependentSourceTranslationInvariant δ (Q x n hn hnN m hm α out inp).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        (∀ hh q hhh hq m hm α v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (x.productions hh q hhh hq m hm α v u).field
            (y.productions hh q hhh hq m hm α v u).field) →
        ∀ n hn hnN m hm α out inp t z, (Q x n hn hnN m hm α out inp).field t z Y = (Q y n hn hnN m hm α out inp).field t z Z := by
  classical
  let J := {n : Fin (N + 1) // 1 ≤ n.val}
  have hprod (n : J) := independentPositiveCrossDegreeProduction (ι := ι) d base D N R count qs
    BG BV BE BP hND hBG hBV hBE hBP n.val.val n.property (by have := n.val.isLt; omega)
  choose C hC Qcore hnat hcross using hprod
  let K := independentFiniteStepBudget C
  have hK : 1 ≤ K := independentFiniteStepBudget_one_le C (fun n => zero_le_one.trans (hC n))
  have ho n (hnN : n ≤ N) : base ≤ liftProductionOrder base D N R 0 n :=
    (Nat.le_succ base).trans
      (weakJointRecurrenceReserve_base (4 * (D + 4)) base (liftProductionRankMax N R)
        (ambientRecurrenceRank N 0 n) (by have := liftProductionRank_le N R 0 n (Nat.zero_le R) hnN; omega))
  let Q := fun (x : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE BP)
    n (hn : 1 ≤ n) (hnN : n ≤ N) m (hm : m ≤ n) (α : DerivativeWord2 m) out inp =>
      ((Qcore (⟨⟨n, by omega⟩, hn⟩ : J) x m hm α out inp).monoOrder base (ho n hnN)).enlargeBudget K
        (independentFiniteStepBudget_entry_le C (fun n => zero_le_one.trans (hC n)) _)
        (mul_nonneg x.response_nonneg
          (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp))
  refine ⟨K, hK, Q, ?_, ?_⟩
  · intro x n hn hnN m hm α out inp δ hδ
    exact hnat _ x m hm α out inp δ hδ
  · intro x y U Y Z hU hzero hresponse he hp n hn hnN m hm α out inp t z
    exact hcross _ x y U Y Z hU hzero hresponse he hp m hm α out inp t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite data-independent price covers every order in the weak physical menu. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def weakPhysicalPiolaMenuPrice (Ks K N : ℕ) (C B : ℝ) : ℝ :=
  independentFiniteStepBudget (fun j : Fin (K + 1) × Fin (K + 1) =>
    weakPhysicalPiolaPrice Ks K N j.1.val j.2.val C B)

theorem weakPhysicalPiolaMenuPrice_one_le (Ks K N : ℕ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    1 ≤ weakPhysicalPiolaMenuPrice Ks K N C B :=
  independentFiniteStepBudget_one_le _ (fun _ => weakPhysicalPiolaPrice_nonneg _ _ _ _ _ _ _ hC hB)

theorem weakPhysicalPiolaPrice_le_menu (Ks K N n d : ℕ) (C B : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hn : n ≤ K) (hd : d ≤ K) :
    weakPhysicalPiolaPrice Ks K N n d C B ≤ weakPhysicalPiolaMenuPrice Ks K N C B :=
  independentFiniteStepBudget_entry_le
    (fun j : Fin (K + 1) × Fin (K + 1) => weakPhysicalPiolaPrice Ks K N j.1.val j.2.val C B)
    (fun _ => weakPhysicalPiolaPrice_nonneg _ _ _ _ _ _ _ hC hB)
    (⟨n, Nat.lt_succ_of_le hn⟩, ⟨d, Nat.lt_succ_of_le hd⟩)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produce the full coefficient menu before forming inherited mean fluxes. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentInheritedCrossMeanUniformProduction (d H D N R count qs hh n m : ℕ)
    (α : DerivativeWord2 m) (lam : ℝ) (hND : N ≤ D) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (BG BV BE : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ P : ∀ x : IndependentLiftNaturalPrimitiveDatum ι d
      (independentLiftPrimitiveTopOrder (H + D + 2) D N R) D N R count qs BG BV BE,
      IndependentLiftMenuProductions x.primitive (H + D + 2) B,
      (∀ x,
        (∀ δ ∈ x.translations, ∀ p q l β v u,
          IndependentSourceTranslationInvariant δ
            (fun t z Y => independentFiniteLiftFields x.primitive (P x) p q l β t z Y v u)) ∧
        ∀ out inp : ι, ∃ Q : IndependentParameterSourceReserve H (fun t z Y k =>
          independentMeanFluxCoefficientSource x.primitive.edge x.primitive.edgeField
            (independentIntrinsicSlowEmbedding d) 1 x.primitive.G x.primitive.v
            (independentFiniteLiftFields x.primitive (P x)) hh n m α lam out inp k t z Y),
          ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower x.primitive.M hh out inp *
            (2 * independentMeanFluxCoefficientCost (2 + d) H D n m count α lam 1 BG BV BE B)) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U →
        IndependentLiftPrimitiveSlowSliceEq x.primitive y.primitive U Y Z →
        ∀ p q l β v u,
          IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
            (fun t z W => independentFiniteLiftFields x.primitive (P x) p q l β t z W v u)
            (fun t z W => independentFiniteLiftFields y.primitive (P y) p q l β t z W v u) := by
  obtain ⟨B, hB, P, hPNat, hPCross⟩ := independentLiftCrossNaturalFiniteProduction (ι := ι)
    d (H + D + 2) D N R count qs BG BV BE hND hBG hBV hBE
  refine ⟨B, hB, P, ?_, ?_⟩
  · intro x
    let S := x.primitive
    refine ⟨?_, ?_⟩
    · intro δ hδ p q l β v u
      exact independentFiniteLiftFields_translation_invariant S (P x) δ
        (fun p q hp hq l hl β v u => hPNat x p q hp hq l hl β v u δ hδ) p q l β v u
    · intro out inp
      have hroom : H ≤ independentLiftPrimitiveTopOrder (H + D + 2) D N R :=
        (Nat.le_add_right H (D + 2)).trans
          (independentLiftPrimitiveTopOrder_base_le (H + D + 2) D N R)
      choose Qc hc using fun p q l β v u => independentFiniteLiftFields_reserve S (P x) hB p q l β v u
      exact independentMeanFluxVector_uniform_production H S.edge S.edgeField
        (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
        1 S.G S.v (independentFiniteLiftFields S (P x)) hh n hn hhpos out inp m α lam
        (fun i j => (S.metric_entries i j).restrictOrder H (by omega))
        (fun i => (S.drift_entries i).restrictOrder H (by omega))
        (fun p q _ l β v u => Qc p q l.val β v u)
        (fun v u e γ hγ β => (S.edges v u e γ hγ β).restrictOrder H (by omega))
        S.M S.matrix_nonneg count BG BV BE B hBG hBV hBE (zero_le_one.trans hB)
        (fun i j r hr => S.metric_entries_bound i j r (by omega))
        (fun i r hr => S.drift_bound i r (by omega))
        (fun p q _ l β v u r hr => hc p q l.val β v u r hr)
        (fun v u e γ hγ β r hr => S.edge_bound v u e γ hγ β r (by omega))
        S.edge_maps S.edge_lengths
  · intro x y U Y Z hU hzero he p q l β v u
    apply independentFiniteLiftFields_slow_slice_congr x.primitive y.primitive (P x) (P y) Y Z
    intro hh n hhh hn m hm α v u t V hV z
    let U' : Set (Vec 2) := (fun W => W + V) ⁻¹' U
    have hU' : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
    have hz' : (0 : Vec 2) ∈ U' := by simpa only [U', Set.mem_preimage, zero_add] using hV
    exact hPCross x y U'
      (independentIntrinsicSlowEmbedding d V + Y) (independentIntrinsicSlowEmbedding d V + Z)
      hU' hz' (he.recenter V) hh n hhh hn m hm α v u t z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine primitive inverses produce the response-linear menu jointly across all primitive inputs. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossUniformProduction (d base D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q : ∀ x : IndependentPositiveNaturalPrimitiveDatum ι d base D N R count qs BG BV BE,
      ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ out inp,
      IndependentScalarCoefficientProduction (2 + d) base n
        x.data.primitive.a x.data.primitive.b x.data.primitive.U
        (fun Y => x.data.primitive.Cc (independentStoredParameterProjection d Y) 0 n)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.data.primitive.M 0 out inp) C,
      (∀ x n hn hnN m hm α out inp δ, δ ∈ x.data.translations →
        IndependentSourceTranslationInvariant δ (Q x n hn hnN m hm α out inp).field) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ n hn hnN m hm α out inp t z,
          (Q x n hn hnN m hm α out inp).field t z Y = (Q y n hn hnN m hm α out inp).field t z Z := by
  let menu := independentLiftPrimitiveTopOrder base D N R + 2 * D + 2
  obtain ⟨BP, hBP, P, hPNat, hPCross⟩ := independentLiftCrossNaturalFiniteProduction (ι := ι)
    d menu D N R count qs BG BV BE hND hBG hBV hBE
  obtain ⟨C, hC, Qcore, hnat, hcross⟩ := independentPositiveCrossFiniteProduction (ι := ι)
    d base D N R count qs BG BV BE BP hND hBG hBV hBE hBP
  let datum := fun x : IndependentPositiveNaturalPrimitiveDatum ι d base D N R count qs BG BV BE =>
    (⟨⟨x.data.primitive.monoOrder (independentLiftPrimitiveTopOrder base D N R)
        (independentPositivePrimitiveTopOrder_room base D N R),
        x.data.fastOrder, x.data.translations, x.data.metric_translation, x.data.edge_translation⟩,
      P x.data, x.response, x.response_nonneg, x.response_small, x.drift_response,
      (fun δ hδ hh q hhh hq m hm α v u => hPNat x.data hh q hhh hq m hm α v u δ hδ)⟩ :
      IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE BP)
  let Q := fun x n hn hnN m hm α out inp => Qcore (datum x) n hn hnN m hm α out inp
  refine ⟨C, hC, Q, ?_, ?_⟩
  · intro x n hn hnN m hm α out inp δ hδ
    exact hnat (datum x) n hn hnN m hm α out inp δ hδ
  · intro x y U Y Z hU hzero hresponse he n hn hnN m hm α out inp t z
    apply hcross (datum x) (datum y) U Y Z hU hzero hresponse
      (he.monoOrder _ (independentPositivePrimitiveTopOrder_room base D N R)) ?_ n hn hnN m hm α out inp t z
    intro hh q hhh hq l hl β v u τ V hV w
    let U' : Set (Vec 2) := (fun W => W + V) ⁻¹' U
    have hU' : IsOpen U' := hU.preimage (continuous_id.add continuous_const)
    have hz' : (0 : Vec 2) ∈ U' := by simpa only [U', Set.mem_preimage, zero_add] using hV
    exact hPCross x.data y.data U'
      (independentIntrinsicSlowEmbedding d V + Y) (independentIntrinsicSlowEmbedding d V + Z)
      hU' hz' (he.recenter V) hh q hhh hq l hl β v u τ w

end AVRegularity.EntryWeakProofs
end
end

section
/-! The jointly selected positive coefficients give coherent Eddy means with squared response. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentPositiveCrossEddyProduction (d H D N R count qs : ℕ) (BG BV BE : ℝ)
    (hND : N ≤ D) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ f : ∀ _x : IndependentPositiveNaturalPrimitiveDatum ι d H D N R count qs BG BV BE,
      ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → DerivativeWord2 m → ι → ι → Fin 2 →
      ℝ → Vec 2 → Vec (2 + d) → ℝ,
      (∀ x n hn hnN m hm α out inp k,
        ∃ Q : IndependentParameterSourceReserve H (f x n hn hnN m hm α out inp k),
          (∀ r ≤ H, Q.budget r ≤ (x.response ^ 2 * finiteMatrixPower x.data.primitive.M 0 out inp) * C) ∧
          (∀ t ∈ Icc x.data.primitive.a x.data.primitive.b, ∀ Y ∈ x.data.primitive.U, ∀ z,
            f x n hn hnN m hm α out inp k t z Y = fieldCellMean (fun w =>
              x.data.primitive.v t w k • x.data.primitive.Cc (independentStoredParameterProjection d Y)
                0 n m α t (independentIntrinsicSlowProjection d Y) w out inp 1)) ∧
          (∀ δ ∈ x.data.translations, IndependentSourceTranslationInvariant δ (f x n hn hnN m hm α out inp k))) ∧
      ∀ x y U Y Z, IsOpen U → (0 : Vec 2) ∈ U → x.response = y.response →
        IndependentLiftPrimitiveSlowSliceEq x.data.primitive y.data.primitive U Y Z →
        ∀ n hn hnN m hm α out inp k t z,
          f x n hn hnN m hm α out inp k t z Y = f y n hn hnN m hm α out inp k t z Z := by
  obtain ⟨CP, hCP, P, hnat, hcross⟩ := independentPositiveCrossUniformProduction (ι := ι)
    d H D N R count qs BG BV BE hND hBG hBV hBE
  let C := (((2 + d : ℕ) : ℝ) + 1) ^ H * ((H + 1 : ℕ) *
    (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * BV * CP))
  have hCP0 : 0 ≤ CP := zero_le_one.trans hCP
  let X := IndependentPositiveNaturalPrimitiveDatum ι d H D N R count qs BG BV BE
  let f := fun (x : X) n hn hnN m hm α out inp (k : Fin 2) t (_ : Vec 2) Y =>
    fieldCellMean (fun w => x.data.primitive.v t w k • (P x n hn hnN m hm α out inp).field t w Y)
  refine ⟨C, by dsimp only [C]; positivity, f, ?_, ?_⟩
  · intro x n hn hnN m hm α out inp k
    have hroom : H ≤ independentPositivePrimitiveTopOrder H D N R + D :=
      ((independentLiftPrimitiveTopOrder_base_le H D N R).trans
        (independentPositivePrimitiveTopOrder_room H D N R)).trans (Nat.le_add_right _ _)
    let Qv := (x.data.primitive.drift_entries k).restrictOrder H hroom
    have hv r (hr : r ≤ H) : Qv.budget r ≤ x.response * BV :=
      x.drift_response k r (hr.trans (independentLiftPrimitiveTopOrder_base_le H D N R))
    obtain ⟨Q, hQ⟩ := independentDriftMean_squared_response_production
      (fun t z (_ : Vec (2 + d)) => x.data.primitive.v t z k)
      (P x n hn hnN m hm α out inp).field Qv (P x n hn hnN m hm α out inp).reserve
      x.response (finiteMatrixPower x.data.primitive.M 0 out inp) BV CP x.response_nonneg
      (finiteMatrixPower_nonneg x.data.primitive.M x.data.primitive.matrix_nonneg 0 out inp)
      hBV hCP0 hv (P x n hn hnN m hm α out inp).bound
    refine ⟨Q, hQ, ?_, ?_⟩
    · intro t ht Y hY z
      apply congrArg fieldCellMean
      funext w
      rw [(P x n hn hnN m hm α out inp).copy t ht Y hY w]
    · intro δ hδ
      exact (IndependentSourceTranslationInvariant.smul
        (fun _ _ _ => rfl) (hnat x n hn hnN m hm α out inp δ hδ)).cellMean
  · intro x y U Y Z hU hzero hresponse he n hn hnN m hm α out inp k t z
    apply congrArg fieldCellMean
    funext w
    rw [he.drift, hcross x y U Y Z hU hzero hresponse he n hn hnN m hm α out inp t w]

end AVRegularity.EntryWeakProofs
end
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFiniteLiftFieldReserve
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

section
section
/-! The reconstructed initial exponential test is the exact constant diagonal. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentInitialScalarTest
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ)
    (v u : ι) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) :
    independentScalarLiftTestSource 0 (independentFiniteLiftFields S P 0 0) A v u t z Y =
      if v = u then 1 else 0 := by
  change normalizedLiftTestField
    (independentScalarCoefficientLift (independentFiniteLiftFields S P 0 0) Y) 0 A u v 1 t 0 z = _
  rw [normalized_scalar_lift_test_polynomial]
  by_cases hvu : v = u <;>
    simp [independentScalarCoefficientLift, independentFiniteLiftFields, hvu]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The finite menu reconstruction retains the cross-family equality of its productions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ} {V : Set (Vec 2)}

theorem independentFiniteLiftFields_slow_slice_congr
    (S T : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Q : IndependentLiftMenuProductions T base B)
    (Y Z : Vec (2 + d))
    (he : ∀ hh n hhh hn m hm α v u,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) V Y Z
        (P hh n hhh hn m hm α v u).field (Q hh n hhh hn m hm α v u).field)
    (hh n m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) V Y Z
      (fun t z W => independentFiniteLiftFields S P hh n m α t z W v u)
      (fun t z W => independentFiniteLiftFields T Q hh n m α t z W v u) := by
  intro t X hX z
  dsimp only [independentFiniteLiftFields]
  by_cases hhh : hh ≤ R
  · simp only [dite_eq_left hhh]
    by_cases hn : n ≤ N
    · simp only [dite_eq_left hn]
      by_cases hn0 : n = 0
      · simp only [ite_eq_left hn0]
      · simp only [ite_eq_right hn0, independentCoefficientProductionFields]
        by_cases hm : m ≤ n
        · simp only [dite_eq_left hm]
          exact he hh n hhh hn m hm (canonicalDerivativeWord α) v u t X hX z
        · simp only [dite_eq_right hm]
    · simp only [dite_eq_right hn]
  · simp only [dite_eq_right hhh]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full independent finite fields copy the exact original native coefficients on their open carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ}

def independentFiniteNativeCoefficients (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d)) (hh n : ℕ) : LiftCoeff ι (fun _ => ℝ) :=
  independentScalarCoefficientSlice (independentFiniteLiftFields S P hh n)
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)

theorem independentFiniteNativeCoefficients_copy_positive
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d))
    (hh n m : ℕ) (hhh : hh ≤ R) (hn : n ≤ N) (hn0 : n ≠ 0) (hm : m ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc S.a S.b) (X z : Vec 2)
    (hX : independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y ∈ S.U) (v u : ι) :
    independentFiniteNativeCoefficients S P Y hh n m α t X z v u =
      S.Cc (independentStoredParameterProjection d Y) hh n m α t X z v u := by
  have he := independentFiniteLiftFields_copy_positive S P hh n m hhh hn hn0 hm α t ht
    (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) hX z v u
  rw [independentStoredParameterProjection_slice, independentIntrinsicSlowProjection_slice] at he
  apply ContinuousLinearMap.ext
  intro ξ
  have hr := (S.Cc (independentStoredParameterProjection d Y) hh n m α t X z v u).map_smul ξ 1
  simp only [smul_eq_mul, mul_one] at hr
  simp only [independentFiniteNativeCoefficients, independentScalarCoefficientSlice, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [he, hr]
  exact mul_comm _ _

theorem independentFiniteNativeCoefficients_copy_zero
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d)) (hh : ℕ) (hhh : hh ≤ R)
    (α : DerivativeWord2 0) (t : ℝ) (ht : t ∈ Icc S.a S.b) (X z : Vec 2) (v u : ι) :
    independentFiniteNativeCoefficients S P Y hh 0 0 α t X z v u =
      S.Cc (independentStoredParameterProjection d Y) hh 0 0 α t X z v u := by
  apply ContinuousLinearMap.ext
  intro ξ
  by_cases hh0 : hh = 0
  · subst hh
    have he := congrFun (S.initial (independentStoredParameterProjection d Y)
      (fun _ => Pi.single u ξ) contDiff_const t ht X z) v
    rw [liftApply_constant_single 0 (S.Cc (independentStoredParameterProjection d Y) 0 0) α t X z v u ξ] at he
    simp only [independentFiniteNativeCoefficients, independentScalarCoefficientSlice, independentFiniteLiftFields,
      dite_eq_left (Nat.zero_le R), dite_eq_left (Nat.zero_le N), and_self, ite_true,
      smul_apply, ContinuousLinearMap.id_apply]
    rw [he]
    by_cases hvu : v = u
    · simp only [hvu, ite_true, one_smul, Pi.single_eq_same]
    · simp only [ite_eq_right hvu, zero_smul, Pi.single_eq_of_ne hvu]
  · rw [S.positive_zero_degree _ hh (by omega) hhh 0 α t X z v u]
    simp only [independentFiniteNativeCoefficients, independentScalarCoefficientSlice,
      independentFiniteLiftFields_positive_zero_degree S P hh hh0, zero_smul, zero_apply]

theorem independentFiniteNativeCoefficients_copy
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d))
    (hh n m : ℕ) (hhh : hh ≤ R) (hm : m ≤ n) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (X z : Vec 2)
    (hX : independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y ∈ S.U)
    (v u : ι) :
    independentFiniteNativeCoefficients S P Y hh n m α t X z v u =
      S.Cc (independentStoredParameterProjection d Y) hh n m α t X z v u := by
  by_cases hn : n ≤ N
  · by_cases hn0 : n = 0
    · subst n
      have hm0 : m = 0 := by omega
      subst m
      exact independentFiniteNativeCoefficients_copy_zero S P Y hh hhh α t ht X z v u
    · exact independentFiniteNativeCoefficients_copy_positive S P Y hh n m hhh hn hn0 hm
        α t ht X z hX v u
  · rw [S.above_degree _ hh hhh n (by omega) m α t X z v u]
    simp only [independentFiniteNativeCoefficients, independentScalarCoefficientSlice,
      independentFiniteLiftFields_above_degree S P hh n m (by omega), zero_smul]

end AVRegularity.EntryWeakProofs
end
end

section
/-! A full native menu retains all genuinely produced positive diagonal predecessors at once. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n : ℕ} {BG BV BE B θ : ℝ}

def independentFinitePositivePredecessors
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ : θ ≤ 1) (hB : 0 ≤ B) : IndependentLiftMenuProductions S base B := by
  intro hh q hhh hqN m hm α v u
  by_cases he : hh = 0 ∧ 1 ≤ q ∧ q < n
  · obtain ⟨rfl, hq, hqn⟩ := he
    exact (Q q hq hqn m hm α v u).forgetResponse hθ
      (finiteMatrixPower_nonneg _ S.matrix_nonneg _ _ _) hB
  · exact P hh q hhh hqN m hm α v u

theorem independentFinitePositivePredecessors_field
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ : θ ≤ 1) (hB : 0 ≤ B) (q : ℕ) (hq : 1 ≤ q) (hqn : q < n) (hqN : q ≤ N)
    (m : ℕ) (hm : m ≤ q) (α : DerivativeWord2 m) (v u : ι) :
    (fun t z Y => independentFiniteLiftFields S
      (independentFinitePositivePredecessors S P Q hθ hB) 0 q m α t z Y v u) =
      (Q q hq hqn m hm (canonicalDerivativeWord α) v u).field := by
  funext t z Y
  simp only [independentFiniteLiftFields, dite_eq_left (Nat.zero_le R), dite_eq_left hqN,
    ite_eq_right (show q ≠ 0 by omega), independentCoefficientProductionFields, dite_eq_left hm,
    independentFinitePositivePredecessors,
    dite_eq_left (show 0 = 0 ∧ 1 ≤ q ∧ q < n from ⟨rfl, hq, hqn⟩),
    IndependentScalarCoefficientProduction.forgetResponse]

theorem independentFinitePositivePredecessors_reserve
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ : θ ≤ 1) (hB : 0 ≤ B) (q : ℕ) (hq : 1 ≤ q) (hqn : q < n) (hqN : q ≤ N)
    (m : ℕ) (hm : m ≤ q) (α : DerivativeWord2 m) (v u : ι) :
    ∃ Qr : IndependentParameterSourceReserve base
      (fun t z Y => independentFiniteLiftFields S
        (independentFinitePositivePredecessors S P Q hθ hB) 0 q m α t z Y v u),
      ∀ r ≤ base, Qr.budget r ≤ (θ * finiteMatrixPower S.M 0 v u) * B := by
  have he := independentFinitePositivePredecessors_field S P Q hθ hB q hq hqn hqN m hm α v u
  refine ⟨(Q q hq hqn m hm (canonicalDerivativeWord α) v u).reserve.congrSource he.symm, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  exact (Q q hq hqn m hm (canonicalDerivativeWord α) v u).bound r hr

end AVRegularity.EntryWeakProofs
end
end

section
/-! Positive-response production starts from primitive data and a genuinely produced native menu. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

structure IndependentPositiveNaturalMenuDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d base D N R count qs : ℕ) (BG BV BE B : ℝ) where
  data : IndependentLiftNaturalPrimitiveDatum ι d
    (independentLiftPrimitiveTopOrder base D N R) D N R count qs BG BV BE
  productions : IndependentLiftMenuProductions data.primitive
    (independentLiftPrimitiveTopOrder base D N R + 2 * D + 2) B
  response : ℝ
  response_nonneg : 0 ≤ response
  response_small : response ≤ 1
  drift_response : ∀ i r, r ≤ independentLiftPrimitiveTopOrder base D N R →
    (data.primitive.drift_entries i).budget r ≤ response * BV
  production_translation : ∀ δ ∈ data.translations, ∀ hh n hhh hn m hm α v u,
    IndependentSourceTranslationInvariant δ (productions hh n hhh hn m hm α v u).field

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reconstructed full finite fields retain the actual native inverse on its open carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count hh n : ℕ} {BG BV BE B : ℝ}
  (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
  (P : IndependentLiftMenuProductions S base B)

theorem independentFiniteLiftSource_actual_inverse
    (hB : 1 ≤ B) (hbase : H + 2 * D + 2 ≤ base)
    (hH : 1 ≤ H) (hD : 1 ≤ D) (hhh : hh ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D)
    (A : Vec 2 →L[ℝ] ℝ) (inp : ι) (Y : Vec (2 + d)) (hY : Y ∈ S.U) :
    IsCellFieldInverse (S.molecular Y).G (S.molecular Y).v S.sZ S.a S.b 0
      (fun t z => independentTimeWindowSource (Ioc S.a S.b)
        (fun t z Y out => independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
          A 1 S.G S.v (independentFiniteLiftFields S P) hh n out inp t z Y) t z Y)
      (fun t z => (Real.exp (A (independentIntrinsicSlowProjection d Y)))⁻¹ •
        liftApply n (S.Cc (independentStoredParameterProjection d Y) hh n)
          (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) t
          (independentIntrinsicSlowProjection d Y) z) := by
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y), S.v,
      independentConstituentEdgeSlice S.edge S.edgeField S.edges (independentIntrinsicSlowEmbedding d)
        (independentIntrinsicSliceOffset d Y)⟩
  let Dc := fun p q => independentScalarCoefficientSlice (independentFiniteLiftFields S P p q)
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)
  let Cc := S.Cc (independentStoredParameterProjection d Y)
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)
  let U := independentIntrinsicSliceCarrier d S.U Y
  have hc := S.inverse hh hhh n hn hnN (fun X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ))
    ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const) Y hY
  have hforce t (_ht : t ∈ Icc S.a S.b) z :
      (fun out => independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
          A 1 S.G S.v (independentFiniteLiftFields S P) hh n out inp t z Y) =
      normalizedLiftCellSource Q Dc f hh n A t z (independentIntrinsicSlowProjection d Y) := by
    funext out
    have he := independent_lift_coefficient_cell_source_slice H hH S.edge hD S.edgeField
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
      (independentIntrinsicSliceOffset d Y) A 1 S.G S.v (independentFiniteLiftFields S P)
      hh n hn hnD out inp S.metric_entries S.drift_entries
      (fun p q _hpq m α v u =>
        ((independentFiniteLiftFields_reserve S P hB p q m α v u).choose).restrictOrder
          (H + 2 * D + 2) hbase) S.edges t z (independentIntrinsicSlowProjection d Y)
    rw [independentIntrinsicSliceOffset_base] at he
    exact he
  have hcopy : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q, ∀ α,
      ∀ t ∈ Icc S.a S.b, ∀ X ∈ U, ∀ z v u,
      Cc p q m α t X z v u = Dc p q m α t X z v u := by
    intro p q hpq m hm α t ht X hX z v u
    have hpR : p ≤ R := by rcases hpq with h | ⟨rfl, _⟩ <;> omega
    exact (independentFiniteNativeCoefficients_copy S P Y p q m hpR hm α t ht X z hX v u).symm
  rw [S.molecular_metric, S.molecular_drift]
  have hmat : (fun t => Matrix.of (S.G t Y)) = (fun t => S.G t Y) := by
    funext t i j
    rfl
  have hi := independent_native_inverse_transfer Q Cc Dc f hh n S.sZ hn S.a S.b A U
    (independentIntrinsicSliceCarrier_isOpen d S.U S.open_carrier Y)
    (independentIntrinsicSlowProjection d Y) (independentIntrinsicSliceCarrier_base d S.U Y hY) Y
    (fun t z Y out => independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
          A 1 S.G S.v (independentFiniteLiftFields S P) hh n out inp t z Y) hcopy hforce
    (by simpa only [Q, independentIntrinsicSliceOffset_base, hmat] using hc)
  simpa only [Q, independentIntrinsicSliceOffset_base, hmat] using hi

theorem independentFiniteLiftSource_mean_zero
    (hB : 1 ≤ B) (hbase : H + 2 * D + 2 ≤ base)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) (hn : 1 ≤ n) (hnD : n ≤ D)
    (t : ℝ) (Y : Vec (2 + d)) :
    fieldCellMean (fun z => independentLiftCoefficientCellSource S.edge S.edgeField
      (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
      (independentFiniteLiftFields S P) hh n out inp t z Y) = 0 := by
  exact independent_lift_cell_source_from_centered_earlier_coefficients_mean_zero H S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d) A 1 S.G S.v
    (independentFiniteLiftFields S P) hh n hn hnD out inp S.metric_entries S.drift_entries
    (fun p q _hpq m α v u =>
      ((independentFiniteLiftFields_reserve S P hB p q m α v u).choose).restrictOrder
        (H + 2 * D + 2) hbase) S.edges
    (fun p q _hpq hq m α v u t Y =>
      independentFiniteLiftFields_mean_zero S P p q m hq α t Y v u) t Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native slicing preserves coefficient symmetry without unfolding the finite production
construction. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteNativeCoefficients_perm
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d))
    (hh n m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    independentFiniteNativeCoefficients S P Y hh n m (α ∘ σ) =
      independentFiniteNativeCoefficients S P Y hh n m α := by
  exact congrArg (fun f : ℝ → Vec 2 → Vec (2 + d) → ι → ι → ℝ =>
    fun t X z v u => f t z
      (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) v u •
        ContinuousLinearMap.id ℝ ℝ) (independentFiniteLiftFields_perm S P hh n m α σ)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal first-degree forcing of the reconstructed independent menu. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFirstLiftASource
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ)
    (v u : ι) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) :
    independentLiftCoefficientASource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
      A 1 S.G S.v (independentFiniteLiftFields S P) 0 1 v u t z Y =
      ∑ i : Fin 2, S.v t z i * (A (basisVec i) * (if v = u then 1 else 0)) := by
  have hf : (fun t z Y => independentScalarLiftTestSource 0
      (independentFiniteLiftFields S P 0 0) A v u t z Y) =
      (fun (_ : ℝ) (_ : Vec 2) (_ : Vec (2 + d)) => if v = u then 1 else 0) := by
    funext t z Y
    exact independentInitialScalarTest S P A v u t z Y
  simp only [independentLiftCoefficientASource, independentLiftASource,
    Nat.reduceSub, Nat.reduceLeDiff, ite_false, ite_true, add_zero, sub_zero]
  rw [hf]
  have hb := independentNormalizedCellB1Source_const (independentIntrinsicSlowEmbedding d) A 1
    (fun t Y i j => S.G t Y i j) S.v (if v = u then (1 : ℝ) else 0) t z Y
  simpa only [Real.sqrt_one, one_mul, smul_eq_mul] using hb

theorem independentFirstLiftCellSource
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ)
    (v u : ι) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) :
    independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
      A 1 S.G S.v (independentFiniteLiftFields S P) 0 1 v u t z Y =
      -((∑ i : Fin 2, S.v t z i * (A (basisVec i) * (if v = u then 1 else 0))) -
        fieldCellMean (fun w => ∑ i : Fin 2,
          S.v t w i * (A (basisVec i) * (if v = u then 1 else 0)))) := by
  have hIcc : Finset.Icc 1 (1 - 2 : ℕ) = ∅ := by decide
  simp only [independentLiftCoefficientCellSource, independentCenteredRecurrenceSource,
    hIcc, Finset.sum_empty, add_zero]
  simp only [independentFirstLiftASource]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual finite exponential tests inherit the response-weighted full-family predecessor reserves. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositivePredecessorTest_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ : θ ≤ 1) (hB : 0 ≤ B) (hK : K ≤ base)
    (q : ℕ) (hq : 1 ≤ q) (hqn : q < n) (hqN : q ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    ∃ Qt : IndependentParameterSourceReserve K
      (independentScalarLiftTestSource q
        (independentFiniteLiftFields S (independentFinitePositivePredecessors S P Q hθ hB) 0 q) A v u),
      ∀ r ≤ K, Qt.budget r ≤ (θ * finiteMatrixPower S.M 0 v u) * (finiteLiftSymbolBudget q A * B) := by
  have hprod (m : Fin (q + 1)) (α : DerivativeWord2 m.val) :=
    independentFinitePositivePredecessors_reserve S P Q hθ hB q hq hqn hqN
      m.val (by have := m.isLt; omega) α v u
  choose Qc hQc using hprod
  let Qc' := fun m α => (Qc m α).restrictOrder K hK
  refine ⟨independentScalarLiftTestSourceReserve K q _ A v u Qc', ?_⟩
  intro r hr
  apply independentScalarLiftTestSourceReserve_uniform_budget K q _ A v u Qc'
    (θ * finiteMatrixPower S.M 0 v u) B _ r hr
  intro m α s hs
  exact hQc m α s (hs.trans hK)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Replacing the positive predecessor menu retains every already-produced parameter translation. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n : ℕ} {BG BV BE B θ : ℝ}

theorem independentFinitePositivePredecessors_translation_invariant
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ : θ ≤ 1) (hB : 0 ≤ B) (δ : Vec (2 + d))
    (hP : ∀ hh q hhh hqN m hm α v u,
      IndependentSourceTranslationInvariant δ (P hh q hhh hqN m hm α v u).field)
    (hQ : ∀ q hq hqn m hm α v u,
      IndependentSourceTranslationInvariant δ (Q q hq hqn m hm α v u).field)
    (hh q : ℕ) (hhh : hh ≤ R) (hqN : q ≤ N) (m : ℕ) (hm : m ≤ q)
    (α : DerivativeWord2 m) (v u : ι) :
    IndependentSourceTranslationInvariant δ
      (independentFinitePositivePredecessors S P Q hθ hB hh q hhh hqN m hm α v u).field := by
  dsimp only [independentFinitePositivePredecessors]
  split
  · rename_i he
    obtain ⟨rfl, hq, hqn⟩ := he
    exact hQ q hq hqn m hm α v u
  · exact hP hh q hhh hqN m hm α v u

end AVRegularity.EntryWeakProofs
end
end

section
/-! A positive diagonal inverse step consumes only primitive data and genuinely produced predecessor
productions. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

structure IndependentPositiveResponseDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d k D N R count n qs : ℕ) (BG BV BE B : ℝ) where
  primitive : IndependentLiftPrimitiveData ι d (4 * k + 5) D N R count BG BV BE
  productions : IndependentLiftMenuProductions primitive (4 * k + 5 + 2 * D + 2) B
  fastOrder : primitive.sZ = qs
  response : ℝ
  response_nonneg : 0 ≤ response
  response_small : response ≤ 1
  earlier : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) (4 * k + 5 + 2 * D + 2) q
      primitive.a primitive.b primitive.U
      (fun Y => primitive.Cc (independentStoredParameterProjection d Y) 0 q)
      (independentIntrinsicSlowProjection d) m α v u (response * finiteMatrixPower primitive.M 0 v u) B
  translations : Set (Vec (2 + d))
  metric_translation : ∀ δ ∈ translations, ∀ t Y, primitive.G t (Y + δ) = primitive.G t Y
  edge_translation : ∀ δ ∈ translations, ∀ v u e γ, γ ∈ primitive.edge v u e → ∀ α,
    IndependentSourceTranslationInvariant δ (primitive.edgeField v u e γ α)
  production_translation : ∀ δ ∈ translations, ∀ hh q hhh hqN m hm α v u,
    IndependentSourceTranslationInvariant δ (productions hh q hhh hqN m hm α v u).field
  earlier_translation : ∀ δ ∈ translations, ∀ q hq hqn m hm α v u,
    IndependentSourceTranslationInvariant δ (earlier q hq hqn m hm α v u).field

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Genuine first inverse forcing with its response-linear full-family jet price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count K : ℕ} {BG BV BE B : ℝ}

theorem independentFirstLiftSourceReserve_exists
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qv : ∀ i, IndependentParameterSourceReserve K
      (fun t z (_ : Vec (2 + d)) => S.v t z i))
    (θ C : ℝ) (hQ : ∀ i r, r ≤ K → (Qv i).budget r ≤ θ * C) :
    ∃ Q : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S P) 0 1 v u),
      ∀ r ≤ K, Q.budget r ≤ θ *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
          (C * ∑ i : Fin 2, |A (basisVec i) * (if v = u then 1 else 0)|)) := by
  let c : ℝ := if v = u then 1 else 0
  let Q := independentFirstDriftReserve K A S.v c Qv
  have hQB r (hr : r ≤ K) : Q.budget r ≤ θ *
      (C * ∑ i : Fin 2, |A (basisVec i) * c|) :=
    independentFirstDriftReserve_budget K A S.v c θ C Qv hQ r hr
  have he : (fun t z Y => (-ContinuousLinearMap.id ℝ ℝ)
      ((∑ i : Fin 2, ((A (basisVec i) * c) • ContinuousLinearMap.id ℝ ℝ) (S.v t z i)) -
        fieldCellMean (fun w => ∑ i : Fin 2,
          ((A (basisVec i) * c) • ContinuousLinearMap.id ℝ ℝ) (S.v t w i)))) =
      independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S P) 0 1 v u := by
    funext t z Y
    rw [independentFirstLiftCellSource]
    simp only [neg_apply, ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul, c]
    simp only [mul_comm (A (basisVec _) * (if v = u then (1 : ℝ) else 0))]
  refine ⟨(Q.center.map (-ContinuousLinearMap.id ℝ ℝ)).congrSource he, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change ‖-ContinuousLinearMap.id ℝ ℝ‖ * Q.center.budget r ≤ _
  rw [norm_neg, ContinuousLinearMap.norm_id, one_mul]
  simpa only [c] using
    Q.center_uniform_budget θ (C * ∑ i : Fin 2, |A (basisVec i) * c|) hQB r hr

theorem independentFirstLiftSourceReserve_matrix_response
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Qv : ∀ i, IndependentParameterSourceReserve K
      (fun t z (_ : Vec (2 + d)) => S.v t z i))
    (θ C : ℝ) (hQ : ∀ i r, r ≤ K → (Qv i).budget r ≤ θ * C) :
    ∃ Q : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S P) 0 1 v u),
      ∀ r ≤ K, Q.budget r ≤ (θ * finiteMatrixPower S.M 0 v u) *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
          (C * ∑ i : Fin 2, |A (basisVec i)|)) := by
  obtain ⟨Q, hQ'⟩ := independentFirstLiftSourceReserve_exists S P A v u Qv θ C hQ
  refine ⟨Q, ?_⟩
  intro r hr
  have he : θ *
      ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
        (C * ∑ i : Fin 2, |A (basisVec i) * (if v = u then 1 else 0)|)) =
      (θ * finiteMatrixPower S.M 0 v u) *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
          (C * ∑ i : Fin 2, |A (basisVec i)|)) := by
    rw [finiteMatrixPower_zero]
    by_cases hvu : v = u
    · simp only [hvu, ite_true, mul_one]
    · simp only [ite_eq_right hvu, mul_zero, abs_zero, Finset.sum_const_zero, zero_mul]
  exact (hQ' r hr).trans_eq he

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced positive native predecessors give response-linear uncentered diagonal sources above degree two. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositiveDiagonalASource_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B)
    (hK : K ≤ H) (hbase : K + 2 ≤ base) (hn : 3 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) :
    ∃ QA : IndependentParameterSourceReserve K
      (independentLiftCoefficientASource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S
          (independentFinitePositivePredecessors S P Q hθ hB)) 0 n out inp),
      ∀ r ≤ K, QA.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
        (normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget (n - 1) A * B) +
          normalizedCellB2UniformBudget K A 1 BG (finiteLiftSymbolBudget (n - 2) A * B)) := by
  obtain ⟨Q1, hQ1⟩ := independentPositivePredecessorTest_uniform_production S P Q hθ hB hbase
    (n - 1) (by omega) (by omega) (by omega) A out inp
  obtain ⟨Q2, hQ2⟩ := independentPositivePredecessorTest_uniform_production S P Q hθ hB hbase
    (n - 2) (by omega) (by omega) (by omega) A out inp
  let F := fun p q t z Y w => independentScalarLiftTestSource q
    (independentFiniteLiftFields S (independentFinitePositivePredecessors S P Q hθ hB) p q) A w inp t z Y
  have hprod := independentDiagonalASource_uniform_response K S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
    A 1 (fun t Y i j => S.G t Y i j) S.v F n (by omega) out
    (fun i j => (S.metric_entries i j).restrictOrder (K + 1) (by omega))
    (fun i => (S.drift_entries i).restrictOrder K (by omega)) Q1 Q2
    (θ * finiteMatrixPower S.M 0 out inp) BG BV
    (finiteLiftSymbolBudget (n - 1) A * B) (finiteLiftSymbolBudget (n - 2) A * B)
    (mul_nonneg hθ0 (finiteMatrixPower_nonneg _ S.matrix_nonneg _ _ _)) hBG hBV
    (mul_nonneg (finiteLiftSymbolBudget_nonneg _ _) hB)
    (mul_nonneg (finiteLiftSymbolBudget_nonneg _ _) hB)
    (fun i j r hr => S.metric_entries_bound i j r (by omega))
    (fun i r hr => S.drift_bound i r (by omega)) hQ1 hQ2
  exact hprod

end AVRegularity.EntryWeakProofs
end
end

section
/-! The second diagonal inverse forcing is the centered first cross term; its initial metric term cancels. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count K : ℕ} {BG BV BE B : ℝ}

theorem independentSecondLiftCellSource_of_first_source_reserve
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Q : IndependentParameterSourceReserve K
      (independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
        (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
          A v u t z Y))) (t : ℝ) (z : Vec 2) (Y : Vec (2 + d)) :
    independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
      A 1 S.G S.v (independentFiniteLiftFields S P) 0 2 v u t z Y =
      -(independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
        (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
          A v u t z Y) t z Y - fieldCellMean (fun w =>
            independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
              (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
                A v u t z Y) t w Y)) := by
  let f := independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1
    (fun t Y i j => S.G t Y i j) S.v
    (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1) A v u t z Y)
  let c := fun t Y => independentNormalizedCellB2Source (independentIntrinsicSlowEmbedding d)
    A 1 (fun t Y i j => S.G t Y i j) (fun _ _ _ => if v = u then (1 : ℝ) else 0) t 0 Y
  have hi : (fun t z Y => independentScalarLiftTestSource 0
      (independentFiniteLiftFields S P 0 0) A v u t z Y) =
      (fun (_ : ℝ) (_ : Vec 2) (_ : Vec (2 + d)) => if v = u then (1 : ℝ) else 0) := by
    funext t z Y
    exact independentInitialScalarTest S P A v u t z Y
  have hA t z Y : independentLiftCoefficientASource S.edge S.edgeField
      (independentIntrinsicSlowEmbedding d) A 1 S.G S.v (independentFiniteLiftFields S P)
      0 2 v u t z Y = f t z Y + c t Y := by
    simp only [independentLiftCoefficientASource, independentLiftASource,
      Nat.reduceSub, Nat.reduceLeDiff, ite_true, sub_zero]
    rw [hi]
    rfl
  have hIcc : Finset.Icc 1 (2 - 2 : ℕ) = ∅ := by decide
  simp only [independentLiftCoefficientCellSource, independentCenteredRecurrenceSource,
    hIcc, Finset.sum_empty, add_zero, hA]
  exact congrArg Neg.neg (independent_center_add_fast_constant Q c t z Y)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine positive native productions give every ordered height-zero correction at one response
factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositiveCorrection_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B)
    (hK : K ≤ H) (hbase : K + 2 * D + 2 ≤ base) (hn : 1 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) (j : ℕ) (hj : j ∈ Finset.Icc 1 (n - 2))
    (p : ℕ × ℕ) (hp : p ∈ Finset.HasAntidiagonal.antidiagonal 0) :
    let c := independentFiniteLiftFields S (independentFinitePositivePredecessors S P Q hθ (zero_le_one.trans hB))
    ∃ QT : IndependentParameterSourceReserve K
      (independentLiftMeanCompositionSource j (c p.1 j) (independentIntrinsicSlowEmbedding d) A
        (fun t z Y w => independentLiftCoefficientASource S.edge S.edgeField
          (independentIntrinsicSlowEmbedding d) A 1 S.G S.v c p.2 (n - j) w inp t z Y) out),
      ∀ r ≤ K, QT.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
        independentLiftMeanCompositionCost (2 + d) K j A B
          (independentLiftAProductionMenuCost (K + D) D n count A 1 BG BV BE B) := by
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have he : p = (0, 0) := Prod.ext (by omega) (by omega)
  subst p
  dsimp only
  let Pc := independentFinitePositivePredecessors S P Q hθ (zero_le_one.trans hB)
  let c := independentFiniteLiftFields S Pc
  have hj' := Finset.mem_Icc.mp hj
  have hprod (m : Fin (j + 1)) (α : DerivativeWord2 m.val) (w : ι) :=
    independentFinitePositivePredecessors_reserve S P Q hθ (zero_le_one.trans hB)
      j hj'.1 (by omega) (by omega) m.val (by have := m.isLt; omega) α out w
  choose QC hQC using hprod
  let QC' := fun m α w => (QC m α w).restrictOrder K (by omega)
  have hgeneric p q (m : Fin (q + 1)) (α : DerivativeWord2 m.val) v u :=
    independentFiniteLiftFields_reserve S Pc hB p q m.val α v u
  choose Qc hQc using hgeneric
  have ht := independentLiftCorrection_uniform_response K S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d) A 1
    (fun t Y i j => S.G t Y i j) S.v c 0 n hn hnD out inp j hj (0, 0) hp
    (fun i j => (S.metric_entries i j).restrictOrder (K + D + 1) (by omega))
    (fun i => (S.drift_entries i).restrictOrder (K + D) (by omega))
    (fun p q _hpq m α v u => (Qc p q m α v u).restrictOrder (K + 2 * D + 2) hbase)
    (fun v u e γ hγ α => (S.edges v u e γ hγ α).restrictOrder (K + D + 1) (by omega))
    S.M S.matrix_nonneg count θ BG BV BE B hθ0 hBG hBV hBE (zero_le_one.trans hB)
    (fun i j r hr => S.metric_entries_bound i j r (by omega))
    (fun i r hr => S.drift_bound i r (by omega))
    (fun p q _hpq m α v u r hr => hQc p q m α v u r (by omega))
    (fun w u e γ hγ α r hr => S.edge_bound w u e γ hγ α r (by omega))
    S.edge_maps S.edge_lengths QC'
    (fun m α w r hr => hQC m α w r (by omega))
  exact ht

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual degree-two source retains the response price of its first cross term. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count K : ℕ} {BG BV BE B : ℝ}

theorem independentSecondLiftSourceReserve_exists
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    (Q : IndependentParameterSourceReserve K
      (independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
        (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
          A v u t z Y)))
    (θ C : ℝ) (hQ : ∀ r ≤ K, Q.budget r ≤ θ * C) :
    ∃ Qs : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S P) 0 2 v u),
      ∀ r ≤ K, Qs.budget r ≤ θ *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) * C) := by
  have he : (fun t z Y => (-ContinuousLinearMap.id ℝ ℝ)
      (independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
        (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
          A v u t z Y) t z Y - fieldCellMean (fun w =>
            independentNormalizedCellB1Source (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
              (fun t z Y => independentScalarLiftTestSource 1 (independentFiniteLiftFields S P 0 1)
                A v u t z Y) t w Y))) =
      independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S P) 0 2 v u := by
    funext t z Y
    simpa only [neg_apply, ContinuousLinearMap.id_apply] using
      (independentSecondLiftCellSource_of_first_source_reserve S P A v u Q t z Y).symm
  refine ⟨(Q.center.map (-ContinuousLinearMap.id ℝ ℝ)).congrSource he, ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change ‖-ContinuousLinearMap.id ℝ ℝ‖ * Q.center.budget r ≤ _
  rw [norm_neg, ContinuousLinearMap.norm_id, one_mul]
  exact Q.center_uniform_budget θ C hQ r hr

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full produced menu gives genuine native flux reserves with literal matrix grades. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteLiftFlux_reserve (H : ℕ)
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hbase : H + D + 2 ≤ base) (hT : H ≤ T)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) (k : Fin 2) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftFluxSource
      S.edge S.edgeField (independentIntrinsicSlowEmbedding d) A 1 S.G S.v
      (independentFiniteLiftFields S P) hh n out inp k),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower S.M hh out inp *
        independentLiftFluxProductionCost H D n count A 1 BG BV BE B := by
  choose Qc hc using fun p q m α v u => independentFiniteLiftFields_reserve S P hB p q m α v u
  exact independentLiftFlux_uniform_production H S.edge S.edgeField
    (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d) A
    1 S.G S.v (independentFiniteLiftFields S P) hh n hn hhpos out inp k
    (fun i j => (S.metric_entries i j).restrictOrder H (by omega))
    (fun i => (S.drift_entries i).restrictOrder H (by omega))
    (fun p q _ m α v u => (Qc p q m.val α v u).restrictOrder (H + D + 2) hbase)
    (fun v u e γ hγ α => (S.edges v u e γ hγ α).restrictOrder H (by omega))
    S.M S.matrix_nonneg count BG BV BE B hBG hBV hBE (zero_le_one.trans hB)
    (fun i j r hr => S.metric_entries_bound i j r (by omega))
    (fun i r hr => S.drift_bound i r (by omega))
    (fun p q _ m α v u r hr => hc p q m.val α v u r (hr.trans hbase))
    (fun v u e γ hγ α r hr => S.edge_bound v u e γ hγ α r (by omega))
    S.edge_maps S.edge_lengths

end AVRegularity.EntryWeakProofs
end
end

section
/-! A positive degree step consumes genuinely produced lower degrees at geometric reserve orders. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

structure IndependentPositiveNaturalStepDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d base D N R count qs n : ℕ) (BG BV BE B : ℝ) where
  menu : IndependentPositiveNaturalMenuDatum ι d base D N R count qs BG BV BE B
  earlier : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d)
      (4 * liftProductionOrder base D N R 0 n + 2 * D + 7) q
      menu.data.primitive.a menu.data.primitive.b menu.data.primitive.U
      (fun Y => menu.data.primitive.Cc (independentStoredParameterProjection d Y) 0 q)
      (independentIntrinsicSlowProjection d) m α v u
      (menu.response * finiteMatrixPower menu.data.primitive.M 0 v u) B
  earlier_translation : ∀ δ ∈ menu.data.translations, ∀ q hq hqn m hm α v u,
    IndependentSourceTranslationInvariant δ (earlier q hq hqn m hm α v u).field

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d base D N R count qs n : ℕ} {BG BV BE B : ℝ}

def IndependentPositiveNaturalStepDatum.restrict
    (x : IndependentPositiveNaturalStepDatum ι d base D N R count qs n BG BV BE B) :
    IndependentPositiveResponseDatum ι d (liftProductionOrder base D N R 0 n) D N R count n qs BG BV BE B := by
  let k := liftProductionOrder base D N R 0 n
  have horder : 4 * k + 5 ≤ independentLiftPrimitiveTopOrder base D N R := by
    have ho := liftProductionOrder_le_initial base D N R 0 n
    dsimp only [independentLiftPrimitiveTopOrder, k]
    omega
  exact
    { primitive := x.menu.data.primitive.monoOrder (4 * k + 5) horder
      productions := fun hh q hhh hq m hm α v u =>
        (x.menu.productions hh q hhh hq m hm α v u).monoOrder _ (by omega)
      fastOrder := x.menu.data.fastOrder
      response := x.menu.response
      response_nonneg := x.menu.response_nonneg
      response_small := x.menu.response_small
      earlier := fun q hq hqn m hm α v u =>
        (x.earlier q hq hqn m hm α v u).monoOrder _ (by omega)
      translations := x.menu.data.translations
      metric_translation := x.menu.data.metric_translation
      edge_translation := x.menu.data.edge_translation
      production_translation := x.menu.production_translation
      earlier_translation := x.earlier_translation }

end AVRegularity.EntryWeakProofs
end
end

section
/-! Primitive response data, with an already produced finite menu for literal native inverse transfer. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

structure IndependentFirstResponseDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d k D N R count qs : ℕ) (BG BV BE B : ℝ) where
  primitive : IndependentLiftPrimitiveData ι d (4 * k + 5) D N R count BG BV BE
  productions : IndependentLiftMenuProductions primitive (4 * k + 5 + 2 * D + 2) B
  fastOrder : primitive.sZ = qs
  response : ℝ
  response_nonneg : 0 ≤ response
  drift_response : ∀ i r, r ≤ 4 * k + 5 →
    (primitive.drift_entries i).budget r ≤ response * BV
  translations : Set (Vec (2 + d))
  metric_translation : ∀ δ ∈ translations, ∀ t Y,
    primitive.G t (Y + δ) = primitive.G t Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full actual centered height-zero recurrence retains one positive-response factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count n K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositiveDiagonalCellSource_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < n → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 1 ≤ B)
    (hK : K ≤ H) (hbase : K + 2 * D + 2 ≤ base) (hn : 3 ≤ n) (hnN : n ≤ N) (hnD : n ≤ D)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) :
    ∃ Qs : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S
          (independentFinitePositivePredecessors S P Q hθ (zero_le_one.trans hB))) 0 n out inp),
      ∀ r ≤ K, Qs.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
          (normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget (n - 1) A * B) +
            normalizedCellB2UniformBudget K A 1 BG (finiteLiftSymbolBudget (n - 2) A * B)) +
          ∑ j ∈ Finset.Icc 1 (n - 2), ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal 0,
            independentLiftMeanCompositionCost (2 + d) K j A B
              (independentLiftAProductionMenuCost (K + D) D n count A 1 BG BV BE B)) := by
  let c := independentFiniteLiftFields S
    (independentFinitePositivePredecessors S P Q hθ (zero_le_one.trans hB))
  obtain ⟨QA, hQA⟩ := independentPositiveDiagonalASource_uniform_production S P Q hθ0 hθ hBG hBV
    (zero_le_one.trans hB) hK (by omega) hn hnN A out inp
  have hprod j (hj : j ∈ Finset.Icc 1 (n - 2)) p (hp : p ∈ Finset.HasAntidiagonal.antidiagonal 0) :=
    independentPositiveCorrection_uniform_production S P Q hθ0 hθ hBG hBV hBE hB
      hK hbase (by omega) hnN hnD A out inp j hj p hp
  choose QT hQT using hprod
  refine ⟨independentCenteredRecurrenceSourceReserve 0 n
    (independentLiftCoefficientASource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
      A 1 S.G S.v c 0 n out inp)
    (fun j p => independentLiftMeanCompositionSource j (c p.1 j) (independentIntrinsicSlowEmbedding d) A
      (fun t z Y w => independentLiftCoefficientASource S.edge S.edgeField
        (independentIntrinsicSlowEmbedding d) A 1 S.G S.v c p.2 (n - j) w inp t z Y) out)
    QA QT, ?_⟩
  intro r hr
  exact independentCenteredRecurrenceSourceReserve_priced_budget 0 n _ _ QA QT
    (θ * finiteMatrixPower S.M 0 out inp)
    (normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget (n - 1) A * B) +
      normalizedCellB2UniformBudget K A 1 BG (finiteLiftSymbolBudget (n - 2) A * B))
    (fun j _ => independentLiftMeanCompositionCost (2 + d) K j A B
      (independentLiftAProductionMenuCost (K + D) D n count A 1 BG BV BE B)) hQA hQT r hr

end AVRegularity.EntryWeakProofs
end
end

section
/-! The first positive production supplies the actual second inverse source at one response
factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H base D N R count K : ℕ} {BG BV BE B θ : ℝ}

theorem independentPositiveSecondSource_uniform_production
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B)
    (Q : ∀ q, 1 ≤ q → q < 2 → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) base q S.a S.b S.U
        (fun Y => S.Cc (independentStoredParameterProjection d Y) 0 q)
        (independentIntrinsicSlowProjection d) m α v u (θ * finiteMatrixPower S.M 0 v u) B)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 0 ≤ B)
    (hK : K ≤ H) (hbase : K + 2 ≤ base) (hN : 2 ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (out inp : ι) :
    ∃ Qs : IndependentParameterSourceReserve K
      (independentLiftCoefficientCellSource S.edge S.edgeField (independentIntrinsicSlowEmbedding d)
        A 1 S.G S.v (independentFiniteLiftFields S
          (independentFinitePositivePredecessors S P Q hθ hB)) 0 2 out inp),
      ∀ r ≤ K, Qs.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
        ((1 + (((2 + d : ℕ) : ℝ) + 1) ^ K * (K + 1 : ℕ)) *
          normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget 1 A * B)) := by
  obtain ⟨Q1, hQ1⟩ := independentPositivePredecessorTest_uniform_production S P Q hθ hB hbase
    1 le_rfl (by decide) (by omega) A out inp
  let QG := fun i j => (S.metric_entries i j).restrictOrder (K + 1) (by omega)
  let Qv := fun i => (S.drift_entries i).restrictOrder K (by omega)
  let f := independentScalarLiftTestSource 1
    (independentFiniteLiftFields S (independentFinitePositivePredecessors S P Q hθ hB) 0 1) A out inp
  let QB := independentNormalizedCellB1SourceReserve K (independentIntrinsicSlowEmbedding d)
    (independentIntrinsicSlowEmbedding_norm_le d) A 1 (fun t Y i j => S.G t Y i j) S.v f QG Qv Q1
  have hQB r (hr : r ≤ K) : QB.budget r ≤ (θ * finiteMatrixPower S.M 0 out inp) *
      normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget 1 A * B) :=
    independentNormalizedCellB1SourceReserve_uniform_budget K (independentIntrinsicSlowEmbedding d)
      (independentIntrinsicSlowEmbedding_norm_le d) A 1 (fun t Y i j => S.G t Y i j) S.v f QG Qv Q1
      (θ * finiteMatrixPower S.M 0 out inp) BG BV (finiteLiftSymbolBudget 1 A * B)
      (mul_nonneg hθ0 (finiteMatrixPower_nonneg _ S.matrix_nonneg _ _ _)) hBG hBV
      (mul_nonneg (finiteLiftSymbolBudget_nonneg _ _) hB)
      (fun i j r hr => S.metric_entries_bound i j r (by omega))
      (fun i r hr => S.drift_bound i r (by omega)) hQ1 r hr
  exact independentSecondLiftSourceReserve_exists S
    (independentFinitePositivePredecessors S P Q hθ hB) A out inp QB
    (θ * finiteMatrixPower S.M 0 out inp)
    (normalizedCellB1UniformBudget K A 1 BG BV (finiteLiftSymbolBudget 1 A * B)) hQB

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual first inverse produces response-linear coefficients uniformly over primitive families. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentFirstCrossResponseCoefficientProduction (d k D N R count qs m : ℕ)
    (hD : 1 ≤ D) (hN : 1 ≤ N) (hm : m ≤ 1) (α : DerivativeWord2 m) (out inp : ι)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q : ∀ x : IndependentFirstResponseDatum ι d k D N R count qs BG BV BE B,
      IndependentScalarCoefficientProduction (2 + d) k 1 x.primitive.a x.primitive.b
        x.primitive.U (fun Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
        (independentIntrinsicSlowProjection d) m α out inp
        (x.response * finiteMatrixPower x.primitive.M 0 out inp) C,
      (∀ x δ, δ ∈ x.translations → IndependentSourceTranslationInvariant δ (Q x).field) ∧
      ∀ x x' Y Z,
        x.response * finiteMatrixPower x.primitive.M 0 out inp =
          x'.response * finiteMatrixPower x'.primitive.M 0 out inp →
        x.primitive.a = x'.primitive.a → x.primitive.b = x'.primitive.b →
        x.primitive.v = x'.primitive.v →
        (∀ t, x.primitive.G t Y = x'.primitive.G t Z) →
        (∀ p : Fin (m + 1) × Fin (1 + 1), ∀ t z,
          independentLiftCoefficientCellSource x.primitive.edge x.primitive.edgeField
            (independentIntrinsicSlowEmbedding d)
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 x.primitive.G x.primitive.v
            (independentFiniteLiftFields x.primitive x.productions) 0 1 out inp t z Y =
          independentLiftCoefficientCellSource x'.primitive.edge x'.primitive.edgeField
            (independentIntrinsicSlowEmbedding d)
            ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 x'.primitive.G x'.primitive.v
            (independentFiniteLiftFields x'.primitive x'.productions) 0 1 out inp t z Z) →
        ∀ t z, (Q x).field t z Y = (Q x').field t z Z := by
  let X := IndependentFirstResponseDatum ι d k D N R count qs BG BV BE B
  let A := fun p : Fin (m + 1) × Fin 2 => (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let src := fun (x : X) p => independentLiftCoefficientCellSource x.primitive.edge
    x.primitive.edgeField (independentIntrinsicSlowEmbedding d) (A p) 1 x.primitive.G
    x.primitive.v (independentFiniteLiftFields x.primitive x.productions) 0 1
  let g := fun (x : X) p => independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
    (fun t z Y v => src x p v inp t z Y)
  have hprod (x : X) p := independentFirstLiftSourceReserve_matrix_response x.primitive x.productions
    (A p) out inp (fun i => (x.primitive.drift_entries i).restrictOrder (4 * k + 5) (by omega))
    x.response BV x.drift_response
  choose Q hQ using hprod
  let Qg := fun (x : X) p => ((Q x p).timeWindow (Ioc x.primitive.a x.primitive.b)
    measurableSet_Ioc).congrSource (show independentTimeWindowSource (Ioc x.primitive.a x.primitive.b)
      (src x p out inp) = (fun t z Y => g x p t z Y out) by
        funext t z Y
        by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
        · simp only [g, independentTimeWindowSource, ite_eq_left ht]
        · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply])
  let BS := independentFirstCalibrationPrice (2 + d) (4 * k + 5) m BV
  have hBS : 0 ≤ BS := independentFirstCalibrationPrice_nonneg _ _ _ _ hBV
  have hθ (x : X) : 0 ≤ x.response * finiteMatrixPower x.primitive.M 0 out inp :=
    mul_nonneg x.response_nonneg (finiteMatrixPower_nonneg _ x.primitive.matrix_nonneg _ _ _)
  have hQg (x : X) p r (hr : r ≤ 4 * k + 5) :
      (Qg x p).budget r ≤ (x.response * finiteMatrixPower x.primitive.M 0 out inp) * BS := by
    dsimp only [Qg]
    rw [IndependentParameterSourceReserve.congrSource_budget,
      IndependentParameterSourceReserve.timeWindow_budget]
    exact (hQ x p r hr).trans (mul_le_mul_of_nonneg_left
      (independentFirstSourcePrice_le_calibrated (2 + d) (4 * k + 5) m BV hBV p) (hθ x))
  have hg (x : X) p t (ht : t ≤ x.primitive.a) z Y : g x p t z Y out = 0 := by
    rw [show g x p t z Y = 0 from independent_time_window_Ioc_past_zero
      (fun t z Y => (fun v => src x p v inp t z Y)) x.primitive.a x.primitive.b t ht z Y]
    rfl
  have hmean (x : X) p t Y : fieldCellMean (fun z => g x p t z Y out) = 0 := by
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simp only [g, independentTimeWindowSource, ite_eq_left ht]
      exact independentFiniteLiftSource_mean_zero x.primitive x.productions hB le_rfl
        (A p) out inp le_rfl hD t Y
    · simp only [g, independentTimeWindowSource, ite_eq_right ht, Pi.zero_apply, fieldCellMean_zero]
  have hactual (x : X) p Y (hY : Y ∈ x.primitive.U) :
      IsCellFieldInverse (x.primitive.molecular Y).G (x.primitive.molecular Y).v qs x.primitive.a x.primitive.b 0
        (fun t z => g x p t z Y)
        (fun t z => (Real.exp (((1 : ℝ) • A p) (independentIntrinsicSlowProjection d Y)))⁻¹ •
          liftApply 1 (x.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
            (fun _ Z => Real.exp (((1 : ℝ) • A p) Z) • (Pi.single inp (1 : ℝ) : ι → ℝ))
            t (independentIntrinsicSlowProjection d Y) z) := by
    have hi := independentFiniteLiftSource_actual_inverse x.primitive x.productions hB le_rfl
      (by omega) hD (Nat.zero_le R) le_rfl hN hD (A p) inp Y hY
    rw [x.fastOrder] at hi
    simpa only [g, src, one_smul] using hi
  let Rel : X → Vec (2 + d) → Vec (2 + d) → Prop := fun x Y Z => ∃ δ ∈ x.translations, Y = Z + δ
  have hGR (x : X) Y Z (hYZ : Rel x Y Z) t : x.primitive.G t Y = x.primitive.G t Z := by
    obtain ⟨δ, hδ, rfl⟩ := hYZ
    exact x.metric_translation δ hδ t Z
  have hgR (x : X) p Y Z (_hYZ : Rel x Y Z) t z : g x p t z Y out = g x p t z Z out := by
    by_cases ht : t ∈ Ioc x.primitive.a x.primitive.b
    · simp only [g, src, independentTimeWindowSource, ite_eq_left ht, independentFirstLiftCellSource]
    · simp only [g, independentTimeWindowSource, ite_eq_right ht]
  obtain ⟨C, hC, Qprod, hnat, hcross⟩ := family_variable_window_cross_natural_independent_coefficient_productions_exist (A := X)
    (fun x => x.primitive.window) k (k + 4) k 1 m hm (by omega) (by omega) le_rfl (by omega)
    out inp (fun x => x.primitive.metric) Qg (fun _ => BG) (fun _ => BS) (fun _ => hBG)
    (fun _ => hBS) (fun x => x.primitive.metric_bound)
    (fun x => x.response * finiteMatrixPower x.primitive.M 0 out inp) hθ hQg
    (fun x => x.primitive.molecular) (fun x => x.primitive.molecular_coefficients)
    (fun x => x.primitive.v) (fun x => x.primitive.drift) (fun x => x.primitive.molecular_drift)
    (fun x => x.primitive.molecular_budget) hg hmean Rel hGR hgR qs
    (fun x Y => x.primitive.Cc (independentStoredParameterProjection d Y) 0 1)
    (fun _ => independentIntrinsicSlowProjection d) (fun x => x.primitive.U)
    (fun x Y β σ => x.primitive.symmetric _ 0 (Nat.zero_le R) 1 m β σ) α 1 one_ne_zero hactual
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
end

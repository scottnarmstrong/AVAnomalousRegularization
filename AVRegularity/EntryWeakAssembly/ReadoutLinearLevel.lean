-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.LiftInverseInitialGrade
public import AVRegularity.EntryWeakAssembly.PositiveCutoffMetricEllipticity
import AVRegularity.EntryWeakAssembly.QuietScalarEvolution
import AVRegularity.EntryWeakAssembly.CoordinateWordRawHilbertCurves
public import AVRegularity.EntryWeak.WeakStageSampledReferenceField
public import AVRegularity.EntryWeakAssembly.Assembly.PassageInterfaces
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
import AVRegularity.CycleComparison.Reconstruction.ApproxIdentity
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
@[expose] public noncomputable section
section
namespace AVRegularity.WeakEntryProofs

/-! The full-cell lift recurrence has finite degree support and symmetric derivative words. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_above_order (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n m : ℕ) (hm : n < m)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    weakLiftInverseCoefficients Q inverse N hh n m α t X z v u = 0 := by
  by_cases hn : n ≤ N
  · rw [weakLiftInverseCoefficients_eq_step Q inverse N hh n hn]
    exact weakLiftStepWithInverse_above_order Q inverse _ hh n m hm α t X z v u
  · rw [weakLiftInverseCoefficients_cutoff Q inverse N hh n (by omega)]
    rfl

theorem weakLiftInverseCoefficients_perm (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    weakLiftInverseCoefficients Q inverse N hh n m (α ∘ σ) =
      weakLiftInverseCoefficients Q inverse N hh n m α := by
  by_cases hn : n ≤ N
  · rw [weakLiftInverseCoefficients_eq_step Q inverse N hh n hn]
    exact weakLiftStepWithInverse_perm Q inverse _ hh n m α σ
  · rw [weakLiftInverseCoefficients_cutoff Q inverse N hh n (by omega)]
    rfl
end

/-! Only earlier coefficients enter a positive weak inverse step, even when evaluated on the completed array. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_eq_full_step (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    weakLiftInverseCoefficients Q inverse N hh n =
      weakLiftStepWithInverse Q inverse (weakLiftInverseCoefficients Q inverse N) hh n := by
  rw [weakLiftInverseCoefficients_eq_step Q inverse N hh n hnN]
  have he (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) :=
    weakLiftInverse_prefix_agreement Q inverse N hh n p q hpq
  have hsrc (s : ℝ) (w : ι) := liftCellSourceLeftTerms_congr_predecessors Q
    (fun p q => if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
      weakLiftInverseCoefficients Q inverse N p q else 0)
    (weakLiftInverseCoefficients Q inverse N) hh n hn he s w
  funext m α t X z v u
  simp only [weakLiftStepWithInverse, ite_eq_right (by omega : n ≠ 0), hsrc]
end

/-! The explicit scalar mean terms act on genuine full-cell predecessor fields. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakActualMean_leftTerms_apply
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (hvp : AVenhance.IsZ2Periodic (Q.v t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2)
    (hcoef : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun Y => actualMeanFluxCoefficient Q Cc hh n k m α t Y 0 v u))
    (hfast : ∀ Y m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc hh (n - 1) m α t Y y v u))
    (hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t))
    (hΨ : 3 ≤ n ∨ hh ≠ 0 →
      CoefField True 2 (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t))
    (hsource : hh ≠ 0 → ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hgood : hh ≠ 0 → ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : hh ≠ 0 → ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0)
    (hF : hh ≠ 0 → ∀ k Y, Continuous (sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y)) :
    leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  unfold actualMeanLeftTerms
  by_cases hh0 : hh = 0
  · subst hh
    simp only [actualMeanFluxCoefficient, ite_true]
    apply weakDiagonal_mean_left_terms_apply Q t hG hw Cc n hn f hf X z
    · simpa only [actualMeanFluxCoefficient, ite_true] using hcoef
    · exact hfast
    · exact hid
    · exact hΦ
    · intro hn3
      exact hΨ (Or.inl hn3)
  · simp only [actualMeanFluxCoefficient, ite_eq_right hh0]
    apply weakPositive_mean_left_terms_apply Q hD N t hG hw hvp hΓ Cc hh (by omega)
      n hn f hf X z
    · simpa only [actualMeanFluxCoefficient, ite_eq_right hh0] using hcoef
    · exact hfast
    · exact hΦ
    · exact hΨ (Or.inr hh0)
    · exact hsource hh0
    · exact hgood hh0
    · exact hcut hh0
    · exact hF hh0
end

/-! A full-cell linear inverse applied coefficientwise acts on the complete finite centered source. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftStepWithInverse_finite_action (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (R : Vec 2 → (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ))
    (prior : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (a₀ : Vec 2 → ι → ℝ) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (weakLiftStepWithInverse Q (fun X => R X) prior hh n) (fun _ => a₀) t X z v =
      R X (fun s y => leftTermsApply (liftCellSourceLeftTerms Q prior hh n s v) a₀ X y) t z := by
  have he : liftApply n (weakLiftStepWithInverse Q (fun X => R X) prior hh n)
      (fun _ => a₀) t X z v =
      liftApply n (respondedScalarLiftCoeff R (liftSourceBlockCoefficient Q prior hh n))
        (fun _ => a₀) t X z v := by
    unfold liftApply
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
    apply Finset.sum_congr rfl
    intro α _hα
    apply Finset.sum_congr rfl
    intro u _hu
    simp only [weakLiftStepWithInverse, ite_eq_right (by omega : n ≠ 0), ite_eq_left hm',
      respondedScalarLiftCoeff, liftSourceBlockCoefficient]
  rw [he, respondedScalarLiftCoeff_apply]
  apply congrArg (fun g => R X g t z)
  funext s y
  exact liftSourceBlockCoefficient_action Q prior hh n hn a₀ ha₀ s X y v

theorem weakLiftInverseCoefficients_finite_action (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (R : Vec 2 → (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ))
    (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (a₀ : Vec 2 → ι → ℝ) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (weakLiftInverseCoefficients Q (fun X => R X) N hh n) (fun _ => a₀) t X z v =
      R X (fun s y => leftTermsApply
        (liftCellSourceLeftTerms Q (weakLiftInverseCoefficients Q (fun X => R X) N) hh n s v)
        a₀ X y) t z := by
  rw [weakLiftInverseCoefficients_eq_full_step Q (fun X => R X) N hh n hn hnN]
  exact weakLiftStepWithInverse_finite_action Q R _ hh n hn a₀ ha₀ t X z v
end

/-! Actual mean coefficient reserves supply the smooth composition terms of the source. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem actualMeanLeftTerms_box_of_reserves (H p q : ℕ) (hp : p + 1 ≤ H)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (R : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      JointSourceReserve H (fun t z Y => actualMeanFluxCoefficient Q Cc hh n k m α t Y z v u 1))
    (t : ℝ) (d : LeftTerm (ι → ℝ) (ι → ℝ)) (hd : d ∈ actualMeanLeftTerms Q Cc hh n t) :
    IsBoxSmooth p q d.coeff := by
  apply meanFluxLeftTerms_box n (actualMeanFluxCoefficient Q Cc hh n) t p q _ d hd
  intro k m hm α v u
  apply realLinearMap_field_contDiff_of_value_one (p + 1)
  exact (((R k m hm α v u).regular t).comp₂ contDiff_const contDiff_id).of_le
    (by exact_mod_cast hp)
end

/-! Every finite full-cell forcing coefficient is determined by predecessor germs. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem liftCellSourceLeftTerms_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι (fun _ => ℝ) D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X) (v : ι)
    (hΓ : SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (liftCellSourceLeftTerms Q Cc hh n t v)
      (liftCellSourceLeftTerms Q' Dc hh n t v) := by
  unfold liftCellSourceLeftTerms
  apply List.rel_append
  · apply List.rel_append
    · exact List.rel_map (fun _ _ h => h.smul (-1))
        (liftALeftTerms_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc hh n hn t hG v hΓ he)
    · exact List.rel_map (fun _ _ h => h.postcompose (ContinuousLinearMap.proj v))
        (recurrenceMeanLeftTerms_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc hh n t hG hΓ he)
  · apply leftTermSlowEq_flatMap_same
    intro j hj
    have hj' := Finset.mem_Icc.mp (Finset.mem_toList.mp hj)
    apply leftTermSlowEq_flatMap_same
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_toList.mp hp)
    apply leftTermsComposition_slow_local_congr Ω hΩ
    · exact liftComponentLeftTerms_slow_local_congr j _ _ t v
        (fun m hm α X hX z u => he p.1 j (by
          by_cases hlt : p.1 < hh
          · exact Or.inl hlt
          · exact Or.inr ⟨by omega, by omega⟩) m hm α X hX z v u)
    · apply actualMeanLeftTerms_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc p.2 (n - j) (by omega) t hG hΓ
      intro r s hrs m hm α X hX z v u
      apply he r s _ m hm α X hX z v u
      rcases hrs with hr | ⟨rfl, hs⟩
      · exact Or.inl (by omega)
      · by_cases hlt : p.2 < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩
end

/-! The actual source coefficient used by the full inverse is local in its predecessors. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullCellSourceCoefficient_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι (fun _ => ℝ) D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X)
    (hΓ : AVRegularity.EntryWeakProofs.SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (m : ℕ) (α : DerivativeWord2 m) (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) (v u : ι) :
    leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
      m α t X z v u =
    leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q' Dc hh n t w)
      m α t X z v u :=
  leftTermsBlockCoefficient_slow_local_congr Ω _ _
    (fun w => liftCellSourceLeftTerms_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc hh n hn t hG w hΓ he)
    m α t X hX z v u
end

/-! The literal initial coefficient array has reserves at every finite order. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def weakLiftInverseCoefficients_initialReserve (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (N hh m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    JointSourceReserve H (fun t z Y =>
      weakLiftInverseCoefficients Q inverse N hh 0 m α t Y z v u 1) := by
  let c : ℝ := (if hh = 0 ∧ m = 0 then
    blockIdentityEntry (fun _ : ι => ℝ) v u else 0) 1
  apply (JointSourceReserve.const H c).congrSource
  funext t z Y
  rw [weakLiftInverseCoefficients_zero_degree]

theorem weakLiftInverseCoefficients_initial_action
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (N hh : ℕ) (f : Vec 2 → ι → ℝ) (t : ℝ) :
    liftApply 0 (weakLiftInverseCoefficients Q inverse N hh 0) (fun _ => f) t =
      fun Y _ => if hh = 0 then f Y else 0 := by
  by_cases hhh : hh = 0
  · subst hh
    funext Y z
    simpa only [ite_true] using
      weakLiftInverseCoefficients_identity Q inverse N (fun _ => f) t Y z
  · have he : weakLiftInverseCoefficients Q inverse N hh 0 = 0 := by
      funext m α s Y z v u
      exact weakLiftInverseCoefficients_positive_grade_zero Q inverse N hh (by omega)
        m α s Y z v u
    rw [he]
    funext Y z v
    simp only [liftApply, zero_apply, Finset.sum_const_zero,
      ite_eq_right hhh, Pi.zero_apply]
end

/-! Actual normalized forcing tests produce the exact finite source-coefficient reserve. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def sourceCoefficientReserveOfRepresentation (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (hrep : ∀ (f : Vec 2 → ι → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ t X z,
      leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
        liftCellSource Q Cc (fun _ => f) hh n t X z v)
    (Qs : ∀ p : Fin (m + 1) × Fin (n + 1), JointSourceReserve H
      (fun t z Y => normalizedLiftCellSource Q Cc
        (fun _ X => Real.exp (((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) X) • Pi.single u 1)
        hh n ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) t z Y v)) :
    JointSourceReserve H
      (fun t z Y => liftSourceBlockCoefficient Q Cc hh n m α t Y z v u 1) := by
  have hperm : ∀ β (σ : Equiv.Perm (Fin m)),
      liftSourceBlockCoefficient Q Cc hh n m (β ∘ σ) = liftSourceBlockCoefficient Q Cc hh n m β := by
    intro β σ
    funext t X z v u
    simp only [liftSourceBlockCoefficient, leftTermsBlockCoefficient_perm]
  apply calibratedCoefficientReserve H n m hm (liftSourceBlockCoefficient Q Cc hh n) hperm α v u
  intro p
  apply (Qs p).congrSource
  funext t z Y
  let A := (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let f := fun X => Real.exp (A X) • (Pi.single u 1 : ι → ℝ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  change (Real.exp (A Y))⁻¹ • liftCellSource Q Cc (fun _ => f) hh n t Y z v =
    (Real.exp (A Y))⁻¹ • liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t Y z v
  rw [liftSourceBlockCoefficient_action Q Cc hh n hn f hf t Y z v, hrep f hf]
end

/-! Centered literal forcing tests center each finite inverse-source coefficient. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem sourceCoefficient_mean_zero (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (hrep : ∀ (f : Vec 2 → ι → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ t X z,
      leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
        liftCellSource Q Cc (fun _ => f) hh n t X z v)
    (Qs : ∀ p : Fin (m + 1) × Fin (n + 1), JointSourceReserve H
      (fun t z Y => normalizedLiftCellSource Q Cc
        (fun _ X => Real.exp (((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) X) • Pi.single u 1)
        hh n ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) t z Y v))
    (hmean : ∀ p : Fin (m + 1) × Fin (n + 1), ∀ t Y,
      fieldCellMean (fun z => normalizedLiftCellSource Q Cc
        (fun _ X => Real.exp (((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) X) • Pi.single u 1)
        hh n ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) t z Y v) = 0)
    (t : ℝ) (Y : Vec 2) :
    fieldCellMean (fun z => liftSourceBlockCoefficient Q Cc hh n m α t Y z v u 1) = 0 := by
  have he (p : Fin (m + 1) × Fin (n + 1)) :
      (fun t z Y => normalizedLiftCellSource Q Cc
        (fun _ X => Real.exp (((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) X) • Pi.single u 1)
        hh n ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) t z Y v) =
      (fun t z Y => normalizedLiftTestField (liftSourceBlockCoefficient Q Cc hh n) n
        ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u v 1 t Y z) := by
    funext t z Y
    let A := (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
    let f := fun X => Real.exp (A X) • (Pi.single u 1 : ι → ℝ)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
    change (Real.exp (A Y))⁻¹ • liftCellSource Q Cc (fun _ => f) hh n t Y z v =
      (Real.exp (A Y))⁻¹ • liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t Y z v
    rw [liftSourceBlockCoefficient_action Q Cc hh n hn f hf t Y z v, hrep f hf]
  apply calibratedCoefficient_mean_zero H n m hm (liftSourceBlockCoefficient Q Cc hh n)
    (fun β σ => by
      funext t X z v u
      simp only [liftSourceBlockCoefficient, leftTermsBlockCoefficient_perm]) α v u
    (fun p => (Qs p).congrSource (he p)) _ t Y
  intro p t Y
  exact (congrArg (fun F : ℝ → Vec 2 → Vec 2 → ℝ =>
    fieldCellMean (fun z => F t z Y)) (he p)).symm.trans (hmean p t Y)
end

/-! Genuine finite-window scalar sources remain solvable under finite differential actions. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [DecidableEq ι] in
theorem scalarLift_mem_windowSolvableForcing
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vdrift : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (n : ℕ) (c : LiftCoeff ι (fun _ => ℝ)) (f : Vec 2 → ι → ℝ) (X : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      (fun t z => c m α t X z v u 1) ∈ windowSolvableForcing G vdrift r hr a b hab) :
    (fun t z => liftApply n c (fun _ => f) t X z v) ∈
      windowSolvableForcing G vdrift r hr a b hab := by
  classical
  have hs := (windowSolvableForcing G vdrift r hr a b hab).sum_mem
    (fun m (hm : m ∈ Finset.range (n + 1)) =>
      (windowSolvableForcing G vdrift r hr a b hab).sum_mem (fun α (_ : α ∈ Finset.univ) =>
        (windowSolvableForcing G vdrift r hr a b hab).sum_mem (fun u (_ : u ∈ Finset.univ) =>
          (windowSolvableForcing G vdrift r hr a b hab).smul_mem
            (orderedDerivative α f X u) (hc m (by have := Finset.mem_range.mp hm; omega) α u))))
  have he (m : ℕ) (α : DerivativeWord2 m) (u : ι) (t : ℝ) (z : Vec 2) :
      c m α t X z v u (orderedDerivative α f X u) =
        orderedDerivative α f X u * c m α t X z v u 1 := by
    simpa only [smul_eq_mul, mul_one] using
      map_smul (c m α t X z v u) (orderedDerivative α f X u) (1 : ℝ)
  convert hs using 1
  funext t z
  simp only [liftApply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, he]

theorem fullCellFiniteSource_mem_windowSolvableForcing
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vdrift : ℝ → Vec 2 → Vec 2) (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      (fun t z => liftSourceBlockCoefficient Q Cc hh n m α t X z v u 1) ∈
        windowSolvableForcing G vdrift r hr a b hab) :
    (fun t z => leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z) ∈
      windowSolvableForcing G vdrift r hr a b hab := by
  have hs := scalarLift_mem_windowSolvableForcing G vdrift r hr a b hab n
    (liftSourceBlockCoefficient Q Cc hh n) f X v hc
  convert hs using 1
  funext t z
  exact (liftSourceBlockCoefficient_action Q Cc hh n hn f hf t X z v).symm
end

/-! Every finite native history locally produces jointly regular genuine parameter scalar inverses. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open scoped ContDiff
variable {ι : Type*} {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm H : ℕ}

theorem native_local_parameter_scalar_inverse_with_reserve (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (m : ℕ) (hν : 0 < D.kap m) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm hv) (a b : ℝ) (hab : a < b)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H) (hN : N + 2 ≤ H) (hK : N + 4 ≤ K)
    {g : ℝ → Vec 2 → Vec 2 → ℝ} (Qg : IndependentParameterSourceReserve H g)
    (hg : ∀ t Y, ∫ z in AVenhance.unitCube, g t z Y = 0) (Y₀ : Vec 2) :
    ∃ (U : Set (Vec 2)) (c : Vec 2 → ℝ → Vec 2 → ℝ), IsOpen U ∧ Y₀ ∈ U ∧
      (∀ Y ∈ U, IsCellFieldInverse (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
        (familyLiftData D m slot A ρ edge).v N a b 0 (fun t z => g t z Y) (c Y)) ∧
      (∀ r, r ≤ N → ∀ t ∈ Icc a b,
        ContDiff ℝ (r : ℕ∞) (fun X : Vec 2 × Vec 2 => c X.1 t X.2)) ∧
      ∀ S, S ≤ N → Nonempty (IndependentParameterSourceReserve S
        (independentTimeWindowSource (Ioc a b) (fun t z Y => c Y t z))) := by
  let Q := familyLiftData D m slot A ρ edge
  have hvD : IsCellDrift Q.v := normalizedPulseDrift_isCellDrift hΛ hν hζ hslot
  let P := driftMolecularData Q.v hvD
  obtain ⟨G, lo, B, U, hlo, hB, hU, hY₀, hr, hm, hs, hbG, he, hGeq⟩ :=
    native_local_metric_production D hζ m slot A hl ρ edge a b hab.le Y₀
  let Cv := fun L => (ocEpsilon D.q D.Λ m ^ (1 + D.α) / D.kap m) * pulseFastDerivativeConstant L
  have hCv L : 0 ≤ Cv L := mul_nonneg
    (div_nonneg (Real.rpow_nonneg
      (Construction.Stream.ocEpsilon_pos (q := D.q) (n := m) hΛ).le _) hν.le)
    (pulseFastDerivativeConstant_nonneg L)
  have hvreg (L : ℕ) (_hL : L ≤ H) (t : ℝ) : ContDiff ℝ (L : ℕ∞) (P.v t) :=
    (normalizedPulseDrift_contDiff hΛ hν hslot t).of_le (by simp)
  have hvb (L : ℕ) (_hL : L ≤ H) (t : ℝ) (j : ℕ) (hj : j ≤ L) (k : Fin 2) (z : Vec 2) :
      ‖iteratedFDeriv ℝ j (fun y => P.v t y k) z‖ ≤ Cv L :=
    normalizedPulseDrift_fast_bound hΛ hν hζ hslot L j hj t z k
  obtain ⟨c, hc, hreg, hreserve⟩ := elliptic_parameter_scalar_inverse_with_reserve hab N K hH hN hK P hvD
    G hr hm hs B hB hbG lo hlo he Qg hg Cv hCv hvreg hvb
  refine ⟨U, c, hU, hY₀, ?_, hreg, hreserve⟩
  intro Y hY
  exact cellFieldInverse_metric_congr_on (fun t => G t Y)
    (fun t => Matrix.of (Q.G t Y)) Q.v N a b 0 (fun t z => g t z Y) (c Y)
    (fun t ht => hGeq t ht Y hY) (hc Y)
end

/-! The exact full inverse recurrence admits a common predecessor cutoff, including its initial array. -/

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H D : ℕ}

theorem weakLiftInverseCoefficients_local_cutoff_reserve (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, weakLiftInverseCoefficients Q inv N p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
            f' t z Y = weakLiftInverseCoefficients Q inv N p q m α t Y z v u 1) :
    ∃ χ : Vec 2 → ℝ, tsupport χ ⊆ Ω ∧ χ =ᶠ[𝓝 Y₀] 1 ∧
      Nonempty (∀ p q, p < hh ∨ (p = hh ∧ q < n) →
        ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u, JointSourceReserve H
          (fun t z Y => fullLiftLocalCutoff χ a b (weakLiftInverseCoefficients Q inv N)
            p q m.val α t Y z v u 1)) := by
  let Cc := weakLiftInverseCoefficients Q inv N
  obtain ⟨χ, hs, hone, ⟨R⟩⟩ := finite_full_lift_local_cutoff_reserves a b hab Ω hΩ Y₀ hYΩ
    Cc N hh n hz hloc
  refine ⟨χ, hs, hone, ⟨?_⟩⟩
  intro p q hpq m α v u
  by_cases hq0 : q = 0
  · subst q
    refine (weakLiftInverseCoefficients_initialReserve H Q inv N p m.val α v u).congrSource ?_
    funext t z Y
    rw [fullLiftLocalCutoff_zero_degree]
  · by_cases hqN : q ≤ N
    · exact R p q hpq (by omega) hqN m.val (by omega) α v u
    · refine (JointSourceReserve.zero H).congrSource ?_
      funext t z Y
      rw [fullLiftLocalCutoff_zero χ a b Cc p q
        (weakLiftInverseCoefficients_cutoff Q inv N p q (by omega))]
      rfl
end

/-! The actual native finite-window scalar inverse is a linear response for every history. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
variable {ι : Type*} {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ}

theorem native_family_window_data (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (a b : ℝ) (Y : Vec 2) :
    ∃ lo hi Mv, Uniqueness.WindowData
      (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v a b lo hi Mv := by
  let Q := familyLiftData D m slot A ρ edge
  obtain ⟨lo, hi, hlo, he⟩ := Providers.GenSem.familyLiftData_pos_window D hζ m slot A ρ edge a b Y
  obtain ⟨Mv, hMv⟩ := Providers.GenSem.familyLiftData_v_bounded D hζ m hslot A ρ edge
  exact ⟨lo, hi, Mv, Uniqueness.windowData_of_elliptic
    (fun t => Matrix.of (Q.G t Y)) Q.v a b lo hi Mv
    (fun t => Providers.GenSem.familyLiftData_symm D m slot A ρ edge t Y 0 1)
    hlo he (fun t _ z => hMv t z)⟩

def nativeWindowResponseLinear (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) :
    (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ) :=
  windowResponseLinear _ _ r hr a b hab
    (native_family_window_data D hζ m slot hslot A ρ edge a b Y).choose_spec.choose_spec.choose_spec

theorem nativeWindowResponseLinear_isInverse (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) (g : ℝ → Vec 2 → ℝ)
    (hg : ∃ c, IsCellFieldInverse
      (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v r a b 0 g c) :
    IsCellFieldInverse (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v r a b 0 g
      (nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y g) :=
  windowResponseLinear_isInverse _ _ r hr a b hab _ ⟨g, hg⟩
end

/-! Native linear responses retain the genuine local reserves produced by the scalar PDE. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift
open scoped ContDiff
variable {ι : Type*} {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm H : ℕ}

theorem native_window_response_on_local_reserve (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (m : ℕ) (hν : 0 < D.kap m) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm hv) (a b : ℝ) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (N K : ℕ) (hrN : r ≤ N) (hH : N + (K + N) + 1 ≤ H) (hN : N + 2 ≤ H) (hK : N + 4 ≤ K)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    {g : ℝ → Vec 2 → Vec 2 → ℝ}
    (hsource : ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H g') ∧
      (∀ t Y, ∫ z in AVenhance.unitCube, g' t z Y = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, g' t z Y = g t z Y) :
    let c := fun Y => nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab.le Y
      (fun t z => g t z Y)
    (∀ Y ∈ Ω, IsCellFieldInverse (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v N a b 0 (fun t z => g t z Y) (c Y)) ∧
    (∀ q, q ≤ N → ∀ t ∈ Icc a b,
      ContDiffOn ℝ (q : ℕ∞) (fun X : Vec 2 × Vec 2 => c X.1 t X.2) {X | X.1 ∈ Ω}) ∧
    ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (c' : Vec 2 → ℝ → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (IndependentParameterSourceReserve N
        (independentTimeWindowSource (Ioc a b) (fun t z Y => c' Y t z))) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, c' Y t z = c Y t z := by
  classical
  let Q := familyLiftData D m slot A ρ edge
  let c := fun Y => nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab.le Y
    (fun t z => g t z Y)
  have hp (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω) : ∃ (U : Set (Vec 2)) (u : Vec 2 → ℝ → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧
      (∀ Y ∈ U, IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v N a b 0
        (fun t z => g t z Y) (u Y)) ∧
      (∀ q, q ≤ N → ∀ t ∈ Icc a b,
        ContDiff ℝ (q : ℕ∞) (fun X : Vec 2 × Vec 2 => u X.1 t X.2)) ∧
      Nonempty (IndependentParameterSourceReserve N
        (independentTimeWindowSource (Ioc a b) (fun t z Y => u Y t z))) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, u Y t z = c Y t z := by
    obtain ⟨U, g', hU, hYU, ⟨Qg⟩, hg, he⟩ := hsource Y₀ hYΩ
    obtain ⟨V, u, hV, hYV, hu, hj, hres⟩ :=
      native_local_parameter_scalar_inverse_with_reserve D hζ hΛ m hν slot hslot A hl
        ρ edge a b hab N K hH hN hK Qg hg Y₀
    let W := Ω ∩ (U ∩ V)
    have huf Y (hY : Y ∈ W) : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v N a b 0
        (fun t z => g t z Y) (u Y) :=
      cellFieldInverse_source_congr_on _ _ N a b 0 (fun t z => g' t z Y)
        (fun t z => g t z Y) (u Y) (fun t ht => funext (he t ht Y hY.2.1)) (hu Y hY.2.2)
    refine ⟨W, u, hΩ.inter (hU.inter hV), ⟨hYΩ, hYU, hYV⟩,
      (fun _ hY => hY.1), huf, hj, hres N (Nat.le_refl N), ?_⟩
    intro t ht Y hY z
    have hur := cellFieldInverse_order_mono _ _ N r hrN a b 0 _ _ (huf Y hY)
    have hc := nativeWindowResponseLinear_isInverse D hζ m slot hslot A ρ edge r hr a b hab.le Y _ ⟨u Y, hur⟩
    obtain ⟨lo, hi, Mv, hW⟩ := native_family_window_data D hζ m slot hslot A ρ edge a b Y
    exact Uniqueness.cellField_unique_window hab.le hW (fun _ _ _ => rfl) hur hc t ht z
  refine ⟨?_, ?_, ?_⟩
  · intro Y hY
    obtain ⟨U, u, _hU, hYU, _hUΩ, hu, _hj, _hres, he⟩ := hp Y hY
    exact cellFieldInverse_field_congr_on _ _ N a b hab.le 0 _ (u Y) (c Y) (hu Y hYU)
      (fun t ht => funext (he t ht Y hYU))
  · intro q hq t ht X hX
    obtain ⟨U, u, hU, hYU, _hUΩ, _hu, hj, _hres, he⟩ := hp X.1 hX
    apply ContDiffAt.contDiffWithinAt
    apply (hj q hq t ht).contDiffAt.congr_of_eventuallyEq
    have hnear : ∀ᶠ Z : Vec 2 × Vec 2 in nhds X, Z.1 ∈ U :=
      continuous_fst.continuousAt.eventually (hU.mem_nhds hYU)
    filter_upwards [hnear] with Z hZ
    exact (he t ht Z.1 hZ Z.2).symm
  · intro Y hY
    obtain ⟨U, u, hU, hYU, hUΩ, _hu, _hj, hres, he⟩ := hp Y hY
    exact ⟨U, u, hU, hYU, hUΩ, hres, he⟩
end

/-! Native linear responses retain actual periodicity, centering and zero initial values. -/

section
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
variable {ι : Type*} {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ}

theorem nativeWindowResponseLinear_periodic (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) (g : ℝ → Vec 2 → ℝ)
    (hg : ∃ c, IsCellFieldInverse
      (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v r a b 0 g c) :
    ∀ t, AVenhance.IsZ2Periodic
      (nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y g t) :=
  fun t => windowResponseLinear_periodic _ _ r hr a b hab _ ⟨g, hg⟩ t

theorem nativeWindowResponseLinear_mean_zero (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) (g : ℝ → Vec 2 → ℝ)
    (hg : ∃ c, IsCellFieldInverse
      (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v r a b 0 g c) :
    ∀ t, (∫ z in AVenhance.unitCube,
      nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y g t z) = 0 :=
  fun t => windowResponseLinear_mean_zero _ _ r hr a b hab _ ⟨g, hg⟩ t

theorem nativeWindowResponseLinear_initial_zero (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) (g : ℝ → Vec 2 → ℝ)
    (hg : ∃ c, IsCellFieldInverse
      (fun t => Matrix.of ((familyLiftData D m slot A ρ edge).G t Y))
      (familyLiftData D m slot A ρ edge).v r a b 0 g c) :
    nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y g a = 0 :=
  windowResponseLinear_initial_zero _ _ r hr a b hab _ ⟨g, hg⟩
end

/-! The canonical linear response depends only on the actual recentered metric and drift. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

theorem windowResponseLinear_data_congr
    (G G' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v v' : ℝ → Vec 2 → Vec 2)
    (hG : G = G') (hv : v = v') (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) {lo hi Mv lo' hi' Mv' : ℝ}
    (hW : Uniqueness.WindowData G v a b lo hi Mv)
    (hW' : Uniqueness.WindowData G' v' a b lo' hi' Mv') :
    windowResponseLinear G v r hr a b hab hW =
      windowResponseLinear G' v' r hr a b hab hW' := by
  subst G'
  subst v'
  rfl

variable {ι : Type*} {hv : ι → Type*}
  [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] {Dm : ℕ}

theorem familyLiftData_geometry_congr (D : OCData) (m : ℕ) (slot : ℤ)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (hg : A.geom D = B.geom D) (ρ : ℝ) (edge : ConstituentEdges Dm hv) :
    familyLiftData D m slot A ρ edge = familyLiftData D m slot B ρ edge := by
  have hmetric : (familyLiftData D m slot A ρ edge).G =
      (familyLiftData D m slot B ρ edge).G := by
    funext t X
    exact congrArg (fun M => fun a c => M a c)
      (realChain_recenter_metric_eq_of_geom_eq D A B hA hB hg (ρ • X) (D.cellScaleSq m * t))
  unfold familyLiftData at hmetric ⊢
  congr 1

theorem nativeWindowResponseLinear_geometry_congr (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A B : RealChain)
    (hA : A.WellSlotted) (hB : B.WellSlotted) (hg : A.geom D = B.geom D)
    (ρ : ℝ) (edge : ConstituentEdges Dm hv) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) :
    nativeWindowResponseLinear D hζ m slot hslot A ρ edge r hr a b hab Y =
      nativeWindowResponseLinear D hζ m slot hslot B ρ edge r hr a b hab Y := by
  unfold nativeWindowResponseLinear
  apply windowResponseLinear_data_congr
  · rw [familyLiftData_geometry_congr D m slot A B hA hB hg ρ edge]
  · rfl
end

/-! A positive full-cell rank step inherits a genuine joint reserve from its primitive forcing. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def weakLiftCoefficientForcing (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (prior : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n m : ℕ)
    (α : DerivativeWord2 m) (v u : ι) : ℝ → Vec 2 → Vec 2 → ℝ :=
  fun t z Y => leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q prior hh n t w)
    m α t Y z v u 1
end

/-! The scalar readout of a positive completed coefficient is its literal inverse response. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_apply_one (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (N hh n m : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (Y z : Vec 2) (v u : ι) :
    weakLiftInverseCoefficients Q inv N hh n m α t Y z v u 1 =
      inv Y (fun s y => weakLiftCoefficientForcing Q (weakLiftInverseCoefficients Q inv N)
        hh n m α v u s y Y) t z := by
  rw [weakLiftInverseCoefficients_eq_full_step Q inv N hh n hn hnN]
  simp only [weakLiftStepWithInverse, ite_eq_right (by omega : n ≠ 0), ite_eq_left hm,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, weakLiftCoefficientForcing]
end

/-! Genuine predecessor reserves produce the positive mean-flux coefficients. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def positiveMeanCoefficientReserve (H : ℕ) (hD : 1 ≤ D) (hDH : D ≤ H)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0) (m : ℕ) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (v u : ι) (k : Fin 2)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ β (σ : Equiv.Perm (Fin m)),
      Cc hh (n - 1) m (β ∘ σ) = Cc hh (n - 1) m β) :
    JointSourceReserve H (fun t z Y => positiveMeanFluxCoefficient Q Cc hh n k m α t Y z v u 1) := by
  have hpre : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hpre2 : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  apply calibratedCoefficientReserve H (n - 1) m hm (positiveMeanFluxCoefficient Q Cc hh n k)
    (positiveMeanFluxCoefficient_intrinsic_perm Q Cc hh n k m hperm) α v u
  intro p
  let A := (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let f := fun Y => Real.exp (A Y) • (Pi.single u (1 : ℝ) : ι → ℝ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  let QA := fun w => fluxFromEarlierReserves H hD Q Cc hh n hn hhpos A w u k QG Qv Qc Qedge
  let QM := normalizedLiftFluxMeanComponentReserve H Q Cc (fun _ => f) hh n A v k QA
  apply QM.congrSource
  funext t z Y
  change (Real.exp (A Y))⁻¹ • fieldCellMean (fun y => liftFluxX Q Cc (fun _ => f) hh n t Y y k) v =
    (Real.exp (A Y))⁻¹ • liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k) (fun _ => f) t Y z v
  congr 1
  symm
  apply positiveMeanFluxCoefficient_literal_apply Q hD Cc hh n hn hhpos f hf k t Y z v
  · intro i j
    exact (((QG i j).regular t).comp₂
      (show ContDiff ℝ (H : ℕ∞) (fun _ : Vec 2 => (0 : Vec 2)) from contDiff_const)
      contDiff_id).of_le
      (by exact_mod_cast (Nat.zero_le H))
  · exact continuous_pi (fun i => (Qv i).fast_contDiff t 0 |>.continuous)
  · exact scalarLift_goodField 1 (n - 1) (Cc hh (n - 1)) f hf
      (fun m α v u => (Qc hh (n - 1) hpre m α v u).mono 2 (by omega)) t
  · exact scalarLift_centField 1 (n - 2) (Cc hh (n - 2)) f hf
      (fun m α v u => (Qc hh (n - 2) hpre2 m α v u).mono 2 (by omega))
      (hmean hh (n - 2) hpre2 (Or.inl hhpos)) t
  · intro m hm α w
    exact (scalarCoefficient_goodField (H + D + 2) m (Cc hh (n - 1)) α v w
      (Qc hh (n - 1) hpre ⟨m, by omega⟩ α v w) t).continuous_slice Y
  · intro j hj m hm α v u
    exact scalarCoefficient_boxSmooth (H + D + 2) j ((D - 1) - j) m (by omega)
      (Cc (hh - 1) (n - 1 - j)) α v u
      (Qc (hh - 1) (n - 1 - j) (Or.inl (by omega)) ⟨m, by omega⟩ α v u) t
  · intro q
    exact scalarLift_goodField D q (Cc (hh - 1) q) f hf
      (fun m α v u => (Qc (hh - 1) q (Or.inl (by omega)) m α v u).mono (2 * D) (by omega)) t
  · intro v u d γ hγ α
    exact ((Qedge v u d γ hγ α).goodField t).mono (by omega)
end

/-! The reserved cutoff source is the literal full-cell forcing on its unit-cutoff germ. -/

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem unit_cutoff_open_neighborhood (χ : Vec 2 → ℝ) (Ω : Set (Vec 2))
    (hΩ : IsOpen Ω) (Y₀ : Vec 2) (hY : Y₀ ∈ Ω) (hχ : χ =ᶠ[𝓝 Y₀] 1) :
    ∃ U : Set (Vec 2), IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ ∀ Y ∈ U, χ Y = 1 := by
  have hh : {Y | Y ∈ Ω ∧ χ Y = 1} ∈ 𝓝 Y₀ :=
    Filter.inter_mem (hΩ.mem_nhds hY) hχ
  obtain ⟨U, hU, ho, hYU⟩ := mem_nhds_iff.mp hh
  exact ⟨U, ho, hYU, fun Y hY => (hU hY).1, fun Y hY => (hU hY).2⟩

theorem fullLiftLocalCutoff_source_germ (U : Set (Vec 2)) (hU : IsOpen U)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (χ : Vec 2 → ℝ)
    (hχ : ∀ Y ∈ U, χ Y = 1) (a b : ℝ) (hh n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Icc a b) (hG : ∀ Y ∈ U, Q.G t Y = Q'.G t Y)
    (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (m : ℕ) (α : DerivativeWord2 m) (Y : Vec 2) (hY : Y ∈ U) (z : Vec 2) (v u : ι) :
    weakLiftCoefficientForcing Q' (fullLiftLocalCutoff χ a b Cc) hh n m α v u t z Y =
      weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
  have he := fullCellSourceCoefficient_slow_local_primitive_congr U hU Q Q' hη hv
    Cc (fullLiftLocalCutoff χ a b Cc) hh n hn t hG hΓ
    (fun p q _ l _ β X hX z v u =>
      (fullLiftLocalCutoff_copy χ a b Cc p q l β t ht X (hχ X hX) z v u).symm)
    m α Y hY z v u
  exact (congrArg (fun L => L (1 : ℝ)) he).symm
end

/-! Both branches of the literal mean flux have reserves produced from predecessor data. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def actualMeanCoefficientReserve (H : ℕ) (hD : 1 ≤ D) (hDH : D ≤ H)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (hn : 2 ≤ n) (m : ℕ) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (v u : ι) (k : Fin 2)
    (QG : ∀ i j, JointSourceReserve H (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve H (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve H (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ β (σ : Equiv.Perm (Fin m)),
      Cc hh (n - 1) m (β ∘ σ) = Cc hh (n - 1) m β) :
    JointSourceReserve H (fun t z Y => actualMeanFluxCoefficient Q Cc hh n k m α t Y z v u 1) := by
  by_cases hh0 : hh = 0
  · subst hh
    have hpre : 0 < 0 ∨ (0 = 0 ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
    apply (diagonalMeanCoefficientReserve H Q Cc n k m α v u QG (Qv k)
      ((Qc 0 (n - 1) hpre ⟨m, by omega⟩ α v u).mono H (by omega))).congrSource
    funext t z Y
    simp only [actualMeanFluxCoefficient, ite_true]
  · apply (positiveMeanCoefficientReserve H hD hDH Q Cc hh n hn hh0 m hm α v u k
      QG Qv Qc Qedge hmean hperm).congrSource
    funext t z Y
    simp only [actualMeanFluxCoefficient, ite_eq_right hh0]
end

end AVRegularity.WeakEntryProofs
end
end
end

section
@[expose] public noncomputable section

section
namespace AVRegularity.WeakEntryProofs

/-! A single positive total controls both matrices and the priced marked ledger after rerooting. -/

open Homogenization AVRegularity.Construction.Preservation.Ledger
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Empty histories make every encoded marker exactly one. -/
theorem weakEncoding_marker (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι) (law : BirthLaw) :
    ∀ v, Gw.marker law v = 1 := by
  intro v'
  obtain ⟨v, rfl⟩ := ι.surjective v'
  simp only [GenStage.marker, compMarker, compBirthSet, he.2.1 v, List.map_nil,
    List.toFinset_nil, Finset.prod_empty]

/-- Bound the complete record matrix by the stored total and the actual common size factor. -/
theorem weakEncoding_majorant_total (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι) (law : BirthLaw) (hm : law.rootMass = rootM)
    (Cθ : ℝ) (hCθ : 1 ≤ Cθ)
    (e : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (ι v) (ι u))
    (hmap' : ∀ v u (γ : G.fam.Γ v u),
      (Gw.fam.identity (ι v) (ι u) (e v u γ)).map = (G.fam.identity v u γ).map)
    (hsize : ∀ v u (γ : G.fam.Γ v u),
      (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.size = Cθ * (G.fam.identity v u γ).record.size)
    (hmap : ∀ v u (γ : G.fam.Γ v u), ‖(G.fam.identity v u γ).map‖ ≤ 1) :
    (∑ v, ∑ u, recordMajorant (Gw.mass law) Gw.fam v u) ≤ Cθ * weakStoredTotal G N J η := by
  rw [← ι.sum_comp]
  conv_lhs => arg 2; ext v; rw [← ι.sum_comp]
  have hpoint (v u : CompIn G.comps) :
      recordMajorant (Gw.mass law) Gw.fam (ι v) (ι u) ≤
        Cθ * ∑ γ : G.fam.Γ v u, weakStoredEdgeWeight G N J η ⟨v, u, γ⟩ := by
    unfold recordMajorant
    rw [weakEncoding_mass N J η rootM rootR G Gw ι he law hm u,
      weakEncoding_mass N J η rootM rootR G Gw ι he law hm v, ← (e v u).sum_comp]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ _
    have hm' := hmap' v u γ
    have hs' := hsize v u γ
    rw [hm', hs']
    change _ ≤ Cθ * (Real.sqrt _ * _)
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmap v u γ)
      (mul_nonneg (zero_lt_one.trans_le hCθ).le (G.fam.identity v u γ).record.size_nonneg))
      (Real.sqrt_nonneg (weakMass D N J η u.1 / weakMass D N J η v.1))
    simpa only [one_mul, mul_assoc, mul_left_comm] using hh
  calc
    _ ≤ ∑ v, ∑ u, Cθ * ∑ γ : G.fam.Γ v u, weakStoredEdgeWeight G N J η ⟨v, u, γ⟩ :=
      Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun u _ => hpoint v u))
    _ = _ := by simp only [← Finset.mul_sum, weakStoredTotal, LedgerEdge, Fintype.sum_sigma]

/-- At unit markers and unit prices, a full positive sum is a budget for every ledger clause. -/
theorem weakMajorantBudget_of_total (G : GenStage D ScalarH Dm b j₀) (law : BirthLaw)
    (S : ℝ) (hS : 0 ≤ S) (hm : ∀ v, G.marker law v = 1)
    (hp : ∀ v u (γ : G.fam.Γ v u), constituentPrice (G.fam.identity v u γ).record = 1)
    (hs : (∑ v, ∑ u, recordMajorant (G.mass law) G.fam v u) ≤ S) :
    Assembly.WeakMajorantBudget G law S := by
  classical
  have hn (v u : CompIn G.comps) : 0 ≤ recordMajorant (G.mass law) G.fam v u := by
    unfold recordMajorant
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (G.fam.identity v u γ).record.size_nonneg)
  have hr (v : CompIn G.comps) : (∑ u, recordMajorant (G.mass law) G.fam v u) ≤ S :=
    (Finset.single_le_sum (fun v _ => Finset.sum_nonneg fun u _ => hn v u)
      (Finset.mem_univ v)).trans hs
  have hc (u : CompIn G.comps) : (∑ v, recordMajorant (G.mass law) G.fam v u) ≤ S := by
    have hh : (∑ v, recordMajorant (G.mass law) G.fam v u) ≤
        ∑ u, ∑ v, recordMajorant (G.mass law) G.fam v u :=
      Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun v _ => hn v u)
        (Finset.mem_univ u)
    rw [Finset.sum_comm] at hh
    exact hh.trans hs
  have hprice (m : CompIn G.comps → ℝ) (hm' : ∀ v, m v = 1) :
      pricedRecordMajorant (G.mass law) m G.fam = recordMajorant (G.mass law) G.fam := by
    funext v u
    simp only [pricedRecordMajorant, recordMajorant, hm', one_div_one, one_mul, hp, mul_one]
  have hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S := by
    unfold markedLedger
    rw [hprice _ (fun _ => rfl), hprice _ hm, max_self]
    exact fullLedger_le_of_schur hS ⟨hr, hc⟩
  refine ⟨hn, hr, hc, ?_, ?_, ?_, hledger⟩
  · intro v u; simpa only [hm, one_div_one, one_mul] using hn v u
  · intro v; simpa only [hm, one_div_one, one_mul] using hr v
  · intro u; simpa only [hm, one_div_one, one_mul] using hc u

end AVRegularity.WeakEntryProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.WeakEntryProofs.ReadoutLinear

/-! **One level of the weak readout, linearity and regularity**.

For the weak readout level `i`, built from `weakReadoutStep` and `weakGluedLift`:
* `readoutLinear_step_add_smul`, `readoutLinear_step_contDiff`: the readout step is a finite sum
  with constant weights, so it is additive, homogeneous and keeps the class `C^k`;
* `readoutLinear_lift_add_smul`: the glued lift is additive and homogeneous on `C^N` inputs
  (`gluedLift_add_input`, `labelLift_smul_input`);
* `readoutLinear_lift_contDiff`: the glued lift of a `C^{r+N}` input is `C^r` at a time `t` where
  the coefficients of every pulse with nonzero cutoff are box smooth of order `r`
  (`IsWeakReadoutLifts`, orders `sX, sZ ≥ r`).

Special cases: `r = 0` (continuity only), `c = 0` (the lift of `g₁ + 0 • g₂` is the lift of `g₁`),
a time with no observed pulse (`kset = ∅`, both sides `0`). -/

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The glued lift is homogeneous in its input at a time where the input is of class `C^N`. -/
theorem readoutLinear_gluedLift_smul_input (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) {c : ℝ}
    (hc : c ≠ 0) (ρ e εc : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) {t : ℝ}
    (hχ : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (a : ℝ → Vec 2 → ∀ i, h i) (ha : ContDiff ℝ (N : ℕ∞) (a t)) (κ : ℝ) (x : Vec 2) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label (fun s y => κ • a s y) t x =
      κ • gluedLift kset ϖ c ρ e εc N H Cc chart label a t x := by
  simp only [gluedLift, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hA : ContDiff ℝ (N : ℕ∞)
      ((fun s X => a (c * s) (chart k (c * s) (ρ • X))) (c⁻¹ * t)) :=
    contDiff_chartFrame a (chart k) hc ha ((hχ k hk).of_le (by exact_mod_cast le_top)) ρ
  have h1 := labelLift_smul_input (Cc k) N H εc κ
    (fun s X => a (c * s) (chart k (c * s) (ρ • X))) ρ e c t hA (label k t x)
  rw [smul_comm]
  congr 1

end Generic

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The readout step is additive and homogeneous. -/
theorem readoutLinear_step_add_smul (i : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (g₁ g₂ : CompIn G'.comps → Vec 2 → ℝ) (c : ℝ) :
    weakReadoutStep i η₀ G G' (fun v y => g₁ v y + c • g₂ v y) =
      fun v y => weakReadoutStep i η₀ G G' g₁ v y + c • weakReadoutStep i η₀ G G' g₂ v y := by
  funext v y
  simp only [weakReadoutStep, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v' _ => ?_
  split_ifs <;> ring

open scoped Classical in
/-- The readout step keeps the class `C^k`. -/
theorem readoutLinear_step_contDiff (i : ℕ) (η₀ : ℝ) (G G' : GenStage D ScalarH Dm b j₀)
    (g : CompIn G'.comps → Vec 2 → ℝ) {k : ℕ∞} (hg : ∀ v, ContDiff ℝ k (g v)) (v : CompIn G.comps) :
    ContDiff ℝ k (weakReadoutStep i η₀ G G' g v) := by
  have : weakReadoutStep i η₀ G G' g v = fun x => ∑ v' : CompIn G'.comps,
      if compParent i v'.1 = v.1 then (D.eps (i - 1) ^ η₀) ^ (compWord i v'.1).length * g v' x
        else 0 := rfl
  rw [this]
  refine ContDiff.sum fun v' _ => ?_
  split_ifs
  · exact contDiff_const.mul (hg v')
  · exact contDiff_const

variable (G : GenStage D ScalarH Dm b j₀) (i N depth : ℕ)
  (CcR : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) (t : ℝ)

/-- The glued weak lift is additive and homogeneous on `C^N` inputs. -/
theorem readoutLinear_lift_add_smul (hc : D.cellScaleSq i ≠ 0)
    (g₁ g₂ : CompIn G.comps → Vec 2 → ℝ) (c : ℝ)
    (h₁ : ∀ v, ContDiff ℝ (N : ℕ∞) (g₁ v)) (h₂ : ∀ v, ContDiff ℝ (N : ℕ∞) (g₂ v)) :
    weakGluedLift i N depth G CcR t (fun v y => g₁ v y + c • g₂ v y) =
      fun v y => weakGluedLift i N depth G CcR t g₁ v y +
        c • weakGluedLift i N depth G CcR t g₂ v y := by
  funext v x
  have hχ : ∀ k ∈ ocObsPulses D.α D.q D.Λ i t t, ContDiff ℝ (⊤ : ℕ∞)
      ((fun (k : ℤ) (s' : ℝ) (y : Vec 2) => D.flowOf (i - 1) s' y (D.slotAnchor i k)) k t) :=
    fun k _ => Providers.QuietAtlas.flowOf_contDiff D (i - 1) t (D.slotAnchor i k)
  have e1 := gluedLift_add_input (ocObsPulses D.α D.q D.Λ i t t)
    (fun k => ocCutoff D.α D.q D.Λ i k) hc (D.eps (i - 1)) (D.eps i)
    (D.eps i / D.eps (i - 1)) N depth CcR
    (fun k s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
    (fun k s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s') hχ
    (fun _ y w => g₁ w y) (fun _ y w => c • g₂ w y)
    (contDiff_pi.2 h₁) (contDiff_pi.2 fun w =>
      (show ContDiff ℝ (N : ℕ∞) (fun y => c • g₂ w y) from (h₂ w).const_smul c)) x
  have e2 := readoutLinear_gluedLift_smul_input (ocObsPulses D.α D.q D.Λ i t t)
    (fun k => ocCutoff D.α D.q D.Λ i k) hc (D.eps (i - 1)) (D.eps i)
    (D.eps i / D.eps (i - 1)) N depth CcR
    (fun k s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
    (fun k s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s') hχ
    (fun _ y w => g₂ w y) (contDiff_pi.2 h₂) c x
  exact (congrFun e1 v).trans (congrArg₂ (· + ·) rfl (congrFun e2 v))

variable {sX sZ : ℕ}

/-- **The glued weak lift of a `C^{r+N}` field is `C^r`**, when the lift coefficients of the level
are box smooth of order `sX, sZ ≥ r` on the pulse windows. -/
theorem readoutLinear_lift_contDiff (r : ℕ) (hc : 0 < D.cellScaleSq i)
    (hτ : 0 < ocTau D.α D.q D.Λ i) (hl : IsWeakReadoutLifts i N depth sX sZ G CcR)
    (hrX : r ≤ sX) (hrZ : r ≤ sZ)
    (g : CompIn G.comps → Vec 2 → ℝ) (hg : ∀ v, ContDiff ℝ ((r + N : ℕ) : ℕ∞) (g v))
    (v : CompIn G.comps) :
    ContDiff ℝ (r : ℕ∞) (weakGluedLift i N depth G CcR t g v) := by
  have hglue := gluedLift_contDiff_of_weighted (ocObsPulses D.α D.q D.Λ i t t)
    (fun k => ocCutoff D.α D.q D.Λ i k) (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
    (D.eps i / D.eps (i - 1)) N depth CcR
    (fun k s' y => D.flowOf (i - 1) s' y (D.slotAnchor i k))
    (fun k s' y => D.flowOf (i - 1) (D.slotAnchor i k) y s')
    (fun _ y w => g w y) t (J := r) ?_
  · exact contDiff_pi.1 hglue v
  intro k hk hcut
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  have hwin := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have hcell : (D.cellScaleSq i)⁻¹ * t ∈
      Set.Icc (D.slotStart i k / D.cellScaleSq i)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) := by
    rw [← div_eq_inv_mul]
    exact ⟨(div_le_div_iff_of_pos_right hc).mpr hwin.1,
      (div_le_div_iff_of_pos_right hc).mpr hwin.2⟩
  refine contDiff_pi.2 fun w => ?_
  rw [Construction.Preservation.FullLift.pulsePhysicalLift_freeze_time]
  refine Construction.Preservation.FullLift.pulsePhysicalLift_static_contDiff_of_boxes
    (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) N depth r
    (CcR k) (fun y => D.flowOf (i - 1) (D.cellScaleSq i * ((D.cellScaleSq i)⁻¹ * t)) y
      (D.slotAnchor i k))
    (fun y => D.flowOf (i - 1) (D.slotAnchor i k) y t) (fun y w => g w y) t
    (contDiff_pi.2 hg) ?_ ?_ ?_ w
  · exact (Providers.QuietAtlas.flowOf_contDiff D (i - 1) _ _).of_le (by exact_mod_cast le_top)
  · exact (Providers.QuietAtlas.flowOf_contDiff D (i - 1) _ _).of_le (by exact_mod_cast le_top)
  · intro hh hhH n _ m _ α v' u'
    exact (((hl k hodd) |>.2.2.2.2.2.1 hh hhH n m α v' u' _ hcell).1).mono hrX hrZ

end AVRegularity.WeakEntryProofs.ReadoutLinear
end
end
end

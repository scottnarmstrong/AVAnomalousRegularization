-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.NativeMixedChartBudget
import Mathlib.Algebra.Order.Star.Real

section
section
/-! The exact triangular parameter difference equations produce uniform higher quotient carriers. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

theorem uniform_word_difference_higher_carrier_exists {Y I : Type*}
    {a b : ℝ} (hab : a < b) (N Hmax : ℕ) (P : Y → MolecularData)
    (G H : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hP : ∀ y, dataCoefficients (P y) = ⟨fun t _ => G y [] t, (P y).v, 0, 0⟩)
    (f g : Y → List I → ℝ → Vec 2 → ℂ)
    (F F' : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (D E : Y → List I → ℝ → RawJet2 1 ℂ) (r : Y → ℝ)
    (hGsym : ∀ y t, (G y [] t).IsSymm) (hHsym : ∀ y t, (H y [] t).IsSymm)
    (hD : ∀ y (α : List I), α.length ≤ N →
      IsCellInverseValue (dataCoefficients (P y)) (f y α)
        (F y α + independentWordMetricFlux (fun β t _ => G y β t) (D y) α) (D y α))
    (hE : ∀ y (α : List I), α.length ≤ N →
      IsCellInverseValue ⟨fun t _ => H y [] t, (P y).v, 0, 0⟩ (g y α)
        (F' y α + independentWordMetricFlux (fun β t _ => H y β t) (E y) α) (E y α))
    (V : ∀ y K, K ≤ Hmax → MolecularFiniteDriftBudget (P y) K)
    (Q : ∀ y (α : List I), α.length ≤ N → ∀ K, K ≤ Hmax →
      HigherSourceCarrierData (Icc a b) K (r y • (g y α - f y α)) (r y • (F' y α - F y α)))
    (Ns Nf : List I → ℕ → ℝ)
    (hNs : ∀ α K, 0 ≤ Ns α K) (hNf : ∀ α K, 0 ≤ Nf α K)
    (hQs : ∀ y α hα K hK, (Q y α hα K hK).Ns ≤ Ns α K)
    (hQf : ∀ y α hα K hK, (Q y α hα K hK).Nf ≤ Nf α K)
    (B Bδ : List I → ℝ)
    (hB : ∀ α : List I, α.length ≤ N → 0 ≤ B α)
    (hBδ : ∀ α : List I, α.length ≤ N → 0 ≤ Bδ α)
    (hb : ∀ y (α : List I), α.length ≤ N → ∀ t i j, |G y α t i j| ≤ B α)
    (hm : ∀ y (α : List I), α.length ≤ N → ∀ i j, Measurable (fun t => G y α t i j))
    (hbδ : ∀ y (α : List I), α.length ≤ N → ∀ t i j,
      |r y * (H y α t i j - G y α t i j)| ≤ Bδ α)
    (hmδ : ∀ y (α : List I), α.length ≤ N → ∀ i j,
      Measurable (fun t => r y * (H y α t i j - G y α t i j)))
    (hcarrier : ∀ α : List I, α.length ≤ N → ∀ K, K ≤ Hmax + 1 →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ w : ℝ → TorusHk K ℂ,
        StronglyMeasurable w ∧ (∀ t, ‖w t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (E y α) t)
    (hiD : ∀ y (α : List I), α.length ≤ N → cellValue (D y α) a =ᵐ[
      volume.restrict AVenhance.unitCube] 0)
    (hiE : ∀ y (α : List I), α.length ≤ N → cellValue (E y α) a =ᵐ[
      volume.restrict AVenhance.unitCube] 0)
    (α : List I) (hα : α.length ≤ N) (K : ℕ) (hK : K + α.length ≤ Hmax) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ w : ℝ → TorusHk K ℂ,
      StronglyMeasurable w ∧ (∀ t, ‖w t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (r y • (E y α - D y α)) t := by
  let A := fun y β t => r y • (H y β t - G y β t)
  let q := fun y β => r y • (E y β - D y β)
  let src := fun y β => r y • (g y β - f y β)
  let flux := fun y β => (r y • (F' y β - F y β) +
    independentWordMetricFlux (fun γ t _ => A y γ t) (E y) β) +
      cellMetricFlux (fun t _ => A y [] t) (E y β)
  have hAb (y : Y) (β : List I) (hβ : β.length ≤ N) :
      ∀ t i j, |A y β t i j| ≤ Bδ β := hbδ y β hβ
  have hAm (y : Y) (β : List I) (hβ : β.length ≤ N) :
      ∀ i j, Measurable (fun t => A y β t i j) := hmδ y β hβ
  have hprod (β : List I) (hβ : β.length ≤ N) (L : ℕ) (hL : L ≤ Hmax) :
      ∃ Rs Rf : ℝ, 0 ≤ Rs ∧ 0 ≤ Rf ∧ ∀ y,
        ∃ Q' : HigherSourceCarrierData (Icc a b) L (src y β) (flux y β),
          Q'.Ns ≤ Rs ∧ Q'.Nf ≤ Rf := by
    exact uniform_word_perturbed_higher_source_exists a b N L A E
      (fun y => ⟨fun t _ => H y [] t, (P y).v, 0, 0⟩) g
      (fun y γ => F' y γ + independentWordMetricFlux (fun δ t _ => H y δ t) (E y) γ)
      hE Bδ hBδ hAb hAm β hβ
      (fun γ hγ => hcarrier γ (by omega) (L + 1) (by omega))
      (fun y => src y β) (fun y => r y • (F' y β - F y β))
      (fun y => Q y β hβ L hL) (Ns β L) (Nf β L) (hNs β L) (hNf β L)
      (fun y => hQs y β hβ L hL) (fun y => hQf y β hβ L hL)
  obtain ⟨Rs, Rf, hRs, hRf, Q', hQ's, hQ'f⟩ :=
    uniform_word_higher_source_selection (Icc a b) N Hmax src flux
      (fun β hβ L hL => hprod β hβ L (by omega))
  have hq (y : Y) (β : List I) (hβ : β.length ≤ N) :
      IsCellInverseValue (dataCoefficients (P y)) (src y β)
        (flux y β + independentWordMetricFlux (fun γ t _ => G y γ t) (q y) β) (q y β) :=
    independent_word_difference_time_inverse_value (P y) (G y) (H y) (hP y)
      (f y) (g y) (F y) (F' y) (D y) (E y) β (r y)
      (hGsym y) (hHsym y) (hD y β hβ) (hE y β hβ)
  apply uniform_word_higher_carrier_of_initial_zero hab N Hmax P G src flux q V Q'
    Rs Rf hRs hRf hQ's hQ'f B hB hb hm hq
  · intro y β hβ
    filter_upwards [hiD y β hβ, hiE y β hβ] with z hzD hzE
    change r y • (E y β a (valueIndex2 1) z - D y β a (valueIndex2 1) z) = 0
    simp only [cellValue] at hzD hzE
    rw [hzD, hzE, sub_self, smul_zero]
  · exact hα
  · exact hK

end AVRegularity.EntryWeakProofs
end
end

section
/-! Lower scalar coefficients produce the full independent centered source and its ordered corrections. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentLiftCoefficientCellSource
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (out inp : ι) : ℝ → Vec 2 → Vec d → ℝ :=
  independentCenteredRecurrenceSource hh n
    (independentLiftCoefficientASource edge a L A η G v c hh n out inp)
    (fun j p => independentLiftMeanCompositionSource j (c p.1 j) L A
      (fun t z Y w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z Y) out)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal coefficient tests, lift forcing and mean correction preserve primitive translations. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [NormedSpace ℝ P] in
theorem independentScalarLiftTestSource_translation_invariant
    (δ : P) (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hc : ∀ m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c m α t z Y v u))
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    IndependentSourceTranslationInvariant δ (independentScalarLiftTestSource n c A v u) := by
  intro t z Y
  have he : independentScalarCoefficientLift c (Y + δ) = independentScalarCoefficientLift c Y := by
    funext m α τ X w v' u'
    dsimp only [independentScalarCoefficientLift]
    exact congrArg (fun a : ℝ => a • ContinuousLinearMap.id ℝ ℝ) (hc m α v' u' τ w Y)
  dsimp only [independentScalarLiftTestSource]
  rw [he]

omit [DecidableEq ι] in
theorem independentLiftASource_translation_invariant
    (δ : P) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (ha : ∀ v u d γ, γ ∈ edge v u d → ∀ α, IndependentSourceTranslationInvariant δ (a v u d γ α))
    (hF : ∀ p q u, IndependentSourceTranslationInvariant δ (fun t z Y => F p q t z Y u))
    (hh n : ℕ) (out : ι) :
    IndependentSourceTranslationInvariant δ (independentLiftASource edge a L A η G v F hh n out) := by
  intro t z Y
  have h1 := independentNormalizedCellB1Source_translation_invariant δ L A η G v _ hG (hF hh (n - 1) out) t z Y
  have h2 := independentNormalizedCellB2Source_translation_invariant δ L A η G _ hG (hF hh (n - 2) out) t z Y
  have hs j := independentSourceComponentArray_translation_invariant δ edge a L A η
    (F (hh - 1) (n - j)) ha (hF (hh - 1) (n - j)) j out t z Y
  dsimp only [independentLiftASource]
  rw [h1, h2]
  simp_rw [hs]

omit [DecidableEq ι] in
theorem independentLiftApplySource_translation_invariant {d : ℕ}
    (δ : Vec d) (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hc : ∀ m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c m α t z Y v u))
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec d → ι → ℝ)
    (hf : ∀ u t Y, f t (Y + δ) u = f t Y u) (v : ι) :
    IndependentSourceTranslationInvariant δ (independentLiftApplySource n c L A f v) := by
  intro t z Y
  have hw u := IndependentSourceTranslationInvariant.covariantWord
    (show IndependentSourceTranslationInvariant δ (fun t (_ : Vec 2) Y => f t Y u) from
      fun t _ Y => hf u t Y) L A
  dsimp only [independentLiftApplySource]
  simp_rw [hc _ _ _ _ t z Y, hw _ _ _ t z Y]

omit [DecidableEq ι] in
theorem independentLiftMeanCompositionSource_translation_invariant {d : ℕ}
    (δ : Vec d) (j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hc : ∀ m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c m α t z Y v u))
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ)
    (hF : ∀ u, IndependentSourceTranslationInvariant δ (fun t z Y => F t z Y u)) (v : ι) :
    IndependentSourceTranslationInvariant δ (independentLiftMeanCompositionSource j c L A F v) := by
  exact independentLiftApplySource_translation_invariant δ j c hc L A _
    (fun u t Y => (hF u).cellMean t 0 Y) v

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier centered coefficients give the literal mean-zero condition for inverse production. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_cell_source_from_centered_earlier_coefficients_mean_zero (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + 2 * D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + D + 1) (a v u e γ α)) :
    ∀ (_hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u t Y,
      fieldCellMean (fun z => c p q m.val α t z Y v u) = 0) (t : ℝ) (Y : Vec d),
    fieldCellMean (fun z => independentLiftCoefficientCellSource edge a L A η G v c hh n out inp t z Y) = 0 := by
  intro hmean t Y
  let QA := independentLiftAFromEarlierCoefficients H edge a L hL A η G v c hh n hn out inp
    (fun i j => (QG i j).restrictOrder (H + 1) (by omega))
    (fun i => (Qv i).restrictOrder H (by omega))
    (fun p q hpq m α v u => (Qc p q hpq m α v u).restrictOrder (H + D + 2) (by omega))
    (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + 1) (by omega))
  have QT j (hj : j ∈ Finset.Icc 1 (n - 2)) (p : ℕ × ℕ)
      (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      IndependentParameterSourceReserve H (independentLiftMeanCompositionSource j (c p.1 j) L A
        (fun t z Y w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z Y) out) := by
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
      by_cases hlt : p.1 < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
    let QC := fun m α w => (Qc p.1 j hpre m α out w).restrictOrder H (by omega)
    have hmeanPre (r s : ℕ) (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
        r < hh ∨ (r = hh ∧ s < n) := by
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hlt : r < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩
    let QM := fun w => independentLiftAFromEarlierCoefficients (H + j) edge a L hL A η G v c
      p.2 (n - j) (by omega) w inp
      (fun i k => (QG i k).restrictOrder (H + j + 1) (by omega))
      (fun i => (Qv i).restrictOrder (H + j) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).restrictOrder
        ((H + j) + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + j + 1) (by omega))
    exact independentLiftMeanCompositionSourceReserve H j (c p.1 j) L hL A _ out QC QM
  apply independent_centered_recurrence_mean_zero hh n _ _ QA QT _ t Y
  intro j hj p hp t Y
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
    by_cases hlt : p.1 < hh
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩
  exact independent_lift_mean_composition_mean_zero j (c p.1 j) L A _ out
    (fun m α u => (Qc p.1 j hpre m α out u).restrictOrder H (by omega))
    (fun m α u => hmean p.1 j hpre (by omega) m α out u) t Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! The next lift forcing is determined by primitive and predecessor germs on an open slow slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} {U : Set (Vec 2)}

theorem independentLiftCoefficientASource_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c e : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve 1 (fun t _ W => G t W i j))
    (QG' : ∀ i j, IndependentParameterSourceReserve 1 (fun t _ W => G' t W i j))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
        IndependentParameterSourceReserve (D + 2) (fun t z W => c p q m.val α t z W u inp))
    (Qe : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
        IndependentParameterSourceReserve (D + 2) (fun t z W => e p q m.val α t z W u inp))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve 1 (a v u e γ α))
    (Qb : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve 1 (b v u e γ α))
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn L U Y Z (a v u e γ α) (b v u e γ α))
    (hc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m α v u,
      IndependentSourceSlowSliceEqOn L U Y Z
        (fun t z W => c p q m α t z W v u) (fun t z W => e p q m α t z W v u)) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentLiftCoefficientASource edge a L A η G v c hh n out inp)
      (independentLiftCoefficientASource edge b L A η G' v e hh n out inp) := by
  let F := fun p q t z W u => independentScalarLiftTestSource q (c p q) A u inp t z W
  let F' := fun p q t z W u => independentScalarLiftTestSource q (e p q) A u inp t z W
  have QF p q (hpq : p < hh ∨ (p = hh ∧ q < n)) u :
      IndependentParameterSourceReserve (D + 2) (fun t z W => F p q t z W u) :=
    independentScalarLiftTestSourceReserve (D + 2) q (c p q) A u inp
      (fun m α => Qc p q hpq m α u)
  have QF' p q (hpq : p < hh ∨ (p = hh ∧ q < n)) u :
      IndependentParameterSourceReserve (D + 2) (fun t z W => F' p q t z W u) :=
    independentScalarLiftTestSourceReserve (D + 2) q (e p q) A u inp
      (fun m α => Qe p q hpq m α u)
  exact independentLiftASource_slow_slice_congr edge a b L hL Y Z A η G G' v
    F F' hh n hn out QG QG' QF QF' Qa Qb hU hG ha
    (fun p q hpq u => independentScalarLiftTestSource_slow_slice_congr L Y Z q
      (c p q) (e p q) (hc p q hpq) A u inp)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every ordered mean correction and centered inverse forcing respects stored translations. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCoefficientASource_translation_invariant
    (δ : Vec d) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α, IndependentSourceTranslationInvariant δ (a v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c p q m α t z Y v u))
    (hh n : ℕ) (out inp : ι) :
    IndependentSourceTranslationInvariant δ (independentLiftCoefficientASource edge a L A η G v c hh n out inp) := by
  exact independentLiftASource_translation_invariant δ edge a L A η G v _ hG ha
    (fun p q u => independentScalarLiftTestSource_translation_invariant δ q (c p q) (hc p q) A u inp) hh n out

theorem independentLiftCoefficientCellSource_translation_invariant
    (δ : Vec d) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α, IndependentSourceTranslationInvariant δ (a v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c p q m α t z Y v u))
    (hh n : ℕ) (out inp : ι) :
    IndependentSourceTranslationInvariant δ (independentLiftCoefficientCellSource edge a L A η G v c hh n out inp) := by
  have hA (p q : ℕ) (w : ι) := independentLiftCoefficientASource_translation_invariant
    δ edge a L A η G v c hG ha hc p q w inp
  have hT (j : ℕ) (p : ℕ × ℕ) := independentLiftMeanCompositionSource_translation_invariant
    δ j (c p.1 j) (hc p.1 j) L A
    (fun t z Y w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z Y)
    (hA p.2 (n - j)) out
  intro t z Y
  dsimp only [independentLiftCoefficientCellSource, independentCenteredRecurrenceSource]
  have hmean := (hA hh n out).cellMean t 0 Y
  dsimp only at hmean
  rw [hA hh n out t z Y, hmean]
  apply congrArg (fun w : ℝ => -(independentLiftCoefficientASource edge a L A η G v c hh n out inp t z Y -
    fieldCellMean (fun w => independentLiftCoefficientASource edge a L A η G v c hh n out inp t w Y)) + w)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  exact hT j p t z Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! The next lift forcing is determined by primitive and predecessor germs on an open slow slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} {U : Set (Vec 2)}

theorem independentLiftCoefficientCellSource_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (Y Z : Vec d)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c e : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (D + 1) (fun t _ W => G t W i j))
    (QG' : ∀ i j, IndependentParameterSourceReserve (D + 1) (fun t _ W => G' t W i j))
    (Qv : ∀ i, IndependentParameterSourceReserve D (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
        IndependentParameterSourceReserve (2 * D + 2) (fun t z W => c p q m.val α t z W v u))
    (Qe : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
        IndependentParameterSourceReserve (2 * D + 2) (fun t z W => e p q m.val α t z W v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (D + 1) (a v u e γ α))
    (Qb : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (D + 1) (b v u e γ α))
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn L U Y Z (a v u e γ α) (b v u e γ α))
    (hc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m α v u,
      IndependentSourceSlowSliceEqOn L U Y Z
        (fun t z W => c p q m α t z W v u) (fun t z W => e p q m α t z W v u)) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentLiftCoefficientCellSource edge a L A η G v c hh n out inp)
      (independentLiftCoefficientCellSource edge b L A η G' v e hh n out inp) := by
  have hA p q (hpq : p ≤ hh) (hq : 1 ≤ q) (hqn : q ≤ n) w :
      IndependentSourceSlowSliceEqOn L U Y Z
        (independentLiftCoefficientASource edge a L A η G v c p q w inp)
        (independentLiftCoefficientASource edge b L A η G' v e p q w inp) := by
    have hpre r s (hrs : r < p ∨ (r = p ∧ s < q)) :
        r < hh ∨ (r = hh ∧ s < n) := by
      rcases hrs with hrs | ⟨hrp, hs⟩
      · exact Or.inl (by omega)
      · by_cases hp : r < hh
        · exact Or.inl hp
        · exact Or.inr ⟨by omega, by omega⟩
    exact independentLiftCoefficientASource_slow_slice_congr edge a b L hL Y Z A η G G' v
      c e p q hq w inp
      (fun i j => (QG i j).restrictOrder 1 (by omega))
      (fun i j => (QG' i j).restrictOrder 1 (by omega))
      (fun r s hrs m α u => (Qc r s (hpre r s hrs) m α u inp).restrictOrder (D + 2) (by omega))
      (fun r s hrs m α u => (Qe r s (hpre r s hrs) m α u inp).restrictOrder (D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder 1 (by omega))
      (fun v u e γ hγ α => (Qb v u e γ hγ α).restrictOrder 1 (by omega))
      hU hG ha (fun r s hrs => hc r s (hpre r s hrs))
  intro t X hX z
  dsimp only [independentLiftCoefficientCellSource, independentCenteredRecurrenceSource]
  have hmain := hA hh n le_rfl hn le_rfl out t X hX z
  have hmean : fieldCellMean (fun w => independentLiftCoefficientASource edge a L A η G v c hh n out inp t w (L X + Y)) =
      fieldCellMean (fun w => independentLiftCoefficientASource edge b L A η G' v e hh n out inp t w (L X + Z)) := by
    congr 1
    funext w
    exact hA hh n le_rfl hn le_rfl out t X hX w
  rw [hmain, hmean]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
    by_cases hlt : p.1 < hh
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩
  have hnsub : 1 ≤ n - j := by omega
  have hprior r s (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
      r < hh ∨ (r = hh ∧ s < n) := by
    rcases hrs with hrs | ⟨rfl, hs⟩
    · exact Or.inl (by omega)
    · by_cases hlt : p.2 < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
  let FC := fun t z W w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z W
  let FE := fun t z W w => independentLiftCoefficientASource edge b L A η G' v e p.2 (n - j) w inp t z W
  have QC w : IndependentParameterSourceReserve D (fun t z W => FC t z W w) :=
    independentLiftAFromEarlierCoefficients D edge a L hL A η G v c p.2 (n - j) hnsub w inp
      QG Qv
      (fun r s hrs m α v u => (Qc r s (hprior r s hrs) m α v u).restrictOrder (D + D + 2) (by omega)) Qa
  have QE w : IndependentParameterSourceReserve D (fun t z W => FE t z W w) :=
    independentLiftAFromEarlierCoefficients D edge b L hL A η G' v e p.2 (n - j) hnsub w inp
      QG' Qv
      (fun r s hrs m α v u => (Qe r s (hprior r s hrs) m α v u).restrictOrder (D + D + 2) (by omega)) Qb
  exact independentLiftMeanCompositionSource_slow_slice_congr j (c p.1 j) (e p.1 j)
    L hL Y Z A FC FE out
    (fun w => (QC w).restrictOrder j (by omega))
    (fun w => (QE w).restrictOrder j (by omega)) hU
    (fun m α u => hc p.1 j hpre m α out u)
    (fun w => hA p.2 (n - j) (by omega) hnsub (by omega) w) t X hX z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual odd/scheduled Piola sources assemble with a uniform dimensionless partition price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independentPiolaDimensionlessPrice_nonneg (N Dγ k r : ℕ) (C B₀ : ℝ)
    (hC : 0 ≤ C) (hB₀ : 0 ≤ B₀) :
    0 ≤ independentPiolaDimensionlessPrice N Dγ k C B₀ r := by
  unfold independentPiolaDimensionlessPrice
  apply Finset.sum_nonneg
  intro d _
  apply Finset.sum_nonneg
  intro J _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hC) hB₀)
    (pow_nonneg (by positivity) _)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The native centered chart has exactly the physical Jacobian at its recentered point. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem centeredGeometryChart_fderiv (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) (X : Vec 2) :
    fderiv ℝ (centeredGeometryChart g ρ u) X =
      fderiv ℝ (fun y => g.1 u y g.2.2) (g.2.1 + ρ • X) := by
  let F := fun z : Vec 2 => g.1 u (g.2.1 + z) g.2.2 - g.1 u g.2.1 g.2.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    ((hg u g.2.2).comp (contDiff_const.add contDiff_id)).sub contDiff_const
  have he : centeredGeometryChart g ρ u = rescaledChart ρ F := rfl
  rw [he, rescaledChart_fderiv ρ hρ F hF]
  have hh := (((hg u g.2.2).differentiable (by simp) (g.2.1 + ρ • X)).hasFDerivAt.comp
    (ρ • X) ((hasFDerivAt_id (ρ • X)).const_add g.2.1)).sub_const (g.1 u g.2.1 g.2.2)
  simpa only [F, Function.comp_def, ContinuousLinearMap.comp_id] using hh.fderiv

theorem centeredGeometryChart_jacMatrix (g : ChainGeom) (hg : GeomSpatialSmooth g)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) (X : Vec 2) :
    jacMatrix (centeredGeometryChart g ρ u) X =
      jacMatrix (fun y => g.1 u y g.2.2) (g.2.1 + ρ • X) := by
  ext i j
  simp only [jacMatrix, Matrix.of_apply, centeredGeometryChart_fderiv g hg ρ hρ u X]

theorem centeredGeometryChart_metric_recenter (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (ρ : ℝ) (hρ : 0 < ρ) (u : ℝ) (X : Vec 2) :
    (A.recenter D (ρ • X)).famMetric D u =
      (jacMatrix (centeredGeometryChart (A.geom D) ρ u) X)⁻¹ *
        Matrix.transpose (jacMatrix (centeredGeometryChart (A.geom D) ρ u) X)⁻¹ := by
  rw [centeredGeometryChart_jacMatrix _ (geomSpatialSmooth_geom D A) ρ hρ]
  exact metric_recenter_formula D A hA u (ρ • X)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Slow Jacobian and determinant-one inverse estimates retain all family and fast parameters. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentTransferReassociate : ((P × Vec 2) × Vec 2) →L[ℝ] (P × (Vec 2 × Vec 2)) :=
  ((ContinuousLinearMap.fst ℝ P (Vec 2)).comp
    (ContinuousLinearMap.fst ℝ (P × Vec 2) (Vec 2))).prod
    (((ContinuousLinearMap.snd ℝ P (Vec 2)).comp
      (ContinuousLinearMap.fst ℝ (P × Vec 2) (Vec 2))).prod
      (ContinuousLinearMap.snd ℝ (P × Vec 2) (Vec 2)))

theorem independentTransferReassociate_norm_le :
    ‖independentTransferReassociate (P := P)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro X
  change ‖(X.1.1, X.1.2, X.2)‖ ≤ 1 * ‖X‖
  simp only [one_mul, Prod.norm_def, max_assoc]
  exact le_rfl

theorem independent_centered_transfer_inverse_jacobian_jets
    (F : P × Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u t : ℝ)
    (hsmall : |u - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : n ≤ K) (B : ℝ) (hB : 1 ≤ B)
    (hdet : ∀ Y : (P × Vec 2) × Vec 2,
      (jacMatrix (fun x => independentCenteredTransfer F D m slot u t
        (Y.1.1, Y.1.2, x)) Y.2).det = 1)
    (X : (P × Vec 2) × Vec 2)
    (hparent : ∀ a, 1 ≤ a → a ≤ K + 1 →
      ‖iteratedFDeriv ℝ a F
        (X.1.1, X.2 + D.relDisp m slot u t (X.1.2 + X.2))‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Y : (P × Vec 2) × Vec 2 =>
      (jacMatrix (fun x => independentCenteredTransfer F D m slot u t
        (Y.1.1, Y.1.2, x)) Y.2)⁻¹ i j) X‖ ≤
      positiveJetCompositionBudget (K + 1) (max B (weakTransferJointShearCost (K + 1))) := by
  let T := independentCenteredTransfer F D m slot u t
  let L := independentTransferReassociate (P := P)
  let H := T ∘ L
  have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
    independentCenteredTransfer_contDiff F hF D m slot u t
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hT.comp L.contDiff
  rw [planar_inverse_entry_derivative_norm _ hdet]
  change ‖iteratedFDeriv ℝ n
    (fun Y : (P × Vec 2) × Vec 2 => jacMatrix (fun x => H (Y.1, x)) Y.2 j.rev i.rev) X‖ ≤ _
  apply (independent_parameter_jacobian_entry_jet_bound H hH j.rev i.rev n X).trans
  have hh := finite_affine_derivative_norm_le T (n + 1) (hT.of_le (by simp))
    L independentTransferReassociate_norm_le 0 X
  simp only [add_zero] at hh
  apply hh.trans
  exact independentCenteredTransfer_positive_jets F hF D hΛ hζ m slot hp u t hsmall
    (K + 1) (n + 1) (by omega) (by omega) B hB (L X) hparent

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual molecular pulse supplies the finite drift budget once its genuine Pe is small. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

def pulseFiniteDriftBudget (P : MolecularData) (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {ν : ℝ} {slot : ℤ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ) (hslot : Odd slot)
    (hv : P.v = ocPulseCellDrift α q Λ ζ m ν slot)
    (hsmall : ocEpsilon q Λ m ^ (1 + α) / ν ≤
      smallPecletThreshold K 1 (pulseFastDerivativeConstant K)) :
    MolecularFiniteDriftBudget P K where
  Cv := (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant K
  nonneg := mul_nonneg (div_nonneg (Real.rpow_nonneg
    (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le)
      (pulseFastDerivativeConstant_nonneg K)
  admissible := by rw [hv]; exact normalizedPulseDrift_isCellDrift hΛ hν hζ hslot
  smooth t := by rw [hv]; exact (normalizedPulseDrift_contDiff hΛ hν hslot t).of_le (by simp)
  periodic t := by rw [hv]; exact normalizedPulseDrift_periodic hΛ hν hslot t
  bound := by
    intro t j hj i x
    rw [hv]
    exact normalizedPulseDrift_fast_bound hΛ hν hζ hslot K j hj t x i
  small := smallPecletThreshold_budget K 1 (pulseFastDerivativeConstant K) _
    (div_nonneg (Real.rpow_nonneg
      (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le) hsmall

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual inverse child chart is the reverse-time model at its re-anchored center and phase. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*}

def independentCenteredChildReanchorInput (D : OCData) (k : ℕ) (slot : ℤ) (u r θ : ℝ)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) : P × (Vec 2 × (Vec 2 × Vec 2)) :=
  let δ := D.relDisp k slot u r Y.2.2.1
  (Y.1, Y.2.1 + θ • δ, Y.2.2.1 + δ, Y.2.2.2)

theorem childGeom_inverse_chart_eq_independentCenteredChildChart (D : OCData) (k : ℕ) (slot : ℤ)
    (g : P → ChainGeom) (p : P) (hg : ChainGeometry.InvLaw (g p)) (anchor u ρ θ : ℝ)
    (hρ : ρ ≠ 0) (hθ : θ ≠ 0) (he : D.eps k ≠ 0) (hscale : D.eps k = ρ * θ)
    (c : ChainChild) (C H : Vec 2) (hc : c.center = ρ • C) :
    centeredGeometryChartInv (D.childGeom k slot anchor c (g p)) (D.eps k) u H =
      independentCenteredChildChart D k slot anchor u
        (fun Y : P × Vec 2 => centeredGeometryChart (g Y.1) ρ anchor Y.2)
        (fun Y : P × Vec 2 => centeredGeometryChartInv (g Y.1) ρ u Y.2)
        (fun Y : P × Vec 2 => centeredGeometryChart (g Y.1) ρ u Y.2)
        θ (independentCenteredChildReanchorInput D k slot u anchor θ (p, C, c.phase, H)) := by
  rw [centeredGeometryChartInv_reanchor _ (ChainGeometry.invLaw_childGeom D k slot anchor c hg)]
  rw [← childGeom_reanchor D k slot anchor u (g p) hg c he]
  have hc' : (reanchoredChild D k slot anchor u c).center =
      ρ • (C + θ • D.relDisp k slot u anchor c.phase) := by
    change c.center + D.eps k • D.relDisp k slot u anchor c.phase = _
    rw [hc, hscale, smul_add, smul_smul]
  exact childGeom_chart_eq_independentCenteredChildChart D k slot g p hg u anchor ρ θ
    hρ hθ he hscale (reanchoredChild D k slot anchor u c)
    (C + θ • D.relDisp k slot u anchor c.phase) H hc'

end AVRegularity.EntryWeakProofs
end
end

section
/-! The determinant-one centered Piola matrix is smooth in every independent parameter. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_centered_transfer_inverse_entry_contDiff
    (F : P × Vec 2 → Vec 2) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (D : OCData) (m : ℕ) (slot : ℤ) (u t : ℝ)
    (hdet : ∀ Y : (P × Vec 2) × Vec 2,
      (jacMatrix (fun x => independentCenteredTransfer F D m slot u t
        (Y.1.1, Y.1.2, x)) Y.2).det = 1) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : (P × Vec 2) × Vec 2 =>
      (jacMatrix (fun x => independentCenteredTransfer F D m slot u t
        (Y.1.1, Y.1.2, x)) Y.2)⁻¹ i j) := by
  let H := independentCenteredTransfer F D m slot u t ∘
    independentTransferReassociate (P := P)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    (independentCenteredTransfer_contDiff F hF D m slot u t).comp
      (independentTransferReassociate (P := P)).contDiff
  have he : (fun Y : (P × Vec 2) × Vec 2 =>
      (jacMatrix (fun x => H (Y.1, x)) Y.2)⁻¹ i j) =
      fun Y => (if i = j then 1 else -1) *
        jacMatrix (fun x => H (Y.1, x)) Y.2 j.rev i.rev := by
    funext Y
    exact planar_inverse_entry_formula _ (hdet Y) i j
  change ContDiff ℝ (⊤ : ℕ∞) (fun Y : (P × Vec 2) × Vec 2 =>
    (jacMatrix (fun x => H (Y.1, x)) Y.2)⁻¹ i j)
  rw [he]
  exact (independent_parameter_jacobian_entry_contDiff H hH j.rev i.rev).const_smul (if i = j then (1 : ℝ) else -1)

end AVRegularity.EntryWeakProofs
end
end

section
/-! One positive numeric pulse threshold covers every smaller fast reserve. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def pulseHigherDriftThreshold : ℕ → ℝ
  | 0 => smallPecletThreshold 0 1 (pulseFastDerivativeConstant 0)
  | H + 1 => min (pulseHigherDriftThreshold H)
      (smallPecletThreshold (H + 1) 1 (pulseFastDerivativeConstant (H + 1)))

theorem pulseHigherDriftThreshold_pos (H : ℕ) : 0 < pulseHigherDriftThreshold H := by
  induction H with
  | zero => exact smallPecletThreshold_pos _ _ _
  | succ H ih => exact lt_min ih (smallPecletThreshold_pos _ _ _)

theorem pulseHigherDriftThreshold_le (H K : ℕ) (hK : K ≤ H) :
    pulseHigherDriftThreshold H ≤ smallPecletThreshold K 1 (pulseFastDerivativeConstant K) := by
  induction H with
  | zero =>
      have he : K = 0 := by omega
      subst K
      exact le_rfl
  | succ H ih =>
    by_cases hk : K ≤ H
    · exact (min_le_left _ _).trans (ih hk)
    · have he : K = H + 1 := by omega
      subst K
      exact min_le_right _ _

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual re-anchoring has uniformly bounded full independent center/phase/space jets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independentCenteredChildReanchorInput_contDiff (D : OCData) (m : ℕ) (slot : ℤ)
    (u r θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildReanchorInput (P := P) D m slot u r θ) := by
  have hδ := (relDisp_spatial_smooth D m slot u r).comp
    (centeredChildPhaseProjection (P := P) (V := Vec 2)).contDiff
  exact contDiff_fst.prodMk
    (((centeredChildCenterProjection (P := P) (V := Vec 2)).contDiff.add (hδ.const_smul θ)).prodMk
      (((centeredChildPhaseProjection (P := P) (V := Vec 2)).contDiff.add hδ).prodMk
        (centeredChildSlowProjection (P := P) (V := Vec 2)).contDiff))

theorem independentCenteredChildReanchorInput_positive_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r θ : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (hθ : |θ| ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildReanchorInput D m slot u r θ) Y‖ ≤
      1 + (2 * Real.pi) ^ (K + 1) := by
  let A := independentCenteredChildBase (P := P) D m slot u r θ
  let A₁ := independentCenteredChildBase (P := P) D m slot u r 1
  let L := centeredChildDuplicatePhaseProjection (P := P) (V := Vec 2)
  let φ := A₁ ∘ L
  let S := centeredChildSlowProjection (P := P) (V := Vec 2)
  let Q : (P × (Vec 2 × (Vec 2 × Vec 2))) →L[ℝ] P :=
    ContinuousLinearMap.fst ℝ P (Vec 2 × (Vec 2 × Vec 2))
  let B := 1 + (2 * Real.pi) ^ (K + 1)
  have hB : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  have hA : ContDiff ℝ (n : ℕ∞) A := (independentCenteredChildBase_contDiff D m slot u r θ).of_le (by simp)
  have hA₁ : ContDiff ℝ (n : ℕ∞) A₁ := (independentCenteredChildBase_contDiff D m slot u r 1).of_le (by simp)
  have hφ : ContDiff ℝ (n : ℕ∞) φ := hA₁.comp L.contDiff
  have hS : ContDiff ℝ (n : ℕ∞) S := S.contDiff
  have hQ : ContDiff ℝ (n : ℕ∞) Q := Q.contDiff
  have hbA : ‖iteratedFDeriv ℝ n A Y‖ ≤ B :=
    independentCenteredChildBase_positive_jet_bound D hΛ hζ m slot hp u r θ hsmall hθ K n hn hnK Y
  have hbφ : ‖iteratedFDeriv ℝ n φ Y‖ ≤ B := by
    have hh := finite_affine_derivative_norm_le A₁ n hA₁ L centeredChildDuplicatePhaseProjection_norm_le 0 Y
    simp only [add_zero] at hh
    exact hh.trans (independentCenteredChildBase_positive_jet_bound D hΛ hζ m slot hp u r 1
      hsmall (by norm_num) K n hn hnK (L Y))
  have hbS : ‖iteratedFDeriv ℝ n S Y‖ ≤ B :=
    (linear_positive_derivative_norm_le S n hn Y).trans (centeredChildSlowProjection_norm_le.trans hB)
  have hQnorm : ‖Q‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Z => by
    rw [one_mul]; exact norm_fst_le Z)
  have hbQ : ‖iteratedFDeriv ℝ n Q Y‖ ≤ B :=
    (linear_positive_derivative_norm_le Q n hn Y).trans (hQnorm.trans hB)
  have hbφS : ‖iteratedFDeriv ℝ n (fun Z => (φ Z, S Z)) Y‖ ≤ B :=
    (independent_joint_pair_jet_bound φ S n hφ hS Y).trans (max_le hbφ hbS)
  have hbAφS : ‖iteratedFDeriv ℝ n (fun Z => (A Z, φ Z, S Z)) Y‖ ≤ B :=
    (independent_joint_pair_jet_bound A (fun Z => (φ Z, S Z)) n hA (hφ.prodMk hS) Y).trans
      (max_le hbA hbφS)
  have he : independentCenteredChildReanchorInput (P := P) D m slot u r θ =
      fun Z => (Q Z, A Z, φ Z, S Z) := by
    funext Z
    simp only [independentCenteredChildReanchorInput, A, A₁, φ, Function.comp_apply,
      L, centeredChildDuplicatePhaseProjection_apply, independentCenteredChildBase,
      one_smul, Q, S, centeredChildSlowProjection_apply]
    rfl
  rw [he]
  exact (independent_joint_pair_jet_bound Q (fun Z => (A Z, φ Z, S Z)) n hQ
    (hA.prodMk (hφ.prodMk hS)) Y).trans (max_le hbQ hbAφS)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native inverse-return interpolation lies in the earlier spatial reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centered_native_return_segment_carrier (g : P → ChainGeom) (p : P)
    (hg : GeomSpatialSmooth (g p)) (ρ : ℝ) (hρ : 0 < ρ) (r θ : ℝ) (hθ : |θ| ≤ 1)
    (hc : ∀ x, ‖fderiv ℝ (fun y => (g p).1 r y (g p).2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (C H : Vec 2) (hC : ‖C‖ ≤ 1 + 2 * Real.pi) (S : ℝ) (hH : ‖H‖ ≤ S)
    (Z : P × Vec 2)
    (hZ : Z ∈ segment ℝ (p, centeredGeometryChart (g p) ρ r C)
      (p, centeredGeometryChart (g p) ρ r C + θ • H)) :
    Z.1 = p ∧ ‖Z.2‖ ≤ centeredParentRadius (2 * Real.pi) S := by
  have hS : 0 ≤ S := (norm_nonneg H).trans hH
  have hF : ‖centeredGeometryChart (g p) ρ r C‖ ≤ 2 * (1 + 2 * Real.pi) :=
    (centeredGeometryChart_value_le_two (g p) hg ρ hρ r hc C).trans
      (mul_le_mul_of_nonneg_left hC (by norm_num))
  have hHθ : ‖θ • H‖ ≤ S := by
    rw [norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hθ (norm_nonneg H)).trans_eq (one_mul _)).trans hH
  have hE : ‖centeredGeometryChart (g p) ρ r C + θ • H‖ ≤
      2 * (1 + 2 * Real.pi) + S := (norm_add_le _ _).trans (add_le_add hF hHθ)
  have hR := centeredParentRadius_inverse_input (2 * Real.pi) S (by positivity) hS
  constructor
  · exact independent_spatial_segment_parameter _ _ _ _ hZ
  · exact independent_spatial_segment_norm_le _ _ _ _ _
      ((hF.trans (le_add_of_nonneg_right hS)).trans hR) (hE.trans hR) hZ

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual native path labels carry independently produced incoming fields without changing their witnesses. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {h H : ℕ}

def independentPathTemplateField
    (field : Fin h → (d : Finset.Icc 2 Dm) → DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (_v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (_γ : Constituent d.val ℝ ℝ)
    (α : DerivativeWord2 (d.val - 1)) : ℝ → Vec 2 → P → Vec 2 :=
  if hu : u.val < h then field ⟨u.val, hu⟩ d α else fun _ _ _ => 0

theorem independentPathTemplateField_reserve
    (G : GenStage D hr Dm bw j₀) (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D bw j₀ G.level p)
    (field : Fin h → (d : Finset.Icc 2 Dm) → DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ j d, d.val ≤ (G.fam.identity _ _ (π.step j).2.2).maxOrder → ∀ α,
      IndependentParameterSourceReserve H (field j d α))
    (B : ℝ)
    (hQ : ∀ j d hd α r, r ≤ H → (Q j d hd α).budget r ≤
      (G.fam.identity _ _ (π.step j).2.2).record.size * B)
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.val ℝ ℝ)
    (hγ : γ ∈ pathEdges G π p c v u d) (α : DerivativeWord2 (d.val - 1)) :
    ∃ R : IndependentParameterSourceReserve H (independentPathTemplateField field v u d γ α),
      ∀ r ≤ H, R.budget r ≤ weightedPathMatrix h (stagePathStoredWeight G π) v u * B := by
  unfold pathEdges at hγ
  split at hγ
  next hvu =>
    split at hγ
    next hd =>
      let j : Fin h := ⟨u.val, hvu.2⟩
      unfold independentPathTemplateField
      rw [dite_eq_left hvu.2]
      refine ⟨Q j d hd α, ?_⟩
      intro r hr
      have hm : weightedPathMatrix h (stagePathStoredWeight G π) v u =
          (G.fam.identity _ _ (π.step j).2.2).record.size := by
        simp only [weightedPathMatrix, ite_eq_left hvu.1, stagePathStoredWeight,
          dite_eq_left hvu.2, j]
      rw [hm]
      exact hQ j d hd α r hr
    · exact (List.not_mem_nil hγ).elim
  · exact (List.not_mem_nil hγ).elim

omit [NormedSpace ℝ P] in
theorem independentPathTemplateField_translation
    (δ : P)
    (field : Fin h → (d : Finset.Icc 2 Dm) →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (he : ∀ j d α, IndependentSourceTranslationInvariant δ (field j d α))
    (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (γ : Constituent d.val ℝ ℝ)
    (α : DerivativeWord2 (d.val - 1)) :
    IndependentSourceTranslationInvariant δ (independentPathTemplateField field v u d γ α) := by
  unfold independentPathTemplateField
  split
  · exact he _ d α
  · intro t z Y
    rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal centered forward interpolation fits the earlier spatial reserve with its family parameter fixed. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centered_native_forward_segment_carrier
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (g : P → ChainGeom) (p : P) (hg : GeomSpatialSmooth (g p))
    (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (hc : ∀ x, ‖fderiv ℝ (fun y => (g p).1 (g p).2.2 y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (C phase H : Vec 2) (hC : ‖C‖ ≤ 1 + 2 * Real.pi) (S : ℝ) (hH : ‖H‖ ≤ S)
    (Z : P × Vec 2) :
    let Fi := fun W : P × Vec 2 => centeredGeometryChartInv (g W.1) ρ r W.2
    let Fa := fun W : P × Vec 2 => centeredGeometryChart (g W.1) ρ r W.2
    let Y := (p, C, phase, H)
    let B := independentCenteredChildBase D m slot u r θ Y
    let V := independentCenteredChildDisplacement D m slot u r Fi Fa θ Y
    Z ∈ segment ℝ (p, B) (p, B + θ • V) →
      Z.1 = p ∧ ‖Z.2‖ ≤ centeredParentRadius (2 * Real.pi) S := by
  dsimp only
  intro hz
  let Fi := fun W : P × Vec 2 => centeredGeometryChartInv (g W.1) ρ r W.2
  let Fa := fun W : P × Vec 2 => centeredGeometryChart (g W.1) ρ r W.2
  let Y := (p, C, phase, H)
  let B := independentCenteredChildBase D m slot u r θ Y
  let V := independentCenteredChildDisplacement D m slot u r Fi Fa θ Y
  change Z ∈ segment ℝ (p, B) (p, B + θ • V) at hz
  have hS : 0 ≤ S := (norm_nonneg H).trans hH
  have hraw : ContDiff ℝ 1 (fun X => (g p).1 (g p).2.2 X r) :=
    (hg (g p).2.2 r).of_le (by simp)
  have hI : ContDiff ℝ 1 (fun X => Fi (p, X)) := by
    change ContDiff ℝ 1 (fun X => ρ⁻¹ •
      ((g p).1 (g p).2.2 ((g p).1 r (g p).2.1 (g p).2.2 + ρ • X) r - (g p).2.1))
    exact ((hraw.comp ((contDiff_const (c := (g p).1 r (g p).2.1 (g p).2.2)).add
      (contDiff_id.const_smul ρ))).sub (contDiff_const (c := (g p).2.1))).const_smul ρ⁻¹
  have hV := independentCenteredChildDisplacement_spatial_value_bound D hΛ hζ m slot hp u r hsmall
    Fi Fa Y hI 2 θ (by norm_num) hθ S hH (fun X _ =>
      centeredGeometryChartInv_spatial_derivative_le_two (g p) hg ρ hρ r hc X)
  have hV' : ‖V‖ ≤ 2 * (1 + (2 * Real.pi) ^ 2) * S := hV.trans_eq (by
    unfold independentCenteredChildDisplacementRadius
    ring)
  have hVθ : ‖θ • V‖ ≤ 2 * (1 + (2 * Real.pi) ^ 2) * S := by
    rw [norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hθ₁ (norm_nonneg V)).trans_eq (one_mul _)).trans hV'
  have hB : ‖B‖ ≤ 1 + 2 * (2 * Real.pi) :=
    (independentCenteredChildBase_value_le D hΛ hζ m slot hp u r θ hsmall hθ₁
      Y (1 + 2 * Real.pi) hC).trans_eq (by ring)
  have hE : ‖B + θ • V‖ ≤ 1 + 2 * (2 * Real.pi) + 2 * (1 + (2 * Real.pi) ^ 2) * S :=
    (norm_add_le _ _).trans (add_le_add hB hVθ)
  have hR := centeredParentRadius_forward_input (2 * Real.pi) S (by positivity) hS
  constructor
  · exact independent_spatial_segment_parameter _ _ _ _ hz
  · exact independent_spatial_segment_norm_le _ _ _ _ _
      ((hB.trans (le_add_of_nonneg_right (by positivity))).trans hR) (hE.trans hR) hz

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine earlier chart reserves on a spatial disk produce the full fresh forward mixed jets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centered_native_forward_mixed_production
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (g : P → ChainGeom) (p : P) (hg : GeomSpatialSmooth (g p))
    (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (hforward : ∀ x, ‖fderiv ℝ (fun y => (g p).1 r y (g p).2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (hinverse : ∀ x, ‖fderiv ℝ (fun y => (g p).1 (g p).2.2 y r) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (B : ℝ) (hB : 1 ≤ B)
    (C phase H : Vec 2) (hC : ‖C‖ ≤ 1 + 2 * Real.pi) (S : ℝ) (hH : ‖H‖ ≤ S) :
    let Fu := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
    let Fi := fun Z : P × Vec 2 => centeredGeometryChartInv (g Z.1) ρ r Z.2
    let Fa := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ r Z.2
    ContDiff ℝ (⊤ : ℕ∞) Fu → ContDiff ℝ (⊤ : ℕ∞) Fi → ContDiff ℝ (⊤ : ℕ∞) Fa →
    (∀ f ∈ [Fu, Fi, Fa], ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ X : Vec 2,
      ‖X‖ ≤ centeredParentRadius (2 * Real.pi) S →
      ‖iteratedFDeriv ℝ i f (p, X)‖ ≤ B) →
    ‖iteratedFDeriv ℝ n (independentCenteredChildChart D m slot u r Fu Fi Fa θ)
      (p, C, phase, H)‖ ≤ independentCenteredChildChartMixedCost K B 2 S := by
  dsimp only
  intro hFu hFi hFa hb
  let Fu := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
  let Fi := fun Z : P × Vec 2 => centeredGeometryChartInv (g Z.1) ρ r Z.2
  let Fa := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ r Z.2
  have hS : 0 ≤ S := (norm_nonneg H).trans hH
  have hCR : ‖C‖ ≤ centeredParentRadius (2 * Real.pi) S := by
    apply hC.trans
    calc
      1 + 2 * Real.pi ≤ 2 * (1 + 2 * Real.pi) + S := by
        have hpi : 0 ≤ 2 * Real.pi := by positivity
        linarith only [hpi, hS]
      _ ≤ centeredParentRadius (2 * Real.pi) S :=
        centeredParentRadius_inverse_input _ _ (by positivity) hS
  apply independentCenteredChildChart_mixed_jet_bound D hΛ hζ m slot hp u r hsmall
    Fu Fi Fa hFu hFi hFa K n hn hnK B hB 2 (by norm_num) θ hθ hθ₁
    (p, C, phase, H) S hH
  · intro i hi hiK
    exact hb Fa (by simp [Fa]) i hi (hiK.trans (Nat.le_succ K)) C hCR
  · intro i hi hiK Z hZ
    have hz := centered_native_return_segment_carrier g p hg ρ hρ r θ hθ₁
      hforward C H hC S hH Z hZ
    have he : Z = (p, Z.2) := Prod.ext hz.1 rfl
    rw [he]
    exact hb Fi (by simp [Fi]) i hi hiK Z.2 hz.2
  · intro X _
    exact centeredGeometryChartInv_spatial_derivative_le_two (g p) hg ρ hρ r hinverse X
  · intro i hi hiK Z hZ
    have hz := centered_native_forward_segment_carrier D hΛ hζ m slot hp u r hsmall
      g p hg ρ hρ θ hθ hθ₁ hinverse C phase H hC S hH Z hZ
    have he : Z = (p, Z.2) := Prod.ext hz.1 rfl
    rw [he]
    exact hb Fu (by simp [Fu]) i hi hiK Z.2 hz.2

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier independent scalar coefficient prices produce one common ordered forcing price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def independentLiftCoefficientAProductionCost (H D n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) : ℝ :=
  let BF := finiteLiftSymbolBudget n A * B
  normalizedCellB1UniformBudget H A η BG BV BF + normalizedCellB2UniformBudget H A η BG BF +
    (min D n + 1) * normalizedSourceArrayMatrixBudget H D count A η BE BF

theorem independentLiftCoefficientAProductionCost_nonneg (H D n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentLiftCoefficientAProductionCost H D n count A η BG BV BE B := by
  have hBF := mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB
  exact add_nonneg (add_nonneg
    (normalizedCellB1UniformBudget_nonneg H A η BG BV _ hBG hBV hBF)
    (normalizedCellB2UniformBudget_nonneg H A η BG _ hBG hBF))
    (mul_nonneg (by positivity) (normalizedSourceArrayMatrixBudget_nonneg H D count A η BE _ hBE hBF))

theorem independentLiftCoefficientA_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + D + 2 →
      (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ u e γ hγ α r, r ≤ H + 1 → (Qa out u e γ hγ α).budget r ≤ M out u * BE)
    (hmap : ∀ u e γ, γ ∈ edge out u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ u e, (edge out u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H
      (independentLiftCoefficientASource edge a L A η G v c hh n out inp),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        independentLiftCoefficientAProductionCost H D n count A η BG BV BE B := by
  let F := fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y
  let BF := finiteLiftSymbolBudget n A * B
  let Qt := fun p q (hpq : p < hh ∨ (p = hh ∧ q < n)) K (hK : K ≤ H + D + 2) w =>
    independentScalarLiftTestSourceReserve K q (c p q) A w inp
      (fun m α => (Qc p q hpq m α w inp).restrictOrder K hK)
  have ht p q hpq K hK w (hq : q ≤ n) r (hr : r ≤ K) :
      (Qt p q hpq K hK w).budget r ≤ finiteMatrixPower M p w inp * BF := by
    apply independentScalarLiftTestSourceReserve_menu_budget K q n hq (c p q) A w inp _
      (finiteMatrixPower M p w inp) B (finiteMatrixPower_nonneg M hM p w inp) hB
    · intro m α s hs
      exact hc p q hpq m α w inp s (hs.trans hK)
    · exact hr
  exact independentLiftA_uniform_production H edge a L hL A η G v F hh n out inp QG Qv
    (Qt hh (n - 1) (Or.inr ⟨rfl, by omega⟩) (H + 2) (by omega) out)
    (fun _ => Qt hh (n - 2) (Or.inr ⟨rfl, by omega⟩) (H + 2) (by omega) out)
    (fun hhh j _ w => Qt (hh - 1) (n - j) (Or.inl (by omega)) (H + 1 + D) (by omega) w)
    Qa M hM count BG BV BE BF hBG hBV hBE (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB)
    hG hv (ht _ _ _ _ _ out (Nat.sub_le _ _))
    (fun _ => ht _ _ _ _ _ out (Nat.sub_le _ _))
    (fun hhh j _ w => ht _ _ _ _ _ w (Nat.sub_le _ _)) he hmap hlen

end AVRegularity.EntryWeakProofs
end
end
end

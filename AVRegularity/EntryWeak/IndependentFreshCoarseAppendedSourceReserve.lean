-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentLiftPredecessorFields
import AVRegularity.EntryWeak.MolecularUlFluxNormBound
import AVRegularity.Construction.EntryScales.TerminalCore

section
section
/-! The actual full mixed metric price follows from primitive stream and scheduled weak-chain data. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem uniform_fresh_metric_jet_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.WellSlotted → A.children = [] →
      ∀ p : ℕ → ℤ, A.slots = [p 0] → (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n)) →
      ∀ n ≤ J, ∀ K S, ∀ u ∈ nativeWeakChartWindow D A.baseLevel J p n,
      ∀ Y : Vec (4 * n) × Vec 2, independentFreshCenterStrip Y.1 → ‖Y.2‖ ≤ S →
      ∀ a ≤ K,
      ‖iteratedFDeriv ℝ a (fun Z : Vec (4 * n) × Vec 2 =>
        ((independentFreshChain A (fun j : Fin n => p (j + 1))
          (fun j => D.eps (A.baseLevel + j + 1)) Z.1).recenter D
          (D.eps (A.baseLevel + n) • Z.2)).famMetric D u) Y‖ ≤
        planarGramJetBudget a (nativeMixedChartBudget (K + 1) n S) := by
  obtain ⟨M, hM, hchart⟩ := uniform_fresh_native_chart_production α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hAM hA hchildren p hslots hp hs n hn K S u hu Y hY hS a ha
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  apply independent_fresh_metric_jet_bound_of_chart_reserve D A hA
    (fun j : Fin n => p (j + 1)) (fun j => D.eps (A.baseLevel + j + 1))
    (D.eps (A.baseLevel + n)) (Construction.Stream.ocEpsilon_pos hΛ₁)
    (nativeWeakChartWindow D A.baseLevel J p n) K S (nativeMixedChartBudget (K + 1) n S)
    (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _))
    ?_ (hchart D hDα hDq hDΛ hDζ hseq A hAM hA hchildren p hslots hp hs n hn (K + 1) S)
    u hu Y hY hS a ha
  intro P
  rw [independentFreshChain_geom_eq_indexed D A p hchildren hslots
    (fun j => D.eps (A.baseLevel + j + 1)) P]
  exact finiteWeakChainGeom_area_preserving D hΛ₁ A.baseLevel A.base p _ n
    (fun j hj => hp j (by omega))

end AVRegularity.EntryWeakProofs
end
end

section
/-! A native predecessor datum contains primitive reserves and genuine earlier coefficient
productions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

structure IndependentLiftPredecessorDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count hh n qs : ℕ) (BG BV BE B : ℝ) where
  primitive : IndependentLiftPrimitiveData ι d H D N R count BG BV BE
  fastOrder : primitive.sZ = qs
  earlier : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) (H + 2 * D + 2) q primitive.a primitive.b primitive.U
      (fun Y => primitive.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower primitive.M p v u) B

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite metric price is chosen before the data, parameter points and inverse window. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def nativeWeakMixedMetricBudget (K J : ℕ) (S : ℝ) : ℝ :=
  1 + ∑ r ∈ Finset.range (J + 1), ∑ a ∈ Finset.range (K + 1),
    planarGramJetBudget a (nativeMixedChartBudget (K + 1) r S)

theorem nativeWeakMixedMetricBudget_ge_one (K J : ℕ) (S : ℝ) :
    1 ≤ nativeWeakMixedMetricBudget K J S := by
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro a _
  exact planarGramJetBudget_nonneg a _ (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _))

theorem nativeWeakMixedMetricBudget_bound (K J : ℕ) (S : ℝ) (r a : ℕ)
    (hr : r ≤ J) (ha : a ≤ K) :
    planarGramJetBudget a (nativeMixedChartBudget (K + 1) r S) ≤ nativeWeakMixedMetricBudget K J S := by
  have hinner : planarGramJetBudget a (nativeMixedChartBudget (K + 1) r S) ≤
      ∑ b ∈ Finset.range (K + 1), planarGramJetBudget b (nativeMixedChartBudget (K + 1) r S) :=
    Finset.single_le_sum (fun b _ => planarGramJetBudget_nonneg b _
      (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _))) (Finset.mem_range.mpr (show a < K + 1 by omega))
  have houter : (∑ b ∈ Finset.range (K + 1), planarGramJetBudget b (nativeMixedChartBudget (K + 1) r S)) ≤
      ∑ q ∈ Finset.range (J + 1), ∑ b ∈ Finset.range (K + 1),
        planarGramJetBudget b (nativeMixedChartBudget (K + 1) q S) :=
    Finset.single_le_sum (fun q _ => show 0 ≤ ∑ b ∈ Finset.range (K + 1),
      planarGramJetBudget b (nativeMixedChartBudget (K + 1) q S) from
        Finset.sum_nonneg (fun b _ => planarGramJetBudget_nonneg b _
          (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _)))) (Finset.mem_range.mpr (show r < J + 1 by omega))
  exact (hinner.trans houter).trans (le_add_of_nonneg_left zero_le_one)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual higher inverse words produce joint parameter and fast-cell regularity. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {d H : ℕ}

theorem coordinate_word_classical_joint_contDiff {a b : ℝ} (hab : a < b)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (P : Vec d → MolecularData)
    (hP : ∀ Y, dataCoefficients (P Y) = ⟨(fun t _ => G t Y), (P Y).v, 0, 0⟩)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hPv : ∀ Y, (P Y).v = v)
    (V : ∀ Y r, r ≤ H → MolecularFiniteDriftBudget (P Y) r)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hc : IsCoordinateWordNormJetFamily (cellEnergyNorm univ) N c)
    (hsol : ∀ Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hf : ∀ t, t ≤ a → ∀ z Y, f t z Y = 0)
    (hF : ∀ t, t ≤ a → ∀ z Y, F t z Y = 0)
    (u : List (Fin d) → Vec d → ℝ → TorusHk K ℂ)
    (hu : ∀ w, w.length ≤ N → ∀ Y t, t ∈ Icc a b →
      torusHkValueCLM (u w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c w Y) t)
    (R : List (Fin d) → ℝ)
    (hb : ∀ w, w.length ≤ N → ∀ Y t, ‖u w Y t‖ ≤ R w)
    (w : List (Fin d)) (r n : ℕ) (hw : w.length + r ≤ N)
    (hK : n + r + 4 ≤ K) (t : ℝ) (ht : t ∈ Icc a b) :
    ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u w X.1 t))) X.2) := by
  apply coordinate_word_joint_contDiff d N (K - 4)
    (fun w Y => realClassicalLift K (mapTorusHk Complex.reCLM (u w Y t)))
    _ _ _ w r n hw (by omega)
  · intro p hp m hm
    exact independent_classical_fast_jet_joint_continuous K m (by omega) (c p) (hc.1 p hp)
      (fun Y => u p Y t) t (fun Y => hu p hp Y t ht) (R p) (fun Y => hb p hp Y t)
  · intro p hp Y
    exact realClassicalLift_contDiff K (K - 4) (by omega) _
  · intro p hp m hm i Y z
    exact coordinate_word_classical_derivative hab N K hH QG Qf QF P hP v hv hPv V
      c hc hsol hf hF u hu p hp Y i t ht m (by omega) z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Canonical predecessor fields retain the slice equality of their coefficient productions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count hh n qs : ℕ} {BG BV BE B : ℝ} {U : Set (Vec 2)}

theorem independentLiftPredecessorFields_slow_slice_congr
    (x y : IndependentLiftPredecessorDatum ι d H D N R count hh n qs BG BV BE B)
    (Y Z : Vec (2 + d))
    (he : ∀ p q hpq m hm α v u,
      IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
        (x.earlier p q hpq m hm α v u).field (y.earlier p q hpq m hm α v u).field)
    (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) (m : ℕ)
    (α : DerivativeWord2 m) (v u : ι) :
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
      (fun t z W => independentLiftPredecessorFields x.primitive x.earlier p q m α t z W v u)
      (fun t z W => independentLiftPredecessorFields y.primitive y.earlier p q m α t z W v u) := by
  intro t X hX z
  dsimp only [independentLiftPredecessorFields]
  simp only [dite_eq_left hpq, independentCoefficientProductionFields]
  by_cases hm : m ≤ q
  · simp only [dite_eq_left hm]
    exact he p q hpq m hm (canonicalDerivativeWord α) v u t X hX z
  · simp only [dite_eq_right hm]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced classical inverse words have uniform full joint derivative budgets. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {A : Type*} {d H : ℕ}

theorem family_variable_window_coordinate_word_classical_joint_bound {a b : A → ℝ} (hab : ∀ x, a x < b x)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H)
    {G : A → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : A → ℝ → Vec 2 → Vec d → ℂ} {F : A → ℝ → Vec 2 → Vec d → ComplexCellVector}
    (QG : ∀ x, IndependentParameterMetricReserve H (G x))
    (Qf : ∀ x, IndependentParameterSourceReserve H (f x)) (QF : ∀ x, IndependentParameterSourceReserve H (F x))
    (P : A → Vec d → MolecularData)
    (hP : ∀ x Y, dataCoefficients (P x Y) = ⟨(fun t _ => G x t Y), (P x Y).v, 0, 0⟩)
    (v : A → ℝ → Vec 2 → Vec 2) (hv : ∀ x, IsCellDrift (v x)) (hPv : ∀ x Y, (P x Y).v = v x)
    (V : ∀ x Y r, r ≤ H → MolecularFiniteDriftBudget (P x Y) r)
    (c : A → List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hc : ∀ x, IsCoordinateWordNormJetFamily (cellEnergyNorm univ) N (c x))
    (hsol : ∀ x Y w, w.length ≤ N → IsCellInverseValue (dataCoefficients (P x Y))
      (fun t => cellQ0 (coordinateSourceWord (f x) w Y t))
      (coordinateSourceWord (F x) w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord (G x) p Y) (fun p => c x p Y) w) (c x w Y))
    (hf : ∀ x t, t ≤ a x → ∀ z Y, f x t z Y = 0)
    (hF : ∀ x t, t ≤ a x → ∀ z Y, F x t z Y = 0)
    (u : A → List (Fin d) → Vec d → ℝ → TorusHk K ℂ)
    (hu : ∀ x w, w.length ≤ N → ∀ Y t, t ∈ Icc (a x) (b x) →
      torusHkValueCLM (u x w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c x w Y) t)
    (R : List (Fin d) → ℝ)
    (hb : ∀ x w, w.length ≤ N → ∀ Y t, ‖u x w Y t‖ ≤ R w)
    (hK : 4 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x w r n, w.length + r ≤ N → n + r + 4 ≤ K → ∀ t ∈ Icc (a x) (b x), ∀ X : Vec d × Vec 2,
      ‖iteratedFDeriv ℝ r (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
        (realClassicalLift K (mapTorusHk Complex.reCLM (u x w X.1 t))) X.2) X‖ ≤ ((d : ℝ) + 1) ^ r * B := by
  obtain ⟨S, hS, hRS⟩ := finite_word_uniform_budget_exists d N R
  let B := ∑ m : Fin (K - 4 + 1), cellClassicalSobolevConstant K m.val * S
  have hB : 0 ≤ B := Finset.sum_nonneg fun m _ =>
    mul_nonneg (cellClassicalSobolevConstant_nonneg K m.val) hS
  have hprice (n : ℕ) (hn : n ≤ K - 4) : cellClassicalSobolevConstant K n * S ≤ B :=
    Finset.single_le_sum (fun m _ => mul_nonneg (cellClassicalSobolevConstant_nonneg K m.val) hS)
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (K - 4 + 1)))
  refine ⟨B, hB, ?_⟩
  intro x w r n hw hn t ht X
  apply coordinate_word_joint_derivative_bound d N (K - 4)
    (fun p Y => realClassicalLift K (mapTorusHk Complex.reCLM (u x p Y t)))
    _ _ _ B hB _ w r n hw (by omega) X
  · intro p hp m hm
    exact independent_classical_fast_jet_joint_continuous K m (by omega) (c x p) ((hc x).1 p hp)
      (fun Y => u x p Y t) t (fun Y => hu x p hp Y t ht) (R p) (fun Y => hb x p hp Y t)
  · intro p hp Y
    exact realClassicalLift_contDiff K (K - 4) (by omega) _
  · intro p hp m hm i Y z
    exact coordinate_word_classical_derivative (hab x) N K hH (QG x) (Qf x) (QF x) (P x) (hP x) (v x) (hv x) (hPv x) (V x)
      (c x) (hc x) (hsol x) (hf x) (hF x) (u x) (hu x) p hp Y i t ht m (by omega) z
  · intro p hp m hm Y z
    exact ((realHigherCarrier_derivative_norm_le K m (by omega) (u x p Y t) z).trans
      (mul_le_mul_of_nonneg_left ((hb x p hp Y t).trans (hRS p hp))
        (cellClassicalSobolevConstant_nonneg K m))).trans (hprice m hm)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The exact phase lattice translation set connects produced inverse invariance to appended periodic sampling. -/
@[expose] public noncomputable section
open Homogenization AVenhance Set
namespace AVRegularity.EntryWeakProofs

def independentFreshPhaseTranslations (r : ℕ) : Set (Vec (2 + 4 * r)) :=
  {δ | independentIntrinsicSlowProjection (4 * r) δ = 0 ∧
    (∀ j, independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) δ) = 0) ∧
    ∀ j, ∃ n : Fin 2 → ℤ, independentFreshChildProjection j true
      (independentStoredParameterProjection (4 * r) δ) = latticeShift n}

theorem independentFreshPhaseTranslations_of_equivalent {r : ℕ} (Y Z : Vec (2 + 4 * r))
    (hslow : independentIntrinsicSlowProjection (4 * r) Y = independentIntrinsicSlowProjection (4 * r) Z)
    (hc : ∀ j, independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y) =
      independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Z))
    (hp : ∀ j, ∃ n : Fin 2 → ℤ, independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Y) =
      independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Z) + latticeShift n) :
    Y - Z ∈ independentFreshPhaseTranslations r := by
  constructor
  · rw [map_sub, hslow, sub_self]
  constructor
  · intro j
    rw [map_sub, map_sub, hc j, sub_self]
  · intro j
    obtain ⟨n, hn⟩ := hp j
    refine ⟨n, ?_⟩
    rw [map_sub, map_sub, hn]
    abel

theorem independentFresh_zero_slow_sampling_phase_invariant {r : ℕ} {E : Type*}
    (f : Vec (2 + 4 * r) → E)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations r, ∀ Y, f (Y + δ) = f Y)
    (P Q : Vec (4 * r))
    (hc : ∀ j, independentFreshChildProjection j false P = independentFreshChildProjection j false Q)
    (hp : ∀ j, ∃ n : Fin 2 → ℤ, independentFreshChildProjection j true P =
      independentFreshChildProjection j true Q + latticeShift n) :
    f (independentIntrinsicParameterPacking (4 * r) 0 P) =
      f (independentIntrinsicParameterPacking (4 * r) 0 Q) := by
  let Y := independentIntrinsicParameterPacking (4 * r) 0 P
  let Z := independentIntrinsicParameterPacking (4 * r) 0 Q
  have hYZ : Y - Z ∈ independentFreshPhaseTranslations r := by
    apply independentFreshPhaseTranslations_of_equivalent Y Z
    · simp only [Y, Z, independentIntrinsicParameterPacking_slow]
    · simpa only [Y, Z, independentIntrinsicParameterPacking_stored] using hc
    · simpa only [Y, Z, independentIntrinsicParameterPacking_stored] using hp
  have he : Z + (Y - Z) = Y := by abel
  have hh := hf (Y - Z) hYZ Z
  rw [he] at hh
  exact hh

theorem independentFreshCutoffMetric_phase_translation {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (level : ℕ) (A : RealChain) (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (hp : ∀ p ∈ A.slots ++ List.ofFn slots, Odd p) (ρ a b t : ℝ)
    (χ : Vec (2 + 4 * r) → ℝ)
    (hχ : ∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ Y = χ Z)
    (δ : Vec (2 + 4 * r)) (hδ : δ ∈ independentFreshPhaseTranslations r) (Y : Vec (2 + 4 * r)) :
    clampedParameterMetric (cutoffParameterMetric χ
      (independentFreshNativeMetric D level A slots birthLength ρ)) a b t (Y + δ) =
      clampedParameterMetric (cutoffParameterMetric χ
        (independentFreshNativeMetric D level A slots birthLength ρ)) a b t Y := by
  apply independentFreshCutoffMetric_eq_of_phase_lattice D hΛ level A hA slots birthLength hp ρ a b t χ hχ
  · rw [map_add, hδ.1, add_zero]
  · intro j
    rw [map_add, map_add, hδ.2.1 j, add_zero]
  · intro j
    obtain ⟨n, hn⟩ := hδ.2.2 j
    exact ⟨n, by rw [map_add, map_add, hn]⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Equal-depth coordinate transport preserves the full phase symmetry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentSource_phase_dimension_cast {r s : ℕ} (he : r = s)
    (f : ℝ → Vec 2 → Vec (2 + 4 * r) → Vec 2)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations r, IndependentSourceTranslationInvariant δ f) :
    ∀ δ ∈ independentFreshPhaseTranslations s, IndependentSourceTranslationInvariant δ
      (fun t z Y => f t z (Eq.rec (motive := fun n _ => Vec (2 + 4 * n)) Y he.symm)) := by
  subst s
  exact hf

end AVRegularity.EntryWeakProofs
end
end

section
/-! The geometric-coordinate projection removes phases before applying a bounded smooth clamp. -/
@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.EntryWeakProofs

def independentFreshCarrierMask (r : ℕ) : Vec (2 + 4 * r) →L[ℝ] Vec (2 + 4 * r) :=
  ContinuousLinearMap.pi (fun i => if i.val < 2 ∨ (i.val - 2) % 4 < 2 then
    ContinuousLinearMap.proj i else 0)

theorem independentFreshCarrierMask_idempotent (r : ℕ) (Y : Vec (2 + 4 * r)) :
    independentFreshCarrierMask r (independentFreshCarrierMask r Y) = independentFreshCarrierMask r Y := by
  funext i
  by_cases hi : i.val < 2 ∨ (i.val - 2) % 4 < 2
  · simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply, ite_eq_left hi,
      ContinuousLinearMap.proj_apply]
  · simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply, ite_eq_right hi, zero_apply]

theorem independentFreshCarrierMask_norm_le (r : ℕ) : ‖independentFreshCarrierMask r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro i
  simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply]
  split
  · exact norm_le_pi_norm Y i
  · simp only [zero_apply, norm_zero, norm_nonneg]

theorem independentFreshCarrierMask_norm_le_coordinates (r : ℕ) (Y : Vec (2 + 4 * r)) :
    ‖independentFreshCarrierMask r Y‖ ≤ ‖independentFreshCarrierCoordinates r Y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply]
  split
  · rename_i hi
    change ‖Y i‖ ≤ _
    by_cases hslow : i.val < 2
    · have he : (⟨i.val, hslow⟩ : Fin 2).castAdd (4 * r) = i := Fin.ext rfl
      have hh := norm_le_pi_norm (independentIntrinsicSlowProjection (4 * r) Y) ⟨i.val, hslow⟩
      change ‖Y (Fin.castAdd (4 * r) ⟨i.val, hslow⟩)‖ ≤ _ at hh
      rw [he] at hh
      exact hh.trans (independentFreshCarrierCoordinates_slow_bound r Y)
    · have hk : (i.val - 2) % 4 < 2 := hi.resolve_left hslow
      let j : Fin r := ⟨(i.val - 2) / 4, by have := i.is_lt; omega⟩
      let k : Fin 2 := ⟨(i.val - 2) % 4, hk⟩
      have he : (independentFreshChildCoordinate j false k).natAdd 2 = i := by
        apply Fin.ext
        change 2 + (4 * ((i.val - 2) / 4) + 0 + (i.val - 2) % 4) = i.val
        omega
      have hh := norm_le_pi_norm
        (independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y)) k
      change ‖Y ((independentFreshChildCoordinate j false k).natAdd 2)‖ ≤ _ at hh
      rw [he] at hh
      exact hh.trans (independentFreshCarrierCoordinates_center_bound r Y j)
  · simp only [zero_apply, norm_zero, norm_nonneg]

theorem independentFreshCarrierMask_phase_zero (r : ℕ) (δ : Vec (2 + 4 * r))
    (hδ : δ ∈ independentFreshPhaseTranslations r) : independentFreshCarrierMask r δ = 0 := by
  have he : independentFreshCarrierCoordinates r δ = 0 := by
    apply Prod.ext
    · exact funext (fun j => hδ.2.1 j)
    · exact hδ.1
  have hb := independentFreshCarrierMask_norm_le_coordinates r δ
  rw [he, norm_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

def independentFreshGeometryClamp (r : ℕ) : Vec (2 + 4 * r) → Vec (2 + 4 * r) :=
  independentProjectionClamp (independentFreshCarrierMask r)

theorem independentFreshGeometryClamp_contDiff (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshGeometryClamp r) :=
  independentProjectionClamp_contDiff _

theorem independentFreshGeometryClamp_identity_germ (r : ℕ) (Y : Vec (2 + 4 * r))
    (hY : ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4) :
    independentFreshGeometryClamp r =ᶠ[𝓝 Y] id :=
  independentProjectionClamp_identity_germ _ _
    ((independentFreshCarrierMask_norm_le_coordinates r Y).trans_lt hY)

theorem independentFreshGeometryClamp_phase_translation (r : ℕ) (δ Y : Vec (2 + 4 * r))
    (hδ : δ ∈ independentFreshPhaseTranslations r) :
    independentFreshGeometryClamp r (Y + δ) = independentFreshGeometryClamp r Y + δ :=
  independentProjectionClamp_kernel_translation _ _ _ (independentFreshCarrierMask_phase_zero r δ hδ)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full coarse append sampling preserves fast periodicity through the stored phase lattice. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendPacking_phase_equivalent
    (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (parentSlot slot : ℤ)
    (hp : Odd parentSlot) (ell t : ℝ) (Y : Vec (2 + 4 * r)) (z : Vec 2) (n : Fin 2 → ℤ) :
    (∀ j, independentFreshChildProjection j false
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z + latticeShift n, Y)) =
        independentFreshChildProjection j false
          (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y))) ∧
    (∀ j, ∃ q : Fin 2 → ℤ, independentFreshChildProjection j true
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z + latticeShift n, Y)) =
        independentFreshChildProjection j true
          (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y)) + latticeShift q) := by
  dsimp only [independentFreshCoarseAppendPacking]
  rw [weak_relative_displacement_periodic D hΛ m parentSlot hp]
  have he : z + latticeShift n + D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z =
      (z + D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t z) + latticeShift n := by abel
  rw [he]
  exact independentFreshInsertCoordinates_phase_equivalent r _ _ _ n

theorem independentFreshCoarseAppendedNativeSource_periodic {E : Type*}
    (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (parentSlot slot : ℤ)
    (hp : Odd parentSlot) (ell t : ℝ) (Y : Vec (2 + 4 * r))
    (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → E)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations (r + 1), IndependentSourceTranslationInvariant δ f) :
    IsZ2Periodic (fun z => f t 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
      (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y)))) := by
  intro n z
  obtain ⟨hc, hphase⟩ := independentFreshCoarseAppendPacking_phase_equivalent r D hΛ m parentSlot slot hp ell t Y z n
  exact independentFresh_zero_slow_sampling_phase_invariant (f t 0)
    (fun δ hδ W => hf δ hδ t 0 W) _ _ hc hphase

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native physical families have no child-center boundary under slow recentering. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
open Providers.GenSem

theorem weak_admissible_recenter_empty (D : OCData) (bw : ℝ) (j₀ level : ℕ)
    (slot : ℤ) (A : RealChain) (hchildren : A.children = [])
    (hA : IsAdmissibleChain D bw j₀ level slot A) (h : Vec 2) :
    IsAdmissibleChain D bw j₀ level slot (A.recenter D h) := by
  rw [recenter_nil D A hchildren]
  exact hA

end AVRegularity.EntryWeakProofs
end
end

section
/-! Clamped parameters lie in the reserved center strip and retain their literal phases. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCarrierMask_coordinates (r : ℕ) (Y : Vec (2 + 4 * r)) :
    independentFreshCarrierCoordinates r (independentFreshCarrierMask r Y) =
      independentFreshCarrierCoordinates r Y := by
  apply Prod.ext
  · funext j k
    change independentFreshCarrierMask r Y
      ((independentFreshChildCoordinate j false k).natAdd 2) =
        Y ((independentFreshChildCoordinate j false k).natAdd 2)
    have hi : ((independentFreshChildCoordinate j false k).natAdd 2).val < 2 ∨
        (((independentFreshChildCoordinate j false k).natAdd 2).val - 2) % 4 < 2 := by
      right
      change (2 + (4 * j.val + 0 + k.val) - 2) % 4 < 2
      omega
    simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply, ite_eq_left hi,
      ContinuousLinearMap.proj_apply]
  · funext k
    change independentFreshCarrierMask r Y (k.castAdd (4 * r)) = Y (k.castAdd (4 * r))
    have hi : (k.castAdd (4 * r)).val < 2 ∨ ((k.castAdd (4 * r)).val - 2) % 4 < 2 :=
      Or.inl k.is_lt
    simp only [independentFreshCarrierMask, ContinuousLinearMap.pi_apply, ite_eq_left hi,
      ContinuousLinearMap.proj_apply]

theorem independentFreshGeometryClamp_carrier_bound (r : ℕ) (Y : Vec (2 + 4 * r)) :
    ‖independentFreshCarrierCoordinates r (independentFreshGeometryClamp r Y)‖ ≤ 1 / 2 := by
  rw [← independentFreshCarrierMask_coordinates r (independentFreshGeometryClamp r Y)]
  have hh := (independentFreshCarrierCoordinates r).le_opNorm
    (independentFreshCarrierMask r (independentFreshGeometryClamp r Y))
  have hn := mul_le_mul_of_nonneg_right (independentFreshCarrierCoordinates_norm_le r)
    (norm_nonneg (independentFreshCarrierMask r (independentFreshGeometryClamp r Y)))
  have hle : ‖independentFreshCarrierCoordinates r
      (independentFreshCarrierMask r (independentFreshGeometryClamp r Y))‖ ≤
      ‖independentFreshCarrierMask r (independentFreshGeometryClamp r Y)‖ :=
    hh.trans (by simpa only [one_mul] using hn)
  apply hle.trans
  exact independentProjectionClamp_project_norm _ (independentFreshCarrierMask_idempotent r) Y

theorem independentFreshGeometryClamp_center_strip (r : ℕ) (Y : Vec (2 + 4 * r)) :
    independentFreshCenterStrip (independentStoredParameterProjection (4 * r)
      (independentFreshGeometryClamp r Y)) := by
  intro j
  exact ((independentFreshCarrierCoordinates_center_bound r _ j).trans
    (independentFreshGeometryClamp_carrier_bound r Y)).trans (by norm_num)

theorem independentFreshGeometryClamp_slow_bound (r : ℕ) (Y : Vec (2 + 4 * r)) :
    ‖independentIntrinsicSlowProjection (4 * r) (independentFreshGeometryClamp r Y)‖ ≤ 1 / 2 :=
  (independentFreshCarrierCoordinates_slow_bound r _).trans
    (independentFreshGeometryClamp_carrier_bound r Y)

theorem independentFreshGeometryClamp_positive_jet_budget (r : ℕ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n, 1 ≤ n → ∀ Y,
      ‖iteratedFDeriv ℝ n (independentFreshGeometryClamp r) Y‖ ≤ B n :=
  independentProjectionClamp_positive_jet_budget _ (independentFreshCarrierMask_norm_le r)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! One threshold gives the actual native model strong ellipticity at every independent parameter. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_scaled_metric_eventually_elliptic (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A → ∀ ρ : ℝ,
      ∀ t ∈ Set.Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel),
      ∀ (Y : Vec (2 + 4 * A.children.length)) (ξ : Vec 2),
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j ∧
        (∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2 := by
  obtain ⟨M, hM, hprod⟩ := uniform_scheduled_weak_metric_eventually_elliptic
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq hband A hbase hdepth bw j₀ hA ρ t ht Y ξ
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hl : A.WellSlotted := hA.2.2.1
  let B := fun P : Vec (4 * A.children.length) => independentFreshChain (independentFreshBaseChain A)
    (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A) P
  have hrec : B (independentFreshCoarseChainPacking D A) = A :=
    independentFreshCoarseChainPacking_reconstruct D hΛ₁ A hl
  have hb (P : Vec (4 * A.children.length)) : (B P).baseLevel = A.baseLevel := rfl
  have hs (P : Vec (4 * A.children.length)) : (B P).slots = A.slots := by
    calc
      _ = (B (independentFreshCoarseChainPacking D A)).slots := rfl
      _ = A.slots := congrArg RealChain.slots hrec
  have hc (P : Vec (4 * A.children.length)) : (B P).children.length = A.children.length := by
    calc
      _ = (B (independentFreshCoarseChainPacking D A)).children.length := by
        simp only [B, independentFreshChain, independentFreshBaseChain, List.length_append, List.length_ofFn]
      _ = A.children.length := congrArg (fun C : RealChain => C.children.length) hrec
  let P := independentStoredParameterProjection (4 * A.children.length) Y
  have hctx : (B P).ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hc]
  have hslot : (B P).slot = A.slot := by simp only [RealChain.slot, hs]
  have he := hprod D hDα hDq hDΛ hDζ hseq (B P) A.ctxLevel A.slot
    (by rw [hb]; exact hbase) (by rw [hc]; exact hdepth) hctx
    (by rw [hs, hc]; exact hl) hslot
    (fun q hq => hA.2.2.2.2.1 q (by rw [← hs P]; exact hq))
    (fun k hk => by
      have hk' : k + 1 < A.slots.length := by rw [← hs P]; exact hk
      simpa only [hb, hs] using hA.2.2.2.2.2.1 k hk')
    (D.cellScaleSq A.ctxLevel * t)
    (weak_lift_clock_in_pulse_window D hΛ₁ hζ' hband A.ctxLevel A.slot t ht)
    (ρ • independentIntrinsicSlowProjection (4 * A.children.length) Y) ξ
  simpa only [actualIndependentCoarseScaledMetric, independentFreshNativeMetric,
    independentFreshStoredFamily_eq_chain, B, P] using he

end AVRegularity.EntryWeakProofs
end
end

section
/-! The finite clamp cost is chosen before every stream datum and source weight. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

theorem independentFreshGeometryClamp_finite_jet_cost (r H : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n, 1 ≤ n → n ≤ H → ∀ Y,
      ‖iteratedFDeriv ℝ n (independentFreshGeometryClamp r) Y‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := independentFreshGeometryClamp_positive_jet_budget r
  let C := 1 + ∑ n : Fin (H + 1), B n.val
  have hsum : 0 ≤ ∑ n : Fin (H + 1), B n.val := Finset.sum_nonneg (fun n _ => hB n.val)
  refine ⟨C, le_add_of_nonneg_right hsum, ?_⟩
  intro n hn hnH Y
  have hentry : B n ≤ ∑ j : Fin (H + 1), B j.val :=
    Finset.single_le_sum (fun (j : Fin (H + 1)) _ => hB j.val)
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (H + 1)))
  exact (hb n hn Y).trans (hentry.trans (le_add_of_nonneg_left zero_le_one))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual appended source sampling is measurable along the moving native family. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

theorem relDisp_lower_time_joint_continuous (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (u : ℝ) :
    Continuous (fun X : ℝ × Vec 2 => D.relDisp m slot u X.1 X.2) := by
  have he : (fun X : ℝ × Vec 2 => D.relDisp m slot u X.1 X.2) =
      fun X => -D.relDisp m slot X.1 u X.2 := by
    funext X
    dsimp only [OCData.relDisp]
    rw [intervalIntegral.integral_symm u X.1]
    simp only [neg_smul, smul_neg]
  rw [he]
  exact (contDiff_relDisp D hζ m slot u).continuous.neg

end AVRegularity.EntryWeakProofs
end
end

section
/-! A fixed finite clamp price may be selected before all physical data. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def independentFreshGeometryClampJetCost (r H : ℕ) : ℝ :=
  Classical.choose (independentFreshGeometryClamp_finite_jet_cost r H)

theorem independentFreshGeometryClampJetCost_ge_one (r H : ℕ) :
    1 ≤ independentFreshGeometryClampJetCost r H :=
  (Classical.choose_spec (independentFreshGeometryClamp_finite_jet_cost r H)).1

theorem independentFreshGeometryClampJetCost_bound (r H n : ℕ) (hn : 1 ≤ n) (hnH : n ≤ H)
    (Y : Homogenization.Vec (2 + 4 * r)) :
    ‖iteratedFDeriv ℝ n (independentFreshGeometryClamp r) Y‖ ≤ independentFreshGeometryClampJetCost r H :=
  (Classical.choose_spec (independentFreshGeometryClamp_finite_jet_cost r H)).2 n hn hnH Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full Piola parameter packing is contractive and permits a phase-preserving geometric clamp. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshMovingTransferCoordinates (r : ℕ) :
    ((Vec 2 × Vec (2 + 4 * r)) × Vec 2) →L[ℝ]
      (((Vec (4 * r) × Vec 2) × Vec 2) × Vec 2) :=
  let A := ContinuousLinearMap.fst ℝ (Vec 2 × Vec (2 + 4 * r)) (Vec 2)
  let B := (ContinuousLinearMap.snd ℝ (Vec 2) (Vec (2 + 4 * r))).comp A
  let P := (independentStoredParameterProjection (4 * r)).comp B
  let X := (independentIntrinsicSlowProjection (4 * r)).comp B
  let z := (ContinuousLinearMap.fst ℝ (Vec 2) (Vec (2 + 4 * r))).comp A
  ((P.prod X).prod z).prod (ContinuousLinearMap.snd ℝ _ _)

theorem independentFreshMovingTransferCoordinates_norm_le (r : ℕ) :
    ‖independentFreshMovingTransferCoordinates r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  change max (max ‖independentFreshParameterCoordinates r Y.1.2‖ ‖Y.1.1‖) ‖Y.2‖ ≤ 1 * ‖Y‖
  rw [one_mul]
  have hc := (independentFreshParameterCoordinates r).le_opNorm Y.1.2
  have hb := mul_le_mul_of_nonneg_right (independentFreshParameterCoordinates_norm_le r)
    (norm_nonneg Y.1.2)
  have hcoords : ‖independentFreshParameterCoordinates r Y.1.2‖ ≤ ‖Y.1.2‖ :=
    hc.trans (by simpa only [one_mul] using hb)
  exact max_le (max_le (hcoords.trans ((norm_snd_le Y.1).trans (norm_fst_le Y)))
    ((norm_fst_le Y.1).trans (norm_fst_le Y))) (norm_snd_le Y)

def independentFreshClampedMovingTransferCoordinates (r : ℕ) :
    ((Vec 2 × Vec (2 + 4 * r)) × Vec 2) → (((Vec (4 * r) × Vec 2) × Vec 2) × Vec 2) :=
  independentFreshMovingTransferCoordinates r ∘ independentParameterExtension (independentFreshGeometryClamp r)

theorem independentFreshClampedMovingTransferCoordinates_contDiff (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshClampedMovingTransferCoordinates r) :=
  (independentFreshMovingTransferCoordinates r).contDiff.comp
    (independentParameterExtension_contDiff _ (independentFreshGeometryClamp_contDiff r))

theorem independentFreshClampedMovingTransferCoordinates_positive_jets (r H n : ℕ)
    (hn : 1 ≤ n) (hnH : n ≤ H) (C : ℝ) (hC : 1 ≤ C)
    (hclamp : ∀ j, 1 ≤ j → j ≤ H → ∀ Y,
      ‖iteratedFDeriv ℝ j (independentFreshGeometryClamp r) Y‖ ≤ C)
    (X : (Vec 2 × Vec (2 + 4 * r)) × Vec 2) :
    ‖iteratedFDeriv ℝ n (independentFreshClampedMovingTransferCoordinates r) X‖ ≤ C := by
  let T := independentParameterExtension (V := Vec 2) (W := Vec 2) (independentFreshGeometryClamp r)
  have hT := independentParameterExtension_contDiff (V := Vec 2) (W := Vec 2)
    _ (independentFreshGeometryClamp_contDiff r)
  have hh := (independentFreshMovingTransferCoordinates r).norm_iteratedFDeriv_comp_left
    hT.contDiffAt (n := n) (by simp) (x := X)
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right (independentFreshMovingTransferCoordinates_norm_le r)
    (norm_nonneg (iteratedFDeriv ℝ n T X))
  have hnorm : ‖independentFreshMovingTransferCoordinates r‖ * ‖iteratedFDeriv ℝ n T X‖ ≤
      ‖iteratedFDeriv ℝ n T X‖ := by simpa only [one_mul] using hm
  exact hnorm.trans
    (independentParameterExtension_positive_jet_bound _ (independentFreshGeometryClamp_contDiff r)
      H n hn hnH C hC hclamp X)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full coarse append sampling is measurable along its literal moving family. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendPacking_joint_continuous
    (r : ℕ) (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (parentSlot slot : ℤ)
    (ell : ℝ) (Y : Vec (2 + 4 * r)) :
    Continuous (fun X : ℝ × Vec 2 => independentFreshCoarseAppendPacking r D m parentSlot slot ell X.1 (X.2, Y)) := by
  have hδ := relDisp_lower_time_joint_continuous D hζ m parentSlot (D.slotAnchor (m + 1) slot)
  have hP : Continuous (fun _ : ℝ × Vec 2 => independentStoredParameterProjection (4 * r) Y) := continuous_const
  have hX : Continuous (fun _ : ℝ × Vec 2 => independentIntrinsicSlowProjection (4 * r) Y) := continuous_const
  exact (independentFreshInsertCoordinates r).continuous.comp
    (hP.prodMk ((hX.add (hδ.const_smul ell)).prodMk (continuous_snd.add hδ)))

theorem IndependentParameterSourceReserve.coarseAppendedNative_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (r : ℕ) (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) (parentSlot slot : ℤ)
    (ell : ℝ) (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → E) {K : ℕ}
    (Q : IndependentParameterSourceReserve K f) (Y : Vec (2 + 4 * r)) :
    Measurable (fun X : ℝ × Vec 2 => f X.1 0
      (independentIntrinsicParameterPacking (4 * (r + 1)) 0
        (independentFreshCoarseAppendPacking r D m parentSlot slot ell X.1 (X.2, Y)))) := by
  have hpack := independentFreshCoarseAppendPacking_joint_continuous r D hζ m parentSlot slot ell Y
  have hs := (independentStoredParameterEmbedding (4 * (r + 1))).continuous.comp hpack
  have hm : Measurable (fun X : ℝ × Vec 2 =>
      (X.1, ((0 : Vec 2), independentStoredParameterEmbedding (4 * (r + 1))
        (independentFreshCoarseAppendPacking r D m parentSlot slot ell X.1 (X.2, Y))))) :=
    measurable_fst.prodMk (measurable_const.prodMk hs.measurable)
  have hh := Q.joint_measurable.comp hm
  simpa only [Function.comp_def, independentStoredParameterEmbedding_eq_packing] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual admissible families have an open independent carrier; no boundary cutoff regularity is assumed. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseStoredCarrier (D : OCData) (A : RealChain) (bw : ℝ) : Set (Vec (4 * A.children.length)) :=
  {P | ∀ j : Fin A.children.length,
    ∑ i : Fin 2, |(independentFreshChild (independentFreshCoarseBirthLength D A) j P).center i| <
      (1 + 2) * bw / 4 * D.eps (A.baseLevel + 1 + j)}

theorem actualIndependentCoarseStoredCarrier_isOpen (D : OCData) (A : RealChain) (bw : ℝ) :
    IsOpen (actualIndependentCoarseStoredCarrier D A bw) := by
  unfold actualIndependentCoarseStoredCarrier
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt ?_ continuous_const
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (((continuous_apply i).comp (independentFreshChildProjection j false).continuous).const_smul
    (independentFreshCoarseBirthLength D A j)).abs

def actualIndependentCoarseNativeCarrier (D : OCData) (A : RealChain) (bw : ℝ) : Set (Vec (2 + 4 * A.children.length)) :=
  (independentStoredParameterProjection (4 * A.children.length)) ⁻¹' actualIndependentCoarseStoredCarrier D A bw ∩
    {Y | ‖independentFreshCarrierCoordinates A.children.length Y‖ < 1 / 4}

theorem actualIndependentCoarseNativeCarrier_isOpen (D : OCData) (A : RealChain) (bw : ℝ) :
    IsOpen (actualIndependentCoarseNativeCarrier D A bw) :=
  ((actualIndependentCoarseStoredCarrier_isOpen D A bw).preimage
    (independentStoredParameterProjection _).continuous).inter
    (isOpen_lt (independentFreshCarrierCoordinates _).continuous.norm continuous_const)

theorem actualIndependentCoarseNativeCarrier_admissible (D : OCData) (A : RealChain) (bw : ℝ)
    (j₀ level : ℕ) (slot : ℤ) (hA : IsAdmissibleChain D bw j₀ level slot A)
    (Y : Vec (2 + 4 * A.children.length)) (hY : Y ∈ actualIndependentCoarseNativeCarrier D A bw) :
    IsAdmissibleChain D bw j₀ level slot
      (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) :=
  (actualIndependentCoarseParameterChain_admissible_iff D A bw j₀ level slot hA _).mpr hY.1

theorem actualIndependentCoarseNativeCarrier_native (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (A : RealChain)
    (bw : ℝ) (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (X : Vec 2) (hX : ‖X‖ ≤ 1 / 8) :
    independentIntrinsicParameterPacking (4 * A.children.length) X
      (independentFreshCoarseChainPacking D A) ∈ actualIndependentCoarseNativeCarrier D A bw := by
  constructor
  · rw [mem_preimage, independentIntrinsicParameterPacking_stored]
    apply (actualIndependentCoarseParameterChain_admissible_iff D A bw j₀ level slot hA _).mp
    rw [actualIndependentCoarseParameterChain_native D (by omega) A hA.2.2.1]
    exact hA
  · apply lt_of_le_of_lt ?_ (by norm_num : (1 / 8 : ℝ) < 1 / 4)
    apply independentFreshCarrierCoordinates_norm_le_of_bounds _ _ (1 / 8) (by norm_num)
    · intro j
      rw [independentIntrinsicParameterPacking_stored]
      exact independentFreshCoarseChainPacking_center_bound D hq hΛ A bw hbw j₀ level slot hA j
    · rw [independentIntrinsicParameterPacking_slow]
      exact hX

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every member of the actual stored carrier retains the same inner center bound. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseStoredCarrier_center_bound (D : OCData)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (A : RealChain) (bw : ℝ)
    (hbw : bw ≤ 1 / 10000) (P : Vec (4 * A.children.length))
    (hP : P ∈ actualIndependentCoarseStoredCarrier D A bw) (j : Fin A.children.length) :
    ‖independentFreshChildProjection j false P‖ ≤ 1 / 8 := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  let c := independentFreshChild (independentFreshCoarseBirthLength D A) j P
  have hc : ‖(D.eps (A.baseLevel + 1 + j))⁻¹ • c.center‖ ≤ 1 / 8 := by
    have hh := normalized_center_norm_lt (D.eps (A.baseLevel + 1 + j))
      ((1 + 2) * bw / 4) (Construction.Stream.ocEpsilon_pos hΛ₁) c.center (hP j)
    exact hh.le.trans (by linarith only [hbw])
  have hp : 0 < independentFreshCoarseBirthLength D A j :=
    Construction.Stream.ocEpsilon_pos hΛ₁
  have hh := normalized_center_norm_le_of_length_le (D.eps (A.baseLevel + 1 + j))
    (independentFreshCoarseBirthLength D A j) (1 / 8)
    (Construction.Stream.ocEpsilon_pos hΛ₁) hp
    (EntryScales.epsilon_antitone hq hΛ (by
      change A.baseLevel + j.val ≤ A.baseLevel + 1 + j.val
      omega)) c.center hc
  simpa only [c, independentFreshChild, smul_smul, inv_mul_cancel₀ hp.ne', one_smul] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Empty-base fresh families have an open joint recentering carrier at every depth. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChain_empty_base_recenter_carrier_isOpen {r : ℕ}
    (D : OCData) (A : RealChain) (hA : A.WellSlotted) (hchildren : A.children = [])
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ bw : ℝ)
    (j₀ level : ℕ) (slot : ℤ) (P₀ : Vec (4 * r))
    (h₀ : IsAdmissibleChain D bw j₀ level slot
      (independentFreshChain A slots birthLength P₀)) :
    IsOpen {Y : Vec (4 * r) × Vec 2 |
      IsAdmissibleChain D bw j₀ level slot
        ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2))} := by
  cases r with
  | zero =>
    have he (P : Vec (4 * 0)) : independentFreshChain A slots birthLength P = A := by
      simp only [independentFreshChain, List.ofFn_zero, List.append_nil]
    rw [he P₀] at h₀
    have hs : {Y : Vec (4 * 0) × Vec 2 |
        IsAdmissibleChain D bw j₀ level slot
          ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2))} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro Y
      change IsAdmissibleChain D bw j₀ level slot
        ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2))
      rw [he Y.1]
      exact weak_admissible_recenter_empty D bw j₀ level slot A hchildren h₀ _
    rw [hs]
    exact isOpen_univ
  | succ r =>
    exact independentFreshChain_recenter_carrier_isOpen_succ
      D A hA slots birthLength ρ bw j₀ level slot P₀ h₀

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual molecular native metrics have one full mixed price before D and every admissible family. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_family_coarse_scaled_metric_jets (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J K : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J →
      ∀ (bw : ℝ) (j₀ : ℕ), IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ σ : ℝ, 0 < σ → σ ≤ D.eps A.lastLevel → ∀ t ∈ Set.Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel),
      ∀ Y : Vec (2 + 4 * A.children.length),
      independentFreshCenterStrip (independentStoredParameterProjection (4 * A.children.length) Y) →
      ‖independentIntrinsicSlowProjection (4 * A.children.length) Y‖ ≤ 1 → ∀ n ≤ K,
      ‖iteratedFDeriv ℝ n (independentFreshNativeMetric D A.ctxLevel (independentFreshBaseChain A)
        (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A)
        σ t) Y‖ ≤ nativeWeakMixedMetricBudget K J 1 := by
  choose M hM hchart using fun r => uniform_fresh_native_coarse_chart_production α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ r
  let M₀ := ∑ r ∈ Finset.range (J + 1), M r
  have hle (r : ℕ) (hr : r ≤ J) : M r ≤ M₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  refine ⟨M₀, (hM 0).trans (hle 0 (Nat.zero_le J)), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq hband A hAM hdepth bw j₀ hA σ hσ hσle t ht Y hY hS n hn
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  let r := A.children.length
  let ρ := D.eps (A.baseLevel + r)
  let ell := σ / ρ
  have hρ : 0 < ρ := Construction.Stream.ocEpsilon_pos hΛ₁
  have hell : |ell| ≤ 1 := by
    change |σ / ρ| ≤ 1
    rw [abs_of_pos (div_pos hσ hρ), div_le_one hρ]
    exact hσle
  have hscale : σ = ρ * ell := by
    dsimp only [ell]
    rw [mul_div_cancel₀ _ hρ.ne']
  have hslots : (independentFreshBaseChain A).slots = [realChainSlotSeq A 0] := rfl
  have hchildren : (independentFreshBaseChain A).children = [] := rfl
  have hreserve : independentFreshNativeChartReserve D (independentFreshBaseChain A)
      (fun j : Fin r => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A)
      ρ (nativeWeakChartWindow D A.baseLevel r (realChainSlotSeq A) r) (K + 1) 1
      (nativeMixedChartBudget (K + 1) r 1) := by
    have hb := hchart r D hDα hDq hDΛ hDζ hseq (independentFreshBaseChain A)
      ((hle r hdepth).trans hAM) (independentFreshBaseChain_wellSlotted A) hchildren (realChainSlotSeq A) hslots
      (fun k hk => realChainSlotSeq_odd D A hA k hk)
      (fun k hk => realChainSlotSeq_scheduled D A hA k hk) r le_rfl (K + 1) 1
    change independentFreshNativeChartReserve D (independentFreshBaseChain A)
      (fun j : Fin r => realChainSlotSeq A (j + 1)) (fun j => D.eps (A.baseLevel + j))
      ρ (nativeWeakChartWindow D A.baseLevel r (realChainSlotSeq A) r) (K + 1) 1
      (nativeMixedChartBudget (K + 1) r 1) at hb
    have hbirth : (fun j : Fin r => D.eps (A.baseLevel + j)) = independentFreshCoarseBirthLength D A := rfl
    rw [hbirth] at hb
    exact hb
  have harea : ∀ P, GeomAreaPreserving ((independentFreshChain (independentFreshBaseChain A)
      (fun j : Fin r => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A) P).geom D) := by
    intro P
    change GeomAreaPreserving ((independentFreshChain (independentFreshBaseChain A)
      (fun j : Fin r => realChainSlotSeq A (j + 1)) (fun j => D.eps (A.baseLevel + j)) P).geom D)
    rw [independentFreshChain_geom_eq_indexed D (independentFreshBaseChain A) (realChainSlotSeq A)
      hchildren hslots (fun j => D.eps (A.baseLevel + j)) P]
    exact finiteWeakChainGeom_area_preserving D hΛ₁ A.baseLevel A.base (realChainSlotSeq A) _ r
      (fun j hj => realChainSlotSeq_odd D A hA j (by omega))
  rw [hscale]
  apply (independentFreshNativeMetric_scaled_jet_bound_of_chart_reserve D A.ctxLevel (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) _ _ ρ hρ ell hell _ K 1 _
    (zero_le_one.trans (nativeMixedChartBudget_ge_one _ _ _)) harea hreserve t
    (actual_lift_clock_in_native_chart_window D hΛ₁ hζ' hband A hA.2.2.1 r t ht) Y hY hS n hn).trans
  exact nativeWeakMixedMetricBudget_bound K J 1 r n hdepth hn

end AVRegularity.EntryWeakProofs
end
end

section
/-! Joint time/fast measurability of native inverses uses spatial differentiation of measurable parameters. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem weak_transfer_centered_fast_slow_smooth (D : OCData) (A : RealChain)
    (slot : ℤ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (weakTransferCenteredJoint D A slot t) := by
  let u := D.slotAnchor (A.ctxLevel + 1) slot
  let g := A.geom D
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 × Vec 2 =>
      X.2 + D.relDisp A.ctxLevel A.slot u t (X.1 + X.2)) :=
    contDiff_snd.add ((relDisp_spatial_smooth D A.ctxLevel A.slot u t).comp
      (contDiff_fst.add contDiff_snd))
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => g.1 u y g.2.2) := geomSpatialSmooth_geom D A u g.2.2
  exact ((hg.comp (contDiff_const.add (hh.const_smul (D.eps A.ctxLevel)))).sub
    contDiff_const).const_smul (D.eps A.ctxLevel)⁻¹

theorem weak_transfer_centered_time_fast_slow_continuous (D : OCData) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (slot : ℤ) : Continuous (fun X : (ℝ × Vec 2) × Vec 2 =>
      weakTransferCenteredJoint D A slot X.1.1 (X.1.2, X.2)) := by
  let u := D.slotAnchor (A.ctxLevel + 1) slot
  let g := A.geom D
  have hh : Continuous (fun X : (ℝ × Vec 2) × Vec 2 =>
      X.2 + D.relDisp A.ctxLevel A.slot u X.1.1 (X.1.2 + X.2)) :=
    continuous_snd.add ((relDisp_lower_time_joint_continuous D hζ A.ctxLevel A.slot u).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_snd)))
  have hg : Continuous (fun y => g.1 u y g.2.2) := (geomSpatialSmooth_geom D A u g.2.2).continuous
  exact ((hg.comp (continuous_const.add (hh.const_smul (D.eps A.ctxLevel)))).sub
    continuous_const).const_smul (D.eps A.ctxLevel)⁻¹

theorem weak_transfer_inverse_time_fast_entry_measurable
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot)
    (harea : GeomAreaPreserving (A.geom D)) (slot : ℤ) (h : Vec 2) (i j : Fin 2) :
    Measurable (fun X : ℝ × Vec 2 =>
      (childTransition D slot X.1 (A.recenter D (D.eps A.ctxLevel • h))
        (X.2 + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • h)))⁻¹ i j) := by
  let F := fun (X : ℝ × Vec 2) (y : Vec 2) => weakTransferCenteredJoint D A slot X.1 (X.2, y)
  have hm (y : Vec 2) : Measurable (fun X => F X y) :=
    ((weak_transfer_centered_time_fast_slow_continuous D hζ A slot).comp
      (continuous_id.prodMk continuous_const)).measurable
  have hd (X : ℝ × Vec 2) : Differentiable ℝ (F X) :=
    ((weak_transfer_centered_fast_slow_smooth D A slot X.1).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hdM := fderiv_apply_parameter_measurable F hm hd h (basisVec i.rev)
  have he : (fun X : ℝ × Vec 2 =>
      (childTransition D slot X.1 (A.recenter D (D.eps A.ctxLevel • h))
        (X.2 + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • h)))⁻¹ i j) =
      fun X => (if i = j then (1 : ℝ) else -1) * fderiv ℝ (F X) h (basisVec i.rev) j.rev := by
    funext X
    rw [weak_transfer_matrix_inverse_eq_centered_slow_jacobian_inverse D hΛ hζ A hl slot X.1 (X.2, h)]
    exact planar_inverse_entry_formula _
      (weak_transfer_centered_slow_jacobian_det_one D hΛ hζ A hl hp harea slot X.1 (X.2, h)) i j
  rw [he]
  exact measurable_const.mul ((measurable_pi_apply j.rev).comp hdM)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced finer productions supply a full parent-coordinate source reserve on active windows. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs

def independentFreshCoarseAppendedSource (r : ℕ) (D : OCData) (m : ℕ) (parentSlot slot : ℤ)
    (ell : ℝ) (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → ℝ) :
    ℝ → Vec 2 → Vec (2 + 4 * r) → ℝ :=
  fun t z Y => f t 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0
    (independentFreshCoarseAppendPacking r D m parentSlot slot ell t (z, Y)))

theorem independentFreshCoarseAppendedSource_window_reserve
    (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (parentSlot slot : ℤ) (hp : Odd parentSlot) (ell : ℝ) (hell : |ell| ≤ 1)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K : ℕ) (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → ℝ)
    (Q : IndependentParameterSourceReserve K f) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ j ≤ K, Q.budget j ≤ θ * B)
    (hf : ∀ δ ∈ independentFreshPhaseTranslations (r + 1), IndependentSourceTranslationInvariant δ f) :
    ∃ R : IndependentParameterSourceReserve K
      (independentTimeWindowSource I (independentFreshCoarseAppendedSource r D m parentSlot slot ell f)),
      ∀ n, R.budget n = θ * (K.factorial * B * (1 + (2 * Real.pi) ^ (K + 1)) ^ K) := by
  let g := independentFreshCoarseAppendedSource r D m parentSlot slot ell f
  have hg (t : ℝ) : ContDiff ℝ (K : ℕ∞) (fun X : Vec 2 × Vec (2 + 4 * r) => g t X.1 X.2) :=
    (Q.zeroSlow_contDiff t).comp
      ((independentFreshCoarseAppendPacking_contDiff r D m parentSlot slot ell t).of_le (by simp))
  let R := windowIndependentSourceReserve K I hI g (fun t _ => hg t)
    (fun t _ Y => independentFreshCoarseAppendedNativeSource_periodic r D hΛ m parentSlot slot hp ell t Y f hf)
    (Q.coarseAppendedNative_measurable r D hζ m parentSlot slot ell f)
    (fun _ => θ * (K.factorial * B * (1 + (2 * Real.pi) ^ (K + 1)) ^ K))
    (fun _ => by positivity)
    (fun n hn t ht X => independentFreshCoarseAppendedNativeSource_jet_bound r D hΛ hζ m parentSlot slot hp
      ell t hell (hsmall t ht) K n hn f Q θ B hθ hB hQ X)
  exact ⟨R, fun _ => rfl⟩

end AVRegularity.EntryWeakProofs
end
end
end

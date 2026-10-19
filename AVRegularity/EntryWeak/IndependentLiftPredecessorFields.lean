-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFreshAppendPhasePeriodicity
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

section
section
/-! A finer native slow wavelength is an exact contraction, with stored coordinates unchanged. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeMetric_scale_copy {r : ℕ}
    (D : OCData) (level : ℕ) (A : RealChain) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (ρ ell t : ℝ) :
    independentFreshNativeMetric D level A slots birthLength (ρ * ell) t =
      independentFreshNativeMetric D level A slots birthLength ρ t ∘ independentIntrinsicSlowScaling (4 * r) ell := by
  funext Y
  simp only [independentFreshNativeMetric, Function.comp_apply,
    independentIntrinsicSlowScaling_stored, independentIntrinsicSlowScaling_slow, smul_smul]

theorem independentFreshNativeMetric_contDiff_of_area {r : ℕ}
    (D : OCData) (level : ℕ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (harea : ∀ P, GeomAreaPreserving ((independentFreshChain A slots birthLength P).geom D)) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshNativeMetric D level A slots birthLength ρ t) := by
  let F := fun Z : Vec (4 * r) × Vec 2 =>
    ((independentFreshChain A slots birthLength Z.1).recenter D (ρ • Z.2)).famMetric D (D.cellScaleSq level * t)
  have hf : ContDiff ℝ (⊤ : ℕ∞) F := independent_fresh_centered_metric_contDiff_of_area
    D A hA slots birthLength ρ hρ (D.cellScaleSq level * t) harea
  have he : independentFreshNativeMetric D level A slots birthLength ρ t = F ∘ independentFreshParameterCoordinates r := by
    funext Y
    unfold independentFreshNativeMetric
    rw [independentFreshStoredFamily_eq_chain]
    rfl
  rw [he]
  exact hf.comp (independentFreshParameterCoordinates r).contDiff

theorem independentFreshNativeMetric_scaled_jet_bound_of_chart_reserve {r : ℕ}
    (D : OCData) (level : ℕ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (ell : ℝ) (hell : |ell| ≤ 1) (T : Set ℝ) (K : ℕ) (S B : ℝ) (hB : 0 ≤ B)
    (harea : ∀ P, GeomAreaPreserving ((independentFreshChain A slots birthLength P).geom D))
    (hreserve : independentFreshNativeChartReserve D A slots birthLength ρ T (K + 1) S B)
    (t : ℝ) (ht : D.cellScaleSq level * t ∈ T) (Y : Vec (2 + 4 * r))
    (hY : independentFreshCenterStrip (independentStoredParameterProjection (4 * r) Y))
    (hS : ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ S) (n : ℕ) (hn : n ≤ K) :
    ‖iteratedFDeriv ℝ n (independentFreshNativeMetric D level A slots birthLength (ρ * ell) t) Y‖ ≤
      planarGramJetBudget n B := by
  let L := independentIntrinsicSlowScaling (4 * r) ell
  have hF := independentFreshNativeMetric_contDiff_of_area D level A hA slots birthLength ρ hρ harea t
  rw [independentFreshNativeMetric_scale_copy]
  have hs := finite_affine_derivative_norm_le _ n (hF.of_le (by simp)) L
    (independentIntrinsicSlowScaling_norm_le _ ell hell) 0 Y
  simp only [add_zero] at hs
  have hstored : independentFreshCenterStrip (independentStoredParameterProjection (4 * r) (L Y)) := by
    rw [independentIntrinsicSlowScaling_stored]
    exact hY
  have hslow : ‖independentIntrinsicSlowProjection (4 * r) (L Y)‖ ≤ S := by
    rw [independentIntrinsicSlowScaling_slow, norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hell (norm_nonneg _)).trans_eq (one_mul _)).trans hS
  exact hs.trans (independentFreshNativeMetric_jet_bound_of_chart_reserve D level A hA slots birthLength
    ρ hρ T K S B hB harea hreserve t ht (L Y) hstored hslow n hn)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual pulse smallness supplies every molecular drift production for a genuine parameter
metric. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independentParameterMetric_pulse_molecular_production (H K : ℕ)
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve K G)
    (he : ∀ t Y (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {ν : ℝ} {slot : ℤ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ) (hslot : Odd slot)
    (hsmall : ocEpsilon q Λ m ^ (1 + α) / ν ≤ pulseHigherDriftThreshold H) :
    ∃ M : P → MolecularData,
      (∀ Y, (M Y).G = fun t => G t Y) ∧
      (∀ Y, (M Y).v = ocPulseCellDrift α q Λ ζ m ν slot) ∧
      (∀ Y, dataCoefficients (M Y) =
        ⟨(fun t _ => G t Y), (M Y).v, 0, 0⟩) ∧
      (∀ Y j, j ≤ H → Nonempty (MolecularFiniteDriftBudget (M Y) j)) := by
  have hv := normalizedPulseDrift_isCellDrift (α := α) (q := q) (m := m)
    hΛ hν hζ hslot
  obtain ⟨V, hV⟩ := hv.2.1
  let M := independentParameterMetricMolecularData Q he
    (ocPulseCellDrift α q Λ ζ m ν slot) hv.1 V hV
  refine ⟨M, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · intro Y
    exact independentParameterMetricMolecularData_coefficients Q he (ocPulseCellDrift α q Λ ζ m ν slot) hv.1 V hV Y
  · intro Y j hj
    exact ⟨pulseFiniteDriftBudget (M Y) j hΛ hν hζ hslot rfl
      (hsmall.trans (pulseHigherDriftThreshold_le H j hj))⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual lift metrics keep their prescribed slow length explicit, separately from the family context level. -/
@[expose] public noncomputable section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseScaledMetric (D : OCData) (A : RealChain) (ρ : ℝ)
    (t : ℝ) (Y : Vec (2 + 4 * A.children.length)) : Matrix (Fin 2) (Fin 2) ℝ :=
  independentFreshNativeMetric D A.ctxLevel (independentFreshBaseChain A)
    (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A) ρ t Y

theorem actualIndependentCoarseScaledMetric_isSymm (D : OCData) (A : RealChain)
    (ρ t : ℝ) (Y : Vec (2 + 4 * A.children.length)) : (actualIndependentCoarseScaledMetric D A ρ t Y).IsSymm :=
  independentFreshNativeMetric_isSymm D A.ctxLevel (independentFreshBaseChain A) _ _ _ t Y

theorem actualIndependentCoarseScaledMetric_entry_measurable (D : OCData) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (ρ : ℝ) (Y : Vec (2 + 4 * A.children.length)) (i j : Fin 2) :
    Measurable (fun t => actualIndependentCoarseScaledMetric D A ρ t Y i j) :=
  independentFreshNativeMetric_entry_measurable D hζ A.ctxLevel (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) _ _ _ Y i j

theorem actualIndependentCoarseScaledMetric_contDiff (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw : ℝ) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (actualIndependentCoarseScaledMetric D A ρ t) := by
  apply independentFreshNativeMetric_contDiff_of_area D A.ctxLevel (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) _ _ _ hρ
  intro P
  change GeomAreaPreserving ((independentFreshChain (independentFreshBaseChain A)
    (fun j : Fin A.children.length => realChainSlotSeq A (j + 1))
    (fun j => D.eps (A.baseLevel + j)) P).geom D)
  rw [independentFreshChain_geom_eq_indexed D (independentFreshBaseChain A) (realChainSlotSeq A)
    rfl rfl (fun j => D.eps (A.baseLevel + j)) P]
  exact finiteWeakChainGeom_area_preserving D hΛ A.baseLevel A.base (realChainSlotSeq A) _ _
    (fun j hj => realChainSlotSeq_odd D A hA j (by omega))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The full actual metric realization has exactly the original native lift metric on every slow slice. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem actualIndependentCoarseScaledMetric_slice (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (ρ : ℝ) (slot : ℤ) (edge : ConstituentEdges Dm h) (Y : Vec (2 + 4 * A.children.length))
    (t : ℝ) (X : Vec 2) :
    actualIndependentCoarseScaledMetric D A ρ t
      (independentIntrinsicSlowEmbedding (4 * A.children.length) X +
        independentIntrinsicSliceOffset (4 * A.children.length) Y) =
      (familyLiftData D A.ctxLevel slot
        (actualIndependentCoarseParameterChain D A (independentStoredParameterProjection (4 * A.children.length) Y)) ρ edge).G t X := by
  rw [actualIndependentCoarseParameterChain_eq_fresh D A hA]
  funext i j
  exact independentFreshNativeMetric_slice D A.ctxLevel (independentFreshBaseChain A)
    (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A)
    ρ slot edge Y t X i j

end AVRegularity.EntryWeakProofs
end
end

section
/-! Primitive independent data and the actual native inverse clauses, before coefficient production. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

structure IndependentLiftPrimitiveData (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count : ℕ) (BG BV BE : ℝ) where
  a : ℝ
  b : ℝ
  window : a < b
  U : Set (Vec (2 + d))
  open_carrier : IsOpen U
  G : ℝ → Vec (2 + d) → Matrix (Fin 2) (Fin 2) ℝ
  v : ℝ → Vec 2 → Vec 2
  drift : IsCellDrift v
  edge : ConstituentEdges D (fun _ : ι => ℝ)
  edgeField : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
    DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec (2 + d) → Vec 2
  M : ι → ι → ℝ
  matrix_nonneg : ∀ v u, 0 ≤ M v u
  metric : IndependentParameterMetricReserve H G
  metric_bound : ∀ r ≤ H, metric.budget r ≤ BG
  metric_entries : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j)
  metric_entries_bound : ∀ i j r, r ≤ H + D + 1 → (metric_entries i j).budget r ≤ BG
  drift_entries : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec (2 + d)) => v t z i)
  drift_bound : ∀ i r, r ≤ H + D → (drift_entries i).budget r ≤ BV
  edges : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
    IndependentParameterSourceReserve (H + D + 1) (edgeField v u e γ α)
  edge_bound : ∀ v u e γ hγ α r, r ≤ H + D + 1 → (edges v u e γ hγ α).budget r ≤ M v u * BE
  edge_maps : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1
  edge_lengths : ∀ v u e, (edge v u e).length ≤ count
  molecular : Vec (2 + d) → MolecularData
  molecular_coefficients : ∀ Y, dataCoefficients (molecular Y) =
    ⟨(fun t _ => G t Y), (molecular Y).v, 0, 0⟩
  molecular_metric : ∀ Y, (molecular Y).G = fun t => G t Y
  molecular_drift : ∀ Y, (molecular Y).v = v
  molecular_budget : ∀ Y K, K ≤ H → MolecularFiniteDriftBudget (molecular Y) K
  sZ : ℕ
  Cc : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)
  initial : ∀ Z, ∀ a₀ : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ →
    ∀ t ∈ Icc a b, ∀ X z, liftApply 0 (Cc Z 0 0) (fun _ => a₀) t X z = a₀ X
  positive_zero_degree : ∀ Z hh, 1 ≤ hh → hh ≤ R → ∀ m α t X z v u, Cc Z hh 0 m α t X z v u = 0
  above_degree : ∀ Z hh, hh ≤ R → ∀ n, N < n → ∀ m α t X z v u, Cc Z hh n m α t X z v u = 0
  above_order : ∀ Z hh, hh ≤ R → ∀ n m, n < m → ∀ α t X z v u, Cc Z hh n m α t X z v u = 0
  symmetric : ∀ Z hh, hh ≤ R → ∀ n m β (σ : Equiv.Perm (Fin m)), Cc Z hh n m (β ∘ σ) = Cc Z hh n m β
  inverse : ∀ hh, hh ≤ R → ∀ n, 1 ≤ n → n ≤ N →
    ∀ a₀ : Vec 2 → ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ Y ∈ U,
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y), v,
        independentConstituentEdgeSlice edge edgeField edges (independentIntrinsicSlowEmbedding d)
          (independentIntrinsicSliceOffset d Y)⟩
    IsCellFieldInverse (fun t => G t Y) v sZ a b 0
      (fun t z => liftCellSource Q (Cc (independentStoredParameterProjection d Y)) (fun _ => a₀)
        hh n t (independentIntrinsicSlowProjection d Y) z)
      (fun t z => liftApply n (Cc (independentStoredParameterProjection d Y) hh n) (fun _ => a₀)
        t (independentIntrinsicSlowProjection d Y) z)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Restricting primitive reserves preserves the literal native family and every paper recursion clause. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count : ℕ} {BG BV BE : ℝ}

def IndependentLiftPrimitiveData.monoOrder
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE) (K : ℕ) (hK : K ≤ H) :
    IndependentLiftPrimitiveData ι d K D N R count BG BV BE where
  a := S.a
  b := S.b
  window := S.window
  U := S.U
  open_carrier := S.open_carrier
  G := S.G
  v := S.v
  drift := S.drift
  edge := S.edge
  edgeField := S.edgeField
  M := S.M
  matrix_nonneg := S.matrix_nonneg
  metric := S.metric.restrictOrder K hK
  metric_bound r hr := S.metric_bound r (hr.trans hK)
  metric_entries i j := (S.metric_entries i j).restrictOrder (K + D + 1) (by omega)
  metric_entries_bound i j r hr := S.metric_entries_bound i j r (by omega)
  drift_entries i := (S.drift_entries i).restrictOrder (K + D) (by omega)
  drift_bound i r hr := S.drift_bound i r (by omega)
  edges v u e γ hγ α := (S.edges v u e γ hγ α).restrictOrder (K + D + 1) (by omega)
  edge_bound v u e γ hγ α r hr := S.edge_bound v u e γ hγ α r (by omega)
  edge_maps := S.edge_maps
  edge_lengths := S.edge_lengths
  molecular := S.molecular
  molecular_coefficients := S.molecular_coefficients
  molecular_metric := S.molecular_metric
  molecular_drift := S.molecular_drift
  molecular_budget Y k hk := S.molecular_budget Y k (hk.trans hK)
  sZ := S.sZ
  Cc := S.Cc
  initial := S.initial
  positive_zero_degree := S.positive_zero_degree
  above_degree := S.above_degree
  above_order := S.above_order
  symmetric := S.symmetric
  inverse := S.inverse

end AVRegularity.EntryWeakProofs
end
end

section
/-! Primitive input data with genuine phase translations, before any coefficient is produced. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

structure IndependentLiftNaturalPrimitiveDatum (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d H D N R count qs : ℕ) (BG BV BE : ℝ) where
  primitive : IndependentLiftPrimitiveData ι d H D N R count BG BV BE
  fastOrder : primitive.sZ = qs
  translations : Set (Vec (2 + d))
  metric_translation : ∀ δ ∈ translations, ∀ t Y, primitive.G t (Y + δ) = primitive.G t Y
  edge_translation : ∀ δ ∈ translations, ∀ v u e γ, γ ∈ primitive.edge v u e → ∀ α,
    IndependentSourceTranslationInvariant δ (primitive.edgeField v u e γ α)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Internal comparison of genuinely produced primitive data on an open intrinsic slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count : ℕ} {BG BV BE : ℝ}

structure IndependentLiftPrimitiveSlowSliceEq
    (S T : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
    (U : Set (Vec 2)) (Y Z : Vec (2 + d)) : Prop where
  window_left : S.a = T.a
  window_right : S.b = T.b
  drift : S.v = T.v
  matrix : S.M = T.M
  edge : S.edge = T.edge
  metric : ∀ i j, IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
    (fun t (_ : Vec 2) W => S.G t W i j) (fun t _ W => T.G t W i j)
  edge_fields : ∀ v u e γ, γ ∈ S.edge v u e → ∀ α,
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding d) U Y Z
      (S.edgeField v u e γ α) (T.edgeField v u e γ α)

theorem IndependentLiftPrimitiveSlowSliceEq.recenter
    {S T : IndependentLiftPrimitiveData ι d H D N R count BG BV BE}
    {U : Set (Vec 2)} {Y Z : Vec (2 + d)}
    (he : IndependentLiftPrimitiveSlowSliceEq S T U Y Z) (W : Vec 2) :
    IndependentLiftPrimitiveSlowSliceEq S T ((fun X => X + W) ⁻¹' U)
      (independentIntrinsicSlowEmbedding d W + Y) (independentIntrinsicSlowEmbedding d W + Z) where
  window_left := he.window_left
  window_right := he.window_right
  drift := he.drift
  matrix := he.matrix
  edge := he.edge
  metric i j := (he.metric i j).recenter W
  edge_fields v u e γ hγ α := (he.edge_fields v u e γ hγ α).recenter W

end AVRegularity.EntryWeakProofs
end
end

section
/-! A common molecular reserve supplies every smaller primitive production order without changing its geometry. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count qs : ℕ} {BG BV BE : ℝ}

def IndependentLiftPrimitiveData.restrictRegularity
    (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE) (K : ℕ) (hK : K ≤ H) :
    IndependentLiftPrimitiveData ι d K D N R count BG BV BE where
  a := S.a
  b := S.b
  window := S.window
  U := S.U
  open_carrier := S.open_carrier
  G := S.G
  v := S.v
  drift := S.drift
  edge := S.edge
  edgeField := S.edgeField
  M := S.M
  matrix_nonneg := S.matrix_nonneg
  metric := S.metric.restrictOrder K hK
  metric_bound r hr := S.metric_bound r (hr.trans hK)
  metric_entries i j := (S.metric_entries i j).restrictOrder (K + D + 1) (by omega)
  metric_entries_bound i j r hr := S.metric_entries_bound i j r (by omega)
  drift_entries i := (S.drift_entries i).restrictOrder (K + D) (by omega)
  drift_bound i r hr := S.drift_bound i r (by omega)
  edges v u e γ hγ α := (S.edges v u e γ hγ α).restrictOrder (K + D + 1) (by omega)
  edge_bound v u e γ hγ α r hr := S.edge_bound v u e γ hγ α r (by omega)
  edge_maps := S.edge_maps
  edge_lengths := S.edge_lengths
  molecular := S.molecular
  molecular_coefficients := S.molecular_coefficients
  molecular_metric := S.molecular_metric
  molecular_drift := S.molecular_drift
  molecular_budget Y j hj := S.molecular_budget Y j (hj.trans hK)
  sZ := S.sZ
  Cc := S.Cc
  initial := S.initial
  positive_zero_degree := S.positive_zero_degree
  above_degree := S.above_degree
  above_order := S.above_order
  symmetric := S.symmetric
  inverse := S.inverse

def IndependentLiftNaturalPrimitiveDatum.restrictRegularity
    (x : IndependentLiftNaturalPrimitiveDatum ι d H D N R count qs BG BV BE)
    (K : ℕ) (hK : K ≤ H) :
    IndependentLiftNaturalPrimitiveDatum ι d K D N R count qs BG BV BE where
  primitive := x.primitive.restrictRegularity K hK
  fastOrder := x.fastOrder
  translations := x.translations
  metric_translation := x.metric_translation
  edge_translation := x.edge_translation

end AVRegularity.EntryWeakProofs
end
end

section
/-! Restricting the reserve order leaves the primitive slow-slice comparison unchanged. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count : ℕ} {BG BV BE : ℝ}

theorem IndependentLiftPrimitiveSlowSliceEq.monoOrder
    {S T : IndependentLiftPrimitiveData ι d H D N R count BG BV BE}
    {U : Set (Vec 2)} {Y Z : Vec (2 + d)}
    (he : IndependentLiftPrimitiveSlowSliceEq S T U Y Z) (K : ℕ) (hK : K ≤ H) :
    IndependentLiftPrimitiveSlowSliceEq (S.monoOrder K hK) (T.monoOrder K hK) U Y Z where
  window_left := he.window_left
  window_right := he.window_right
  drift := he.drift
  matrix := he.matrix
  edge := he.edge
  metric := he.metric
  edge_fields := he.edge_fields

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Genuine produced native metric jets and a fixed carrier cutoff supply the molecular primitive reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
open scoped Matrix Matrix.Norms.Elementwise ContDiff
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseScaledExtendedMetric (D : OCData) (A : RealChain) (ρ : ℝ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ) (a b : ℝ) :=
  clampedParameterMetric (cutoffParameterMetric χ (actualIndependentCoarseScaledMetric D A ρ)) a b

def actualIndependentCoarseScaledMetricReserve (H : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (A : RealChain) (bw : ℝ) (j₀ level : ℕ) (slot : ℤ) (hA : IsAdmissibleChain D bw j₀ level slot A) (ρ : ℝ) (hρ : 0 < ρ)
    (χ : Vec (2 + 4 * A.children.length) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχrange : ∀ Y, χ Y ∈ Icc 0 1)
    (hsupport : ∀ Y ∈ tsupport χ, independentFreshCenterStrip (independentStoredParameterProjection (4 * A.children.length) Y) ∧
      ‖independentIntrinsicSlowProjection (4 * A.children.length) Y‖ ≤ 1)
    (a b : ℝ) (hab : a ≤ b)
    (he : ∀ t ∈ Icc a b, ∀ Y, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j ∧
      (∑ i, ∑ j, actualIndependentCoarseScaledMetric D A ρ t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hbχ : ∀ n ≤ H, ∀ Y, ‖iteratedFDeriv ℝ n χ Y‖ ≤ C n)
    (BG : ℝ) (hBG : 0 ≤ BG)
    (hbG : ∀ n ≤ H, ∀ t ∈ Icc a b, ∀ Y,
      independentFreshCenterStrip (independentStoredParameterProjection (4 * A.children.length) Y) →
      ‖independentIntrinsicSlowProjection (4 * A.children.length) Y‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (actualIndependentCoarseScaledMetric D A ρ t) Y‖ ≤ BG) :
    IndependentParameterMetricReserve H (actualIndependentCoarseScaledExtendedMetric D A ρ χ a b) :=
  cutoffIndependentMetricReserve H χ hχ hχrange (tsupport χ) (Subset.rfl)
    (actualIndependentCoarseScaledMetric D A ρ) a b hab
    (fun t i j => (contDiff_apply_apply ℝ ℝ i j).comp (actualIndependentCoarseScaledMetric_contDiff D hΛ A bw j₀ level slot hA ρ hρ t))
    (actualIndependentCoarseScaledMetric_entry_measurable D hζ A ρ)
    (fun t _ Y => actualIndependentCoarseScaledMetric_isSymm D A ρ t Y) he C (fun _ => BG) hC (fun _ => hBG) hbχ
    (fun n hn t ht Y hY i j =>
      (matrix_entry_derivative_norm_le _ (actualIndependentCoarseScaledMetric_contDiff D hΛ A bw j₀ level slot hA ρ hρ t) n Y i j).trans
        (hbG n hn t ht Y (hsupport Y hY).1 (hsupport Y hY).2))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Native and phase-invariant cutoff metrics respect every stored phase lattice equivalence. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeMetric_eq_of_phase_lattice {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (level : ℕ) (A : RealChain) (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (hp : ∀ p ∈ A.slots ++ List.ofFn slots, Odd p) (ρ t : ℝ) (Y Z : Vec (2 + 4 * r))
    (hslow : independentIntrinsicSlowProjection (4 * r) Y = independentIntrinsicSlowProjection (4 * r) Z)
    (hc : ∀ j, independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y) =
      independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Z))
    (hphase : ∀ j, ∃ n : Fin 2 → ℤ,
      independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Y) =
        independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Z) + latticeShift n) :
    independentFreshNativeMetric D level A slots birthLength ρ t Y =
      independentFreshNativeMetric D level A slots birthLength ρ t Z := by
  unfold independentFreshNativeMetric
  simp only [independentFreshStoredFamily_eq_chain, hslow]
  exact realChain_recenter_metric_eq_of_geom_eq D _ _
    (independentFreshChain_wellSlotted A hA slots birthLength _)
    (independentFreshChain_wellSlotted A hA slots birthLength _)
    (independentFreshChain_geom_eq_of_phase_lattice D hΛ A slots birthLength hp _ _ hc hphase) _ _

theorem independentFreshCarrierCoordinates_eq_of_centers {r : ℕ} (Y Z : Vec (2 + 4 * r))
    (hslow : independentIntrinsicSlowProjection (4 * r) Y = independentIntrinsicSlowProjection (4 * r) Z)
    (hc : ∀ j, independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y) =
      independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Z)) :
    independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z := by
  apply Prod.ext
  · funext j
    exact hc j
  · exact hslow

theorem independentFreshCutoffMetric_eq_of_phase_lattice {r : ℕ} (D : OCData) (hΛ : 1 ≤ D.Λ)
    (level : ℕ) (A : RealChain) (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (hp : ∀ p ∈ A.slots ++ List.ofFn slots, Odd p) (ρ a b t : ℝ)
    (χ : Vec (2 + 4 * r) → ℝ)
    (hχ : ∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ Y = χ Z)
    (Y Z : Vec (2 + 4 * r))
    (hslow : independentIntrinsicSlowProjection (4 * r) Y = independentIntrinsicSlowProjection (4 * r) Z)
    (hc : ∀ j, independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y) =
      independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Z))
    (hphase : ∀ j, ∃ n : Fin 2 → ℤ,
      independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Y) =
        independentFreshChildProjection j true (independentStoredParameterProjection (4 * r) Z) + latticeShift n) :
    clampedParameterMetric (cutoffParameterMetric χ
      (independentFreshNativeMetric D level A slots birthLength ρ)) a b t Y =
      clampedParameterMetric (cutoffParameterMetric χ
        (independentFreshNativeMetric D level A slots birthLength ρ)) a b t Z := by
  dsimp only [clampedParameterMetric, cutoffParameterMetric]
  rw [hχ Y Z (independentFreshCarrierCoordinates_eq_of_centers Y Z hslow hc),
    independentFreshNativeMetric_eq_of_phase_lattice D hΛ level A hA slots birthLength hp ρ _ Y Z hslow hc hphase]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual inverse word derivatives and produced quotient carriers identify classical word derivatives. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {d H : ℕ}

theorem coordinate_word_classical_derivative {a b : ℝ} (hab : a < b)
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
    (w : List (Fin d)) (hw : w.length < N) (Y : Vec d) (i : Fin d)
    (t : ℝ) (ht : t ∈ Icc a b) (n : ℕ) (hn : n + 4 ≤ K) (z : Vec 2) :
    HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u w (Y + h • basisVec i) t))) z)
      (iteratedFDeriv ℝ n (realClassicalLift K (mapTorusHk Complex.reCLM (u (i :: w) Y t))) z) 0 := by
  obtain ⟨R, _, hq⟩ := coordinate_word_uniform_quotient_carrier_exists hab N (K + N) hH
    QG Qf QF P hP v hv hPv V c hsol hf hF w (by omega) K (by omega) i
  let D := fun h : ℝ => c w (Y + h • basisVec i)
  have hD0 : D 0 = c w Y := by simp only [D, zero_smul, add_zero]
  have he : Tendsto (fun h : ℝ => cellEnergyNorm univ
      (h⁻¹ • (D h - D 0) - c (i :: w) Y)) (𝓝[≠] 0) (𝓝 0) := by
    rw [hD0]
    exact hc.2 w hw Y i
  refine classical_fast_jet_derivative_of_energy_quotients K n hn
    (fun h => u w (Y + h • basisVec i) t) (u (i :: w) Y t) D (c (i :: w) Y) t
    (fun h => hu w (by omega) _ t ht)
    (hu (i :: w) (by simp only [List.length_cons]; omega) Y t ht) he R ?_ z
  intro h hh
  obtain ⟨q, _, hb, hread⟩ := hq Y h hh
  refine ⟨q t, hb t, ?_⟩
  simpa only [D, zero_smul, add_zero] using hread t ht

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual birth scales and scheduled primitive windows produce every finite mixed native chart reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem fresh_native_chart_reserve_of_small_windows (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (A : RealChain) (hA : A.WellSlotted) (hm : 1 ≤ A.baseLevel)
    (hchildren : A.children = []) (p : ℕ → ℤ) (hslots : A.slots = [p 0]) (J : ℕ)
    (hp : ∀ n ≤ J, Odd (p n))
    (hs : ∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n))
    (hprimitive : WeakPrimitiveChartSmall D A.baseLevel J 1)
    (hclose : ∀ n ≤ J, ∀ P : Vec (4 * n), ∀ u ∈ nativeWeakChartWindow D A.baseLevel J p n, ∀ x,
      let g := (independentFreshChain A (fun j : Fin n => p (j + 1))
        (fun j => D.eps (A.baseLevel + j + 1)) P).geom D
      ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 ∧
      ‖fderiv ℝ (fun y => g.1 g.2.2 y u) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) :
    ∀ n ≤ J, ∀ K S, independentFreshNativeChartReserve D A
      (fun j : Fin n => p (j + 1)) (fun j => D.eps (A.baseLevel + j + 1))
      (D.eps (A.baseLevel + n)) (nativeWeakChartWindow D A.baseLevel J p n) K S
      (nativeMixedChartBudget K n S) := by
  have hΛ₁ : 1 ≤ D.Λ := le_trans (by norm_num : 1 ≤ (128 : ℕ)) hΛ
  have hctx : A.ctxLevel = A.baseLevel + 1 := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hchildren, List.length_nil, Nat.add_zero]
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ := renewal_window_antitone (by linarith : D.α < 1) hδ.le hq.1 hΛ
  have hsub : ∀ n < J, nativeWeakChartWindow D A.baseLevel J p (n + 1) ⊆
      nativeWeakChartWindow D A.baseLevel J p n := fun n hn =>
    nativeWeakChartWindow_subset_parent D hΛ₁ A.baseLevel J p n (by omega)
      (hτ (by omega)) (hs n hn)
  apply independentFreshNativeChartReserve_of_primitive_windows D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
    A hA hm (p 0) hchildren hslots (fun j => p (j + 1))
    (fun j => D.eps (A.baseLevel + j + 1)) (fun j => D.eps (A.baseLevel + j))
    (fun j => D.eps (A.baseLevel + j + 1) / D.eps (A.baseLevel + j))
    (fun j => D.eps (A.baseLevel + j + 1) / D.eps (A.baseLevel + j))
    (nativeWeakChartWindow D A.baseLevel J p) J
    (fun _ _ => Construction.Stream.ocEpsilon_pos hΛ₁) (by simpa only [Nat.add_zero] using (le_refl (D.eps A.baseLevel)))
  · intro u hu
    have hb := (hprimitive (A.baseLevel + 1) le_rfl).1
    simp only [Nat.add_sub_cancel] at hb
    change |u - D.slotAnchor (A.baseLevel + 1) (p 0)| ≤ _
    apply le_trans ?_ hb
    change |u - D.slotAnchor (A.baseLevel + 1) (p 0)| ≤
      finiteChainWindowRadius J 0 * ocTauPP D.α D.q D.Λ (A.baseLevel + 1) at hu
    apply hu.trans
    have ht : 0 ≤ ocTauPP D.α D.q D.Λ (A.baseLevel + 1) := (Construction.Stream.ocTauPP_pos hΛ₁).le
    simp only [finiteChainWindowRadius, Nat.sub_zero]
    nlinarith only [ht, mul_nonneg (show (0 : ℝ) ≤ 2 * J + 1 by positivity) ht]
  · intro n _
    exact native_weak_chart_scale_step D hq.1 hΛ A hchildren n
  · intro n hn
    have he : (A.slots ++ List.ofFn (fun j : Fin n => p (j + 1))).getLastD 0 = p n := by
      have hl : A.slots ++ List.ofFn (fun j : Fin n => p (j + 1)) =
          List.ofFn (fun j : Fin (n + 1) => p j) := by
        rw [hslots, List.ofFn_succ]
        rfl
      rw [hl, List.ofFn_succ']
      simp
    rw [he]
    exact hp n (by omega)
  · exact hsub
  · intro n hn
    rw [hctx]
    exact hsub n hn (nativeWeakChartWindow_anchor D hΛ₁ A.baseLevel J p (n + 1))
  · intro n hn u hu
    rw [hctx]
    exact nativeWeakChartWindow_shear_small D hΛ₁ A.baseLevel J p hprimitive n u hu
  · intro n hn P _ u hu x
    exact hclose n (by omega) P u hu x

end AVRegularity.EntryWeakProofs
end
end

section
/-! Parent-normalized center scales and scheduled primitive windows produce every finite mixed native chart reserve. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem fresh_native_coarse_chart_reserve_of_small_windows (D : OCData) (s : ℝ)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hseq : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ)
    (A : RealChain) (hA : A.WellSlotted) (hm : 1 ≤ A.baseLevel)
    (hchildren : A.children = []) (p : ℕ → ℤ) (hslots : A.slots = [p 0]) (J : ℕ)
    (hp : ∀ n ≤ J, Odd (p n))
    (hs : ∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n))
    (hprimitive : WeakPrimitiveChartSmall D A.baseLevel J 1)
    (hclose : ∀ n ≤ J, ∀ P : Vec (4 * n), ∀ u ∈ nativeWeakChartWindow D A.baseLevel J p n, ∀ x,
      let g := (independentFreshChain A (fun j : Fin n => p (j + 1))
        (fun j => D.eps (A.baseLevel + j)) P).geom D
      ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 ∧
      ‖fderiv ℝ (fun y => g.1 g.2.2 y u) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1) :
    ∀ n ≤ J, ∀ K S, independentFreshNativeChartReserve D A
      (fun j : Fin n => p (j + 1)) (fun j => D.eps (A.baseLevel + j))
      (D.eps (A.baseLevel + n)) (nativeWeakChartWindow D A.baseLevel J p n) K S
      (nativeMixedChartBudget K n S) := by
  have hΛ₁ : 1 ≤ D.Λ := le_trans (by norm_num : 1 ≤ (128 : ℕ)) hΛ
  have hctx : A.ctxLevel = A.baseLevel + 1 := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hchildren, List.length_nil, Nat.add_zero]
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ := renewal_window_antitone (by linarith : D.α < 1) hδ.le hq.1 hΛ
  have hsub : ∀ n < J, nativeWeakChartWindow D A.baseLevel J p (n + 1) ⊆
      nativeWeakChartWindow D A.baseLevel J p n := fun n hn =>
    nativeWeakChartWindow_subset_parent D hΛ₁ A.baseLevel J p n (by omega)
      (hτ (by omega)) (hs n hn)
  apply independentFreshNativeChartReserve_of_primitive_windows D s hα₀ hα₁ hs₀ hs₁ hq hΛ hζ hseq
    A hA hm (p 0) hchildren hslots (fun j => p (j + 1))
    (fun j => D.eps (A.baseLevel + j)) (fun j => D.eps (A.baseLevel + j))
    (fun j => D.eps (A.baseLevel + j + 1) / D.eps (A.baseLevel + j))
    (fun _ => 1)
    (nativeWeakChartWindow D A.baseLevel J p) J
    (fun _ _ => Construction.Stream.ocEpsilon_pos hΛ₁) (by simpa only [Nat.add_zero] using (le_refl (D.eps A.baseLevel)))
  · intro u hu
    have hb := (hprimitive (A.baseLevel + 1) le_rfl).1
    simp only [Nat.add_sub_cancel] at hb
    change |u - D.slotAnchor (A.baseLevel + 1) (p 0)| ≤ _
    apply le_trans ?_ hb
    change |u - D.slotAnchor (A.baseLevel + 1) (p 0)| ≤
      finiteChainWindowRadius J 0 * ocTauPP D.α D.q D.Λ (A.baseLevel + 1) at hu
    apply hu.trans
    have ht : 0 ≤ ocTauPP D.α D.q D.Λ (A.baseLevel + 1) := (Construction.Stream.ocTauPP_pos hΛ₁).le
    simp only [finiteChainWindowRadius, Nat.sub_zero]
    nlinarith only [ht, mul_nonneg (show (0 : ℝ) ≤ 2 * J + 1 by positivity) ht]
  · intro n _
    exact native_weak_coarse_chart_scale_step D hq.1 hΛ A hchildren n
  · intro n hn
    have he : (A.slots ++ List.ofFn (fun j : Fin n => p (j + 1))).getLastD 0 = p n := by
      have hl : A.slots ++ List.ofFn (fun j : Fin n => p (j + 1)) =
          List.ofFn (fun j : Fin (n + 1) => p j) := by
        rw [hslots, List.ofFn_succ]
        rfl
      rw [hl, List.ofFn_succ']
      simp
    rw [he]
    exact hp n (by omega)
  · exact hsub
  · intro n hn
    rw [hctx]
    exact hsub n hn (nativeWeakChartWindow_anchor D hΛ₁ A.baseLevel J p (n + 1))
  · intro n hn u hu
    rw [hctx]
    exact nativeWeakChartWindow_shear_small D hΛ₁ A.baseLevel J p hprimitive n u hu
  · intro n hn P _ u hu x
    exact hclose n (by omega) P u hu x

end AVRegularity.EntryWeakProofs
end
end

section
/-! A threshold chosen before the data supplies full independent mixed chart production at every finite depth. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_fresh_native_chart_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.WellSlotted → A.children = [] →
      ∀ p : ℕ → ℤ, A.slots = [p 0] → (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n)) →
      ∀ n ≤ J, ∀ K S, independentFreshNativeChartReserve D A
        (fun j : Fin n => p (j + 1)) (fun j => D.eps (A.baseLevel + j + 1))
        (D.eps (A.baseLevel + n)) (nativeWeakChartWindow D A.baseLevel J p n) K S
        (nativeMixedChartBudget K n S) := by
  obtain ⟨M₀, hM₀, hprim⟩ := weak_finite_chart_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq
    Λ hΛ (2 * (J : ℝ) + 1) 1 (by positivity) (by norm_num)
  obtain ⟨M₁, _, hclose⟩ := uniform_fresh_native_spatial_closeness α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hAM hA hchildren p hslots hp hs
  have hα₀' : 0 < D.α := by rw [hDα]; exact hα₀
  have hα₁' : D.α < 1 / 3 := by rw [hDα]; exact hα₁
  have hs₁' : s < (1 - D.α) / 2 := by rw [hDα]; exact hs₁
  have hq' : IsAdmissibleQ D.α s D.q := by rw [hDα, hDq]; exact hq
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hseq' : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by
    rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  have hm : 1 ≤ A.baseLevel := le_trans (by omega : 1 ≤ M₀)
    ((le_max_left M₀ M₁).trans hAM)
  have hprimitive : WeakPrimitiveChartSmall D A.baseLevel J 1 := by
    intro m hm
    have hb := hprim m (by have hM := (le_max_left M₀ M₁).trans hAM; omega)
    simpa only [hDα, hDq, hDΛ] using hb
  apply fresh_native_chart_reserve_of_small_windows D s hα₀' hα₁' hs₀ hs₁' hq' hΛ' hζ' hseq'
    A hA hm hchildren p hslots J hp hs hprimitive
  exact hclose D hDα hDq hDΛ hDζ hseq A ((le_max_right M₀ M₁).trans hAM)
    hchildren p hslots hp hs (fun j => D.eps (A.baseLevel + j + 1))

end AVRegularity.EntryWeakProofs
end
end

section
/-! A threshold chosen before the data supplies full independent mixed chart production at every finite depth. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_fresh_native_coarse_chart_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.WellSlotted → A.children = [] →
      ∀ p : ℕ → ℤ, A.slots = [p 0] → (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n)) →
      ∀ n ≤ J, ∀ K S, independentFreshNativeChartReserve D A
        (fun j : Fin n => p (j + 1)) (fun j => D.eps (A.baseLevel + j))
        (D.eps (A.baseLevel + n)) (nativeWeakChartWindow D A.baseLevel J p n) K S
        (nativeMixedChartBudget K n S) := by
  obtain ⟨M₀, hM₀, hprim⟩ := weak_finite_chart_eventually_small α s q hα₀ hα₁ hs₀ hs₁ hq
    Λ hΛ (2 * (J : ℝ) + 1) 1 (by positivity) (by norm_num)
  obtain ⟨M₁, _, hclose⟩ := uniform_fresh_native_spatial_closeness α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨max M₀ M₁, hM₀.trans (le_max_left _ _), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hAM hA hchildren p hslots hp hs
  have hα₀' : 0 < D.α := by rw [hDα]; exact hα₀
  have hα₁' : D.α < 1 / 3 := by rw [hDα]; exact hα₁
  have hs₁' : s < (1 - D.α) / 2 := by rw [hDα]; exact hs₁
  have hq' : IsAdmissibleQ D.α s D.q := by rw [hDα, hDq]; exact hq
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hseq' : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by
    rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  have hm : 1 ≤ A.baseLevel := le_trans (by omega : 1 ≤ M₀)
    ((le_max_left M₀ M₁).trans hAM)
  have hprimitive : WeakPrimitiveChartSmall D A.baseLevel J 1 := by
    intro m hm
    have hb := hprim m (by have hM := (le_max_left M₀ M₁).trans hAM; omega)
    simpa only [hDα, hDq, hDΛ] using hb
  apply fresh_native_coarse_chart_reserve_of_small_windows D s hα₀' hα₁' hs₀ hs₁' hq' hΛ' hζ' hseq'
    A hA hm hchildren p hslots J hp hs hprimitive
  exact hclose D hDα hDq hDΛ hDζ hseq A ((le_max_right M₀ M₁).trans hAM)
    hchildren p hslots hp hs (fun j => D.eps (A.baseLevel + j))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The exact initial and cutoff clauses provide all independent zero and absent-degree
productions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d K D N R count : ℕ} {BG BV BE : ℝ}

namespace IndependentLiftPrimitiveData

theorem zero_degree_production (S : IndependentLiftPrimitiveData ι d K D N R count BG BV BE)
    (H hh m : ℕ) (hhh : hh ≤ R) (hm : m ≤ 0) (α : DerivativeWord2 m) (v u : ι)
    (C : ℝ) (hC : 1 ≤ C) :
    Nonempty (IndependentScalarCoefficientProduction (2 + d) H 0 S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) hh 0)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C) := by
  have hm0 : m = 0 := by omega
  subst m
  by_cases hhh0 : hh = 0
  · subst hh
    let f := fun (_ : ℝ) (_ : Vec 2) (_ : Vec (2 + d)) => if v = u then (1 : ℝ) else 0
    refine ⟨⟨f, IndependentParameterSourceReserve.const H (if v = u then (1 : ℝ) else 0), ?_, ?_, ?_, ?_⟩⟩
    · intro r _
      have hb : (IndependentParameterSourceReserve.const (P := Vec (2 + d)) H
          (if v = u then (1 : ℝ) else 0)).budget r ≤ finiteMatrixPower S.M 0 v u :=
        constant_test_matrix_budget H S.M v u r
      exact hb.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hC (finiteMatrixPower_nonneg S.M S.matrix_nonneg 0 v u))
    · intro t ht Y _ z
      have he := congrFun (S.initial (independentStoredParameterProjection d Y)
        (fun _ => Pi.single u (1 : ℝ)) contDiff_const t ht (independentIntrinsicSlowProjection d Y) z) v
      rw [liftApply_constant_single 0 (S.Cc (independentStoredParameterProjection d Y) 0 0)
        α t (independentIntrinsicSlowProjection d Y) z v u 1] at he
      change (if v = u then (1 : ℝ) else 0) =
        S.Cc (independentStoredParameterProjection d Y) 0 0 0 α t (independentIntrinsicSlowProjection d Y) z v u 1
      rw [he]
      by_cases hvu : v = u
      · simp only [hvu, ite_true, Pi.single_eq_same]
      · simp only [ite_eq_right hvu, Pi.single_eq_of_ne hvu]
    · intro h
      omega
    · intro h
      omega
  · refine ⟨⟨fun _ _ _ => 0, IndependentParameterSourceReserve.zero H, ?_, ?_, ?_, ?_⟩⟩
    · intro r _
      exact mul_nonneg (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u) (zero_le_one.trans hC)
    · intro t _ Y _ z
      rw [S.positive_zero_degree _ hh (by omega) hhh 0 α t (independentIntrinsicSlowProjection d Y) z v u]
      rfl
    · intro h
      omega
    · intro h
      omega

theorem above_degree_production (S : IndependentLiftPrimitiveData ι d K D N R count BG BV BE)
    (H hh n m : ℕ) (hhh : hh ≤ R) (hn : N < n) (α : DerivativeWord2 m) (v u : ι)
    (C : ℝ) (hC : 0 ≤ C) :
    Nonempty (IndependentScalarCoefficientProduction (2 + d) H n S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C) := by
  refine ⟨⟨fun _ _ _ => 0, IndependentParameterSourceReserve.zero H, ?_, ?_, ?_, ?_⟩⟩
  · intro r _
    exact mul_nonneg (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u) hC
  · intro t _ Y _ z
    rw [S.above_degree _ hh hhh n hn m α t (independentIntrinsicSlowProjection d Y) z v u]
    rfl
  · intro _ t Y
    exact fieldCellMean_zero
  · intro _ t _ z Y
    rfl

end IndependentLiftPrimitiveData
end AVRegularity.EntryWeakProofs
end
end

section
/-! The exact initial and cutoff clauses provide all independent zero and absent-degree
productions. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d K D N R count : ℕ} {BG BV BE : ℝ}

namespace IndependentLiftPrimitiveData

theorem zero_degree_explicit_natural_production (S : IndependentLiftPrimitiveData ι d K D N R count BG BV BE)
    (H hh m : ℕ) (hhh : hh ≤ R) (hm : m ≤ 0) (α : DerivativeWord2 m) (v u : ι)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ Q : IndependentScalarCoefficientProduction (2 + d) H 0 S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) hh 0)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C,
      (∀ δ : Vec (2 + d), IndependentSourceTranslationInvariant δ Q.field) ∧
      Q.field = (fun _ _ _ => if hh = 0 then (if v = u then (1 : ℝ) else 0) else 0) := by
  have hm0 : m = 0 := by omega
  subst m
  by_cases hhh0 : hh = 0
  · subst hh
    let f := fun (_ : ℝ) (_ : Vec 2) (_ : Vec (2 + d)) => if v = u then (1 : ℝ) else 0
    refine ⟨⟨f, IndependentParameterSourceReserve.const H (if v = u then (1 : ℝ) else 0), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro r _
      have hb : (IndependentParameterSourceReserve.const (P := Vec (2 + d)) H
          (if v = u then (1 : ℝ) else 0)).budget r ≤ finiteMatrixPower S.M 0 v u :=
        constant_test_matrix_budget H S.M v u r
      exact hb.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hC (finiteMatrixPower_nonneg S.M S.matrix_nonneg 0 v u))
    · intro t ht Y _ z
      have he := congrFun (S.initial (independentStoredParameterProjection d Y)
        (fun _ => Pi.single u (1 : ℝ)) contDiff_const t ht (independentIntrinsicSlowProjection d Y) z) v
      rw [liftApply_constant_single 0 (S.Cc (independentStoredParameterProjection d Y) 0 0)
        α t (independentIntrinsicSlowProjection d Y) z v u 1] at he
      change (if v = u then (1 : ℝ) else 0) =
        S.Cc (independentStoredParameterProjection d Y) 0 0 0 α t (independentIntrinsicSlowProjection d Y) z v u 1
      rw [he]
      by_cases hvu : v = u
      · simp only [hvu, ite_true, Pi.single_eq_same]
      · simp only [ite_eq_right hvu, Pi.single_eq_of_ne hvu]
    · intro h
      omega
    · intro h
      omega
    · intro δ t z Y
      rfl
    · simp only [f, ite_true]
  · refine ⟨⟨fun _ _ _ => 0, IndependentParameterSourceReserve.zero H, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro r _
      exact mul_nonneg (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u) (zero_le_one.trans hC)
    · intro t _ Y _ z
      rw [S.positive_zero_degree _ hh (by omega) hhh 0 α t (independentIntrinsicSlowProjection d Y) z v u]
      rfl
    · intro h
      omega
    · intro h
      omega

    · intro δ t z Y
      rfl
    · simp only [ite_eq_right hhh0]

theorem above_degree_explicit_natural_production (S : IndependentLiftPrimitiveData ι d K D N R count BG BV BE)
    (H hh n m : ℕ) (hhh : hh ≤ R) (hn : N < n) (α : DerivativeWord2 m) (v u : ι)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ Q : IndependentScalarCoefficientProduction (2 + d) H n S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) hh n)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M hh v u) C,
      (∀ δ : Vec (2 + d), IndependentSourceTranslationInvariant δ Q.field) ∧
      Q.field = (fun _ _ _ => 0) := by
  refine ⟨⟨fun _ _ _ => 0, IndependentParameterSourceReserve.zero H, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
  · intro r _
    exact mul_nonneg (finiteMatrixPower_nonneg S.M S.matrix_nonneg hh v u) hC
  · intro t _ Y _ z
    rw [S.above_degree _ hh hhh n hn m α t (independentIntrinsicSlowProjection d Y) z v u]
    rfl
  · intro _ t Y
    exact fieldCellMean_zero
  · intro _ t _ z Y
    rfl
  · intro δ t z Y
    rfl

end IndependentLiftPrimitiveData
end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine earlier productions supply all independent forcing fields and native predecessor
germs. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d H D N R count K hh n : ℕ} {BG BV BE B : ℝ}
  (S : IndependentLiftPrimitiveData ι d H D N R count BG BV BE)
  (P : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m, m ≤ q → ∀ α : DerivativeWord2 m, ∀ v u,
    IndependentScalarCoefficientProduction (2 + d) K q S.a S.b S.U
      (fun Y => S.Cc (independentStoredParameterProjection d Y) p q)
      (independentIntrinsicSlowProjection d) m α v u (finiteMatrixPower S.M p v u) B)

def independentLiftPredecessorFields :
    ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec (2 + d) → ι → ι → ℝ :=
  fun p q => if hpq : p < hh ∨ (p = hh ∧ q < n) then independentCoefficientProductionFields (P p q hpq)
    else fun _ _ _ _ _ _ _ => 0

def independentLiftPredecessorFields_reserve (p q : ℕ)
    (hpq : p < hh ∨ (p = hh ∧ q < n)) (m : Fin (q + 1)) (α : DerivativeWord2 m.val) (v u : ι) :
    IndependentParameterSourceReserve K (fun t z Y => independentLiftPredecessorFields S P p q m.val α t z Y v u) :=
  (independentCoefficientProductionFields_reserve (P p q hpq) m.val (by omega) α v u).congrSource (by
    funext t z Y
    simp only [independentLiftPredecessorFields, dite_eq_left hpq])

theorem independentLiftPredecessorFields_bound (p q : ℕ)
    (hpq : p < hh ∨ (p = hh ∧ q < n)) (m : Fin (q + 1)) (α : DerivativeWord2 m.val)
    (v u : ι) (r : ℕ) (hr : r ≤ K) :
    (independentLiftPredecessorFields_reserve S P p q hpq m α v u).budget r ≤
      finiteMatrixPower S.M p v u * B := by
  rw [independentLiftPredecessorFields_reserve, IndependentParameterSourceReserve.congrSource_budget]
  exact independentCoefficientProductionFields_bound (P p q hpq) m.val (by omega) α v u r hr

theorem independentLiftPredecessorFields_mean_zero (p q : ℕ)
    (hpq : p < hh ∨ (p = hh ∧ q < n)) (hq : 1 ≤ q)
    (m : Fin (q + 1)) (α : DerivativeWord2 m.val) (v u : ι) (t : ℝ) (Y : Vec (2 + d)) :
    fieldCellMean (fun z => independentLiftPredecessorFields S P p q m.val α t z Y v u) = 0 := by
  simp only [independentLiftPredecessorFields, dite_eq_left hpq]
  exact independentCoefficientProductionFields_mean_zero (P p q hpq) hq m.val (by omega) α t Y v u

theorem independentLiftPredecessorFields_native_copy (p q : ℕ)
    (hpq : p < hh ∨ (p = hh ∧ q < n)) (hpR : p ≤ R)
    (m : ℕ) (hm : m ≤ q) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc S.a S.b)
    (Y : Vec (2 + d)) (X : Vec 2) (hX : X ∈ independentIntrinsicSliceCarrier d S.U Y)
    (z : Vec 2) (v u : ι) :
    independentScalarCoefficientSlice (independentLiftPredecessorFields S P p q)
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y) m α t X z v u =
      S.Cc (independentStoredParameterProjection d Y) p q m α t X z v u := by
  simp only [independentLiftPredecessorFields, dite_eq_left hpq]
  exact independent_stored_production_family_native_copy S.a S.b B S.U (fun Z => S.Cc Z p q)
    (fun v u => finiteMatrixPower S.M p v u) (P p q hpq) m hm
    (fun Z β σ => S.symmetric Z p hpR q m β σ) α t ht Y X z hX v u

end AVRegularity.EntryWeakProofs
end
end
end

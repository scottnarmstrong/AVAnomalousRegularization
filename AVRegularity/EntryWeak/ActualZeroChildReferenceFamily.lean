-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentLiftCellUniformProduction

section
section
/-! The actual weak metric has a full fresh-parameter realization with exact native slices. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshStoredFamily {r : ℕ} (A : RealChain) (slots : Fin r → ℤ)
    (birthLength : Fin r → ℝ) : Vec (4 * r) → RealChain :=
  independentChainExtension (fun _ => A) (independentFreshChildrenList slots birthLength)

def independentFreshNativeMetric {r : ℕ} (D : OCData) (level : ℕ) (A : RealChain)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ)
    (t : ℝ) (Y : Vec (2 + 4 * r)) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((independentFreshStoredFamily A slots birthLength (independentStoredParameterProjection (4 * r) Y)).recenter D
    (ρ • independentIntrinsicSlowProjection (4 * r) Y)).famMetric D (D.cellScaleSq level * t)

theorem independentFreshNativeMetric_slice {r Dm : ℕ}
    {ι : Type*} {hv : ι → Type*} [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]
    (D : OCData) (level : ℕ) (A : RealChain) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ)
    (ρ : ℝ) (slot : ℤ) (edge : ConstituentEdges Dm hv) (Y : Vec (2 + 4 * r))
    (t : ℝ) (X : Vec 2) (i j : Fin 2) :
    independentFreshNativeMetric D level A slots birthLength ρ t
      (independentIntrinsicSlowEmbedding (4 * r) X + independentIntrinsicSliceOffset (4 * r) Y) i j =
      (familyLiftData D level slot
        (independentFreshStoredFamily A slots birthLength (independentStoredParameterProjection (4 * r) Y)) ρ edge).G t X i j := by
  simp only [independentFreshNativeMetric, independentIntrinsicSlowProjection_slice,
    independentStoredParameterProjection_slice]
  rfl

theorem independentFreshNativeMetric_entry_measurable {r : ℕ}
    (D : OCData) (hζ : IsFastProfile D.ζ) (level : ℕ) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ : ℝ) (Y : Vec (2 + 4 * r)) (i j : Fin 2) :
    Measurable (fun t => independentFreshNativeMetric D level A slots birthLength ρ t Y i j) :=
  ((recentered_metric_entry_continuous_time D hζ _
    (independentChainExtension_wellSlotted (fun _ => A) (independentFreshChildrenList slots birthLength)
      (fun _ => hA) (independentStoredParameterProjection (4 * r) Y))
    (ρ • independentIntrinsicSlowProjection (4 * r) Y) i j).comp
    (continuous_const.mul continuous_id)).measurable

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal full native metric keeps its genuine Gram symmetry at every parameter point. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeMetric_isSymm {r : ℕ} (D : OCData) (level : ℕ) (A : RealChain)
    (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ t : ℝ) (Y : Vec (2 + 4 * r)) :
    (independentFreshNativeMetric D level A slots birthLength ρ t Y).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact actual_family_metric_symmetric D
    ((independentFreshStoredFamily A slots birthLength (independentStoredParameterProjection (4 * r) Y)).recenter D
      (ρ • independentIntrinsicSlowProjection (4 * r) Y)) (D.cellScaleSq level * t) j i

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine earlier fields identify the complete literal synthetic native inverse source. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_coefficient_cell_source_slice (H : ℕ) (hH : 1 ≤ H)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + 2 * D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + D + 1) (a v u e γ α)) (t : ℝ) (z X : Vec 2) :
    independentLiftCoefficientCellSource edge a L A η G v c hh n out inp t z (L X + offset) =
      normalizedLiftCellSource
        ⟨η, fun t X => G t (L X + offset), v,
          independentConstituentEdgeSlice edge a Qa L offset⟩
        (fun p q => independentScalarCoefficientSlice (c p q) L offset)
        (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) hh n A t z X out := by
  let QA := fun u => independentLiftAFromEarlierCoefficients H edge a L hL A η G v c hh n hn u inp
    (fun i j => (QG i j).restrictOrder (H + 1) (by omega))
    (fun i => (Qv i).restrictOrder H (by omega))
    (fun p q hpq m α v u => (Qc p q hpq m α v u).restrictOrder (H + D + 2) (by omega))
    (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + 1) (by omega))
  have QM j (hj : j ∈ Finset.Icc 1 (n - 2)) (p : ℕ × ℕ)
      (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) (w : ι) :
      IndependentParameterSourceReserve (H + j)
        (independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp) := by
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hmeanPre (r s : ℕ) (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
        r < hh ∨ (r = hh ∧ s < n) := by
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hlt : r < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩
    exact independentLiftAFromEarlierCoefficients (H + j) edge a L hL A η G v c
      p.2 (n - j) (by omega) w inp
      (fun i k => (QG i k).restrictOrder (H + j + 1) (by omega))
      (fun i => (Qv i).restrictOrder (H + j) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).restrictOrder
        ((H + j) + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + j + 1) (by omega))
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨η, fun t X => G t (L X + offset), v, independentConstituentEdgeSlice edge a Qa L offset⟩
  let Cc := fun p q => independentScalarCoefficientSlice (c p q) L offset
  let f := fun (_ : ℝ) X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)
  have hA t z X u : independentLiftCoefficientASource edge a L A η G v c hh n u inp t z
      (L X + offset) = normalizedLiftASource Q Cc f hh n A t z X u := by
    exact independent_lift_coefficient_a_source_slice H hH edge hD a L hL offset A η G v c hh n hn u inp
      (fun i k => (QG i k).restrictOrder (H + 1) (by omega))
      (fun p q hpq m α v u => (Qc p q hpq m α v u).restrictOrder (H + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + 1) (by omega)) t z X
  have hM j (hj : j ∈ Finset.Icc 1 (n - 2)) p
      (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) t z X u :
      independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) u inp t z
        (L X + offset) = normalizedLiftASource Q Cc f p.2 (n - j) A t z X u := by
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hmeanPre r s (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
        r < hh ∨ (r = hh ∧ s < n) := by
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hlt : r < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩
    exact independent_lift_coefficient_a_source_slice (H + j) (by omega) edge hD a L hL offset A η G v c
      p.2 (n - j) (by omega) u inp
      (fun i k => (QG i k).restrictOrder (H + j + 1) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).restrictOrder
        (H + j + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + j + 1) (by omega)) t z X
  exact independent_lift_cell_source_affine edge a L hL offset A η G v c Q Cc f hh n out inp
    QA QM hA hM t z X (by
      intro j _ p _ m α u
      simp only [Cc, independentScalarCoefficientSlice, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, mul_one])

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite literal flux-mean calibration retains full independent reserves and each matrix weight. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentMeanFluxCoefficientSource
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ) (out inp : ι) (k : Fin 2)
    (t : ℝ) (_ : Vec 2) (Y : Vec d) : ℝ :=
  ∑ p : Fin (m + 1) × Fin (n - 1 + 1), liftCalibrationWeight (n - 1) m α lam p •
    fieldCellMean (fun z => independentLiftFluxSource edge a J
      (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) η G v c hh n out inp k t z Y)

def independentMeanFluxCoefficientCost (d H D n m count : ℕ) (α : DerivativeWord2 m)
    (lam η BG BV BE B : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) × Fin (n - 1 + 1),
    ‖liftCalibrationWeight (n - 1) m α lam p • ContinuousLinearMap.id ℝ ℝ‖ *
      (((d : ℝ) + 1) ^ H * ((H + 1 : ℕ) * independentLiftFluxProductionCost H D n count
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) η BG BV BE B))

theorem independentMeanFluxCoefficientSource_reserve_of_tests
    (H n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (f : (Fin (m + 1) × Fin (n - 1 + 1)) → ℝ → Vec 2 → Vec d → ℝ)
    (Q : ∀ p, IndependentParameterSourceReserve H (f p))
    (θ : ℝ) (B : Fin (m + 1) × Fin (n - 1 + 1) → ℝ)
    (hQ : ∀ p j, j ≤ H → (Q p).budget j ≤ θ * B p) :
    ∃ R : IndependentParameterSourceReserve H (fun t z Y =>
      ∑ p : Fin (m + 1) × Fin (n - 1 + 1), liftCalibrationWeight (n - 1) m α lam p • f p t z Y),
      ∀ j ≤ H, R.budget j ≤ θ *
        ∑ p : Fin (m + 1) × Fin (n - 1 + 1),
          ‖liftCalibrationWeight (n - 1) m α lam p • ContinuousLinearMap.id ℝ ℝ‖ * B p := by
  let L := fun p : Fin (m + 1) × Fin (n - 1 + 1) =>
    liftCalibrationWeight (n - 1) m α lam p • ContinuousLinearMap.id ℝ ℝ
  obtain ⟨R, hR⟩ := independentSourceReserve_sum_with_budget Finset.univ H
    (fun p t z Y => L p (f p t z Y)) (fun p => (Q p).map (L p))
  refine ⟨R.congrSource (by
    funext t z Y
    simp only [L, smul_apply, ContinuousLinearMap.id_apply]), ?_⟩
  intro j hj
  rw [IndependentParameterSourceReserve.congrSource_budget, hR j]
  change (∑ p, ‖L p‖ * (Q p).budget j) ≤ _
  apply (Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hQ p j hj) (norm_nonneg _))).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [L]
  ring

theorem independentMeanFluxCoefficientSource_translation_invariant
    (δ : Vec d) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α, IndependentSourceTranslationInvariant δ (a v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c p q m α t z Y v u))
    (hh n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ) (out inp : ι) (k : Fin 2) :
    IndependentSourceTranslationInvariant δ (independentMeanFluxCoefficientSource edge a J η G v c hh n m α lam out inp k) := by
  intro t z Y
  dsimp only [independentMeanFluxCoefficientSource]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg (fun x : ℝ => liftCalibrationWeight (n - 1) m α lam p • x)
  exact (independentLiftFluxSource_translation_invariant δ edge a J
    (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) η G v c hG ha hc hh n out inp k).cellMean t z Y

theorem independentMeanFluxCoefficient_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (out inp : ι) (k : Fin 2)
    (m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α, IndependentParameterSourceReserve H (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + D + 2 → (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ v u e γ hγ α r, r ≤ H → (Qa v u e γ hγ α).budget r ≤ M v u * BE)
    (hm : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ v u e, (edge v u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H
      (independentMeanFluxCoefficientSource edge a J η G v c hh n m α lam out inp k),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        independentMeanFluxCoefficientCost d H D n m count α lam η BG BV BE B := by
  let A := fun p : Fin (m + 1) × Fin (n - 1 + 1) =>
    lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))
  choose QT hQT using fun p : Fin (m + 1) × Fin (n - 1 + 1) =>
    independentLiftFluxMean_uniform_production H edge a J hJ (A p) η G v c hh n hn hhpos out inp k
      QG Qv Qc Qa M hM count BG BV BE B hBG hBV hBE hB hG hv hc he hm hlen
  obtain ⟨Q, hQ⟩ := independentMeanFluxCoefficientSource_reserve_of_tests H n m α lam
    (fun p t (_ : Vec 2) Y => fieldCellMean (fun z => independentLiftFluxSource edge a J (A p) η G v c hh n out inp k t z Y))
    QT (finiteMatrixPower M hh out inp)
    (fun p => ((d : ℝ) + 1) ^ H * ((H + 1 : ℕ) * independentLiftFluxProductionCost H D n count (A p) η BG BV BE B)) hQT
  exact ⟨Q, hQ⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The recursive stored-family construction and finite fresh-chain menu denote the same real chain. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshStoredFamily_eq_chain {r : ℕ} (A : RealChain) (slots : Fin r → ℤ)
    (birthLength : Fin r → ℝ) (Y : Vec (4 * r)) :
    independentFreshStoredFamily A slots birthLength Y = independentFreshChain A slots birthLength Y := by
  unfold independentFreshStoredFamily
  rw [independentChainExtension_eq_chain]
  simp only [independentFreshChildrenList, List.map_ofFn, Function.comp_def, independentFreshChain]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal finite chains retain the full joint flow regularity and fixed discrete anchor. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChain_flow_joint_contDiff {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (u s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      ((independentFreshChain A slots birthLength Y.1).geom D).1 u Y.2 s) := by
  have hf := (independentFreshChainExtension_joint_smooth D A hA slots birthLength).1 u s
  simpa only [← independentFreshStoredFamily_eq_chain, independentFreshStoredFamily] using hf

theorem independentFreshChain_center_contDiff {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun P : Vec (4 * r) =>
      ((independentFreshChain A slots birthLength P).geom D).2.1) := by
  have hc := (independentFreshChainExtension_joint_smooth D A hA slots birthLength).2
  simpa only [← independentFreshStoredFamily_eq_chain, independentFreshStoredFamily] using hc

theorem independentFreshChain_anchor_eq {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (P : Vec (4 * r)) :
    ((independentFreshChain A slots birthLength P).geom D).2.2 =
      independentChainExtensionAnchor D A.ctxLevel (A.geom D).2.2
        (independentFreshChildrenList slots birthLength) := by
  rw [← independentFreshStoredFamily_eq_chain]
  unfold independentFreshStoredFamily
  rw [independentChainExtension_geom D _ (fun _ => A) (fun _ => hA) _ _
    (fun _ => rfl) (fun _ => rfl)]
  exact independentChainExtensionGeom_anchor D _ A.ctxLevel A.slot (fun _ => A.geom D)
    (A.geom D).2.2 (fun _ => rfl) P

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual two-component independent flux-mean source retains the same matrix price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentMeanFluxVector_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (out inp : ι)
    (m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α, IndependentParameterSourceReserve H (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + D + 2 → (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ v u e γ hγ α r, r ≤ H → (Qa v u e γ hγ α).budget r ≤ M v u * BE)
    (hm : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ v u e, (edge v u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H (fun t z Y k =>
      independentMeanFluxCoefficientSource edge a J η G v c hh n m α lam out inp k t z Y),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        (2 * independentMeanFluxCoefficientCost d H D n m count α lam η BG BV BE B) := by
  choose Qk hQk using fun k : Fin 2 => independentMeanFluxCoefficient_uniform_production H edge a
    J hJ η G v c hh n hn hhpos out inp k m α lam QG Qv Qc Qa M hM count BG BV BE B
    hBG hBV hBE hB hG hv hc he hm hlen
  let F := fun k t z Y => independentMeanFluxCoefficientSource edge a J η G v c hh n m α lam out inp k t z Y
  refine ⟨independentSourcePiReserve H F Qk, ?_⟩
  intro r hr
  have hb := independentSourcePiReserve_uniform_budget H F Qk
    (finiteMatrixPower M hh out inp * independentMeanFluxCoefficientCost d H D n m count α lam η BG BV BE B)
    hQk r hr
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hb
  exact hb.trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
/-! A pointwise normalized native copy suffices to identify its component mean. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι]

theorem independentFluxMean_point_copy (F native : Vec 2 → ι → ℝ) (r : ℝ)
    (hF : Continuous F) (hcopy : ∀ z v, F z v = r • native z v) (v : ι) :
    fieldCellMean (fun z => F z v) = r • fieldCellMean native v := by
  have he : F = fun z => r • native z := by
    funext z v
    exact hcopy z v
  have hp := fieldCellMean_pi_apply F hF v
  have hm : fieldCellMean F = r • fieldCellMean native := by
    rw [he, fieldCellMean_smul]
  exact hp.trans (congrFun hm v)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal finite fresh menu has full smooth centered forward and inverse charts. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChainChart_joint_smooth {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      centeredGeometryChart ((independentFreshChain A slots birthLength Y.1).geom D) ρ u Y.2) := by
  have he : (fun Y : Vec (4 * r) × Vec 2 =>
      centeredGeometryChart ((independentFreshChain A slots birthLength Y.1).geom D) ρ u Y.2) =
      (fun Y : Vec (4 * r) × Vec 2 => ρ⁻¹ •
        (independentFreshStoredFamily A slots birthLength Y.1).famMap D u (ρ • Y.2)) := by
    funext Y
    rw [← independentFreshStoredFamily_eq_chain]
    rfl
  rw [he]
  exact independentFreshFamilyChart_joint_smooth D A hA slots birthLength ρ u

theorem independentFreshChainChartInv_joint_smooth {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin r → ℤ) (birthLength : Fin r → ℝ) (ρ u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      centeredGeometryChartInv ((independentFreshChain A slots birthLength Y.1).geom D) ρ u Y.2) := by
  let es := independentFreshChildrenList slots birthLength
  let B := independentFreshStoredFamily A slots birthLength
  let anchor := independentChainExtensionAnchor D A.ctxLevel (A.geom D).2.2 es
  have ha Y : ((B Y).geom D).2.2 = anchor := by
    change ((independentChainExtension (fun _ => A) es Y).geom D).2.2 = anchor
    rw [independentChainExtension_geom D es (fun _ => A) (fun _ => hA)
      A.ctxLevel A.slot (fun _ => rfl) (fun _ => rfl)]
    exact independentChainExtensionGeom_anchor D es A.ctxLevel A.slot (fun _ => A.geom D)
      (A.geom D).2.2 (fun _ => rfl) Y
  obtain ⟨hf, hc⟩ := independentFreshChainExtension_joint_smooth D A hA slots birthLength
  have horigin : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 =>
      ((B Y.1).geom D).1 u ((B Y.1).geom D).2.1 anchor) :=
    (hf u anchor).comp (contDiff_fst.prodMk (hc.comp contDiff_fst))
  have hleft := (hf anchor u).comp
    (contDiff_fst.prodMk (horigin.add (contDiff_snd.const_smul ρ)))
  have hright : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec (4 * r) × Vec 2 => ((B Y.1).geom D).2.1) :=
    hc.comp contDiff_fst
  have he : (fun Y : Vec (4 * r) × Vec 2 =>
      centeredGeometryChartInv ((independentFreshChain A slots birthLength Y.1).geom D) ρ u Y.2) =
      (fun Y : Vec (4 * r) × Vec 2 => ρ⁻¹ •
        (((B Y.1).geom D).1 anchor (((B Y.1).geom D).1 u ((B Y.1).geom D).2.1 anchor +
          ρ • Y.2) u - ((B Y.1).geom D).2.1)) := by
    funext Y
    rw [← independentFreshStoredFamily_eq_chain]
    change centeredGeometryChartInv ((B Y.1).geom D) ρ u Y.2 = _
    rw [centeredGeometryChartInv, ha]
  rw [he]
  exact (hleft.sub hright).const_smul _

end AVRegularity.EntryWeakProofs
end
end

section
/-! A finite common price covers every exponential test before all native cell data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

def independentCalibratedCellSourcePrice (d H D hh n m count : ℕ) (BG BV BE B : ℝ) : ℝ :=
  ∑ p : Fin (m + 1) × Fin (n + 1), independentLiftCellProductionCost d H D hh n count
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 BG BV BE B

theorem independentCalibratedCellSourcePrice_nonneg (d H D hh n m count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentCalibratedCellSourcePrice d H D hh n m count BG BV BE B :=
  Finset.sum_nonneg fun (p : Fin (m + 1) × Fin (n + 1)) _ => independentLiftCellProductionCost_nonneg d H D hh n count
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))
    1 BG BV BE B hBG hBV hBE hB

theorem independentLiftCellProductionCost_le_calibrated (d H D hh n m count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (p : Fin (m + 1) × Fin (n + 1)) :
    independentLiftCellProductionCost d H D hh n count
      ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) 1 BG BV BE B ≤
      independentCalibratedCellSourcePrice d H D hh n m count BG BV BE B :=
  Finset.single_le_sum (fun (p : Fin (m + 1) × Fin (n + 1)) _ => independentLiftCellProductionCost_nonneg d H D hh n count
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))
    1 BG BV BE B hBG hBV hBE hB) (Finset.mem_univ p)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Parent-normalized independent child coordinates give the literal real-chain family with fixed scheduling metadata. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def actualIndependentCoarseParameterChain (D : OCData) (A : RealChain)
    (P : Vec (4 * A.children.length)) : RealChain :=
  { A with children := List.ofFn (fun j => independentFreshChild (independentFreshCoarseBirthLength D A) j P) }

theorem actualIndependentCoarseParameterChain_eq_fresh (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (P : Vec (4 * A.children.length)) :
    actualIndependentCoarseParameterChain D A P = independentFreshStoredFamily (independentFreshBaseChain A)
      (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) (independentFreshCoarseBirthLength D A) P := by
  rw [independentFreshStoredFamily_eq_chain]
  have hs : [realChainSlotSeq A 0] ++ List.ofFn (fun j : Fin A.children.length => realChainSlotSeq A (j + 1)) = A.slots := by
    rw [← realChain_slots_ofFn A hA, List.ofFn_succ]
    rfl
  simp only [independentFreshChain, independentFreshBaseChain, List.nil_append, hs,
    actualIndependentCoarseParameterChain]

theorem actualIndependentCoarseParameterChain_native (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (hA : A.WellSlotted) :
    actualIndependentCoarseParameterChain D A (independentFreshCoarseChainPacking D A) = A := by
  rw [actualIndependentCoarseParameterChain_eq_fresh D A hA, independentFreshStoredFamily_eq_chain]
  exact independentFreshCoarseChainPacking_reconstruct D hΛ A hA

theorem actualIndependentCoarseParameterChain_admissible_iff (D : OCData) (A : RealChain)
    (bw : ℝ) (j₀ level : ℕ) (slot : ℤ) (hA : IsAdmissibleChain D bw j₀ level slot A)
    (P : Vec (4 * A.children.length)) :
    IsAdmissibleChain D bw j₀ level slot (actualIndependentCoarseParameterChain D A P) ↔
      ∀ j : Fin A.children.length,
        ∑ i : Fin 2, |(independentFreshChild (independentFreshCoarseBirthLength D A) j P).center i| <
          (1 + 2) * bw / 4 * D.eps (A.baseLevel + 1 + j) := by
  have hctx : (actualIndependentCoarseParameterChain D A P).ctxLevel = A.ctxLevel := by
    simp only [actualIndependentCoarseParameterChain, RealChain.ctxLevel, RealChain.lastLevel, List.length_ofFn]
  constructor
  · intro h j
    have hj : j.val < (actualIndependentCoarseParameterChain D A P).children.length := by
      simpa only [actualIndependentCoarseParameterChain, List.length_ofFn] using j.is_lt
    have hh := h.2.2.2.2.2.2 j hj
    simpa only [actualIndependentCoarseParameterChain, List.length_ofFn, List.getElem_ofFn, Fin.eta] using hh
  · intro h
    refine ⟨hctx.trans hA.1, hA.2.1, ?_, hA.2.2.2.1, hA.2.2.2.2.1,
      hA.2.2.2.2.2.1, ?_⟩
    · simpa only [actualIndependentCoarseParameterChain, List.length_ofFn] using hA.2.2.1
    · intro j hj
      have hj' : j < A.children.length := by simpa only [actualIndependentCoarseParameterChain, List.length_ofFn] using hj
      simpa only [actualIndependentCoarseParameterChain, List.getElem_ofFn] using h ⟨j, hj'⟩

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! The genuinely moved last child center is smooth in the complete independent family and offset. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def independentFreshRecenterLastChildCenter {r : ℕ} (D : OCData) (A : RealChain)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (ρ : ℝ)
    (Y : Vec (4 * (r + 1)) × Vec 2) : Vec 2 :=
  let B := independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y.1)
  (recenteredChild D (A.ctxLevel + r) (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r)))
    (B.geom D) (independentFreshChild birthLength (Fin.last r) Y.1) (ρ • Y.2)).center

theorem independentFreshRecenterLastChildCenter_contDiff {r : ℕ} (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (ρ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentFreshRecenterLastChildCenter D A slots birthLength ρ) := by
  let prefixSlots : Fin r → ℤ := fun j => slots j.castSucc
  let prefixLengths : Fin r → ℝ := fun j => birthLength j.castSucc
  let L : (Vec (4 * (r + 1)) × Vec 2) →L[ℝ] Vec (4 * r) := (independentFreshPrefixProjection r).comp
    (ContinuousLinearMap.fst ℝ (Vec (4 * (r + 1))) (Vec 2))
  let B : Vec (4 * r) → RealChain := independentFreshChain A prefixSlots prefixLengths
  let a := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
  let s := independentChainExtensionAnchor D A.ctxLevel (A.geom D).2.2
    (independentFreshChildrenList (fun j : Fin r => slots j.castSucc) (fun j => birthLength j.castSucc))
  let center := fun Y : Vec (4 * (r + 1)) × Vec 2 => ((B (L Y)).geom D).2.1
  let childCenter := fun Y : Vec (4 * (r + 1)) × Vec 2 =>
    (independentFreshChild birthLength (Fin.last r) Y.1).center
  have hc : ContDiff ℝ (⊤ : ℕ∞) center :=
    (independentFreshChain_center_contDiff D A hA prefixSlots prefixLengths).comp (f := fun Y => L Y) L.contDiff
  have hchild : ContDiff ℝ (⊤ : ℕ∞) childCenter :=
    ((independentFreshChildProjection (Fin.last r) false).contDiff.comp contDiff_fst).const_smul _
  let inner := fun Y : Vec (4 * (r + 1)) × Vec 2 =>
    ((B (L Y)).geom D).1 a (center Y + childCenter Y) s
  let outer := fun Y : Vec (4 * (r + 1)) × Vec 2 =>
    ((B (L Y)).geom D).1 s (inner Y + ρ • Y.2) a
  have hf (u v : ℝ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun Z : (Vec (4 * (r + 1)) × Vec 2) × Vec 2 =>
        ((B (L Z.1)).geom D).1 u Z.2 v) := by
    let K : ((Vec (4 * (r + 1)) × Vec 2) × Vec 2) →L[ℝ] (Vec (4 * r) × Vec 2) :=
      (L.comp (ContinuousLinearMap.fst ℝ (Vec (4 * (r + 1)) × Vec 2) (Vec 2))).prod
        (ContinuousLinearMap.snd ℝ (Vec (4 * (r + 1)) × Vec 2) (Vec 2))
    exact (independentFreshChain_flow_joint_contDiff D A hA prefixSlots prefixLengths u v).comp
      (f := fun Z => K Z) K.contDiff
  have hout : ContDiff ℝ (⊤ : ℕ∞) (fun Y => outer Y - center Y) := by
    exact jointFlowRecenterCenter_contDiff
      (fun Y => ((B (L Y)).geom D).1) center childCenter
      (fun Y => ρ • Y.2) a s hf hc hchild (contDiff_snd.const_smul ρ)
  have he : independentFreshRecenterLastChildCenter D A slots birthLength ρ =
      fun Y => outer Y - center Y := by
    funext Y
    dsimp only [independentFreshRecenterLastChildCenter, recenteredChild]
    rw [independentFreshChain_anchor_eq D A hA prefixSlots prefixLengths]
    change childCenter Y + (outer Y - center Y - childCenter Y) = outer Y - center Y
    abel
  rw [he]
  exact hout

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced lift fluxes and their finite mean coefficients depend only on open slow germs. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Set (Vec 2)}

theorem independentLiftFluxSource_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (Y Z : Vec d)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c e : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (Qc : ∀ p q, ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (D + 1) (fun t z W => c p q m.val α t z W v u))
    (Qe : ∀ p q, ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (D + 1) (fun t z W => e p q m.val α t z W v u))
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn J U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn J U Y Z (a v u e γ α) (b v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceSlowSliceEqOn J U Y Z
      (fun t z W => c p q m α t z W v u) (fun t z W => e p q m α t z W v u))
    (hh n : ℕ) (out inp : ι) (k : Fin 2) :
    IndependentSourceSlowSliceEqOn J U Y Z
      (independentLiftFluxSource edge a J A η G v c hh n out inp k)
      (independentLiftFluxSource edge b J A η G' v e hh n out inp k) := by
  let F := fun p q t z W w => independentScalarLiftTestSource q (c p q) A w inp t z W
  let F' := fun p q t z W w => independentScalarLiftTestSource q (e p q) A w inp t z W
  have hF p q w : IndependentSourceSlowSliceEqOn J U Y Z
      (fun t z W => F p q t z W w) (fun t z W => F' p q t z W w) :=
    independentScalarLiftTestSource_slow_slice_congr J Y Z q (c p q) (e p q) (hc p q) A w inp
  have QF p q w : IndependentParameterSourceReserve (D + 1) (fun t z W => F p q t z W w) :=
    independentScalarLiftTestSourceReserve (D + 1) q (c p q) A w inp (fun m α => Qc p q m α w inp)
  have QF' p q w : IndependentParameterSourceReserve (D + 1) (fun t z W => F' p q t z W w) :=
    independentScalarLiftTestSourceReserve (D + 1) q (e p q) A w inp (fun m α => Qe p q m α w inp)
  have hd j := (hF hh (n - 1) out).fastPartial j
  have hs j := (hF hh (n - 2) out).covariantSlow hU (QF _ _ out) (QF' _ _ out) (by omega) A j
  dsimp only [IndependentSourceSlowSliceEqOn] at hF hG hd hs
  intro t X hX z
  have hcross : independentLiftFluxCrossSource J A η G v
      (fun t z W => F hh (n - 1) t z W out) (fun t z W => F hh (n - 2) t z W out) k t z (J X + Y) =
      independentLiftFluxCrossSource J A η G' v
        (fun t z W => F' hh (n - 1) t z W out) (fun t z W => F' hh (n - 2) t z W out) k t z (J X + Z) := by
    dsimp only [independentLiftFluxCrossSource]
    simp_rw [hF hh (n - 1) out t X hX z, hG _ _ t X hX z, hd _ t X hX z, hs _ t X hX z]
  change _ - _ = _ - _
  refine congrArg₂ (fun r s : ℝ => r - s) hcross ?_
  apply congrArg (fun r : ℝ => Real.sqrt η • r)
  apply Finset.sum_congr rfl
  intro j _
  exact independentSourceFluxComponentCoefficient_slow_slice_congr (H := 1)
    edge a b J hJ Y Z A η _ _
    (fun w => (QF (hh - 1) (n - j) w).restrictOrder (1 + D) (by omega))
    (fun w => (QF' (hh - 1) (n - j) w).restrictOrder (1 + D) (by omega))
    hU (fun v u e γ hγ α => ha v u e γ hγ α)
    (fun w => hF (hh - 1) (n - j) w) k (j - 1) out t X hX z

theorem independentMeanFluxCoefficientSource_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (Y Z : Vec d)
    (η : ℝ)
    (G G' : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c e : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (Qc : ∀ p q, ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (D + 1) (fun t z W => c p q m.val α t z W v u))
    (Qe : ∀ p q, ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (D + 1) (fun t z W => e p q m.val α t z W v u))
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn J U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn J U Y Z (a v u e γ α) (b v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceSlowSliceEqOn J U Y Z
      (fun t z W => c p q m α t z W v u) (fun t z W => e p q m α t z W v u))
    (hh n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ) (out inp : ι) (k : Fin 2) :
    IndependentSourceSlowSliceEqOn J U Y Z
      (independentMeanFluxCoefficientSource edge a J η G v c hh n m α lam out inp k)
      (independentMeanFluxCoefficientSource edge b J η G' v e hh n m α lam out inp k) := by
  intro t X hX z
  dsimp only [independentMeanFluxCoefficientSource]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun r : ℝ => liftCalibrationWeight (n - 1) m α lam p • r)
  apply congrArg fieldCellMean
  funext w
  exact independentLiftFluxSource_slow_slice_congr edge a b J hJ Y Z
    (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) η G G' v c e
    Qc Qe hU hG ha hc hh n out inp k t X hX w

end AVRegularity.EntryWeakProofs
end
end

section
/-! Recentering a fresh family changes precisely its literal last child. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChain_recenter_children_succ {r : ℕ} (D : OCData) (A : RealChain)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (ρ : ℝ)
    (Y : Vec (4 * (r + 1)) × Vec 2) :
    ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2)).children =
      let B := independentFreshChain A (fun j => slots j.castSucc)
        (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y.1)
      B.children ++ [recenteredChild D (A.ctxLevel + r)
        (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r)))
        (B.geom D) (independentFreshChild birthLength (Fin.last r) Y.1) (ρ • Y.2)] := by
  rw [independentFreshChain_succ]
  dsimp only
  let B := independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y.1)
  change ((⟨B.baseLevel, B.slots ++ [slots (Fin.last r)], B.base,
    B.children ++ [independentFreshChild birthLength (Fin.last r) Y.1]⟩ : RealChain).recenter D
    (ρ • Y.2)).children = _
  rw [recenter_append_child]
  have hctx : B.baseLevel + 1 + B.children.length = A.ctxLevel + r := by
    change A.baseLevel + 1 + (A.children ++ List.ofFn
      (fun j : Fin r => independentFreshChild (fun i => birthLength i.castSucc) j
        (independentFreshPrefixProjection r Y.1))).length = A.ctxLevel + r
    simp only [List.length_append, List.length_ofFn, RealChain.ctxLevel, RealChain.lastLevel]
    omega
  simp only [hctx]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
/-! All child-center coordinates of the actual recentered fresh family are continuous. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChain_recenter_child_getD_center_continuous_succ {r : ℕ}
    (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (ρ : ℝ) (j : ℕ) :
    Continuous (fun Y : Vec (4 * (r + 1)) × Vec 2 =>
      (((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2)).children.getD
        j ⟨0, 0⟩).center) := by
  let L : (Vec (4 * (r + 1)) × Vec 2) →L[ℝ] Vec (4 * r) :=
    (independentFreshPrefixProjection r).comp (ContinuousLinearMap.fst ℝ _ _)
  let B : Vec (4 * r) → RealChain := independentFreshChain A
    (fun k => slots k.castSucc) (fun k => birthLength k.castSucc)
  let last : (Vec (4 * (r + 1)) × Vec 2) → ChainChild := fun Y =>
    recenteredChild D (A.ctxLevel + r)
      (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r)))
      ((B (L Y)).geom D) (independentFreshChild birthLength (Fin.last r) Y.1) (ρ • Y.2)
  have he : (fun Y : Vec (4 * (r + 1)) × Vec 2 =>
      ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2)).children) =
      fun Y => (B (L Y)).children ++ [last Y] := by
    funext Y
    exact independentFreshChain_recenter_children_succ D A slots birthLength ρ Y
  have he' := congrArg (fun f => fun Y : Vec (4 * (r + 1)) × Vec 2 =>
    ((f Y : List ChainChild).getD j ⟨0, 0⟩).center) he
  rw [he']
  apply list_append_child_getD_center_continuous (fun Y => (B (L Y)).children) last
    (A.children.length + r)
  · intro Y
    simp only [B, independentFreshChain, List.length_append, List.length_ofFn]
  · intro k
    exact (independentFreshChain_child_getD_center_contDiff A
      (fun i => slots i.castSucc) (fun i => birthLength i.castSucc) k).continuous.comp L.continuous
  · exact (independentFreshRecenterLastChildCenter_contDiff D A hA slots birthLength ρ).continuous

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual full stored families have fixed metadata, smooth charts, and determinant-one geometry. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem actualIndependentCoarseParameterChain_ctxLevel (D : OCData) (A : RealChain)
    (P : Vec (4 * A.children.length)) :
    (actualIndependentCoarseParameterChain D A P).ctxLevel = A.ctxLevel := by
  simp only [actualIndependentCoarseParameterChain, RealChain.ctxLevel, RealChain.lastLevel, List.length_ofFn]

theorem actualIndependentCoarseParameterChain_slot (D : OCData) (A : RealChain)
    (P : Vec (4 * A.children.length)) :
    (actualIndependentCoarseParameterChain D A P).slot = A.slot := rfl

theorem actualIndependentCoarseParameterChain_wellSlotted (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (P : Vec (4 * A.children.length)) :
    (actualIndependentCoarseParameterChain D A P).WellSlotted := by
  change A.slots.length = (List.ofFn (fun j => independentFreshChild
    (independentFreshCoarseBirthLength D A) j P)).length + 1
  rw [List.length_ofFn]
  exact hA

theorem actualIndependentCoarseParameterChain_chart_contDiff (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (ρ u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Z : Vec (4 * A.children.length) × Vec 2 =>
      centeredGeometryChart ((actualIndependentCoarseParameterChain D A Z.1).geom D) ρ u Z.2) := by
  have he : actualIndependentCoarseParameterChain D A = fun P =>
      independentFreshChain (independentFreshBaseChain A)
        (fun j : Fin A.children.length => realChainSlotSeq A (j + 1))
        (independentFreshCoarseBirthLength D A) P := by
    funext P
    rw [actualIndependentCoarseParameterChain_eq_fresh D A hA, independentFreshStoredFamily_eq_chain]
  rw [he]
  exact independentFreshChainChart_joint_smooth D (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) _ _ ρ u

theorem actualIndependentCoarseParameterChain_area (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) {bw : ℝ} {j₀ i : ℕ} {slot : ℤ}
    (hA : IsAdmissibleChain D bw j₀ i slot A) (P : Vec (4 * A.children.length)) :
    GeomAreaPreserving ((actualIndependentCoarseParameterChain D A P).geom D) := by
  rw [actualIndependentCoarseParameterChain_eq_fresh D A hA.2.2.1, independentFreshStoredFamily_eq_chain]
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
/-! Full independent flux fields copy the literal native physical flux. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_coefficient_flux_source_slice (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (out inp : ι) (k : Fin 2)
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α)) (t : ℝ) (z X : Vec 2) :
    independentLiftFluxSource edge a L A η G v c hh n out inp k t z (L X + offset) =
      (Real.exp (A X))⁻¹ •
        (liftFluxX ⟨η, fun t X => G t (L X + offset), v,
          independentConstituentEdgeSlice edge a Qa L offset⟩
          (fun p q => independentScalarCoefficientSlice (c p q) L offset)
          (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) hh n t X z k) out := by
  symm
  exact independent_lift_flux_affine edge hD a Qa L hL offset A η G v
    (fun p q => independentScalarCoefficientSlice (c p q) L offset)
    (fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y)
    hh n hn hhpos out inp k
    (fun p q hpq w => independentScalarLiftTestSourceReserve (H + 1 + D + 1) q (c p q) A w inp
      (fun m α => (Qc p q hpq m α w inp).restrictOrder (H + 1 + D + 1) (by omega)))
    (fun p q _ t X z => independent_coefficient_slice_apply q (c p q) L offset A inp t X z)
    t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! The joint stored-coordinate and slow-offset carrier is genuinely open. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshChain_recenter_carrier_isOpen_succ {r : ℕ}
    (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (ρ bw : ℝ)
    (j₀ level : ℕ) (slot : ℤ) (P₀ : Vec (4 * (r + 1)))
    (h₀ : IsAdmissibleChain D bw j₀ level slot
      (independentFreshChain A slots birthLength P₀)) :
    IsOpen {Y : Vec (4 * (r + 1)) × Vec 2 |
      IsAdmissibleChain D bw j₀ level slot
        ((independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2))} := by
  apply weak_admissible_family_isOpen D bw j₀ level slot
    (independentFreshChain A slots birthLength P₀)
    (fun Y : Vec (4 * (r + 1)) × Vec 2 =>
      (independentFreshChain A slots birthLength Y.1).recenter D (ρ • Y.2)) h₀
  · intro Y
    rw [(Providers.GenSem.recenter_baseLevel D _ _).1]
    rfl
  · intro Y
    rw [(Providers.GenSem.recenter_baseLevel D _ _).2]
    rfl
  · intro Y
    rw [independentFreshChain_recenter_children_succ]
    simp only [independentFreshChain, List.length_append, List.length_singleton, List.length_ofFn]
    omega
  · intro j
    exact independentFreshChain_recenter_child_getD_center_continuous_succ
      D A hA slots birthLength ρ j

end AVRegularity.EntryWeakProofs
end
end

section
/-! A threshold before the actual data gives unit Pe and all retained pulse drift budgets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_weak_pulse_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (H : ℕ) :
    ∃ M₀ : ℕ, ∀ D : OCData, M₀ ≤ D.term →
      D.α = α → D.q = q → D.Λ = Λ → IsOCBandChain α q Λ D.ζ D.term D.κ →
      ∀ m, D.term < m →
        D.eps m ^ (1 + D.α) / D.kap m ≤ 1 ∧
        D.eps m ^ (1 + D.α) / D.kap m ≤ pulseHigherDriftThreshold H := by
  obtain ⟨M₀, hp⟩ := weak_peclet_eventually_small hα₀ hα₁ hs₀ hs₁ hq Λ hΛ
    (min 1 (pulseHigherDriftThreshold H)) (lt_min zero_lt_one (pulseHigherDriftThreshold_pos H))
  refine ⟨M₀, ?_⟩
  intro D hterm hDα hDq hDΛ hband m hm
  have hb : D.eps m ^ (1 + D.α) / D.kap m ≤ min 1 (pulseHigherDriftThreshold H) := by
    rw [weakData_kap_terminal D m (by omega)]
    simpa only [OCData.eps, hDα, hDq, hDΛ] using hp D.term hterm (D.κ D.term) hband.1 m hm
  exact ⟨hb.trans (min_le_left _ _), hb.trans (min_le_right _ _)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full native metrics compare through literal stored-family geometry, including off-carrier references. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshNativeMetric_geom_congr {r : ℕ} (D : OCData) (level : ℕ)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (slots slots' : Fin r → ℤ) (birthLength birthLength' : Fin r → ℝ)
    (ρ : ℝ) (Y Z : Vec (2 + 4 * r))
    (hgeom : (independentFreshStoredFamily A slots birthLength
        (independentStoredParameterProjection (4 * r) Y)).geom D =
      (independentFreshStoredFamily B slots' birthLength'
        (independentStoredParameterProjection (4 * r) Z)).geom D)
    (hslow : independentIntrinsicSlowProjection (4 * r) Y =
      independentIntrinsicSlowProjection (4 * r) Z) (t : ℝ) :
    independentFreshNativeMetric D level A slots birthLength ρ t Y =
      independentFreshNativeMetric D level B slots' birthLength' ρ t Z := by
  dsimp only [independentFreshNativeMetric]
  rw [hslow]
  apply weak_family_metric_recenter_geom_congr
  · exact independentChainExtension_wellSlotted (fun _ => A)
      (independentFreshChildrenList slots birthLength) (fun _ => hA) _
  · exact independentChainExtension_wellSlotted (fun _ => B)
      (independentFreshChildrenList slots' birthLength') (fun _ => hB) _
  · exact hgeom

theorem independentFreshNativeMetric_slow_slice_geom_congr {r : ℕ} (D : OCData) (level : ℕ)
    (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (slots slots' : Fin r → ℤ) (birthLength birthLength' : Fin r → ℝ)
    (ρ : ℝ) (Y Z : Vec (2 + 4 * r))
    (hgeom : (independentFreshStoredFamily A slots birthLength
        (independentStoredParameterProjection (4 * r) Y)).geom D =
      (independentFreshStoredFamily B slots' birthLength'
        (independentStoredParameterProjection (4 * r) Z)).geom D)
    (hslow : independentIntrinsicSlowProjection (4 * r) Y =
      independentIntrinsicSlowProjection (4 * r) Z) (U : Set (Vec 2)) (i j : Fin 2) :
    IndependentSourceSlowSliceEqOn (independentIntrinsicSlowEmbedding (4 * r)) U Y Z
      (fun t (_ : Vec 2) W => independentFreshNativeMetric D level A slots birthLength ρ t W i j)
      (fun t _ W => independentFreshNativeMetric D level B slots' birthLength' ρ t W i j) := by
  intro t X _hX _z
  have he := independentFreshNativeMetric_geom_congr D level A B hA hB slots slots'
    birthLength birthLength' ρ
    (independentIntrinsicSlowEmbedding (4 * r) X + Y)
    (independentIntrinsicSlowEmbedding (4 * r) X + Z)
    (by simpa only [map_add, independentStoredParameterProjection_embedding, zero_add] using hgeom)
    (by simp only [map_add, independentIntrinsicSlowProjection_embedding, hslow]) t
  exact congrFun (congrFun he i) j

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual molecular solving clocks lie inside the native chart reserve window. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

theorem actual_family_pulse_in_native_chart_window (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (hA : A.WellSlotted) (J : ℕ) (u : ℝ)
    (hu : u ∈ ocPulseWindow D.α D.q D.Λ A.ctxLevel A.slot) :
    u ∈ nativeWeakChartWindow D A.baseLevel J (realChainSlotSeq A) A.children.length := by
  have hc : A.baseLevel + 1 + A.children.length = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel]
    omega
  change |u - D.slotAnchor (A.baseLevel + 1 + A.children.length)
    (realChainSlotSeq A A.children.length)| ≤ _
  rw [hc, realChainSlotSeq_last A hA]
  have hb : |u - D.slotAnchor A.ctxLevel A.slot| ≤ ocTauPP D.α D.q D.Λ A.ctxLevel :=
    weak_lift_anchor_distance D.α D.q hΛ A.ctxLevel A.slot u hu
  have hR : (1 : ℝ) ≤ finiteChainWindowRadius J A.children.length := by
    unfold finiteChainWindowRadius
    exact le_add_of_nonneg_left (by positivity)
  exact hb.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hR (Construction.Stream.ocTauPP_pos hΛ).le)

theorem actual_lift_clock_in_native_chart_window (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (A : RealChain) (hA : A.WellSlotted) (J : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
      ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)) :
    D.cellScaleSq A.ctxLevel * t ∈ nativeWeakChartWindow D A.baseLevel J (realChainSlotSeq A) A.children.length :=
  actual_family_pulse_in_native_chart_window D hΛ A hA J _
    (weak_lift_clock_in_pulse_window D hΛ hζ hband A.ctxLevel A.slot t ht)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The zero-child anchor's full coordinates realize the literal moving reference family. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def weakZeroChildParameterPacking (A : RealChain) (slot : ℤ)
    (P : Vec (4 * (A.children.length + 1))) : Vec (4 * (weakZeroChildAnchor A slot).children.length) :=
  (show A.children.length + 1 = (weakZeroChildAnchor A slot).children.length by
    simp only [weakZeroChildAnchor, List.length_append, List.length_singleton]) ▸ P

def weakZeroChildReferenceFamily (D : OCData) (A : RealChain) (slot : ℤ)
    (P : Vec (4 * (A.children.length + 1))) : RealChain :=
  independentFreshChain (independentFreshBaseChain A)
    (Fin.lastCases slot (fun j => realChainSlotSeq A (j + 1)))
    (fun j => D.eps (A.baseLevel + j)) P

theorem actualZeroChildParameterChain_eq_reference (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slot : ℤ) (P : Vec (4 * (A.children.length + 1))) :
    actualIndependentCoarseParameterChain D (weakZeroChildAnchor A slot)
      (weakZeroChildParameterPacking A slot P) = weakZeroChildReferenceFamily D A slot P := by
  have hs : [realChainSlotSeq A 0] ++
      List.ofFn (Fin.lastCases slot (fun j : Fin A.children.length => realChainSlotSeq A (j + 1))) =
      A.slots ++ [slot] := by
    rw [List.ofFn_succ']
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, List.concat_eq_append, ← List.append_assoc]
    have hh := realChain_slots_ofFn A hA
    rw [List.ofFn_succ] at hh
    simpa only [List.singleton_append, Fin.val_zero, Fin.val_succ] using congrArg (fun L => L ++ [slot]) hh
  have hlen : A.children.length + 1 = (weakZeroChildAnchor A slot).children.length := by
    simp only [weakZeroChildAnchor, List.length_append, List.length_singleton]
  have hc := independentFreshChild_ofFn_cast _ _ hlen
    (fun j : Fin (A.children.length + 1) => D.eps (A.baseLevel + j))
    (independentFreshCoarseBirthLength D (weakZeroChildAnchor A slot)) (fun _ => rfl) P
  exact congrArg₂ (fun (ss : List ℤ) (cc : List ChainChild) =>
    (⟨A.baseLevel, ss, A.base, cc⟩ : RealChain)) hs.symm hc.symm

theorem weakZeroChildReferenceFamily_prefix (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slot : ℤ) (P : Vec (4 * A.children.length)) :
    independentFreshChain (independentFreshBaseChain A)
      (fun j : Fin A.children.length => Fin.lastCases slot
        (fun k => realChainSlotSeq A (k + 1)) j.castSucc)
      (fun j : Fin A.children.length => D.eps (A.baseLevel + j.castSucc.val)) P =
      actualIndependentCoarseParameterChain D A P := by
  rw [actualIndependentCoarseParameterChain_eq_fresh D A hA, independentFreshStoredFamily_eq_chain]
  simp only [Fin.lastCases_castSucc]
  rfl

theorem weakZeroChildReferenceFamily_append_geometry (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (slot : ℤ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hρeps : ρ = D.eps (A.ctxLevel - 1)) (t : ℝ) (z : Vec 2)
    (Y : Vec (2 + 4 * A.children.length)) :
    (weakZeroChildReferenceFamily D A slot
      (independentFreshCoarseAppendPacking A.children.length D A.ctxLevel A.slot slot
        (D.eps A.ctxLevel / ρ) t (z, Y))).geom D =
      (((actualIndependentCoarseParameterChain D A
        (independentStoredParameterProjection (4 * A.children.length) Y)).recenter D
          (ρ • independentIntrinsicSlowProjection (4 * A.children.length) Y)).appendChild D slot t z).geom D := by
  let slots : Fin (A.children.length + 1) → ℤ :=
    Fin.lastCases slot (fun j => realChainSlotSeq A (j + 1))
  let birth : Fin (A.children.length + 1) → ℝ := fun j => D.eps (A.baseLevel + j)
  have hbirth : birth (Fin.last A.children.length) = ρ := by
    rw [hρeps]
    dsimp only [birth, Fin.val_last]
    congr 1
  have hctx : (independentFreshBaseChain A).ctxLevel + A.children.length = A.ctxLevel := by
    simp only [independentFreshBaseChain, RealChain.ctxLevel, RealChain.lastLevel, List.length_nil]
    omega
  have he := independentFreshCoarseAppendPacking_reference_geom D (independentFreshBaseChain A)
    (independentFreshBaseChain_wellSlotted A) slots birth ρ hρ hbirth t (z, Y)
  dsimp only at he
  dsimp only [slots, birth] at he
  rw [weakZeroChildReferenceFamily_prefix D A hA slot] at he
  rw [hctx, actualIndependentCoarseParameterChain_slot D A, Fin.lastCases_last] at he
  exact he

end AVRegularity.EntryWeakProofs
end
end
end

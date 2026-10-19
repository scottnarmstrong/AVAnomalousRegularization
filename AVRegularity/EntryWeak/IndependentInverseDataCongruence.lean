-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentExplicitNaturalCoefficientCalibration
public import AVRegularity.EntryWeak.IndependentSourceFluxComponentReserve
import AVRegularity.CycleEvolution.CellInverseJetEquationExistence

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Produced independent forcing and mean corrections identify the literal actual inverse source. -/

variable {d D H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_centered_recurrence_eq_actual
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (out : ι)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ)
    (QF : ∀ u, IndependentParameterSourceReserve H (fun t z Y => F t z Y u))
    (T : ℕ → (ℕ × ℕ) → ℝ → Vec 2 → Vec d → ℝ)
    (t : ℝ) (z X : Vec 2) (Y : Vec d)
    (hA : ∀ z u, F t z Y u = normalizedLiftASource Q Cc f hh n A t z X u)
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      T j ab t z Y = (Real.exp (A X))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z out) :
    independentCenteredRecurrenceSource hh n (fun t z Y => F t z Y out) T t z Y =
      normalizedLiftCellSource Q Cc f hh n A t z X out := by
  let Qwhole := independentSourcePiReserve H (fun u t z Y => F t z Y u) QF
  have hc : Continuous (fun z => F t z Y) :=
    ((Qwhole.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
  have he : (fun z => F t z Y) =
      fun z => (Real.exp (A X))⁻¹ • liftA Q Cc f hh n t X z := by
    funext z u
    exact hA z u
  have hp := fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) out) hc
  change fieldCellMean (fun z => F t z Y out) = fieldCellMean (fun z => F t z Y) out at hp
  have hm : fieldCellMean (fun z => F t z Y out) =
      (Real.exp (A X))⁻¹ • liftMean Q Cc f hh n t X out := by
    rw [hp, he, fieldCellMean_smul]
    rfl
  unfold independentCenteredRecurrenceSource
  dsimp only
  rw [hA z out, hm]
  simp only [normalizedLiftCellSource, liftCellSource, smul_add, smul_neg, smul_sub,
    Finset.smul_sum, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply,
    Pi.smul_apply, normalizedLiftASource]
  apply congrArg (fun x => -((Real.exp (A X))⁻¹ • liftA Q Cc f hh n t X z out -
    (Real.exp (A X))⁻¹ • liftMean Q Cc f hh n t X out) + x)
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_congr rfl (fun ab hab => hT j hj ab hab)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Parameterized constituent slices have the literal inherited source flux coefficients. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D H : ℕ}

def independentConstituentEdgeSlice (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve H (a v u d γ α))
    (L : Vec 2 →L[ℝ] P) (offset : P) : ConstituentEdges D (fun _ : ι => ℝ) := by
  classical
  exact fun v u d => (edge v u d).map fun γ =>
    { map := γ.map
      coeff := fun α t X z => if hγ : γ ∈ edge v u d then a v u d γ α t z (L X + offset) else 0
      periodic := fun α t X n z => by
        dsimp only
        split_ifs with hγ
        · exact (Qa v u d γ hγ α).periodic t (L X + offset) n z
        · rfl
      record := γ.record
      birthExcess_ge := γ.birthExcess_ge }

omit [DecidableEq ι] in
theorem independent_source_flux_affine_slice
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve H (a v u d γ α))
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (offset : P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z Y => f t z Y u))
    (k : Fin 2) (j : ℕ) (v : ι) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ • sourceFluxComponentCoefficient
      (independentConstituentEdgeSlice edge a Qa L offset) η t
      (fun X z => Real.exp (A X) • f t z (L X + offset)) k j v X z =
      independentSourceFluxComponentCoefficient edge a L A η f k j v t z (L X + offset) := by
  classical
  simp only [sourceFluxComponentCoefficient, independentSourceFluxComponentCoefficient,
    independentConstituentEdgeSlice, Pi.smul_apply, Finset.smul_sum, List.smul_sum,
    List.map_map, Function.comp_def]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hγ
  apply Finset.sum_congr rfl
  intro α _
  simp only [dite_eq_left hγ]
  rw [smul_comm (Real.exp (A X))⁻¹, ← map_smul]
  rw [independent_covariant_list_affine_slice (Qf u) (List.ofFn α)
    (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.property).2; omega)
    L hL A η offset j t z X]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Actual edge-label and field equalities transport slices independently of reserve witnesses. -/

section
variable {ι P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {D H T : ℕ}

theorem independentConstituentEdgeSlice_congr
    (edge other : ConstituentEdges D (fun _ : ι => ℝ))
    (field otherField : ∀ _v _u : ι, ∀ d : Finset.Icc 2 D, Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ v u d, ∀ γ ∈ edge v u d, ∀ word,
      IndependentParameterSourceReserve H (field v u d γ word))
    (R : ∀ v u d, ∀ γ ∈ other v u d, ∀ word,
      IndependentParameterSourceReserve T (otherField v u d γ word))
    (he : edge = other) (hf : field = otherField) (L : Vec 2 →L[ℝ] P) (offset : P) :
    independentConstituentEdgeSlice edge field Q L offset =
      independentConstituentEdgeSlice other otherField R L offset := by
  subst other
  subst otherField
  rfl
end

/-! Empty eddy families remain literally empty under every native source slice and lift rescaling. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D H : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem independentConstituentEdgeSlice_empty
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (Qa : ∀ (v u : ι) (e : Finset.Icc 2 D) (γ : Constituent e.val ℝ ℝ), γ ∈ [] → ∀ α,
      IndependentParameterSourceReserve H (a v u e γ α))
    (L : Vec 2 →L[ℝ] Vec d) (offset : Vec d) :
    independentConstituentEdgeSlice (fun _ _ _ => []) a Qa L offset = (fun _ _ _ => []) := by
  funext v u e
  simp only [independentConstituentEdgeSlice, List.map_nil]

omit [Fintype ι] [DecidableEq ι] in
theorem liftEdges_empty (c lam : ℝ) :
    liftEdges (ι := ι) (h := fun _ => ℝ) (D := D) c lam (fun _ _ _ => []) = (fun _ _ _ => []) := by
  funext v u e
  simp only [liftEdges, List.map_nil]
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Independent native edge slices commute with restriction to the fixed weak order cap. -/

variable {ι P : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {Dm H T : ℕ}

def restrictedIndependentEdgeField (K : ℕ) (hKD : K ≤ Dm)
    (field : ∀ _v _u : ι, ∀ d : Finset.Icc 2 Dm, Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (v u : ι) (d : Finset.Icc 2 K) (γ : Constituent d.val ℝ ℝ) :
    DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2 :=
  field v u ⟨d.val, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ γ

omit [Fintype ι] [DecidableEq ι] in
theorem independentConstituentEdgeSlice_restrict (K : ℕ) (hKD : K ≤ Dm)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (field : ∀ _v _u : ι, ∀ d : Finset.Icc 2 Dm, Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ v u d, ∀ γ ∈ edge v u d, ∀ word,
      IndependentParameterSourceReserve H (field v u d γ word))
    (R : ∀ v u d, ∀ γ ∈ restrictConstituentEdges K hKD edge v u d, ∀ word,
      IndependentParameterSourceReserve T (restrictedIndependentEdgeField K hKD field v u d γ word))
    (L : Vec 2 →L[ℝ] P) (offset : P) :
    restrictConstituentEdges K hKD (independentConstituentEdgeSlice edge field Q L offset) =
      independentConstituentEdgeSlice (restrictConstituentEdges K hKD edge)
        (restrictedIndependentEdgeField K hKD field) R L offset := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem SlowOpenEdgeEq.restrictOrder {U : Set (Vec 2)} {t : ℝ}
    {edge other : ConstituentEdges Dm (fun _ : ι => ℝ)}
    (he : SlowOpenEdgeEq U t edge other) (K : ℕ) (hKD : K ≤ Dm) :
    SlowOpenEdgeEq U t (restrictConstituentEdges K hKD edge) (restrictConstituentEdges K hKD other) :=
  fun v u d => he v u ⟨d.val, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The actual outer source divergence preserves full independent family reserves. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def independentSourceComponentArray
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ) (j : ℕ) (v : ι) (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  ∑ k : Fin 2, independentCovariantCoefficientStep L A η k
    (fun i => independentSourceFluxComponentCoefficient edge a L A η f k i v) j t z Y

def independentSourceComponentArrayReserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve (H + 1) (a v u d γ α))
    (j : ℕ) (v : ι) :
    IndependentParameterSourceReserve H (independentSourceComponentArray edge a L A η f j v) :=
  IndependentParameterSourceReserve.fintypeSum H _ (fun k =>
    independentCovariantStepReserve H L hL A η _ k j (fun i =>
      independentSourceFluxComponentReserve (H + 1) edge a L hL A η f Qf Qa k i v))

omit [DecidableEq ι] in
theorem independent_source_component_affine_slice (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (offset : P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve (H + 1) (a v u d γ α))
    (j : ℕ) (v : ι) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ • sourceComponentCoefficientArray
      (independentConstituentEdgeSlice edge a Qa L offset) η t
      (fun X z => Real.exp (A X) • f t z (L X + offset)) j v X z =
      independentSourceComponentArray edge a L A η f j v t z (L X + offset) := by
  classical
  simp only [sourceComponentCoefficientArray, independentSourceComponentArray, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : (fun i => sourceFluxComponentCoefficient
      (independentConstituentEdgeSlice edge a Qa L offset) η t
      (fun X z => Real.exp (A X) • f t z (L X + offset)) k i v) =
      fun i X z => Real.exp (A X) •
        independentSourceFluxComponentCoefficient edge a L A η f k i v t z (L X + offset) := by
    funext i X z
    have hh := independent_source_flux_affine_slice edge a Qa L hL offset A η f Qf k i v t z X
    calc
      _ = Real.exp (A X) • ((Real.exp (A X))⁻¹ • _) := by
        rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
      _ = _ := by rw [hh]
  rw [he]
  exact independent_covariant_step_affine_slice _
    (fun i => independentSourceFluxComponentReserve (H + 1) edge a L hL A η f Qf Qa k i v)
    (by omega) L hL A η offset k j t z X

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Inherited finite edge sources preserve every stored phase translation. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] {D : ℕ}

theorem independentSourceFluxComponentCoefficient_translation_invariant
    (δ : P) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (ha : ∀ v u d γ, γ ∈ edge v u d → ∀ α,
      IndependentSourceTranslationInvariant δ (a v u d γ α))
    (hf : ∀ u, IndependentSourceTranslationInvariant δ (fun t z Y => f t z Y u))
    (k : Fin 2) (j : ℕ) (v : ι) :
    IndependentSourceTranslationInvariant δ (independentSourceFluxComponentCoefficient edge a L A η f k j v) := by
  classical
  intro t z Y
  dsimp only [independentSourceFluxComponentCoefficient]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hγ
  apply Finset.sum_congr rfl
  intro α hα
  rw [ha v u d γ hγ α t z Y,
    (hf u).covariantList L A η (List.ofFn α) j t z Y]

theorem independentSourceComponentArray_translation_invariant
    (δ : P) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (ha : ∀ v u d γ, γ ∈ edge v u d → ∀ α,
      IndependentSourceTranslationInvariant δ (a v u d γ α))
    (hf : ∀ u, IndependentSourceTranslationInvariant δ (fun t z Y => f t z Y u))
    (j : ℕ) (v : ι) :
    IndependentSourceTranslationInvariant δ (independentSourceComponentArray edge a L A η f j v) := by
  intro t z Y
  dsimp only [independentSourceComponentArray]
  apply Finset.sum_congr rfl
  intro k hk
  exact IndependentSourceTranslationInvariant.covariantStep _
    (fun i => independentSourceFluxComponentCoefficient_translation_invariant δ edge a L A η f ha hf k i v)
    L A η k j t z Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The ordered mean correction retains genuine independent derivatives and composed matrix grades. -/

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentLiftMeanCompositionSource (j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι) : ℝ → Vec 2 → Vec d → ℝ :=
  independentLiftApplySource j c L A (fun t Y u => fieldCellMean (fun z => F t z Y u)) v

def independentLiftMeanCompositionSourceReserve (H j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (QF : ∀ u, IndependentParameterSourceReserve (H + j) (fun t z Y => F t z Y u)) :
    IndependentParameterSourceReserve H (independentLiftMeanCompositionSource j c L A F v) :=
  independentLiftApplySourceReserve H j c L hL A _ v Qc (fun u => (QF u).mean)

theorem independentLiftMeanCompositionSourceReserve_matrix_budget (H j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (QF : ∀ u, IndependentParameterSourceReserve (H + j) (fun t z Y => F t z Y u))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (a b : ℕ) (w : ι)
    (B BF : ℝ) (hB : 0 ≤ B) (hBF : 0 ≤ BF)
    (hQc : ∀ m α u r, r ≤ H → (Qc m α u).budget r ≤ finiteMatrixPower M a v u * B)
    (hQF : ∀ u r, r ≤ H + j → (QF u).budget r ≤ finiteMatrixPower M b u w * BF)
    (r : ℕ) (hr : r ≤ H) :
    (independentLiftMeanCompositionSourceReserve H j c L hL A F v Qc QF).budget r ≤
      (liftApplyFiniteWordCount j : ℝ) *
        (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ r * B *
          ((1 + ‖A‖) ^ j * (((d : ℝ) + 1) ^ (H + j) * ((H + j + 1 : ℕ) * BF)))) *
        finiteMatrixPower M (a + b) v w := by
  unfold independentLiftMeanCompositionSourceReserve
  apply independentLiftApplySourceReserve_matrix_budget H j c L hL A _ M hM a b v w Qc _
    B (((d : ℝ) + 1) ^ (H + j) * ((H + j + 1 : ℕ) * BF)) hB
    (mul_nonneg (pow_nonneg (by positivity) _) (mul_nonneg (Nat.cast_nonneg _) hBF)) hQc
  · intro u s hs
    exact (QF u).mean_uniform_budget (finiteMatrixPower M b u w) BF (hQF u) s hs
  · exact hr

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Inherited finite edge sources preserve every stored phase translation. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D H : ℕ} {U : Set (Vec 2)}

omit [DecidableEq ι] in
theorem independentSourceFluxComponentCoefficient_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f g : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z W => f t z W u))
    (Qg : ∀ u, IndependentParameterSourceReserve (H + D) (fun t z W => g t z W u))
    (hU : IsOpen U)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn L U Y Z (a v u e γ α) (b v u e γ α))
    (hf : ∀ u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => f t z W u) (fun t z W => g t z W u))
    (k : Fin 2) (j : ℕ) (v : ι) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentSourceFluxComponentCoefficient edge a L A η f k j v)
      (independentSourceFluxComponentCoefficient edge b L A η g k j v) := by
  classical
  intro t X hX z
  dsimp only [independentSourceFluxComponentCoefficient]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hγ
  apply Finset.sum_congr rfl
  intro α _
  have hw : (List.ofFn α).length ≤ H + D := by
    simp only [List.length_ofFn]
    have hd := (Finset.mem_Icc.mp e.property).2
    omega
  rw [ha v u e γ hγ α t X hX z,
    independentCovariantListCoefficients_slow_slice_congr L hL Y Z A η
      (Qf u) (Qg u) hU (hf u) (List.ofFn α) hw j t X hX z]

theorem independentSourceComponentArray_slow_slice_congr
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a b : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f g : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z W => f t z W u))
    (Qg : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z W => g t z W u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u e γ α))
    (Qb : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + 1) (b v u e γ α))
    (hU : IsOpen U)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α,
      IndependentSourceSlowSliceEqOn L U Y Z (a v u e γ α) (b v u e γ α))
    (hf : ∀ u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => f t z W u) (fun t z W => g t z W u))
    (j : ℕ) (v : ι) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentSourceComponentArray edge a L A η f j v)
      (independentSourceComponentArray edge b L A η g j v) := by
  intro t X hX z
  dsimp only [independentSourceComponentArray]
  apply Finset.sum_congr rfl
  intro k _
  exact independentCovariantCoefficientStep_slow_slice_congr L Y Z A η _ _
    (fun i => independentSourceFluxComponentReserve (H + 1) edge a L hL A η f Qf Qa k i v)
    (fun i => independentSourceFluxComponentReserve (H + 1) edge b L hL A η g Qg Qb k i v)
    hU (fun i => independentSourceFluxComponentCoefficient_slow_slice_congr
      edge a b L hL Y Z A η f g Qf Qg hU ha hf k i v) k j t X hX z

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Ordered mean corrections inherit centering from their earlier scalar coefficients. -/

variable {d H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem independent_lift_mean_composition_mean_zero (j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (hmean : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u t Y,
      fieldCellMean (fun z => c m.val α t z Y v u) = 0) (t : ℝ) (Y : Vec d) :
    fieldCellMean (fun z => independentLiftMeanCompositionSource j c L A F v t z Y) = 0 :=
  independent_lift_apply_mean_zero j c L A _ v Qc hmean t Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Every inherited flux term retains its edge and incoming amplitudes on the independent parameter space. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : Type*}

def independentSourceFluxComponentTerm (η : ℝ) (A : Vec 2 →L[ℝ] ℝ)
    (L : Vec 2 →L[ℝ] P) (f : ℝ → Vec 2 → P → ι → ℝ) (u : ι) (d : ℕ)
    (e : ℝ → Vec 2 → P → Vec 2) (γ : Constituent d ℝ ℝ)
    (α : DerivativeWord2 (d - 1)) (k : Fin 2) (j : ℕ)
    (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  e t z Y k • γ.map (independentCovariantListCoefficients L A η (List.ofFn α)
    (fun t z Y => f t z Y u) j t z Y)

theorem independentSourceFluxTerm_uniform_reserve (H D d : ℕ) (hd : d ≤ D)
    (η : ℝ) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → Vec 2 → P → ι → ℝ) (u : ι)
    (Lslow : Vec 2 →L[ℝ] P) (hLslow : ‖Lslow‖ ≤ 1)
    (e : ℝ → Vec 2 → P → Vec 2) (γ : Constituent d ℝ ℝ) (α : DerivativeWord2 (d - 1)) (k : Fin 2) (j : ℕ)
    (Qe : IndependentParameterSourceReserve H e)
    (Qf : IndependentParameterSourceReserve (H + D) (fun t z Y => f t z Y u))
    (θ φ BE BF : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF)
    (hmap : ‖γ.map‖ ≤ 1)
    (he : ∀ r ≤ H, Qe.budget r ≤ θ * BE)
    (hf : ∀ r ≤ H + D, Qf.budget r ≤ φ * BF) :
    ∃ Q : IndependentParameterSourceReserve H (independentSourceFluxComponentTerm η A Lslow f u d e γ α k j),
      ∀ r ≤ H, Q.budget r ≤ (θ * φ) * normalizedSourceFluxTermBudget H D A η BE BF := by
  let C := sourceCovariantWordConstant A η
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg A)))
  let R := Qf.covariantList H Lslow hLslow A η (List.ofFn α)
    (by simp only [List.length_ofFn]; omega) j
  have hR (r : ℕ) (hr : r ≤ H) := Qf.covariantList_uniform_budget φ BF hφ hBF hf
    H Lslow hLslow A η (List.ofFn α) (by simp only [List.length_ofFn]; omega) j r hr
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hL : ‖L‖ ≤ 1 := cell_coordinate_projection_norm_le k
  have hqe (r : ℕ) (hr : r ≤ H) : (Qe.map L).budget r ≤ θ * BE := by
    change ‖L‖ * Qe.budget r ≤ θ * BE
    calc
      _ ≤ ‖L‖ * (θ * BE) := mul_le_mul_of_nonneg_left (he r hr) (norm_nonneg L)
      _ ≤ 1 * (θ * BE) := mul_le_mul_of_nonneg_right hL (mul_nonneg hθ hBE)
      _ = _ := one_mul _
  have hqr (r : ℕ) (hr : r ≤ H) : (R.map γ.map).budget r ≤ φ * (C ^ D * BF) := by
    have hb := hR r hr
    change R.budget r ≤ φ * (C ^ (List.ofFn α).length * BF) at hb
    have hp : C ^ (List.ofFn α).length ≤ C ^ D :=
      pow_le_pow_right₀ hC (by simp only [List.length_ofFn]; omega)
    change ‖γ.map‖ * R.budget r ≤ _
    calc
      _ ≤ 1 * R.budget r := mul_le_mul_of_nonneg_right hmap (R.budget_nonneg r)
      _ = R.budget r := one_mul _
      _ ≤ φ * (C ^ (List.ofFn α).length * BF) := hb
      _ ≤ φ * (C ^ D * BF) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp hBF) hφ
  refine ⟨(Qe.map L).scalarProduct (R.map γ.map), ?_⟩
  intro r hr
  exact (Qe.map L).bilinear_uniform_budget (R.map γ.map) (ContinuousLinearMap.lsmul ℝ ℝ)
    θ φ BE (C ^ D * BF) hθ hφ hBE
    (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) hBF) hqe hqr r hr

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The ordered lift forcing is produced from lower cell degrees and the preceding source grade. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def independentLiftASource
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ) (hh n : ℕ) (out : ι)
    (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  independentNormalizedCellB1Source L A η G v (fun t z Y => F hh (n - 1) t z Y out) t z Y +
    (if 2 ≤ n then independentNormalizedCellB2Source L A η G
      (fun t z Y => F hh (n - 2) t z Y out) t z Y else 0) -
    (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      independentSourceComponentArray edge a L A η (F (hh - 1) (n - j)) j out t z Y)

def independentLiftASourceReserve (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ) (hh n : ℕ) (out : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Q1 : IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 1) t z Y out))
    (Q2 : 2 ≤ n → IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 2) t z Y out))
    (Qprev : hh ≠ 0 → ∀ j ∈ Finset.range (min D n + 1), ∀ u,
      IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => F (hh - 1) (n - j) t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α)) :
    IndependentParameterSourceReserve H (independentLiftASource edge a L A η G v F hh n out) := by
  let B2 := fun t z Y => if 2 ≤ n then independentNormalizedCellB2Source L A η G
    (fun t z Y => F hh (n - 2) t z Y out) t z Y else 0
  have QB2 : IndependentParameterSourceReserve H B2 := by
    by_cases hn : 2 ≤ n
    · exact (independentNormalizedCellB2SourceReserve H L hL A η G _ QG (Q2 hn)).congrSource
        (by funext t z Y; exact (ite_eq_left hn).symm)
    · exact (IndependentParameterSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_right hn).symm)
  let S := fun t z Y => if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
    independentSourceComponentArray edge a L A η (F (hh - 1) (n - j)) j out t z Y
  have QS : IndependentParameterSourceReserve H S := by
    by_cases hhh : hh = 0
    · exact (IndependentParameterSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_left hhh).symm)
    · exact (IndependentParameterSourceReserve.finsetSum _ H _ (fun j hj =>
        independentSourceComponentArrayReserve H edge a L hL A η _ (Qprev hhh j hj) Qa j out)).congrSource
        (by funext t z Y; exact (ite_eq_right hhh).symm)
  let T : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  exact (((independentNormalizedCellB1SourceReserve H L hL A η G v _ QG Qv Q1).add QB2).add
    (QS.map T)).congrSource (by funext t z Y; simp only [independentLiftASource,
      T, neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]; rfl)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Full independent productions give native slow germs for fixed stored family parameters. -/

variable {d H n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem independent_stored_production_family_native_copy
    (a b C : ℝ) (U : Set (Vec (2 + d)))
    (c : Vec d → LiftCoeff ι (fun _ => ℝ)) (M : ι → ι → ℝ)
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction (2 + d) H n a b U
        (fun Y => c (independentStoredParameterProjection d Y))
        (independentIntrinsicSlowProjection d) m α v u (M v u) C)
    (m : ℕ) (hm : m ≤ n)
    (hs : ∀ Y β (σ : Equiv.Perm (Fin m)), c Y m (β ∘ σ) = c Y m β)
    (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc a b)
    (Y : Vec (2 + d)) (X z : Vec 2)
    (hX : independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y ∈ U)
    (v u : ι) :
    independentScalarCoefficientSlice (independentCoefficientProductionFields P)
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y) m α t X z v u =
      c (independentStoredParameterProjection d Y) m α t X z v u := by
  have he := independentCoefficientProductionFields_copy P m hm (fun Y => hs _) α t ht
    (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) hX z v u
  rw [independentStoredParameterProjection_slice, independentIntrinsicSlowProjection_slice] at he
  apply ContinuousLinearMap.ext
  intro ξ
  have hr := (c (independentStoredParameterProjection d Y) m α t X z v u).map_smul ξ 1
  simp only [smul_eq_mul, mul_one] at hr
  simp only [independentScalarCoefficientSlice, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [he, hr]
  exact mul_comm _ _

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Independent source production identifies the paper's literal inherited source coefficients. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D H : ℕ}

def independent_edge_slice_source_reserve
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve H (a v u d γ α))
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (offset : P)
    (v u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val ℝ ℝ)
    (hγ : γ ∈ independentConstituentEdgeSlice edge a Qa L offset v u d)
    (α : DerivativeWord2 (d.val - 1)) :
    JointSourceReserve H (fun t z Y => γ.coeff α t Y z) := by
  classical
  apply Classical.choice
  obtain ⟨δ, hδ, he⟩ := List.mem_map.mp hγ
  subst γ
  have hf : (fun t z Y => a v u d δ α t z (L Y + offset)) =
      fun t z Y => (if _h : δ ∈ edge v u d then a v u d δ α t z (L Y + offset) else 0) := by
    funext t z Y
    rw [dite_eq_left hδ]
  exact ⟨((Qa v u d δ hδ α).affineSlice L hL offset).congrSource hf⟩

theorem independent_source_coeff_affine_slice (H : ℕ) (hH : 1 ≤ H)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (offset : P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (f : ℝ → Vec 2 → P → ι → ℝ)
    (Qf : ∀ u, IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => f t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IndependentParameterSourceReserve (H + 1) (a v u d γ α))
    (j : ℕ) (hj : j ≤ D) (v : ι) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ • sourceCoeff
      (independentConstituentEdgeSlice edge a Qa L offset) η j t
      (fun X z => Real.exp (A X) • f t z (L X + offset)) X z v =
      independentSourceComponentArray edge a L A η f j v t z (L X + offset) := by
  let es := independentConstituentEdgeSlice edge a Qa L offset
  let Qs := fun u => (Qf u).affineSlice L hL offset
  let Qwhole := jointSourcePiReserve (H + 1 + D)
    (fun u t z Y => f t z (L Y + offset) u) Qs
  let Qe := fun v u d γ hγ α => independent_edge_slice_source_reserve edge a Qa L hL offset v u d γ hγ α
  have he : (fun Y z => sourceCoeff es η j t
      (fun X z => Real.exp (A X) • f t z (L X + offset)) Y z v) =
      sourceComponentCoefficientArray es η t
        (fun X z => Real.exp (A X) • f t z (L X + offset)) j v := by
    rw [sourceCoeff_eq_sourceCoefficientArray es hD η t _
      ((Qwhole.exponentialGoodField A t).mono (by omega))
      (fun v u d γ hγ α => ((Qe v u d γ hγ α).goodField t).mono (by omega))]
    apply sourceCoefficientArray_component_eq es hD η t _ j hj
    · intro v u d γ hγ α
      apply Weighted.isBoxSmooth_of_joint_contDiff
      exact (((Qe v u d γ hγ α).goodField t).mono (by omega : 1 + 1 ≤ H + 1)).1
    · apply Weighted.isBoxSmooth_of_joint_contDiff
      exact ((Qwhole.exponentialGoodField A t).mono
        (by omega : j + (D - j) ≤ H + 1 + D)).1
  rw [congrFun (congrFun he X) z]
  exact independent_source_component_affine_slice H edge a L hL offset A η f Qf Qa j v t z X

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent source data identify the produced higher readout with each actual local inverse. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.spacetime_memLp {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (a b : ℝ) (Y : P) :
    MemLp (Function.uncurry (fun t z => f t z Y)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  let _ : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simp only [Measure.restrict_apply_univ, weak_unitCube_volume]; exact ENNReal.one_lt_top⟩
  apply MemLp.of_bound (Q.measurable Y).aestronglyMeasurable (Q.budget 0)
  exact Filter.Eventually.of_forall fun X => by
    simpa only [norm_iteratedFDeriv_zero] using Q.derivative_bound 0 (Nat.zero_le H) X.1 (X.2, Y)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independent_actual_inverse_higher_readout_eq_functional [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a ≤ b) {H : ℕ} (g : ℝ → Vec 2 → P → E) (ℓ : E →L[ℝ] ℝ)
    (Q : IndependentParameterSourceReserve H (fun t z Y => ℓ (g t z Y)))
    (Y : P) (hmean : ∀ t, fieldCellMean (fun z => ℓ (g t z Y)) = 0)
    (M : MolecularData) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue (dataCoefficients M)
      (fun t => cellQ0 (fun z => (ℓ (g t z Y) : ℂ))) 0 D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (sZ : ℕ) (c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse M.G M.v sZ a b 0 (fun t z => g t z Y) c)
    (K : ℕ) (hK : 2 ≤ K) (u : ℝ → TorusHk K ℂ)
    (hu : ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    ∀ t ∈ Icc a b, realClassicalLift K (mapTorusHk Complex.reCLM (u t)) = fun z => ℓ (c t z) := by
  have hs : ∀ t, cellQ0 (fun z => (ℓ (g t z Y) : ℂ)) = fun z => (ℓ (g t z Y) : ℂ) := by
    intro t
    exact cellQ0_eq_self_of_mean_zero _ (realCellMean_zero _ (hmean t))
  have hg := (Q.map Complex.ofRealCLM).spacetime_memLp a b Y
  have he := dataActual_inverse_canonical_eq_functional hab M _ D hD.1
    (fun t z => g t z Y) c ℓ
    (Filter.Eventually.of_forall fun t => Filter.EventuallyEq.of_eq (hs t)) hg hi sZ hc K hK u hu
  intro t ht
  rw [← realCellRawReadout_high_eq K (u t) D t (hD.1.2.2.1 t (mem_univ _)).1 (hu t ht)]
  exact he t ht

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem realHigherCarrier_zero_of_value_zero (K : ℕ)
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ) (u : TorusHk K ℂ)
    (hm : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hz : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    realClassicalLift K (mapTorusHk Complex.reCLM u) = 0 := by
  have he : cellRawTrace D t = 0 := Lp.ext
    (((cellRawTrace_ae D t hm).trans hz).trans (Lp.coeFn_zero ℂ 2
      (volume.restrict AVenhance.unitCube)).symm)
  rw [← realCellRawReadout_high_eq K u D t hm hu, he, realCellClassicalReadout_zero]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Relative shear retains every independent family coordinate with a norm-one projection. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_retained_shear_positive_jets (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u t : ℝ)
    (hsmall : |u - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (X : P × (Vec 2 × Vec 2)) :
    ‖iteratedFDeriv ℝ n (fun Y : P × (Vec 2 × Vec 2) =>
      (Y.1, Y.2.2 + D.relDisp m slot u t (Y.2.1 + Y.2.2))) X‖ ≤
      max 1 (weakTransferJointShearCost K) := by
  let S := fun Z : Vec 2 × Vec 2 => Z.2 + D.relDisp m slot u t (Z.1 + Z.2)
  let L : (P × (Vec 2 × Vec 2)) →L[ℝ] (Vec 2 × Vec 2) :=
    ContinuousLinearMap.snd ℝ P (Vec 2 × Vec 2)
  let Q : (P × (Vec 2 × Vec 2)) →L[ℝ] P :=
    ContinuousLinearMap.fst ℝ P (Vec 2 × Vec 2)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.2‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_snd_le Y
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.1‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_fst_le Y
  have hS : ContDiff ℝ (⊤ : ℕ∞) S :=
    contDiff_snd.add ((relDisp_spatial_smooth D m slot u t).comp
      (contDiff_fst.add contDiff_snd))
  have hs : ‖iteratedFDeriv ℝ n (S ∘ L) X‖ ≤ weakTransferJointShearCost K := by
    have hh := finite_affine_derivative_norm_le S n (hS.of_le (by simp)) L hL 0 X
    simp only [add_zero] at hh
    exact hh.trans (weak_transfer_joint_shear_positive_jets D hΛ hζ m slot hp u t
      hsmall K n hn hnK (L X))
  exact (independent_joint_pair_jet_bound Q (S ∘ L) n Q.contDiff
    ((hS.comp L.contDiff).of_le (by simp)) X).trans
    (max_le_max ((linear_positive_derivative_norm_le Q n hn X).trans hQ) hs)
end

/-! Full family transfer jets consume centered chart jets at the actual shear sampling point. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredTransfer (F : P × Vec 2 → Vec 2) (D : OCData)
    (m : ℕ) (slot : ℤ) (u t : ℝ) (Y : P × (Vec 2 × Vec 2)) : Vec 2 :=
  F (Y.1, Y.2.2 + D.relDisp m slot u t (Y.2.1 + Y.2.2))

theorem independentCenteredTransfer_contDiff (F : P × Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (D : OCData) (m : ℕ) (slot : ℤ) (u t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredTransfer F D m slot u t) := by
  exact hF.comp (contDiff_fst.prodMk
    ((contDiff_snd.comp contDiff_snd).add ((relDisp_spatial_smooth D m slot u t).comp
      ((contDiff_fst.comp contDiff_snd).add (contDiff_snd.comp contDiff_snd)))))

theorem independentCenteredTransfer_positive_jets (F : P × Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u t : ℝ)
    (hsmall : |u - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (B : ℝ) (hB : 1 ≤ B)
    (X : P × (Vec 2 × Vec 2))
    (hparent : ∀ a, 1 ≤ a → a ≤ K →
      ‖iteratedFDeriv ℝ a F
        (X.1, X.2.2 + D.relDisp m slot u t (X.2.1 + X.2.2))‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (independentCenteredTransfer F D m slot u t) X‖ ≤
      positiveJetCompositionBudget K (max B (weakTransferJointShearCost K)) := by
  let S := fun Y : P × (Vec 2 × Vec 2) =>
    (Y.1, Y.2.2 + D.relDisp m slot u t (Y.2.1 + Y.2.2))
  have hS : ContDiff ℝ (⊤ : ℕ∞) S :=
    contDiff_fst.prodMk ((contDiff_snd.comp contDiff_snd).add
      ((relDisp_spatial_smooth D m slot u t).comp
        ((contDiff_fst.comp contDiff_snd).add (contDiff_snd.comp contDiff_snd))))
  change ‖iteratedFDeriv ℝ n (F ∘ S) X‖ ≤ _
  exact finite_positive_jet_composition_bound F S hF hS K n hn hnK X
    (max B (weakTransferJointShearCost K)) (hB.trans (le_max_left _ _))
    (fun a ha haK => (hparent a ha haK).trans (le_max_left _ _))
    (fun a ha haK => (independent_retained_shear_positive_jets D hΛ hζ m slot hp u t
      hsmall K a ha haK X).trans (max_le
        (hB.trans (le_max_left _ _)) (le_max_right _ _)))
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Constructed independent inverse readouts depend only on their metric and forcing. -/

theorem independent_inverse_higher_readout_eq_of_data_eq
    {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f f' : ℝ → Vec 2 → ℂ) (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ f F D)
    (hD' : IsCellInverseValue ⟨G', v, 0, 0⟩ f' F' D')
    (hg : G = G') (hf : f = f') (hF : F = F')
    (K : ℕ) (t : ℝ) (u u' : TorusHk K ℂ)
    (hu : torusHkValueCLM u =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hu' : torusHkValueCLM u' =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t) :
    realClassicalLift K (mapTorusHk Complex.reCLM u) =
      realClassicalLift K (mapTorusHk Complex.reCLM u') := by
  subst G'
  subst f'
  subst F'
  have he := cellAllTimeInverse_unique_arbitrary_source hG hv f F D D' hD hD' t
  have hm := (hD.1.2.2.1 t (mem_univ _)).1
  have hm' := (hD'.1.2.2.1 t (mem_univ _)).1
  have ht : cellRawTrace D t = cellRawTrace D' t := Lp.ext
    ((cellRawTrace_ae D t hm).trans (he.trans (cellRawTrace_ae D' t hm').symm))
  rw [← realCellRawReadout_high_eq K u D t hm hu,
    ← realCellRawReadout_high_eq K u' D' t hm' hu', ht]

end AVRegularity.EntryWeakProofs
end

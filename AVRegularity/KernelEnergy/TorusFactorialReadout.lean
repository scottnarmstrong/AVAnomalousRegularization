-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
public import AVRegularity.KernelEnergy.PlaneFluxTerm
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizer
public import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Time-integrated flux pairings preserve subtraction of time L² sources. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusFluxPairing_integral_sub {k : ℕ} {a b t : ℝ} (hab : a ≤ b)
    (hat : a ≤ t) (htb : t ≤ b)
    (F Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Set.Icc a b))) (φ : TorusHk 1 E) :
    (∫ r in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (F r - Q r) x) (torusH1GradientL2CLM (E := E) φ x)) =
    (∫ r in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (F r) x) (torusH1GradientL2CLM (E := E) φ x)) -
    ∫ r in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (Q r) x) (torusH1GradientL2CLM (E := E) φ x) := by
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl htb
  have hFi := ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (torusFluxSource_test_integrable k a b F hF φ)).mono_set hsub
  have hQi := ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (torusFluxSource_test_integrable k a b Q hQ φ)).mono_set hsub
  have hpoint (r : ℝ) :
      (∫ x in AVenhance.unitCube, inner ℝ (Galerkin.torusHkValueCLM (F r - Q r) x)
        (torusH1GradientL2CLM (E := E) φ x)) =
      (∫ x in AVenhance.unitCube, inner ℝ (Galerkin.torusHkValueCLM (F r) x)
        (torusH1GradientL2CLM (E := E) φ x)) -
      ∫ x in AVenhance.unitCube, inner ℝ (Galerkin.torusHkValueCLM (Q r) x)
        (torusH1GradientL2CLM (E := E) φ x) := by
    simp only [← L2.inner_def, map_sub, inner_sub_left]
  simp_rw [hpoint]
  exact intervalIntegral.integral_sub hFi hQi

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

private theorem truncateValueIndex2 {m n : ℕ} (hmn : m ≤ n) :
    truncateJetIndex hmn (valueIndex2 m) = valueIndex2 n := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · rfl

theorem planeRegularizerLift {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G]
    [BorelSpace G] [CompleteSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H]
    [BorelSpace H] [CompleteSpace H] (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (t₀ t₁ t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      (Lp G 2 (volume.restrict (Set.univ : Set (Vec 2)))))
    (hS : IsSpatialRegularizer ρ k D t₀ t₁ c r S)
    (V : PlaneHk Set.univ (k + 1) H) :
    ∃ Y : PlaneHk Set.univ (k + (D - 2) + 1) G,
      Y.val (valueIndex2 (k + (D - 2) + 1)) =
        S t ((C.compLpL 2 (volume.restrict Set.univ)) (V.val (valueIndex2 (k + 1)))) ∧
      ∀ q : Fin 2, ∀ m : ℕ, (hm : m + 2 ≤ D) →
        ∃ Z : PlaneHk Set.univ (k + m) G,
          Z.val (valueIndex2 (k + m)) =
            S t ((C.compLpL 2 (volume.restrict Set.univ))
              ((derivativePlaneHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
                (valueIndex2 k))) ∧
          derivFactorialNormSq m ρ Z.val ≤
            (c m / r ^ m) ^ 2 * factorialNormSq ρ
              ((mapPlaneHk C (derivativePlaneHk (K := k) (r := 1)
                (fun _ : Fin 1 => q) V)).val) ∧
          truncatePlaneHk (by omega : k + m ≤ k + (D - 2))
            (derivativePlaneHk (K := k + (D - 2)) (r := 1)
              (fun _ : Fin 1 => q) Y) = Z := by
  classical
  let kHi : ℕ := k + (D - 2)
  have htr : 1 ≤ k + 1 := by omega
  let baseInput : PlaneHk Set.univ 1 G :=
    mapPlaneHk C (truncatePlaneHk htr V)
  have hbaseValue : baseInput.val (valueIndex2 1) =
      (C.compLpL 2 (volume.restrict Set.univ)) (V.val (valueIndex2 (k + 1))) := by
    rw [mapPlaneHk_jet_eq_compLp]
    have hidx : truncateJetIndex htr (valueIndex2 1) = valueIndex2 (k + 1) :=
      truncateValueIndex2 htr
    rw [truncatePlaneHk_apply, hidx]
  let gradInput : Fin 2 → PlaneHk Set.univ k G := fun q =>
    mapPlaneHk C (derivativePlaneHk (K := k) (r := 1) (fun _ : Fin 1 => q) V)
  have hsource : ∀ q : Fin 2,
      baseInput.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ =
        (gradInput q).val (valueIndex2 k) := by
    intro q
    rw [mapPlaneHk_jet_eq_compLp, mapPlaneHk_jet_eq_compLp]
    apply congrArg (fun z => (C.compLpL 2 (volume.restrict Set.univ)) z)
    apply Lp.ext
    have hidx : truncateJetIndex htr
        (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => q⟩ : JetIndex2 1) =
        prefixJetIndex (fun _ : Fin 1 => q) (valueIndex2 k) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      ·
        change (fun _ : Fin 1 => q) ≍ Fin.append (fun _ : Fin 1 => q) Fin.elim0
        have hword : Fin.append (fun _ : Fin 1 => q) Fin.elim0 =
            (fun _ : Fin 1 => q) := by
          funext j
          fin_cases j
          rfl
        rw [hword]
    rw [truncatePlaneHk_apply, derivativePlaneHk_apply, hidx]
  obtain ⟨base, hbaseS, hbaseGrad⟩ := hS.2.1 t ht baseInput
  have hmax : (D - 2) + 2 ≤ D := by omega
  have hmaxGain : ∀ q : Fin 2, ∃ g : PlaneHk Set.univ (k + (D - 2)) G,
      g.val (valueIndex2 (k + (D - 2))) = S t ((gradInput q).val (valueIndex2 k)) ∧
      derivFactorialNormSq (D - 2) ρ g.val ≤
        (c (D - 2) / r ^ (D - 2)) ^ 2 * factorialNormSq ρ (gradInput q).val := by
    intro q
    exact hS.2.2.2 t ht (D - 2) hmax (gradInput q)
  choose g hgValue hgNorm using hmaxGain
  have hgradClass : ∀ q : Fin 2,
      base.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ =
        (g q).val (valueIndex2 (k + (D - 2))) := by
    intro q
    calc
      base.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ = S t
          (baseInput.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩) := hbaseGrad q
      _ = S t ((gradInput q).val (valueIndex2 k)) := congrArg (S t) (hsource q)
      _ = (g q).val (valueIndex2 (k + (D - 2))) := (hgValue q).symm
  have hgrad : ∀ q : Fin 2,
      base.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ =ᵐ[volume.restrict Set.univ]
        (g q).toFunction.jet (valueIndex2 (k + (D - 2))) := by
    intro q
    change (fun x => base.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x) =ᵐ[
      volume.restrict Set.univ] fun x => (g q).val (valueIndex2 (k + (D - 2))) x
    exact Lp.ext_iff.mp (hgradClass q)
  obtain ⟨Y, hYbase, hYgrad⟩ :=
    exists_planeHk_succ_of_gradient_eq base g hgrad
  refine ⟨Y, ?_, ?_⟩
  · calc
      Y.val (valueIndex2 ((k + (D - 2)) + 1)) = base.val (valueIndex2 1) := hYbase
      _ = S t (baseInput.val (valueIndex2 1)) := hbaseS
      _ = S t ((C.compLpL 2 (volume.restrict Set.univ))
          (V.val (valueIndex2 (k + 1)))) := congrArg (S t) hbaseValue
  · intro q m hm
    have hm' : m ≤ D - 2 := by omega
    let kLow : ℕ := k + m
    have hLow : kLow ≤ kHi := by dsimp [kLow, kHi]; omega
    obtain ⟨Z, hZ, hZnorm⟩ := hS.2.2.2 t ht m hm (gradInput q)
    have hgradInputValue : (gradInput q).val (valueIndex2 k) =
        (C.compLpL 2 (volume.restrict Set.univ))
          ((derivativePlaneHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
            (valueIndex2 k)) := by
      exact mapPlaneHk_jet_eq_compLp C _ _
    have hZ' : Z.val (valueIndex2 (k + m)) = S t
        ((C.compLpL 2 (volume.restrict Set.univ))
          ((derivativePlaneHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
            (valueIndex2 k))) := hZ.trans (congrArg (S t) hgradInputValue)
    let gLow : PlaneHk Set.univ kLow G := truncatePlaneHk hLow (g q)
    have hidxLow : truncateJetIndex hLow (valueIndex2 kLow) =
        valueIndex2 kHi := truncateValueIndex2 hLow
    have hgLow : gLow.val (valueIndex2 kLow) =
        S t ((gradInput q).val (valueIndex2 k)) := by
      change (g q).val (truncateJetIndex hLow (valueIndex2 kLow)) = _
      rw [hidxLow]
      exact hgValue q
    have hsame : gLow = Z := PlaneHk.ext_value isOpen_univ (hgLow.trans hZ.symm)
    have hgradTrunc :
        truncatePlaneHk hLow (derivativePlaneHk (K := kHi) (r := 1)
          (fun _ : Fin 1 => q) Y) = Z := by
      calc
        _ = gLow := congrArg (truncatePlaneHk hLow) (hYgrad q)
        _ = Z := hsame
    have hZnorm' : derivFactorialNormSq m ρ Z.val ≤
        (c m / r ^ m) ^ 2 * factorialNormSq ρ (gradInput q).val := by
      simpa [gradInput] using hZnorm
    exact ⟨Z, hZ', hZnorm', hgradTrunc⟩

private theorem truncateValueIndex2Torus {m n : ℕ} (hmn : m ≤ n) :
    truncateJetIndex hmn (valueIndex2 m) = valueIndex2 n := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · rfl

theorem torusRegularizerLift {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G]
    [BorelSpace G] [CompleteSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H]
    [BorelSpace H] [CompleteSpace H] (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (t₀ t₁ t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp G 2 (volume.restrict AVenhance.unitCube)))
    (hS : IsSpatialRegularizerTorus ρ k D t₀ t₁ c r S)
    (V : TorusHk (k + 1) H) :
    ∃ Y : TorusHk (k + (D - 2) + 1) G,
      Y.val (valueIndex2 (k + (D - 2) + 1)) =
        S t ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
          (V.val (valueIndex2 (k + 1)))) ∧
      ∀ q : Fin 2, ∀ m : ℕ, (hm : m + 2 ≤ D) →
        ∃ Z : TorusHk (k + m) G,
          Z.val (valueIndex2 (k + m)) =
            S t ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
              ((derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
                (valueIndex2 k))) ∧
          derivFactorialNormSq m ρ Z.val ≤
            (c m / r ^ m) ^ 2 * factorialNormSq ρ
              ((mapTorusHk C (derivativeTorusHk (K := k) (r := 1)
                (fun _ : Fin 1 => q) V)).val) ∧
          truncateTorusHk (by omega : k + m ≤ k + (D - 2))
            (derivativeTorusHk (K := k + (D - 2)) (r := 1)
              (fun _ : Fin 1 => q) Y) = Z := by
  classical
  let kHi : ℕ := k + (D - 2)
  have htr : 1 ≤ k + 1 := by omega
  let baseInput : TorusHk 1 G :=
    mapTorusHk C (truncateTorusHk htr V)
  have hbaseValue : baseInput.val (valueIndex2 1) =
      (C.compLpL 2 (volume.restrict AVenhance.unitCube))
        (V.val (valueIndex2 (k + 1))) := by
    rw [mapTorusHk_jet_eq_compLp]
    have hidx : truncateJetIndex htr (valueIndex2 1) = valueIndex2 (k + 1) :=
      truncateValueIndex2Torus htr
    rw [truncateTorusHk_apply, hidx]
  let gradInput : Fin 2 → TorusHk k G := fun q =>
    mapTorusHk C (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) V)
  have hsource : ∀ q : Fin 2,
      baseInput.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ =
        (gradInput q).val (valueIndex2 k) := by
    intro q
    rw [mapTorusHk_jet_eq_compLp, mapTorusHk_jet_eq_compLp]
    apply congrArg (fun z => (C.compLpL 2
      (volume.restrict AVenhance.unitCube)) z)
    have hidx : truncateJetIndex htr
        (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => q⟩ : JetIndex2 1) =
        prefixJetIndex (fun _ : Fin 1 => q) (valueIndex2 k) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      ·
        change (fun _ : Fin 1 => q) ≍ Fin.append (fun _ : Fin 1 => q) Fin.elim0
        have hword : Fin.append (fun _ : Fin 1 => q) Fin.elim0 =
            (fun _ : Fin 1 => q) := by
          funext j
          fin_cases j
          rfl
        rw [hword]
    rw [truncateTorusHk_apply, derivativeTorusHk_apply, hidx]
  obtain ⟨base, hbaseS, hbaseGrad⟩ := hS.2.1 t ht baseInput
  have hmax : (D - 2) + 2 ≤ D := by omega
  have hmaxGain : ∀ q : Fin 2, ∃ g : TorusHk (k + (D - 2)) G,
      g.val (valueIndex2 (k + (D - 2))) = S t ((gradInput q).val (valueIndex2 k)) ∧
      derivFactorialNormSq (D - 2) ρ g.val ≤
        (c (D - 2) / r ^ (D - 2)) ^ 2 * factorialNormSq ρ (gradInput q).val := by
    intro q
    exact hS.2.2.2 t ht (D - 2) hmax (gradInput q)
  choose g hgValue hgNorm using hmaxGain
  have hgradClass : ∀ q : Fin 2,
      base.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ =
        (g q).val (valueIndex2 (k + (D - 2))) := by
    intro q
    calc
      base.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ = S t
          (baseInput.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩) := hbaseGrad q
      _ = S t ((gradInput q).val (valueIndex2 k)) := congrArg (S t) (hsource q)
      _ = (g q).val (valueIndex2 (k + (D - 2))) := (hgValue q).symm
  obtain ⟨Y, hYbase, hYgrad⟩ :=
    exists_torusHk_succ_of_gradient_eq base g hgradClass
  refine ⟨Y, ?_, ?_⟩
  · calc
      Y.val (valueIndex2 (k + (D - 2) + 1)) = base.val (valueIndex2 1) := hYbase
      _ = S t (baseInput.val (valueIndex2 1)) := hbaseS
      _ = S t ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
          (V.val (valueIndex2 (k + 1)))) := congrArg (S t) hbaseValue
  · intro q m hm
    let kLow : ℕ := k + m
    have hLow : kLow ≤ kHi := by dsimp [kLow, kHi]; omega
    obtain ⟨Z, hZ, hZnorm⟩ := hS.2.2.2 t ht m hm (gradInput q)
    have hgradInputValue : (gradInput q).val (valueIndex2 k) =
        (C.compLpL 2 (volume.restrict AVenhance.unitCube))
          ((derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
            (valueIndex2 k)) := by
      exact mapTorusHk_jet_eq_compLp C _ _
    have hZ' : Z.val (valueIndex2 (k + m)) = S t
        ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
          ((derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) V).val
            (valueIndex2 k))) := hZ.trans (congrArg (S t) hgradInputValue)
    let gLow : TorusHk kLow G := truncateTorusHk hLow (g q)
    have hidxLow : truncateJetIndex hLow (valueIndex2 kLow) =
        valueIndex2 kHi := truncateValueIndex2Torus hLow
    have hgLow : gLow.val (valueIndex2 kLow) =
        S t ((gradInput q).val (valueIndex2 k)) := by
      change (g q).val (truncateJetIndex hLow (valueIndex2 kLow)) = _
      rw [hidxLow]
      exact hgValue q
    have hsame : gLow = Z := TorusHk.ext_value (hgLow.trans hZ.symm)
    have hgradTrunc :
        truncateTorusHk hLow (derivativeTorusHk (K := kHi) (r := 1)
          (fun _ : Fin 1 => q) Y) = Z := by
      calc
        _ = gLow := congrArg (truncateTorusHk hLow) (hYgrad q)
        _ = Z := hsame
    have hZnorm' : derivFactorialNormSq m ρ Z.val ≤
        (c m / r ^ m) ^ 2 * factorialNormSq ρ (gradInput q).val := by
      simpa [gradInput] using hZnorm
    exact ⟨Z, hZ', hZnorm', hgradTrunc⟩

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
    Lp G 2 (volume.restrict AVenhance.unitCube))
  (hS : IsSpatialRegularizerTorus ρ k D a b c r S)

include hD hS in
theorem torusRegularizedInput_exists (t : ℝ) (ht : t ∈ Set.Icc a b) (V : TorusHk (k + 1) H) :
    ∃ Y : TorusHk (k + D - 1) G,
      Y.val (valueIndex2 (k + D - 1)) =
        S t (C.compLp (V.val (valueIndex2 (k + 1)))) := by
  obtain ⟨Y, hY, _⟩ := torusRegularizerLift ρ k D hD a b t ht c r C S hS V
  have he : k + (D - 2) + 1 = k + D - 1 := by omega
  refine ⟨castTorusHk he Y, ?_⟩
  rw [castTorusHk_valueIndex]
  exact hY

def torusRegularizedInput (t : ℝ) (ht : t ∈ Set.Icc a b) (V : TorusHk (k + 1) H) :
    TorusHk (k + D - 1) G :=
  Classical.choose (torusRegularizedInput_exists ρ k D hD a b c r C S hS t ht V)

theorem torusRegularizedInput_value (t : ℝ) (ht : t ∈ Set.Icc a b) (V : TorusHk (k + 1) H) :
    (torusRegularizedInput ρ k D hD a b c r C S hS t ht V).val (valueIndex2 (k + D - 1)) =
      S t (C.compLp (V.val (valueIndex2 (k + 1)))) :=
  Classical.choose_spec (torusRegularizedInput_exists ρ k D hD a b c r C S hS t ht V)

def torusRegularizedInputLinearMap (t : ℝ) (ht : t ∈ Set.Icc a b) :
    TorusHk (k + 1) H →ₗ[ℝ] TorusHk (k + D - 1) G where
  toFun := torusRegularizedInput ρ k D hD a b c r C S hS t ht
  map_add' U V := by
    apply TorusHk.ext_value
    rw [torusRegularizedInput_value]
    change S t ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
      (U.val (valueIndex2 (k + 1)) + V.val (valueIndex2 (k + 1)))) = _
    rw [(C.compLpL 2 (volume.restrict AVenhance.unitCube)).map_add, (S t).map_add]
    change _ = (torusRegularizedInput ρ k D hD a b c r C S hS t ht U).val
        (valueIndex2 (k + D - 1)) +
      (torusRegularizedInput ρ k D hD a b c r C S hS t ht V).val (valueIndex2 (k + D - 1))
    rw [torusRegularizedInput_value, torusRegularizedInput_value]
    rfl
  map_smul' q U := by
    apply TorusHk.ext_value
    rw [torusRegularizedInput_value]
    change S t ((C.compLpL 2 (volume.restrict AVenhance.unitCube))
      (q • U.val (valueIndex2 (k + 1)))) = _
    rw [(C.compLpL 2 (volume.restrict AVenhance.unitCube)).map_smul, (S t).map_smul]
    change _ = q • (torusRegularizedInput ρ k D hD a b c r C S hS t ht U).val
      (valueIndex2 (k + D - 1))
    rw [torusRegularizedInput_value]
    rfl
end

/-! Retain every regularizer gain to control the complete higher lifted carrier. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

theorem torusRegularizer_exists_shifted_bounds (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → Lp G 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S) (V : TorusHk (k + 1) H) :
    ∃ Y : TorusHk (k + (D - 2) + 1) G,
      Y.val (valueIndex2 (k + (D - 2) + 1)) =
        S t (C.compLp (V.val (valueIndex2 (k + 1)))) ∧
      ∀ m : ℕ, ∀ hm : m ≤ D - 2 + 1,
        derivFactorialNormSq m ρ (truncateTorusHk (by omega : k + m ≤ k + (D - 2) + 1) Y).val ≤
          (if m = 0 then (c 0) ^ 2 else 2 * (c (m - 1) / r ^ (m - 1)) ^ 2) *
            (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) := by
  classical
  obtain ⟨Y, hY, hgrad⟩ := torusRegularizerLift ρ k D hD a b t ht c r C S hS V
  refine ⟨Y, hY, ?_⟩
  intro m hm
  cases m with
  | zero =>
    let Z := mapTorusHk C (truncateTorusHk (Nat.le_succ k) V)
    have he : truncateTorusHk (by omega : k + 0 ≤ k + (D - 2) + 1) Y =
        torusRegularizerCarrier ρ k D hD a b c r S hS t ht Z := by
      apply TorusHk.ext_value
      change Y.val (valueIndex2 (k + (D - 2) + 1)) =
        (torusRegularizerCarrier ρ k D hD a b c r S hS t ht Z).val (valueIndex2 k)
      rw [torusRegularizerCarrier_value]
      dsimp only [Z]
      rw [mapTorusHk_jet_eq_compLp]
      exact hY
    rw [he]
    have hb := (torusRegularizerCarrier_factorial_bound ρ k D hD a b c r S hS t ht Z).trans
      (mul_le_mul_of_nonneg_left (mappedLowerInput_factorial_bound ρ k C V) (sq_nonneg (c 0)))
    simpa [derivFactorialNormSq, factorialNormSq, derivativeNormSq] using hb
  | succ m =>
    have hmD : m + 2 ≤ D := by omega
    choose Z hZv hZb hZeq using (fun q : Fin 2 => hgrad q m hmD)
    let T : TorusHk (k + m + 1) G := truncateTorusHk (by omega) Y
    have hg (q : Fin 2) : derivativeTorusHk (K := k + m) (r := 1) (fun _ : Fin 1 => q) T = Z q := by
      rw [truncateTorus_derivative_commute (by omega : k + m ≤ k + (D - 2)) Y q]
      exact hZeq q
    have hb (q : Fin 2) : derivFactorialNormSq m ρ (Z q).val ≤
        (c m / r ^ m) ^ 2 * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) :=
      (hZb q).trans (mul_le_mul_of_nonneg_left (mappedGradientInput_factorial_bound ρ k C V q)
        (sq_nonneg (c m / r ^ m)))
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin 2))) => hb q)
    rw [← torusDerivFactorialNormSq_succ ρ T Z hg] at hs
    simpa only [Nat.succ_sub_one, Nat.add_succ, ite_eq_right (Nat.succ_ne_zero m),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
      mul_assoc, T] using hs
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Fixed factorial readouts of a Sobolev carrier and its gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusFactorialReadout (ρ : ℝ) (k : ℕ) :
    TorusHk k E →L[ℝ] JetL2 (volume.restrict AVenhance.unitCube) k E :=
  (factorialWeightedJetCLM ρ k).comp (torusHkGraph (E := E) k).toSubmodule.subtypeL

@[simp] theorem torusFactorialReadout_apply (ρ : ℝ) (k : ℕ) (u : TorusHk k E) :
    torusFactorialReadout ρ k u = AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ u.val := rfl

theorem torusFactorialReadout_norm (ρ : ℝ) (k : ℕ) (u : TorusHk k E) :
    ‖torusFactorialReadout ρ k u‖ = Real.sqrt (factorialNormSq ρ u.val) := by
  rw [torusFactorialReadout_apply, ← AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_normSq ρ u.val,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

variable [FiniteDimensional ℝ E]

def torusFactorialGradientReadout (ρ : ℝ) (k : ℕ) : TorusHk (k + 1) E →L[ℝ]
    JetL2 (volume.restrict AVenhance.unitCube) k (PiLp 2 (fun _ : Fin 2 => E)) :=
  (torusFactorialReadout ρ k).comp (torusGradientTensorCLM (E := E) k)

@[simp] theorem torusFactorialGradientReadout_apply (ρ : ℝ) (k : ℕ) (w : TorusHk (k + 1) E) :
    torusFactorialGradientReadout ρ k w =
      AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (torusGradientTensor w).val := by
  simp only [torusFactorialGradientReadout, ContinuousLinearMap.comp_apply,
    torusFactorialReadout_apply, torusGradientTensorCLM_apply]

theorem torusFactorialGradientReadout_normSq (ρ : ℝ) (k : ℕ) (w : TorusHk (k + 1) E) :
    ‖torusFactorialGradientReadout ρ k w‖ ^ 2 = gradFactorialNormSq ρ w.val := by
  rw [torusFactorialGradientReadout_apply, AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_normSq,
    torusGradientTensor_factorialNormSq]

theorem torusCarrierGradFactorial_nonneg (ρ : ℝ) (k : ℕ) (w : TorusHk (k + 1) E) :
    0 ≤ gradFactorialNormSq ρ w.val := by
  rw [← torusFactorialGradientReadout_normSq]
  exact sq_nonneg _

end AVRegularity.KernelEnergy
end

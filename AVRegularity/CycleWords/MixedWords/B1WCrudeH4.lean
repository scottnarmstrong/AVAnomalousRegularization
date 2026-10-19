-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.SharpBlocksAssembly
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import AVRegularity.CycleWords.MixedWords.B1WWeightedNormFacts
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpBlocks
import AVRegularity.CycleWords.MixedWords.B1WData
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp same-level families from pairwise sharp operators

`SharpSameOpsStatement` gives for each pair of stages a real-linear `T : H^N → H^n`
with the value identity and four sharp facts: the norm `≤ C₀ ζ ‖ψ‖`, the same for slow
tests `E + D`, the pairing `⟨1+R, T(E+D)⟩ ≤ C₀ ζ² |E|`, and commutation with the transverse
projection in the least window.  `sharpSameLevel_of_ops` assembles `sharpSameLevel` from it through
the Schur layer `SharpPairData`. -/

universe u v

open Classical in
/-- **Sharp same-level pair operators.** -/
def SharpSameOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ) (M₀ : ℝ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ r ∈ Icc F.a F.b, ∀ (N : ℕ), n + 1 ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ i i' : B1WIndex ι h Nw m Ks,
    ∃ T : TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
      (∀ ψ : TorusHk N ℂ, (torusHkValueCLM (T ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wSameTransform θ (F.G r) (F.v r) i i'
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
      (∀ ψ : TorusHk N ℂ, ‖T ψ‖ ≤ (if SameRel i i' then C0 *
        min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) else 0) * ‖ψ‖) ∧
      (∀ (E : ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ →
        ‖T (torusHigherConstant N E + Dd)‖ ≤ (if SameRel i i' then C0 *
          min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) else 0) * ‖E‖) ∧
      (∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) →
        ∀ (E : ℂ) (Dd : TorusHk N ℂ),
          ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ →
        ‖sharpPair R (T (torusHigherConstant N E + Dd))‖ ≤ (if SameRel i i' then C0 *
          min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ^ 2 else 0) * ‖E‖) ∧
      (∀ p, IsLeastWindow F.reg p r →
        ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
        (∀ U, torusHkValueCLM (PN U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        (∀ U, torusHkValueCLM (Pn U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        ∀ ψ : TorusHk N ℂ, Pn (T ψ) = T (PN ψ))

section Assemble

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

open Classical in
theorem sameRel_weight_row [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (c : ℝ) (hc : 0 ≤ c)
    (S' : Finset (B1WIndex ι h Nw m Ks)) (i : B1WIndex ι h Nw m Ks) :
    ∑ i' ∈ S', (if SameRel i i' then c else 0) ≤ 5 * c := by
  have := sameRel_card_right i
  calc ∑ i' ∈ S', (if SameRel i i' then c else 0)
      ≤ ∑ i', (if SameRel i i' then c else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
          split_ifs <;> simp [hc]
    _ = (Finset.univ.filter fun i' => SameRel i i').card * c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 * c := mul_le_mul_of_nonneg_right (by exact_mod_cast this) hc

open Classical in
theorem sameRel_weight_col [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (c : ℝ) (hc : 0 ≤ c)
    (S : Finset (B1WIndex ι h Nw m Ks)) (i' : B1WIndex ι h Nw m Ks) :
    ∑ i ∈ S, (if SameRel i i' then c else 0) ≤ 5 * c := by
  have := sameRel_card_left i'
  calc ∑ i ∈ S, (if SameRel i i' then c else 0)
      ≤ ∑ i, (if SameRel i i' then c else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
          split_ifs <;> simp [hc]
    _ = (Finset.univ.filter fun i => SameRel i i').card * c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 * c := mul_le_mul_of_nonneg_right (by exact_mod_cast this) hc

end Assemble

/-- The four sharp sums from pairwise data, with the constants of `sharpSameLevel`. -/
theorem sharp_final {I : Type*} {S S' : Finset I} {N n : ℕ}
    {T : I → I → TorusHk N ℂ →L[ℝ] TorusHk n ℂ} {C0 ζ x M₀ q : ℝ} {w1 w3 : I → I → ℝ}
    (hd : SharpPairData S S' T (M₀ * x) (|M₀| * x) (5 * (C0 * ζ)) (5 * (C0 * ζ))
      (5 * (C0 * ζ)) (5 * (C0 * ζ)) (5 * (C0 * ζ ^ 2)) (5 * (C0 * ζ ^ 2)) w1 w1 w3)
    (hx0 : 0 ≤ x) (hC0 : 0 ≤ C0) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hq : 1 ≤ q) (hRb : |M₀| * x + 1 ≤ q)
    (ψ : I → TorusHk N ℂ) :
    (∑ i' ∈ S', ‖∑ i ∈ S, T i i' (ψ i)‖ ^ 2 ≤ (5 * C0 * q) ^ 2 * ∑ i ∈ S, ‖ψ i‖ ^ 2) ∧
    (∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * x →
      ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (ψ i))‖ ^ 2 ≤
        (5 * C0 * q) ^ 2 * ζ ^ 2 * ∑ i ∈ S, ‖ψ i‖ ^ 2) ∧
    (∀ (E : ℂ) (β : I → ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * x * ‖E‖ →
      (∀ i ∈ S, ψ i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + Dd)) →
      (∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * x →
        ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (ψ i))‖ ^ 2 ≤
          (5 * C0 * q) ^ 2 * ζ ^ 4 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖β i‖ ^ 2) ∧
      ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (ψ i)‖ ^ 2 ≤
        (5 * C0 * q) ^ 2 * ζ ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖β i‖ ^ 2) := by
  have hq0 : 0 ≤ q := by linarith
  have hCq : 0 ≤ 5 * C0 * q := by positivity
  have e1 : 5 * (C0 * ζ) * (5 * (C0 * ζ)) = (5 * C0) ^ 2 * ζ ^ 2 := by ring
  have e2 : 5 * (C0 * ζ ^ 2) * (5 * (C0 * ζ ^ 2)) = (5 * C0) ^ 2 * ζ ^ 4 := by ring
  have hq2 : (5 * C0) ^ 2 ≤ (5 * C0 * q) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hq)]
  have hζ2 : ζ ^ 2 ≤ 1 := pow_le_one₀ hζ0 hζ1
  refine ⟨?_, ?_, ?_⟩
  · refine (sharp_assembly_norm hd ψ).trans ?_
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc (5 * C0) ^ 2 * ζ ^ 2 ≤ (5 * C0) ^ 2 * 1 := by gcongr
      _ ≤ _ := by linarith
  · intro R hR
    have hR' : ‖R‖ ≤ |M₀| * x := hR.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx0)
    refine (sharp_assembly_pair hd ψ R hR').trans ?_
    rw [e1]
    have hs : 0 ≤ ∑ i ∈ S, ‖ψ i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hRq : (|M₀| * x + 1) ^ 2 ≤ q ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRb 2
    calc (|M₀| * x + 1) ^ 2 * ((5 * C0) ^ 2 * ζ ^ 2) * ∑ i ∈ S, ‖ψ i‖ ^ 2
        ≤ q ^ 2 * ((5 * C0) ^ 2 * ζ ^ 2) * ∑ i ∈ S, ‖ψ i‖ ^ 2 := by gcongr
      _ = _ := by ring
  · intro E β Dd hD hψ
    have hs : 0 ≤ ∑ i ∈ S, ‖β i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨fun R hR => ?_, ?_⟩
    · have hR' : ‖R‖ ≤ |M₀| * x := hR.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx0)
      refine (sharp_assembly_slow_pair hd ψ E β Dd hD hψ R hR').trans ?_
      rw [e2]
      have : (5 * C0) ^ 2 * ζ ^ 4 ≤ (5 * C0 * q) ^ 2 * ζ ^ 4 := by gcongr
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (sq_nonneg _)) hs
    · refine (sharp_assembly_slow_norm hd ψ E β Dd hD hψ).trans ?_
      rw [e1]
      have : (5 * C0) ^ 2 * ζ ^ 2 ≤ (5 * C0 * q) ^ 2 * ζ ^ 2 := by gcongr
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (sq_nonneg _)) hs

open Classical in
/-- **Assembly of `sharpSameLevel`** from the pairwise sharp operators. -/
theorem sharpSameLevel_of_ops (hO : SharpSameOpsStatement.{u, v}) :
    SharpSameLevelStatement.{u, v} := by
  intro K Nw D m d Ks ρ n M₀
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m d Ks ρ n M₀
  refine ⟨5 * C0 * (|M₀| * |ρ| + 1), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr k k' _hlev N hnN hdN ψ
  choose T hTv hTn hTs hTp hTc using fun i i' => hC g₁ F θ hρ r hr N hnN hdN i i'
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hS1 : 1 ≤ F.S := F.piece.hS
  have hiv : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hζ0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (by linarith)
  have hζ1 : min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ≤ 1 :=
    min_le_left _ _
  have hq : 1 ≤ |M₀| * |ρ| + 1 := by nlinarith [mul_nonneg (abs_nonneg M₀) (abs_nonneg ρ)]
  have hRb : |M₀| * fibreNorm (planeFibreFrequency F.η θ) + 1 ≤ |M₀| * |ρ| + 1 := by
    have : fibreNorm (planeFibreFrequency F.η θ) ≤ |ρ| := hρ.trans (le_abs_self ρ)
    nlinarith [abs_nonneg M₀]
  have hd : SharpPairData (stageSet b1wSt k) (stageSet b1wSt k') T
      (M₀ * fibreNorm (planeFibreFrequency F.η θ)) (|M₀| * fibreNorm (planeFibreFrequency F.η θ))
      _ _ _ _ _ _ _ _ _ :=
    { nn1 := fun i i' => by split_ifs <;> simp [mul_nonneg hC0 hζ0]
      nn2 := fun i i' => by split_ifs <;> simp [mul_nonneg hC0 hζ0]
      nn3 := fun i i' => by split_ifs <;> simp [mul_nonneg hC0 (sq_nonneg _)]
      hB1 := by positivity
      hB2 := by positivity
      hB3 := by positivity
      hRb := mul_nonneg (abs_nonneg _) hx0
      row1 := fun i _ => sameRel_weight_row _ (mul_nonneg hC0 hζ0) _ i
      col1 := fun i' _ => sameRel_weight_col _ (mul_nonneg hC0 hζ0) _ i'
      row2 := fun i _ => sameRel_weight_row _ (mul_nonneg hC0 hζ0) _ i
      col2 := fun i' _ => sameRel_weight_col _ (mul_nonneg hC0 hζ0) _ i'
      row3 := fun i _ => sameRel_weight_row _ (mul_nonneg hC0 (sq_nonneg _)) _ i
      col3 := fun i' _ => sameRel_weight_col _ (mul_nonneg hC0 (sq_nonneg _)) _ i'
      hN := fun i _ i' _ φ => hTn i i' φ
      hS := fun i _ i' _ E Dd hD => hTs i i' E Dd hD
      hP := fun R hR i _ i' _ E Dd hD => hTp i i' R hR E Dd hD }
  have hF := sharp_final hd hx0 hC0 hζ0 hζ1 hq hRb ψ
  refine ⟨fun i' => if i' ∈ stageSet b1wSt k' then ∑ i ∈ stageSet b1wSt k, T i i' (ψ i) else 0,
    ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    simp only [hi', ↓reduceIte]
    exact torusHk_value_sum_ae (stageSet b1wSt k) (fun i => T i i' (ψ i)) _
      (fun i _ => hTv i i' (ψ i))
  · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by simp only [hi', ↓reduceIte])) hF.1
  · refine ⟨fun R hR => ?_, fun E β Dd hD hψ => ⟨fun R hR => ?_, ?_⟩⟩
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte, sharpPair])) (hF.2.1 R hR)
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte, sharpPair])) ((hF.2.2 E β Dd hD hψ).1 R hR)
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte])) (hF.2.2 E β Dd hD hψ).2
  · intro p hp PN Pn h1 h2
    have key := sharp_assembly_transverse hd ψ PN Pn
      (fun i i' φ => hTc i i' p hp PN Pn h1 h2 φ)
    have hCz := mul_nonneg hC0 hζ0
    have hq0 : 0 ≤ |M₀| * |ρ| + 1 := by linarith
    have h1' : 5 * (C0 * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)) ≤
        5 * C0 * (|M₀| * |ρ| + 1) := by
      nlinarith [mul_nonneg hC0 (sub_nonneg.2 hζ1), mul_nonneg hC0 (sub_nonneg.2 hq)]
    have hb : 5 * (C0 * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)) *
        (5 * (C0 * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹))) ≤
        (5 * C0 * (|M₀| * |ρ| + 1)) ^ 2 := by
      rw [sq]
      exact mul_le_mul h1' h1' (by linarith) (by positivity)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
      simp only [hi', ↓reduceIte])) (key.trans ?_)
    exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The block decomposition at one time

At a time `r` where the stage expansion holds, the sources of a stage `k` against tests `z_i` (with
`H^N` representatives `ψ_i`) decompose along the earlier stages as the blocks of the hypotheses
`H3s` and `H4` of the abstract fibre word `afw_bound` ask (`b1w_blocks_at`), given `H^{s_{k'}}`
representatives of the slow test `q`. The representation (`b1w_stage_representation`) and the block
algebra (`b1w_blocks_of_representation`) give the coefficients along `q(r)` and the admissible
remainders, with `ℓ²` bounds `B · (∑_i ‖ψ_i‖²)^{1/2}` from the transform families (provided as
`hprov`); the families of single tests make the paired terms integrable. `H3s` (`b1w_H3s_at`) and
the block splitting of `H4` are its two uses: weighted slow tests, and the decayed adjoint fast
curves. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The block decomposition at one time.** -/
theorem b1w_blocks_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (tr : ℝ → ComplexCellL2)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2)
    (hq : ∀ k' < k, ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = q)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r
                (fun y => star (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (cR Q : ℝ) (hcR : ‖tr r + cellConstantCLM 1‖ ≤ cR) (hQ0 : 0 ≤ Q)
    (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0)
    (hνq : ∀ k' < k, b1wNu s k' q ≤ Q) (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ)
    (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤
        cR * (B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) /
          ‖cellComplexPair (tr r + cellConstantCLM 1) q‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
        B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) +
          Q * (cR * (B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) /
            ‖cellComplexPair (tr r + cellConstantCLM 1) q‖)) ∧
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  choose Φf hΦf hΦb using hprov ψ
  obtain ⟨Φall, hΦall⟩ : ∃ Φall : B1WIndex ι h Nw m Ks → ComplexCellL2, Φall = fun i' =>
      if hi : b1wSt i' < k then torusHkValueCLM (Φf (b1wSt i') hi i') else 0 := ⟨_, rfl⟩
  -- the classical representatives of the tests
  have hcl : ∀ i, ContDiff ℝ (n + 1 : ℕ) (torusHigherClassicalValue N (ψ i)) := fun i =>
    torusHigherClassicalValue_contDiff N (n + 1) (by omega) (ψ i)
  have hzcl : ∀ i, (torusHkValueCLM (z i) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      torusHigherClassicalValue N (ψ i) := by
    intro i
    rw [hzψ i]
    exact (torusHigherClassicalValue_ae N (by omega) (ψ i)).symm
  have hst : ∀ i, ContDiff ℝ n (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp
      ((hcl i).of_le (by exact_mod_cast Nat.le_succ n))
  have hper : ∀ i, AVenhance.IsZ2Periodic (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i mm y => by simp only [torusHigherClassicalValue_periodic N (ψ i) mm y]
  have hc1 : ∀ i, ContDiff ℝ 1 (torusHigherClassicalValue N (ψ i)) := fun i =>
    (hcl i).of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))
  -- the paired terms are integrable: the family of the single test `ψ_i` is `c_i/c_{i'} conj T`
  have hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (torusHigherClassicalValue N (ψ i) y)) y))
        (volume.restrict AVenhance.unitCube) := by
    intro i hi i' hi'
    obtain ⟨Φ1, hΦ1, -⟩ := hprov (fun j => if j = i then ψ i else 0) (b1wSt i') hi'
    have hv := hΦ1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    refine (cellComplex_pairing_integrable (W i') (torusHkValueCLM (Φ1 i'))).congr ?_
    filter_upwards [hv] with y hy
    rw [hy, Finset.sum_eq_single_of_mem i hi fun j _ hj => ?_]
    · simp only [ite_true, star_mul', star_star, b1wScaleRatio_star]
      ring
    · simp only [hj, ite_false, torusHigherClassicalValue_zero N (by omega), Pi.zero_apply,
        star_zero, b1wTestTransform_zero_test, mul_zero]
  have hrep := b1w_stage_representation F θ r k hπ hϖ W S Fl z
    (fun i => torusHigherClassicalValue N (ψ i)) (fun i _ => hc1 i)
    (fun i _ => hzcl i) hS hF (fun i hi => hExp i hi _ (hst i) (hper i))
    (fun i hi i' hi' => hearly i hi i' hi' _) hW hint Φall
    (fun i' hi' => by
      rw [hΦall]
      simp only [hi', dite_true]
      exact hΦf (b1wSt i') hi' i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩))
  -- the block algebra
  have hΦrep : ∀ k' < k, ∀ i' ∈ stageSet b1wSt k', ∃ U : TorusHk (s k') ℂ,
      torusHkValueCLM U = Φall i' := by
    intro k' hk' i' hi'
    have hst : b1wSt i' = k' := (Finset.mem_filter.1 hi').2
    subst hst
    exact ⟨Φf (b1wSt i') hk' i', by rw [hΦall]; simp [hk']⟩
  have hBk : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (Φall i') ^ 2) ≤
      B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
    intro k' hk'
    have hle : ∀ i' ∈ stageSet b1wSt k', b1wNu s k' (Φall i') ≤ ‖Φf k' hk' i'‖ := by
      intro i' hi'
      have hst : b1wSt i' = k' := (Finset.mem_filter.1 hi').2
      refine b1wNu_le s k' (Φf k' hk' i') ?_
      rw [hΦall]
      subst hst
      simp [hk']
    calc Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (Φall i') ^ 2)
        ≤ Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖Φf k' hk' i'‖ ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i' hi' => ?_)
          exact pow_le_pow_left₀ (b1wNu_nonneg _ _ _) (hle i' hi') 2
      _ ≤ Real.sqrt (B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) :=
          Real.sqrt_le_sqrt (hΦb k' hk')
      _ = B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
  exact b1w_blocks_of_representation s tr r b1wSt k W q
    (∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i))
    Φall (fun _ => B * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)) cR Q hcR hQ0 hg hq hνq
    hΦrep hBk hrep

end Frame
end

/-! # The hypothesis `H3s` at one time

At a time `r` where the stage expansion holds, the slow tests' sources of a stage `k`, weighted by
any coefficients `β`, decompose along the earlier stages as H3s of the abstract fibre word asks
(`b1w_H3s_at`). The weights are moved into the tests (the pairing is conjugate-linear in the test,
`cellComplexSource_scalar_test`): `ψ_i = conj β_i · w`, with `w` an `H^N` representative of `q(r)`.
The block decomposition at one time (`b1w_blocks_at`) then gives the coefficients and the
admissible tests, with `ℓ²` bounds `B · stageNorm β · ‖w‖`. In the form of the abstract fibre word
(`b1w_H3s_good_at`): with the slow test's representatives `≤ C_w ‖⟨1 + r, q⟩‖`, the bounds are
`Θ = B C_w (1 + c_R + c_R C_w)` times the weights, and `‖⟨1 + r, q⟩‖ = ‖N₀‖ Γ(r)`. -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **H3s at one time.** -/
theorem b1w_H3s_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (tr : ℝ → ComplexCellL2)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2)
    (qs : TorusHk 1 ℂ) (w : TorusHk N ℂ) (hwq : torusHkValueCLM w = q)
    (hqs : torusHkValueCLM qs = q) (hq : ∀ k' < k, ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = q)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r
                (fun y => star (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (cR Q : ℝ) (hcR : ‖tr r + cellConstantCLM 1‖ ≤ cR) (hQ0 : 0 ≤ Q)
    (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0)
    (hνq : ∀ k' < k, b1wNu s k' q ≤ Q) (β : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤ cR * (B * stageNorm b1wSt k β * ‖w‖) /
        ‖cellComplexPair (tr r + cellConstantCLM 1) q‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
        B * stageNorm b1wSt k β * ‖w‖ + Q * (cR * (B * stageNorm b1wSt k β * ‖w‖) /
          ‖cellComplexPair (tr r + cellConstantCLM 1) q‖)) ∧
      ∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
      ψ = fun i => torusHigherScalarCLM N (star (β i)) w := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ,
      z = fun i => cellH1Scalar (star (β i)) qs := ⟨_, rfl⟩
  have hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i) := by
    intro i
    refine Lp.ext ?_
    have h1 := cellH1Scalar_jet_ae (star (β i)) qs (valueIndex2 1)
    have h3 := cellScalarCLM_ae (star (β i)) q
    have h4 : torusHkValueCLM (ψ i) = cellScalarCLM (star (β i)) q := by
      rw [hψdef, torusHigherScalarCLM_value, hwq]
    rw [h4, hz]
    filter_upwards [h1, h3] with y hy1 hy3
    rw [hy3]
    change (cellH1Scalar (star (β i)) qs).val (valueIndex2 1) y = _
    rw [hy1]
    change star (β i) * (torusHkValueCLM qs) y = _
    rw [hqs]
  have hψn : Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) = stageNorm b1wSt k β * ‖w‖ := by
    have hsum : ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 = (stageNorm b1wSt k β * ‖w‖) ^ 2 := by
      unfold stageNorm
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψdef, torusHigherScalarCLM_norm, norm_star, mul_pow]
    rw [hsum, Real.sqrt_sq (mul_nonneg (stageNorm_nonneg _ _ _) (norm_nonneg _))]
  have hX : ∑ i ∈ stageSet b1wSt k, β i *
      cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs =
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) :=
    Finset.sum_congr rfl fun i _ => by
      rw [hz]
      exact (congrArg (fun c => c * _) (star_star (β i)).symm).trans
        (cellComplexSource_scalar_test _ _ _ qs (star (β i))).symm
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_blocks_at F θ r k hπ hϖ s n N hN tr W S Fl q hq hS
    hF hExp hearly hW B hB hprov cR Q hcR hQ0 hg hνq z ψ hzψ
  rw [hψn] at h2 h3
  exact ⟨κ, φ, h1, fun k' hk' => (h2 k' hk').trans_eq (by ring),
    fun k' hk' => (h3 k' hk').trans_eq (by ring), hX.trans h4⟩

/-- **H3s at a good time, in the form of the abstract fibre word** (the crude pass, `ζ = 1`). The
slow test's representatives are bounded by `C_w ‖E‖`, where `E = ⟨1 + r, q⟩ ≠ 0` and
`‖E‖ = ‖N₀‖ Γ(r)`. The coefficients and the remainders are then bounded by
`Θ = B C_w (1 + c_R + c_R C_w)` times the weights, and the decomposition is exact. -/
theorem b1w_H3s_good_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (tr : ℝ → ComplexCellL2)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2)
    (qs : TorusHk 1 ℂ) (w : TorusHk N ℂ) (hwq : torusHkValueCLM w = q)
    (hqs : torusHkValueCLM qs = q) (E : ℂ) (hE : cellComplexPair (tr r + cellConstantCLM 1) q = E)
    (hE0 : E ≠ 0) (Cw : ℝ) (hCw : 0 ≤ Cw) (hw : ‖w‖ ≤ Cw * ‖E‖)
    (hq : ∀ k' < k, ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = q ∧ ‖U‖ ≤ Cw * ‖E‖)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r
                (fun y => star (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (cR : ℝ) (hcR : ‖tr r + cellConstantCLM 1‖ ≤ cR) (N₀ : ℂ) (Γr : ℝ)
    (hNΓ : ‖N₀‖ * Γr = ‖E‖) (εs : ℝ) (hεs : 0 ≤ εs) (β : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤
        B * Cw * (1 + cR + cR * Cw) * stageNorm b1wSt k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
        B * Cw * (1 + cR + cR * Cw) * (‖N₀‖ * Γr) * stageNorm b1wSt k β) ∧
      ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ ≤
        ‖N₀‖ * εs * stageNorm b1wSt k β := by
  have hcR0 : 0 ≤ cR := (norm_nonneg _).trans hcR
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE0
  have hEn : ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ = ‖E‖ := by rw [hE]
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_H3s_at F θ r k hπ hϖ s n N hN tr W S Fl q qs w hwq hqs
    (fun k' hk' => (hq k' hk').imp fun _ hU => hU.1) hS hF hExp hearly hW B hB hprov cR
    (Cw * ‖E‖) hcR (mul_nonneg hCw (norm_nonneg _)) (by rw [hE]; exact hE0)
    (fun k' hk' => by
      obtain ⟨U, hU, hUb⟩ := hq k' hk'
      exact (b1wNu_le s k' U hU).trans hUb) β
  set sβ := stageNorm b1wSt k β with hsβ
  have hsβ0 : 0 ≤ sβ := stageNorm_nonneg _ _ _
  have hBs : 0 ≤ B * sβ := mul_nonneg hB hsβ0
  -- the coefficient bound, before `Θ`
  have hκb : cR * (B * sβ * ‖w‖) / ‖E‖ ≤ cR * B * Cw * sβ := by
    calc cR * (B * sβ * ‖w‖) / ‖E‖ ≤ cR * (B * sβ * (Cw * ‖E‖)) / ‖E‖ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hBs) hcR0) hEpos.le
      _ = cR * B * Cw * sβ := by rw [div_eq_iff hEpos.ne']; ring
  have hΘ1 : cR * B * Cw ≤ B * Cw * (1 + cR + cR * Cw) := by
    have he : B * Cw * (1 + cR + cR * Cw) = cR * B * Cw + B * Cw * (1 + cR * Cw) := by ring
    rw [he]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hB hCw) (add_nonneg zero_le_one (mul_nonneg hcR0 hCw)))
  have hΘ2 : B * Cw * (1 + cR * Cw) ≤ B * Cw * (1 + cR + cR * Cw) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hB hCw)
  refine ⟨κ, φ, h1, fun k' hk' => ?_, fun k' hk' => ?_, ?_⟩
  · calc stageNorm b1wSt k' κ ≤ cR * (B * sβ * ‖w‖) / ‖E‖ := by
          rw [← hEn]; exact h2 k' hk'
      _ ≤ cR * B * Cw * sβ := hκb
      _ ≤ B * Cw * (1 + cR + cR * Cw) * sβ := mul_le_mul_of_nonneg_right hΘ1 hsβ0
  · rw [hNΓ]
    calc Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2)
        ≤ B * sβ * ‖w‖ + Cw * ‖E‖ * (cR * (B * sβ * ‖w‖) / ‖E‖) :=
          (h3 k' hk').trans_eq (by rw [hEn])
      _ ≤ B * sβ * (Cw * ‖E‖) + Cw * ‖E‖ * (cR * B * Cw * sβ) :=
          add_le_add (mul_le_mul_of_nonneg_left hw hBs)
            (mul_le_mul_of_nonneg_left hκb (mul_nonneg hCw (norm_nonneg _)))
      _ = B * Cw * (1 + cR * Cw) * ‖E‖ * sβ := by ring
      _ ≤ B * Cw * (1 + cR + cR * Cw) * ‖E‖ * sβ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘ2 (norm_nonneg _)) hsβ0
  · rw [h4, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hεs) (stageNorm_nonneg _ _ _)

end Frame
end

/-! # The hypothesis `H3s` at every time (the crude pass)

The stage expansion, the letter transform bound, the identification of the stage forcing with the
literal forcing of the amplitude identification, and the `L²` slices hold for almost every time. On
a set `G` of good times, of full measure in `[a, b]`, H3s holds exactly (`b1w_H3s_good_at`). Off `G`
the stage forcing is set to `0`: the stage curves stay Hilbert curves
(`cellWeakHilbertCurve_indicator_forcing`, the forcing only matters a.e.), and H3s holds trivially
there (`b1w_H3s_zero_forcing`). So H3s holds at every `r ∈ [a, b]` (`b1w_crude_H3s`), in the form of
`afw_bound` with `ζ = 1` and `ε_s = 0`. -/

section
universe u v

/-- **Forcing set to `0` off a set of full measure** keeps a Hilbert curve. -/
theorem cellWeakHilbertCurve_indicator_forcing {a b : ℝ} (C : CellCoefficients)
    (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} {S : ℝ → ComplexCellL2}
    {Fl : ℝ → Fin 2 → ComplexCellL2}
    (h : CellWeakHilbertCurve a b u slice fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) (S t) (Fl t))
    (Good : Set ℝ) (hGood : ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Good) :
    CellWeakHilbertCurve a b u slice fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) (Good.indicator S t) (Good.indicator Fl t) := by
  refine h.dual_congr ?_
  filter_upwards [hGood] with t ht
  rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]

/-- **H3s with zero forcing**: the coefficients and the remainders `0`. -/
theorem b1w_H3s_zero_forcing {I : Type*} [Fintype I] (st : I → ℕ) (s : ℕ → ℕ)
    (tr : ℝ → ComplexCellL2) (r : ℝ) (k : ℕ) (θc : Fin 2 → ℂ) (W : I → ComplexCellL2)
    (q : ComplexCellL2) (qs : TorusHk 1 ℂ) (Θ X : ℝ) (hΘ : 0 ≤ Θ) (hX : 0 ≤ X) (N₀ : ℂ)
    (β : I → ℂ) :
    ∃ (κ : I → ℂ) (φ : I → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet st k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * 1 ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (φ i') ^ 2) ≤
        Θ * 1 * X * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource θc 0 (fun _ => 0) qs -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm st k β := by
  have hν : ∀ k', b1wNu s k' 0 = 0 := fun k' =>
    le_antisymm ((b1wNu_le s k' 0 (map_zero _)).trans_eq norm_zero) (b1wNu_nonneg _ _ _)
  have hβ := stageNorm_nonneg st k β
  refine ⟨0, 0, fun k' _ i' _ => ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩,
    fun k' _ => ?_, fun k' _ => ?_, ?_⟩
  · have h0 : stageNorm st k' (0 : I → ℂ) = 0 := by
      unfold stageNorm
      simp
    rw [h0]
    positivity
  · simp only [Pi.zero_apply, hν, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  · simp only [cellComplexSource_zero, mul_zero, Finset.sum_const_zero, Pi.zero_apply, zero_mul,
      cellComplexPair_zero_right, add_zero, sub_zero, norm_zero, le_refl]

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **H3s at every time** (the crude pass, `ζ = 1`, `ε_s = 0`), for the stage curves
`W_i = c_i Dθ_i` with the forcing `c_i (src_i, Fl_i)` set to `0` off the good times `G`. At a good
time the decomposition is exact (`b1w_H3s_good_at`); off `G` there is no forcing. -/
theorem b1w_crude_H3s {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (hη : 0 < F.η) (s : ℕ → ℕ) (n : ℕ)
    (hn : ∀ k, n + 3 ≤ s k)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Good : Set ℝ)
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (tr q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hGq : ∀ r ∈ Good, torusHkValueCLM (qs r) = q r) (E : ℝ → ℂ)
    (hE : ∀ r ∈ Icc F.a F.b, cellComplexPair (tr r + cellConstantCLM 1) (q r) = E r)
    (hE0 : ∀ r, E r ≠ 0) (Cw : ℝ) (hCw : 0 ≤ Cw) (M : ℕ)
    (hrep : ∀ r ∈ Icc F.a F.b, ∀ k < M, ∃ U : TorusHk (s k) ℂ,
      torusHkValueCLM U = q r ∧ ‖U‖ ≤ Cw * ‖E r‖)
    (cR : ℝ) (hcR : ∀ r ∈ Icc F.a F.b, ‖tr r + cellConstantCLM 1‖ ≤ cR) (N₀ : ℂ) (Γ : ℝ → ℝ)
    (hNΓ : ∀ r ∈ Icc F.a F.b, ‖N₀‖ * Γ r = ‖E r‖) (Θ : ℝ)
    (hΘ : B * Cw * (1 + cR + cR * Cw) ≤ Θ) :
    ∀ r ∈ Icc F.a F.b, ∀ k < M, ∀ β : B1WIndex ι h Nw m Ks → ℂ,
      ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤ Θ * 1 ^ 2 * stageNorm b1wSt k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
        Θ * 1 * (‖N₀‖ * Γ r) * stageNorm b1wSt k β) ∧
      ‖∑ i ∈ stageSet b1wSt k, β i * cellComplexSource
          (fun j => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ j)
          (Good.indicator (fun t =>
            cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t)) r)
          (Good.indicator (fun t j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
            (cellSourceSlice (fun r z => Fl i r z j) t)) r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (q r) +
            cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
              (cellRawTrace (Dθ i') r)) (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm b1wSt k β := by
  intro r hr k hk β
  have hcR0 : 0 ≤ cR := (norm_nonneg _).trans (hcR r hr)
  have hΘ0 : 0 ≤ Θ := (mul_nonneg (mul_nonneg hB hCw) (by positivity)).trans hΘ
  have hX : 0 ≤ ‖N₀‖ * Γ r := by rw [hNΓ r hr]; exact norm_nonneg _
  by_cases hg : r ∈ Good
  swap
  · -- no forcing off the good times
    simp only [Set.indicator_of_notMem hg]
    exact b1w_H3s_zero_forcing b1wSt s tr r k _ _ (q r) (qs r) _ _ hΘ0 hX N₀ β
  -- a good time
  simp only [Set.indicator_of_mem hg, one_pow, mul_one]
  rw [fibreShift_eq hη θ]
  obtain ⟨w, hwq, hw⟩ := hrep r hr k hk
  have hβ0 := stageNorm_nonneg b1wSt k β
  have hS' : ∀ i, (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (src i) r) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
        b1wScale F.π F.ϖ F.ηg F.letters i *
          amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y := fun i => by
    obtain ⟨hm, hlit, -, -⟩ := hGsrc r hg i
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (src i) r), cellSourceSlice_ae (src i) r hm, hlit] with y h1 h2 h3
    rw [h1, h2, h3]
  have hF' : ∀ i j, (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j := fun i j => by
    obtain ⟨-, -, hm, hlit⟩ := hGsrc r hg i
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r),
      cellSourceSlice_ae (fun r z => Fl i r z j) r (hm j), hlit] with y h1 h2 h3
    rw [h1, h2, h3]
  have hW' : ∀ i', (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
      (cellRawTrace (Dθ i') r) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
        b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y := fun i' => by
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i')
      (cellRawTrace (Dθ i') r), cellRawTrace_ae (Dθ i') r (hmem i' r hr), hval i' r hr]
      with y h1 h2 h3
    rw [h1, h2, h3]
    rfl
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_H3s_good_at F θ r k hπ hϖ s n (s k) (hn k) tr
    (fun i' => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i') (cellRawTrace (Dθ i') r))
    (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
    (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r))
    (q r) (qs r) w hwq (hGq r hg) (E r) (hE r hr) (hE0 r) Cw hCw hw
    (fun k' hk' => hrep r hr k' (hk'.trans hk))
    (fun i _ => hS' i) (fun i _ j => hF' i j) (fun i _ => hGexp r hg i)
    (fun i hi i' hi' => hearly i i' (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r)
    hW' B hB (fun ψ k' hk' => hprov r hg k k' hk' ψ) cR (hcR r hr) N₀ (Γ r)
    (hNΓ r hr) 0 le_rfl β
  exact ⟨κ, φ, h1, fun k' hk' => (h2 k' hk').trans (mul_le_mul_of_nonneg_right hΘ hβ0),
    fun k' hk' => (h3 k' hk').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘ hX) hβ0), h4⟩

end Frame
end

/-! # The hypothesis `H4` at every time (the crude pass)

H4 of the abstract fibre word, with the crude adjoint curves (`b1w_crude_adjoint`, rate
`c_f = π²/8`) as the test families. Their slices are represented in `H^{s_k}` at every time
(`b1w_adjoint_family`), so at a good time the block decomposition (`b1w_blocks_at`) is exact, with
the bounds of `b1w_H4_good_at`; off the good times there is no stage forcing. The result
(`b1w_crude_H4`) is H4 in the form of `afw_bound` with `ζ = 1`, `ε_f = 0`, `C_f = C_a` and
`Θ = B (1 + c_R + c_R C_w)`. -/

section
universe u v

/-- `√(∑ x_i²) ≤ c √(∑ y_i²)` when `0 ≤ x_i ≤ c y_i`. -/
theorem sqrt_sum_sq_le_mul {α : Type*} (S : Finset α) (x y : α → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hxy : ∀ i ∈ S, x i ≤ c * y i) :
    Real.sqrt (∑ i ∈ S, x i ^ 2) ≤ c * Real.sqrt (∑ i ∈ S, y i ^ 2) := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hx i hi) (hxy i hi) 2

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The stage forcing and values at a good time** are the literal forcing of the amplitude
identification and the stage values, rescaled by the stage scales. -/
theorem b1w_good_stage_ae {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (r : ℝ)
    (hval : ∀ i, cellValue (Dθ i) r =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 r) y)))
    (hmem : ∀ i, MemLp (cellValue (Dθ i) r) 2 (volume.restrict AVenhance.unitCube))
    (hsrc : ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r) :
    (∀ i, (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r) :
        Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
          b1wScale F.π F.ϖ F.ηg F.letters i *
            amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y) ∧
    (∀ i j, (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
        (cellSourceSlice (fun r z => Fl i r z j) r) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
          b1wScale F.π F.ϖ F.ηg F.letters i *
            amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j) ∧
    ∀ i', (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i') (cellRawTrace (Dθ i') r) :
        Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
          b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y := by
  refine ⟨fun i => ?_, fun i j => ?_, fun i' => ?_⟩
  · obtain ⟨hm, hlit, -, -⟩ := hsrc i
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (src i) r), cellSourceSlice_ae (src i) r hm, hlit] with y h1 h2 h3
    rw [h1, h2, h3]
  · obtain ⟨-, -, hm, hlit⟩ := hsrc i
    filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r),
      cellSourceSlice_ae (fun r z => Fl i r z j) r (hm j), hlit] with y h1 h2 h3
    rw [h1, h2, h3]
  · filter_upwards [cellScalarCLM_ae (b1wScale F.π F.ϖ F.ηg F.letters i')
      (cellRawTrace (Dθ i') r), cellRawTrace_ae (Dθ i') r (hmem i'), hval i'] with y h1 h2 h3
    rw [h1, h2, h3]
    rfl

/-- **H4's clause (3) at a good time**: the block decomposition of the stage sources against
represented tests `z_i = ψ_i`, with `√(∑‖ψ_i‖²) ≤ Y`, has coefficients `≤ Θ Y/‖E‖` and remainders
`≤ Θ Y`, `Θ = B (1 + c_R + c_R C_w)`, where `E = ⟨1 + r, q⟩`. -/
theorem b1w_H4_good_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (tr : ℝ → ComplexCellL2)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2) (E : ℂ)
    (hE : cellComplexPair (tr r + cellConstantCLM 1) q = E) (hE0 : E ≠ 0) (Cw : ℝ)
    (hCw : 0 ≤ Cw)
    (hq : ∀ k' < k, ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = q ∧ ‖U‖ ≤ Cw * ‖E‖)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r
                (fun y => star (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (cR : ℝ) (hcR : ‖tr r + cellConstantCLM 1‖ ≤ cR) (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ)
    (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) (Y : ℝ)
    (hY : Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ≤ Y) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤ B * (1 + cR + cR * Cw) * Y / ‖E‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
        B * (1 + cR + cR * Cw) * Y) ∧
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  have hcR0 : 0 ≤ cR := (norm_nonneg _).trans hcR
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE0
  have hEn : ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ = ‖E‖ := by rw [hE]
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_blocks_at F θ r k hπ hϖ s n N hN tr W S Fl q
    (fun k' hk' => (hq k' hk').imp fun _ hU => hU.1) hS hF hExp hearly hW B hB hprov cR
    (Cw * ‖E‖) hcR (mul_nonneg hCw (norm_nonneg _)) (by rw [hE]; exact hE0)
    (fun k' hk' => by
      obtain ⟨U, hU, hUb⟩ := hq k' hk'
      exact (b1wNu_le s k' U hU).trans hUb) z ψ hzψ
  set X := Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := hX0.trans hY
  have hΘ0 : 0 ≤ B * (1 + cR + cR * Cw) := mul_nonneg hB (by positivity)
  have hκb : cR * (B * X) / ‖E‖ ≤ B * (1 + cR + cR * Cw) * Y / ‖E‖ := by
    refine div_le_div_of_nonneg_right ?_ hEpos.le
    calc cR * (B * X) ≤ cR * (B * Y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hB) hcR0
      _ ≤ B * (1 + cR + cR * Cw) * Y := by
          have he : B * (1 + cR + cR * Cw) * Y = cR * (B * Y) + B * (1 + cR * Cw) * Y := by ring
          rw [he]
          exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB (by positivity)) hY0)
  refine ⟨κ, φ, h1, fun k' hk' => ((h2 k' hk').trans_eq (by rw [hEn])).trans hκb,
    fun k' hk' => ?_, h4⟩
  calc Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2)
      ≤ B * X + Cw * ‖E‖ * (cR * (B * X) / ‖E‖) := (h3 k' hk').trans_eq (by rw [hEn])
    _ = B * (1 + cR * Cw) * X := by
        have he : Cw * ‖E‖ * (cR * (B * X) / ‖E‖) = Cw * cR * B * X := by
          rw [mul_div_assoc', div_eq_iff hEpos.ne']
          ring
        rw [he]
        ring
    _ ≤ B * (1 + cR + cR * Cw) * Y :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hB) hY hX0 hΘ0

/-- **H4 at every time** (the crude pass: `c_f = π²/8`, `ζ = 1`, `ε_f = 0`, `C_f = C_a`), for the
stage curves `W_i = c_i Dθ_i` with the forcing set to `0` off the good times, and any
`Θ ≥ B (1 + c_R + c_R C_w)`. The test families are the crude adjoint curves `hadj`. -/
theorem b1w_crude_H4 {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (hη : 0 < F.η) (s : ℕ → ℕ) (n : ℕ)
    (hn : ∀ k, n + 3 ≤ s k)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Good : Set ℝ)
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
            =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
              ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
                star (b1wTestTransform F θ i i' r (fun y => star
                  (torusHigherClassicalValue (s k) (ψ i) y)) y)) ∧
          ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (tr q : ℝ → ComplexCellL2) (E : ℝ → ℂ)
    (hE : ∀ r ∈ Icc F.a F.b, cellComplexPair (tr r + cellConstantCLM 1) (q r) = E r)
    (hE0 : ∀ r, E r ≠ 0) (Cw : ℝ) (hCw : 0 ≤ Cw) (M : ℕ)
    (hrep : ∀ r ∈ Icc F.a F.b, ∀ k < M, ∃ U : TorusHk (s k) ℂ,
      torusHkValueCLM U = q r ∧ ‖U‖ ≤ Cw * ‖E r‖)
    (cR : ℝ) (hcR : ∀ r ∈ Icc F.a F.b, ‖tr r + cellConstantCLM 1‖ ≤ cR) (N₀ : ℂ) (Γ : ℝ → ℝ)
    (hNΓ : ∀ r ∈ Icc F.a F.b, ‖N₀‖ * Γ r = ‖E r‖)
    (C : CellCoefficients) (hCθ : C.θ = fun j => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ j)
    (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (Ca : ℝ) (hCa : 0 ≤ Ca)
    (hadj : ∀ k < M, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2, b1wAdm s tr k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        ∀ r ∈ Icc F.a T, b1wAdm s tr k r (Ψv r) ∧
          b1wNu s k (Ψv r) ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu s k ψ)
    (Θ : ℝ) (hΘ : B * (1 + cR + cR * Cw) ≤ Θ) :
    ∀ t ∈ Icc 0 (F.b - F.a), ∀ k < M, ∀ ψ : B1WIndex ι h Nw m Ks → ComplexCellL2,
      (∀ i ∈ stageSet b1wSt k, b1wAdm s tr k (F.a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNu s k (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2)
        (Ψs : B1WIndex ι h Nw m Ks → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet b1wSt k, CellWeakHilbertCurve F.a (F.a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (F.a + t) = ψ i) ∧
        (∀ i ∈ stageSet b1wSt k, b1wAdm s tr k F.a (Ψv i F.a)) ∧
        Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNu s k (Ψv i F.a) ^ 2) ≤
          Ca * Real.exp (-(Real.pi ^ 2 / 8) * t) ∧
        ∀ r ∈ Icc F.a (F.a + t),
          ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
          (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
          (∀ k' < k, stageNorm b1wSt k' κ ≤
            Θ * 1 * Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNu s k' (φ i') ^ 2) ≤
            Θ * Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r))) ∧
          ‖∑ i ∈ stageSet b1wSt k, cellComplexSource C.θ
              (Good.indicator (fun t =>
                cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t)) r)
              (Good.indicator (fun t j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
                (cellSourceSlice (fun r z => Fl i r z j) t)) r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
              (κ i' * cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
                  (cellRawTrace (Dθ i') r)) (q r) +
                cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
                  (cellRawTrace (Dθ i') r)) (φ i'))‖ ≤
            0 / Γ (F.a + t) := by
  intro t ht k hk ψ hψ hψ1
  have hT : F.a + t ∈ Icc F.a F.b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs1 : 1 ≤ s k := by have := hn k; omega
  have hcR0 : 0 ≤ cR := (norm_nonneg _).trans (hcR F.a ⟨le_rfl, F.ordered⟩)
  have hΘ0 : 0 ≤ Θ := (mul_nonneg hB (by positivity)).trans hΘ
  obtain ⟨Ψv, Ψs, U, hcurve, hfin, hvalU, hprop⟩ := b1w_adjoint_family b1wSt s k hs1 tr C hG V
    hv hb F.a (F.a + t) Ca (hadj k hk (F.a + t) hT) ψ hψ
  have haT : F.a ∈ Icc F.a (F.a + t) := ⟨le_rfl, by linarith [ht.1]⟩
  -- the decay factor from `T = a + t` to `r`, and the bound of the representatives
  have hdec : ∀ r ∈ Icc F.a (F.a + t),
      Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2) ≤
        Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := by
    intro r hr
    have hc : 0 ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) :=
      mul_nonneg hCa (Real.exp_pos _).le
    calc Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2)
        ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) *
            Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNu s k (ψ i) ^ 2) :=
          sqrt_sum_sq_le_mul _ _ _ hc (fun i _ => norm_nonneg _)
            (fun i hi => (hprop i hi r hr).2.2)
      _ ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) * 1 :=
          mul_le_mul_of_nonneg_left hψ1 hc
      _ = Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := mul_one _
  refine ⟨Ψv, Ψs, fun i hi => ⟨hcurve i, hfin i hi⟩, fun i hi => (hprop i hi F.a haT).1, ?_,
    fun r hr => ?_⟩
  · have h0 := hdec F.a haT
    have he : F.a + t - F.a = t := by ring
    rw [he] at h0
    refine le_trans (le_of_eq ?_) h0
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun i hi => ?_)
    rw [(hprop i hi F.a haT).2.1]
  have hrI : r ∈ Icc F.a F.b := ⟨hr.1, hr.2.trans hT.2⟩
  have hY0 : 0 ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) :=
    mul_nonneg hCa (Real.exp_pos _).le
  have hX : 0 ≤ ‖N₀‖ * Γ r := by rw [hNΓ r hrI]; exact norm_nonneg _
  by_cases hg : r ∈ Good
  swap
  · -- no forcing off the good times
    simp only [Set.indicator_of_notMem hg]
    have hν : ∀ k', b1wNu s k' 0 = 0 := fun k' =>
      le_antisymm ((b1wNu_le s k' 0 (map_zero _)).trans_eq norm_zero) (b1wNu_nonneg _ _ _)
    refine ⟨0, 0, fun k' _ i' _ => ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩,
      fun k' _ => ?_, fun k' _ => ?_, ?_⟩
    · have h0 : stageNorm b1wSt k' (0 : B1WIndex ι h Nw m Ks → ℂ) = 0 := by
        unfold stageNorm
        simp
      rw [h0]
      exact div_nonneg (by positivity) hX
    · simp only [Pi.zero_apply, hν, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero]
      positivity
    · have hz : ∀ i, cellComplexSource C.θ 0 0 (Ψs i r) = 0 := fun i =>
        cellComplexSource_zero C.θ (Ψs i r)
      simp only [hz, Finset.sum_const_zero, Pi.zero_apply, zero_mul,
        cellComplexPair_zero_right, add_zero, sub_zero, norm_zero, zero_div, le_refl]
  -- a good time
  obtain ⟨hS', hF', hW'⟩ := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hrI)
    (fun i => hmem i r hrI) (hGsrc r hg)
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_H4_good_at F θ r k hπ hϖ s n (s k) (hn k) tr
    (fun i' => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i') (cellRawTrace (Dθ i') r))
    (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
    (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r))
    (q r) (E r) (hE r hrI) (hE0 r) Cw hCw (fun k' hk' => hrep r hrI k' (hk'.trans hk))
    (fun i _ => hS' i)
    (fun i _ j => hF' i j) (fun i _ => hGexp r hg i)
    (fun i hi i' hi' => hearly i i' (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r)
    hW' B hB (fun ψ k' hk' => hprov r hg k k' hk' ψ) cR (hcR r hrI) (fun i => Ψs i r)
    (fun i => U i r) (fun i => hvalU i r hr) _ (hdec r hr)
  refine ⟨κ, φ, h1, fun k' hk' => (h2 k' hk').trans ?_, fun k' hk' => (h3 k' hk').trans ?_, ?_⟩
  · rw [hNΓ r hrI]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    calc B * (1 + cR + cR * Cw) * (Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)))
        ≤ Θ * (Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r))) :=
          mul_le_mul_of_nonneg_right hΘ hY0
      _ = Θ * 1 * Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := by ring
  · calc B * (1 + cR + cR * Cw) * (Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)))
        ≤ Θ * (Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r))) :=
          mul_le_mul_of_nonneg_right hΘ hY0
      _ = Θ * Ca * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := by ring
  · simp only [Set.indicator_of_mem hg]
    rw [hCθ, fibreShift_eq hη θ, h4, sub_self, norm_zero, zero_div]

end Frame
end

end AVRegularity.CycleWords.Assembly
end

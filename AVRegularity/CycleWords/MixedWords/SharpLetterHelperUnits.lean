-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.SharpLetterFactPair
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CoupledEnergy.Galerkin.PlainFamilyMeasurableFromRows

@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-- Head-class cache: the normed group of the periodic Sobolev carrier. -/
local instance sharpHelperTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
/-- Head-class cache: the inner product space of the periodic Sobolev carrier. -/
local instance sharpHelperTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
/-- Head-class cache: the normed space of the periodic Sobolev carrier. -/
local instance sharpHelperTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

end AVRegularity.CycleWords.Assembly
end

attribute [local instance] AVRegularity.CycleWords.Assembly.sharpHelperTorusNormed
  AVRegularity.CycleWords.Assembly.sharpHelperTorusInner
  AVRegularity.CycleWords.Assembly.sharpHelperTorusSpace

section
/-! # `SharpLetterSlowNormFact` from the helper `SharpLetterGainFact` -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

theorem sl80_scal_norm_sq {I : Type*} (S : Finset I) (N : ℕ) (b : I → ℂ) (Dd : TorusHk N ℂ) :
    ∑ i ∈ S, ‖torusHigherScalarCLM N (b i) Dd‖ ^ 2 = ‖Dd‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [torusHigherScalarCLM_norm]; ring

theorem sl80_const_trunc_sq {I : Type*} (S : Finset I) {L N : ℕ} (hLN : L ≤ N) (b : I → ℂ) (E : ℂ) :
    ∑ i ∈ S, ‖truncateTorusHk hLN (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 =
      ‖torusHigherConstant L (1 : ℂ)‖ ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusHigherConstant_smul, torusHigherConstant_truncate hLN, torusHigherConstant_norm,
    norm_mul]
  ring

section Pieces

variable {I I' : Type*} {N n : ℕ}

/-- Pointwise decomposition of the slow family into the constant part (gain and remainder) and the
`Dd` part. -/
theorem sl80_slow_decomp (S : Finset I) (T T' Tg T0 : I → I' → TorusHk N ℂ →L[ℝ] TorusHk n ℂ)
    (i' : I') (eqT : ∀ i ∈ S, T i i' = T' i i')
    (eqsplit : ∀ i ∈ S, ∀ ψ, T i i' ψ = Tg i i' ψ + T0 i i' ψ) (E : ℂ) (b : I → ℂ)
    (Dd : TorusHk N ℂ) (f : I → TorusHk N ℂ)
    (hf : ∀ i ∈ S, f i = torusHigherScalarCLM N (b i) (torusHigherConstant N E + Dd)) :
    ‖∑ i ∈ S, T i i' (f i)‖ ≤
      ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ +
      ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ +
      ‖∑ i ∈ S, T' i i' (torusHigherScalarCLM N (b i) Dd)‖ := by
  have hU : ∑ i ∈ S, T i i' (f i) =
      ∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E)) +
      ∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E)) +
      ∑ i ∈ S, T' i i' (torusHigherScalarCLM N (b i) Dd) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have e1 := eqsplit i hi (torusHigherScalarCLM N (b i) (torusHigherConstant N E))
    have e2 : T i i' (torusHigherScalarCLM N (b i) Dd) =
        T' i i' (torusHigherScalarCLM N (b i) Dd) := by rw [eqT i hi]
    rw [hf i hi, map_add, map_add, e1, e2]
  refine le_trans (le_of_eq (congrArg (fun U => ‖U‖) hU)) ?_
  exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)

end Pieces

open Classical in
/-- **The slow-test norm fact** from the gain split and the plain letter bound. -/
theorem sharpLetterSlowNorm_of_gain (hG : SharpLetterGainFact.{u, v}) :
    SharpLetterSlowNormFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n M₀
  obtain ⟨C, hC, kG⟩ := hG K Nw D m d Ks pos ρ n
  obtain ⟨C1, hC1, k1⟩ := letterOps.{u, v} K Nw D m d Ks pos ρ n
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = ∑ l : Fin Nw, ‖torusHigherConstant (n + d l) (1 : ℂ)‖ :=
    ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := hKc ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Kc * C + C * (1 + |ρ|) + C1 * |M₀| * (1 + |ρ|), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [kG g₁ F θ hlet hJ hρ, k1 g₁ F θ hlet hJ hρ] with r a1 a2
  intro l N hN1 hN2
  obtain ⟨Tg, T0, hv, hb⟩ := a1 l N hN1 hN2
  obtain ⟨T', hT'v, hT'b⟩ := a2 l N hN1 hN2
  intro T hTv S S' x x' β β' hS hS' w0 ζ E b Dd hD f hf
  obtain ⟨hb1, -, hb3⟩ := hb S S' x x' β β' hS hS'
  obtain ⟨hϖ0, hϖζ⟩ := sl80_varpi F θ
  obtain ⟨hζ0, hxζ⟩ := sl80_zeta F θ ρ hρ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hSg : 0 ≤ ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hκ : ‖torusHigherConstant (n + d l) (1 : ℂ)‖ ≤ Kc := by
    rw [hKc]
    exact Finset.single_le_sum (f := fun l : Fin Nw => ‖torusHigherConstant (n + d l) (1 : ℂ)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
  have eqT : ∀ i ∈ S, ∀ i' ∈ S', T i i' = T' i i' := fun i hi i' hi' =>
    ContinuousLinearMap.ext fun ψ =>
      sl80_val_unique hTv hT'v i i' (hS i hi).1 (hS' i' hi').1 ψ
  have eqsplit : ∀ i ∈ S, ∀ i' ∈ S', ∀ ψ, T i i' ψ = Tg i i' ψ + T0 i i' ψ :=
    fun i hi i' hi' ψ => sl80_split hTv hv i i' (hS i hi).1 (hS' i' hi').1 ψ
  have hpt : ∀ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ≤
      ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ +
      ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ +
      ‖∑ i ∈ S, T' i i' (torusHigherScalarCLM N (b i) Dd)‖ := fun i' hi' =>
    sl80_slow_decomp S T T' Tg T0 i' (fun i hi => eqT i hi i' hi')
      (fun i hi ψ => eqsplit i hi i' hi' ψ) E b Dd f hf
  have hA : ∑ i' ∈ S', ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 ≤
      (Kc * C * ζ * w0) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have h1 := hb1 (fun i => torusHigherScalarCLM N (b i) (torusHigherConstant N E))
    rw [sl80_const_trunc_sq S hN1 b E] at h1
    have h2 : C * F.ϖ * w0 * ‖torusHigherConstant (n + d l) (1 : ℂ)‖ ≤ Kc * C * ζ * w0 := by
      have h5 := mul_le_mul_of_nonneg_left (mul_le_mul hϖζ hκ (norm_nonneg _) hζ0)
        (mul_nonneg hC hw0)
      calc _ = C * w0 * (F.ϖ * ‖torusHigherConstant (n + d l) (1 : ℂ)‖) := by ring
        _ ≤ C * w0 * (ζ * Kc) := h5
        _ = _ := by ring
    refine h1.trans (le_trans (le_of_eq (by ring)) (sl80_sq_le _ _ _ (by positivity) h2 hSg))
  have hB : ∑ i' ∈ S', ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 ≤
      (C * (1 + |ρ|) * ζ * w0) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have hle : C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * (1 + |ρ|) * ζ * w0 := by
      calc C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * ((1 + |ρ|) * ζ) * w0 := by gcongr
        _ = _ := by ring
    have := (hb3 E b).trans (sl80_sq_le _ _ (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) (by positivity) hle hSg
      |> fun h => le_trans (le_of_eq (by ring)) h)
    exact this
  have hZ : ∑ i' ∈ S', ‖∑ i ∈ S, T' i i' (torusHigherScalarCLM N (b i) Dd)‖ ^ 2 ≤
      (C1 * |M₀| * (1 + |ρ|) * ζ * w0) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have h1 := hT'b S S' x x' β β' hS hS' (fun i => torusHigherScalarCLM N (b i) Dd)
    have e : C1 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
        then 1 else 0) * letterCompWeight (F.letters l) x x' = C1 * w0 := by
      simp only [w0]; ring
    rw [e, sl80_scal_norm_sq] at h1
    have hD' : ‖Dd‖ ≤ (|M₀| * ((1 + |ρ|) * ζ)) * ‖E‖ := by
      have : M₀ * fibreNorm (planeFibreFrequency F.η θ) ≤ |M₀| * ((1 + |ρ|) * ζ) :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) hx0).trans
          (mul_le_mul_of_nonneg_left hxζ (abs_nonneg _))
      exact hD.trans (mul_le_mul_of_nonneg_right this (norm_nonneg _))
    have hD2 : ‖Dd‖ ^ 2 ≤ (|M₀| * ((1 + |ρ|) * ζ)) ^ 2 * ‖E‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hD' 2
    have hbs : 0 ≤ ∑ i ∈ S, ‖b i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine h1.trans ?_
    calc (C1 * w0) ^ 2 * (‖Dd‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)
        ≤ (C1 * w0) ^ 2 * ((|M₀| * ((1 + |ρ|) * ζ)) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD2 hbs) (sq_nonneg _)
      _ = _ := by ring
  have key := sl80_sum3 S' (fun i' => ‖∑ i ∈ S, T i i' (f i)‖)
    (fun i' => ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖)
    (fun i' => ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖)
    (fun i' => ‖∑ i ∈ S, T' i i' (torusHigherScalarCLM N (b i) Dd)‖)
    (Kc * C * ζ * w0) (C * (1 + |ρ|) * ζ * w0) (C1 * |M₀| * (1 + |ρ|) * ζ * w0)
    (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) (by positivity) (by positivity) (by positivity) hSg
    (fun _ _ => norm_nonneg _) hpt hA hB hZ
  refine key.trans (le_of_eq ?_)
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the gain / zero split of the letter families (definitions and step (i))

`letterGamP P` is `letterGam` with the transfer index `a` restricted to the predicate `P`.
`slSel g β β₀ a` says that `a` is a gain index (`g = true`: `1 ≤ |β| - |β₀| + |a|`) or a zero index.
`letterGfamP g` is `letterGfam` built from the filtered `letterGam`.  The gain and the zero family add
up to `letterGfam` (`slGfam_split`).  `SlBlockSplit` is the bundle of the operator facts of one block
at one Sobolev level. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

open Classical in
/-- `letterGam` restricted to the transfer indices `a` with `P a`. -/
def letterGamP (P : ℕ × ℕ → Prop) (θ : Vec 2) (pos : Bool) (slow : ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (d : ℕ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2) (β₀ : ℕ × ℕ)
    (k : Fin 2) (β' : ℕ × ℕ) (ψ : Vec 2 → ℂ) : Vec 2 → ℂ := fun z =>
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
    ∑ ω : DerivativeWord2 s,
      (((δ ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
            Finset.range ((wordCount α).2 + 1),
          if β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) ∧ P a then
            ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                (β₀.1 + (wordCount ω).1).descFactorial a.1 *
                (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
              fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                (fun z' => ((iteratedFDeriv ℝ s (fun X => coeff α r X z' k) X₀
                  (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z)
          else 0)

/-- The gain indices (`g = true`) and the zero indices (`g = false`) of the transfer `a` from the
moment `β` to the moment `β₀`. -/
def slSel (g : Bool) (β β₀ a : ℕ × ℕ) : Prop :=
  if g then 1 ≤ β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)
  else ¬ 1 ≤ β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)

theorem letterGam_split (P : ℕ × ℕ → Prop) (θ : Vec 2) (pos : Bool) (slow : ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (d : ℕ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (β₀ : ℕ × ℕ) (k : Fin 2) (β' : ℕ × ℕ) (ψ : Vec 2 → ℂ) (z : Vec 2) :
    letterGam θ pos slow δ X₀ r d coeff β₀ k β' ψ z =
      letterGamP P θ pos slow δ X₀ r d coeff β₀ k β' ψ z +
        letterGamP (fun a => ¬ P a) θ pos slow δ X₀ r d coeff β₀ k β' ψ z := by
  classical
  unfold letterGam letterGamP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) <;>
    by_cases h2 : P a <;> simp [h1, h2]

section Fam

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

open Classical in
/-- The family `letterGfam` built from the filtered `letterGam`: gain (`g = true`) or zero part. -/
def letterGfamP (g : Bool) (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) :
    Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → (Vec 2 → ℂ) → Vec 2 → ℂ :=
  fun b b' f z =>
    ((letterVars β).map fun w => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
      ((L.edge x x' ⟨d, hd⟩).map fun γ =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((R * w.1 : ℝ) : ℂ) * star (letterGamP (slSel g β w.2.1) θ L.positive L.slow δ X₀ r d
            γ.coeff w.2.1 w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))).sum
      else 0).sum

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
open Classical in
/-- **Step (i).** The gain family and the zero family add up to `letterGfam`. -/
theorem slGfam_split (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) (b : Fin (Module.finrank ℝ (h x)))
    (b' : Fin (Module.finrank ℝ (h x'))) (f : Vec 2 → ℂ) (z : Vec 2) :
    letterGfamP true θ L A δ X₀ r x x' β β' R b b' f z +
        letterGfamP false θ L A δ X₀ r x x' β β' R b b' f z =
      letterGfam θ L A δ X₀ r x x' β β' R b b' f z := by
  unfold letterGfamP letterGfam
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    rw [← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun γ _ => ?_
    rw [← mul_add, ← mul_add, ← star_add]
    congr 3
    exact (letterGam_split (slSel true β w.2.1) _ _ _ _ _ _ _ _ _ _ _ _ _).symm.trans
      (by simp)
  · simp [hd]

end Fam

section Bundle

/-- The constants `ℂ → H^L`, as a real-linear map. -/
def slConstLin (L : ℕ) : ℂ →ₗ[ℝ] TorusHk L ℂ where
  toFun := torusHigherConstant L
  map_add' a b := by
    apply TorusHk.ext_value
    change torusHkValueCLM (torusHigherConstant L (a + b)) =
      torusHkValueCLM (torusHigherConstant L a + torusHigherConstant L b)
    rw [map_add, torusHigherConstant_value, torusHigherConstant_value,
      torusHigherConstant_value, map_add]
  map_smul' c a := by
    apply TorusHk.ext_value
    change torusHkValueCLM (torusHigherConstant L (c • a)) =
      torusHkValueCLM (c • torusHigherConstant L a)
    rw [map_smul, torusHigherConstant_value, torusHigherConstant_value, map_smul]

/-- The constants `ℂ → H^L`, as a continuous real-linear map. -/
def slConstCLM (L : ℕ) : ℂ →L[ℝ] TorusHk L ℂ := LinearMap.toContinuousLinearMap (slConstLin L)

theorem slConstCLM_apply (L : ℕ) (E : ℂ) : slConstCLM L E = torusHigherConstant L E := rfl

/-- The cell mean of the value of an element of `H^K`. -/
def slMeanOp (K : ℕ) : TorusHk K ℂ →L[ℝ] ℂ := cellMeanCLM.comp torusHkValueCLM

/-- **The bundle of operator facts of one block at the Sobolev level `L`**: the gain operator `Tg`
and the zero operator `Tz` with their value formulas (on `H^N`, `N ≥ max L Nmin`, through the truncation), the block norm bound of `Tg`, the block bound of
the mean of `Tz`, the block bound of `Tz` on constants, and the block bound of the mean of `Tg + Tz` on
constants. -/
def SlBlockSplit (L n Nmin : ℕ) {m₁ m₂ : ℕ}
    (Gg Gz : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ) (c1 c2 c3 c4 : ℝ) : Prop :=
  ∃ Tg Tz : Fin m₁ → Fin m₂ → TorusHk L ℂ →L[ℝ] TorusHk n ℂ,
    (∀ (N : ℕ) (hLN : L ≤ N), Nmin ≤ N → ∀ b b' (ψ : TorusHk N ℂ),
      (torusHkValueCLM (Tg b b' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] Gg b b' (torusHigherClassicalValue N ψ)) ∧
    (∀ (N : ℕ) (hLN : L ≤ N), Nmin ≤ N → ∀ b b' (ψ : TorusHk N ℂ),
      (torusHkValueCLM (Tz b b' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] Gz b b' (torusHigherClassicalValue N ψ)) ∧
    BlockBound c1 Tg ∧
    BlockBound c2 (fun b b' => (slMeanOp n).comp (Tz b b')) ∧
    BlockBound c3 (fun b b' => (Tz b b').comp (slConstCLM L)) ∧
    BlockBound c4 (fun b b' => (slMeanOp n).comp ((Tg b b' + Tz b b').comp (slConstCLM L)))

end Bundle

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # `SharpLetterSlowPairFact` from the helpers `SharpLetterGainFact`, `SharpLetterConstMeanFact` -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

theorem sl80_sum4 {α : Type*} (s : Finset α) (a x y z w : α → ℝ) (P Q R W Sg : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hW : 0 ≤ W) (hSg : 0 ≤ Sg)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hle : ∀ i ∈ s, a i ≤ x i + (y i + z i) + w i)
    (h1 : ∑ i ∈ s, x i ^ 2 ≤ P ^ 2 * Sg) (h2 : ∑ i ∈ s, y i ^ 2 ≤ Q ^ 2 * Sg)
    (h3 : ∑ i ∈ s, z i ^ 2 ≤ R ^ 2 * Sg) (h4 : ∑ i ∈ s, w i ^ 2 ≤ W ^ 2 * Sg) :
    ∑ i ∈ s, a i ^ 2 ≤ (P + (Q + R) + W) ^ 2 * Sg := by
  have hs := Real.sqrt_nonneg Sg
  have hsq : Real.sqrt Sg ^ 2 = Sg := Real.sq_sqrt hSg
  have e : ∀ T : ℝ, T ^ 2 * Sg = (T * Real.sqrt Sg) ^ 2 := fun T => by rw [mul_pow, hsq]
  have m23 := sl80_l2_add s y z _ _ (mul_nonneg hQ hs) (mul_nonneg hR hs)
    (by rw [← e]; exact h2) (by rw [← e]; exact h3)
  refine le_trans ?_ (sl80_sum3 s a x (fun i => y i + z i) w P (Q + R) W Sg hP (add_nonneg hQ hR) hW
    hSg ha hle h1 (by rw [e]; refine m23.trans (le_of_eq ?_); ring) h4)
  exact le_rfl

theorem sl80_Dd_bound (M₀ X ρ ζ d e : ℝ) (hx0 : 0 ≤ X) (hxζ : X ≤ (1 + |ρ|) * ζ) (he : 0 ≤ e)
    (hD : d ≤ M₀ * X * e) : d ≤ (|M₀| * ((1 + |ρ|) * ζ)) * e := by
  have : M₀ * X ≤ |M₀| * ((1 + |ρ|) * ζ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hx0).trans
      (mul_le_mul_of_nonneg_left hxζ (abs_nonneg _))
  exact hD.trans (mul_le_mul_of_nonneg_right this he)

theorem sl80_norm3 (a b c : ℂ) (g : ℝ) (hb : ‖b‖ ≤ g) : ‖a + (b + c)‖ ≤ ‖a‖ + (g + ‖c‖) :=
  (norm_add_le a (b + c)).trans
    (add_le_add le_rfl ((norm_add_le b c).trans (add_le_add hb le_rfl)))

theorem sl80_pair_alg {n : ℕ} (R : ComplexCellL2) (Ua Ug U0 U : TorusHk n ℂ)
    (hU : U = Ua + (Ug + U0)) :
    ‖sharpPair R U‖ ≤ ‖cellMeanCLM (torusHkValueCLM Ua)‖ +
      (‖Ug‖ + ‖cellMeanCLM (torusHkValueCLM U0)‖) + ‖R‖ * ‖U‖ := by
  have h1 : ‖cellMeanCLM (torusHkValueCLM Ug)‖ ≤ ‖Ug‖ :=
    (cellMeanCLM_norm_le _).trans (sharp_value_norm_le _)
  refine (sharpPair_le_mean R _).trans ?_
  have hm : cellMeanCLM (torusHkValueCLM U) = cellMeanCLM (torusHkValueCLM Ua) +
      (cellMeanCLM (torusHkValueCLM Ug) + cellMeanCLM (torusHkValueCLM U0)) := by
    rw [hU]; simp only [map_add]
  rw [hm]
  exact add_le_add (sl80_norm3 _ _ _ _ h1) le_rfl

section Pieces

variable {I I' : Type*} {N n : ℕ}

/-- Pointwise decomposition of the pairing of the slow family. -/
theorem sl80_pair_decomp (S : Finset I) (T Tg T0 : I → I' → TorusHk N ℂ →L[ℝ] TorusHk n ℂ)
    (i' : I') (eqsplit : ∀ i ∈ S, ∀ ψ, T i i' ψ = Tg i i' ψ + T0 i i' ψ) (R : ComplexCellL2)
    (E : ℂ) (b : I → ℂ) (Dd : TorusHk N ℂ) (f : I → TorusHk N ℂ)
    (hf : ∀ i ∈ S, f i = torusHigherScalarCLM N (b i) (torusHigherConstant N E + Dd)) :
    ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ≤
      ‖cellMeanCLM (torusHkValueCLM
        (∑ i ∈ S, T i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))))‖ +
      (‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) Dd)‖ +
        ‖cellMeanCLM (torusHkValueCLM
          (∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) Dd)))‖) +
      ‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖ := by
  refine sl80_pair_alg R _ _ _ _ ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hf i hi, map_add, map_add, eqsplit i hi (torusHigherScalarCLM N (b i) Dd)]

end Pieces

theorem sl80_Dd_transfer (A c μ dd e bs : ℝ) (hbs : 0 ≤ bs) (hdd : dd ^ 2 ≤ μ ^ 2 * e ^ 2)
    (h : A ≤ c ^ 2 * (dd ^ 2 * bs)) : A ≤ (c * μ) ^ 2 * (e ^ 2 * bs) := by
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_right hdd hbs
  calc c ^ 2 * (dd ^ 2 * bs) ≤ c ^ 2 * (μ ^ 2 * e ^ 2 * bs) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = _ := by ring

open Classical in
/-- **The slow-slow pairing fact** from the gain split, the plain letter bound (through the slow-test
norm fact) and the mean of the full family on constants. -/
theorem sharpLetterSlowPair_of (hG : SharpLetterGainFact.{u, v})
    (hM : SharpLetterConstMeanFact.{u, v}) : SharpLetterSlowPairFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n M₀
  obtain ⟨C, hC, kG⟩ := hG K Nw D m d Ks pos ρ n
  obtain ⟨C4, hC4, k4⟩ := hM K Nw D m d Ks pos ρ n
  obtain ⟨C3, hC3, k3⟩ := sharpLetterSlowNorm_of_gain.{u, v} hG K Nw D m d Ks pos ρ n M₀
  refine ⟨C4 + C * |M₀| * (1 + |ρ|) + C * (1 + |ρ|) * (|M₀| * (1 + |ρ|)) +
    |M₀| * (1 + |ρ|) * C3, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [kG g₁ F θ hlet hJ hρ, k4 g₁ F θ hlet hJ hρ, k3 g₁ F θ hlet hJ hρ]
    with r a1 a4 a3
  intro l N hN1 hN2
  obtain ⟨Tg, T0, hv, hb⟩ := a1 l N hN1 hN2
  intro T hTv S S' x x' β β' hS hS' w0 ζ E b Dd hD f hf R hR
  obtain ⟨hb1, hb2, -⟩ := hb S S' x x' β β' hS hS'
  have hx4 := a4 l N hN1 hN2 T hTv S S' x x' β β' hS hS' E b
  have hx3 := a3 l N hN1 hN2 T hTv S S' x x' β β' hS hS' E b Dd hD f hf
  obtain ⟨hϖ0, hϖζ⟩ := sl80_varpi F θ
  obtain ⟨hζ0, hxζ⟩ := sl80_zeta F θ ρ hρ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hbs : 0 ≤ ∑ i ∈ S, ‖b i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSg : 0 ≤ ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 := mul_nonneg (sq_nonneg _) hbs
  have eqsplit : ∀ i ∈ S, ∀ i' ∈ S', ∀ ψ, T i i' ψ = Tg i i' ψ + T0 i i' ψ :=
    fun i hi i' hi' ψ => sl80_split hTv hv i i' (hS i hi).1 (hS' i' hi').1 ψ
  have hpt := fun i' (hi' : i' ∈ S') => sl80_pair_decomp S T Tg T0 i'
    (fun i hi ψ => eqsplit i hi i' hi' ψ) R E b Dd f hf
  have hμ0 : 0 ≤ |M₀| * ((1 + |ρ|) * ζ) := by positivity
  have hD' := sl80_Dd_bound M₀ _ ρ ζ _ _ hx0 hxζ (norm_nonneg E) hD
  have hD2 : ‖Dd‖ ^ 2 ≤ (|M₀| * ((1 + |ρ|) * ζ)) ^ 2 * ‖E‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  -- the Tg part
  have hX2 : ∑ i' ∈ S', ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) Dd)‖ ^ 2 ≤
      (C * ζ * w0 * (|M₀| * ((1 + |ρ|) * ζ))) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have h1 := hb1 (fun i => torusHigherScalarCLM N (b i) Dd)
    have h2 : ∑ i ∈ S, ‖truncateTorusHk hN1 (torusHigherScalarCLM N (b i) Dd)‖ ^ 2 ≤
        ‖Dd‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 := by
      rw [← sl80_scal_norm_sq S N b Dd]
      exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
        (truncateTorusHk_norm_le _ _) 2
    have h3 := sl80_Dd_transfer _ (C * F.ϖ * w0) _ _ _ _ hbs hD2
      (h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)))
    exact h3.trans (sl80_sq_le _ _ _ (by positivity) (by gcongr) hSg)
  have hX3 : ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM
        (∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) Dd)))‖ ^ 2 ≤
      (C * (1 + |ρ|) * ζ * w0 * (|M₀| * ((1 + |ρ|) * ζ))) ^ 2 *
        (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have h1 := hb2 (fun i => torusHigherScalarCLM N (b i) Dd)
    rw [sl80_scal_norm_sq] at h1
    have h3 := sl80_Dd_transfer _ (C * fibreNorm (planeFibreFrequency F.η θ) * w0) _ _ _ _ hbs hD2 h1
    have hle : C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * (1 + |ρ|) * ζ * w0 := by
      calc C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * ((1 + |ρ|) * ζ) * w0 := by gcongr
        _ = _ := by ring
    exact h3.trans (sl80_sq_le _ _ _ (by positivity) (by gcongr) hSg)
  have hX4 : ∑ i' ∈ S', (‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖) ^ 2 ≤
      ((|M₀| * ((1 + |ρ|) * ζ)) * (C3 * ζ * w0)) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
    have hR' : ‖R‖ ≤ |M₀| * ((1 + |ρ|) * ζ) :=
      hR.trans (mul_le_mul_of_nonneg_left hxζ (abs_nonneg _))
    calc ∑ i' ∈ S', (‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖) ^ 2
        = ‖R‖ ^ 2 * ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ‖R‖ ^ 2 * ((C3 * ζ * w0) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact hx3) (sq_nonneg _)
      _ ≤ (|M₀| * ((1 + |ρ|) * ζ)) ^ 2 * ((C3 * ζ * w0) ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR' 2)
            (mul_nonneg (sq_nonneg _) hSg)
      _ = _ := by ring
  have key := sl80_sum4 S' (fun i' => ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖)
    (fun i' => ‖cellMeanCLM (torusHkValueCLM
      (∑ i ∈ S, T i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))))‖)
    (fun i' => ‖∑ i ∈ S, Tg i i' (torusHigherScalarCLM N (b i) Dd)‖)
    (fun i' => ‖cellMeanCLM (torusHkValueCLM
      (∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) Dd)))‖)
    (fun i' => ‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖)
    (C4 * ζ ^ 2 * w0) (C * ζ * w0 * (|M₀| * ((1 + |ρ|) * ζ)))
    (C * (1 + |ρ|) * ζ * w0 * (|M₀| * ((1 + |ρ|) * ζ)))
    ((|M₀| * ((1 + |ρ|) * ζ)) * (C3 * ζ * w0)) (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity) hSg
    (fun _ _ => norm_nonneg _) hpt (by rw [← mul_assoc]; exact hx4) hX2 hX3 hX4
  refine key.trans (le_of_eq ?_)
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # from block bounds to bounds on index families

`slBlockReduce` is `block_reduce` for an arbitrary pair of target spaces.  `slIdx` is the passage from
the block operators of the components `x, x'` and moments `β, β'` to the operators indexed by the basis
indices of the stages (the end of `letterOps`), for any family of block operators. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

section Reduce

variable {m₁ m₂ : ℕ} {I I' : Type*} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

open Classical in
/-- `block_reduce` for arbitrary source and target spaces. -/
theorem slBlockReduce (Top : Fin m₁ → Fin m₂ → X →L[ℝ] Y) (c : ℝ)
    (hT : BlockBound c Top) (mk : Fin m₁ → I) (mk' : Fin m₂ → I') (hmk : Function.Injective mk)
    (hmk' : Function.Injective mk') (T : I → I' → X →L[ℝ] Y)
    (hTm : ∀ b b', T (mk b) (mk' b') = Top b b') (S : Finset I) (S' : Finset I')
    (hS : ∀ i ∈ S, ∃ b, mk b = i) (hS' : ∀ i' ∈ S', ∃ b', mk' b' = i') (f : I → X) :
    ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤ c ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  set S₀ : Finset (Fin m₁) := Finset.univ.filter fun b => mk b ∈ S with hS₀
  set S₀' : Finset (Fin m₂) := Finset.univ.filter fun b' => mk' b' ∈ S' with hS₀'
  have e1 : S = S₀.image mk := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, rfl⟩ := hS i hi
      exact Finset.mem_image.2 ⟨b, by simp [hS₀, hi], rfl⟩
    · intro hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_filter.1 hb).2
  have e2 : S' = S₀'.image mk' := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, rfl⟩ := hS' i hi
      exact Finset.mem_image.2 ⟨b, by simp [hS₀', hi], rfl⟩
    · intro hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_filter.1 hb).2
  set g : Fin m₁ → X := fun b => if b ∈ S₀ then f (mk b) else 0 with hg
  have inner_eq : ∀ b' : Fin m₂, ∑ i ∈ S, T i (mk' b') (f i) = ∑ b, Top b b' (g b) := by
    intro b'
    rw [e1, Finset.sum_image (fun a _ b _ hab => hmk hab)]
    simp only [hTm]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S₀)]
    have : ∑ b ∈ Finset.univ.filter (fun b => b ∈ S₀), Top b b' (g b) =
        ∑ b ∈ S₀, Top b b' (f (mk b)) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun b hb => by simp [hg, hb]
    rw [this]
    have h0 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ S₀), Top b b' (g b) = 0 :=
      Finset.sum_eq_zero fun b hb => by simp [hg, (Finset.mem_filter.1 hb).2]
    rw [h0, add_zero]
  calc ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2
      = ∑ b' ∈ S₀', ‖∑ b, Top b b' (g b)‖ ^ 2 := by
        rw [e2, Finset.sum_image (fun a _ b _ hab => hmk' hab)]
        exact Finset.sum_congr rfl fun b' _ => by rw [inner_eq]
    _ ≤ ∑ b', ‖∑ b, Top b b' (g b)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    _ ≤ c ^ 2 * ∑ b, ‖g b‖ ^ 2 := hT.2 g
    _ = c ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
        congr 1
        rw [e1, Finset.sum_image (fun a _ b _ hab => hmk hab)]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S₀)]
        have h1 : ∑ b ∈ Finset.univ.filter (fun b => b ∈ S₀), ‖g b‖ ^ 2 =
            ∑ b ∈ S₀, ‖f (mk b)‖ ^ 2 := by
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          exact Finset.sum_congr rfl fun b hb => by simp [hg, hb]
        have h0 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ S₀), ‖g b‖ ^ 2 = 0 :=
          Finset.sum_eq_zero fun b hb => by simp [hg, (Finset.mem_filter.1 hb).2]
        rw [h1, h0, add_zero]

end Reduce

section Idx

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The block operators of the stages `(x, β), (x', β')` of the levels `l.succ, l.castSucc`, assembled
into an operator family on the basis indices. -/
def slIdxOp (M0 : ℕ)
    (Top : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → X →L[ℝ] Y)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (i i' : B1WIndex ι h Nw m Ks) : X →L[ℝ] Y :=
  Top i.2.1 i'.2.1 (b1wMom i) (b1wMom i') (hM i) (hM i') i.2.2.2 i'.2.2.2

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- **The block bound for the indexed family.** -/
theorem slIdx (M0 : ℕ)
    (Top : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → X →L[ℝ] Y)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (c : ι → ι → ℕ × ℕ → ℕ × ℕ → ℝ)
    (hc : ∀ x x' β β' (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0),
      BlockBound (c x x' β β') (Top x x' β β' hβ hβ'))
    (l : Fin Nw) (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ)
    (hS : ∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β))
    (hS' : ∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) (f : B1WIndex ι h Nw m Ks → X) :
    ∑ i' ∈ S', ‖∑ i ∈ S, slIdxOp M0 Top hM i i' (f i)‖ ^ 2 ≤
      (c x x' β β') ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  classical
  by_cases hSe : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hSe]
    simp
  by_cases hSe' : S'.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hSe']
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨i0, hi0⟩ := hSe
  obtain ⟨i0', hi0'⟩ := hSe'
  obtain ⟨hβ, b0, -⟩ := stage_eq i0 l.succ x β ⟨(hS i0 hi0).1, (hS i0 hi0).2⟩
  obtain ⟨hβ', b0', -⟩ := stage_eq i0' l.castSucc x' β' ⟨(hS' i0' hi0').1, (hS' i0' hi0').2⟩
  let mk : Fin (Module.finrank ℝ (h x)) → B1WIndex ι h Nw m Ks := fun b =>
    ⟨l.succ, x, ⟨β, hβ⟩, b⟩
  let mk' : Fin (Module.finrank ℝ (h x')) → B1WIndex ι h Nw m Ks := fun b =>
    ⟨l.castSucc, x', ⟨β', hβ'⟩, b⟩
  have hMb : β.1 + β.2 ≤ M0 := hM (mk b0)
  have hMb' : β'.1 + β'.2 ≤ M0 := hM (mk' b0')
  exact slBlockReduce (Top x x' β β' hMb hMb') _ (hc x x' β β' hMb hMb') mk mk'
    (fun a b hab => by simpa [mk] using hab) (fun a b hab => by simpa [mk'] using hab)
    (slIdxOp M0 Top hM) (fun b b' => rfl) S S'
    (fun i hi => by
      obtain ⟨hβi, b, hb⟩ := stage_eq i l.succ x β ⟨(hS i hi).1, (hS i hi).2⟩
      exact ⟨b, hb.symm⟩)
    (fun i hi => by
      obtain ⟨hβi, b, hb⟩ := stage_eq i l.castSucc x' β' ⟨(hS' i hi).1, (hS' i hi).2⟩
      exact ⟨b, hb.symm⟩) f

end Idx

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the indexed operators of the letter split from the block operators

`slOps_of_blocks`: given, for every pair of components and moments, the block bundle `SlBlockSplit` at
the level `L ≤ N`, the operators `Tg, T0` on the basis indices of the stages (composed with the
truncation `H^N → H^L`) have the value formula of the sum, and the four index bounds follow from the
block bounds (`slIdx`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

theorem slTrunc_scalar_const {L N : ℕ} (hLN : L ≤ N) (β E : ℂ) :
    truncateTorusHk hLN (torusHigherScalarCLM N β (torusHigherConstant N E)) =
      slConstCLM L (β * E) := by
  rw [torusHigherConstant_smul, torusHigherConstant_truncate hLN]
  rfl

theorem slMean_sum {I : Type*} (S : Finset I) (n : ℕ) (A : I → TorusHk n ℂ) :
    cellMeanCLM (torusHkValueCLM (∑ i ∈ S, A i)) = ∑ i ∈ S, slMeanOp n (A i) :=
  map_sum (slMeanOp n) A S

theorem slScalar_norm_sq {I : Type*} (S : Finset I) (b : I → ℂ) (E : ℂ) :
    ∑ i ∈ S, ‖b i * E‖ ^ 2 = ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring

section Core

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem slIdx_h2 (n L N : ℕ) (hLN : L ≤ N) (M0 : ℕ)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (Tz : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → TorusHk L ℂ →L[ℝ] TorusHk n ℂ)
    (c2 : ι → ι → ℕ × ℕ → ℕ × ℕ → ℝ)
    (h2 : ∀ x x' β β' (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0),
      BlockBound (X := TorusHk L ℂ) (Y := ℂ) (c2 x x' β β')
        (fun b b' => (slMeanOp n).comp (Tz x x' β β' hβ hβ' b b')))
    (l : Fin Nw) (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ)
    (hS : ∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β))
    (hS' : ∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β'))
    (f : B1WIndex ι h Nw m Ks → TorusHk N ℂ) :
    ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S,
        ((slIdxOp M0 Tz hM i i').comp (truncateTorusHk hLN)) (f i)))‖ ^ 2 ≤
      (c2 x x' β β') ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  have key := slIdx (X := TorusHk L ℂ) (Y := ℂ) M0
    (fun x x' β β' hβ hβ' b b' => (slMeanOp n).comp (Tz x x' β β' hβ hβ' b b'))
    hM c2 h2 l S S' x x' β β' hS hS' (fun i => truncateTorusHk hLN (f i))
  have hn : ∑ i ∈ S, ‖truncateTorusHk hLN (f i)‖ ^ 2 ≤ ∑ i ∈ S, ‖f i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
      (truncateTorusHk_norm_le hLN _) 2
  refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _)))
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [slMean_sum]
  simp only [slIdxOp, ContinuousLinearMap.comp_apply]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem slIdx_h3 (n L N : ℕ) (hLN : L ≤ N) (M0 : ℕ)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (Tz : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → TorusHk L ℂ →L[ℝ] TorusHk n ℂ)
    (c3 : ι → ι → ℕ × ℕ → ℕ × ℕ → ℝ)
    (h3 : ∀ x x' β β' (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0),
      BlockBound (X := ℂ) (Y := TorusHk n ℂ) (c3 x x' β β')
        (fun b b' => (Tz x x' β β' hβ hβ' b b').comp (slConstCLM L)))
    (l : Fin Nw) (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ)
    (hS : ∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β))
    (hS' : ∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β'))
    (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ) :
    ∑ i' ∈ S', ‖∑ i ∈ S, ((slIdxOp M0 Tz hM i i').comp (truncateTorusHk hLN))
        (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 ≤
      (c3 x x' β β') ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
  have key := slIdx (X := ℂ) (Y := TorusHk n ℂ) M0
    (fun x x' β β' hβ hβ' b b' => (Tz x x' β β' hβ hβ' b b').comp (slConstCLM L))
    hM c3 h3 l S S' x x' β β' hS hS' (fun i => b i * E)
  rw [slScalar_norm_sq] at key
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun i' _ => ?_
  congr 2
  simp only [slIdxOp, ContinuousLinearMap.comp_apply, slTrunc_scalar_const]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem slIdx_h4 (n L N : ℕ) (hLN : L ≤ N) (M0 : ℕ)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (Tg Tz : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → TorusHk L ℂ →L[ℝ] TorusHk n ℂ)
    (c4 : ι → ι → ℕ × ℕ → ℕ × ℕ → ℝ)
    (h4 : ∀ x x' β β' (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0),
      BlockBound (X := ℂ) (Y := ℂ) (c4 x x' β β')
        (fun b b' => (slMeanOp n).comp
          ((Tg x x' β β' hβ hβ' b b' + Tz x x' β β' hβ hβ' b b').comp (slConstCLM L))))
    (l : Fin Nw) (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ)
    (hS : ∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β))
    (hS' : ∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β'))
    (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ) :
    ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S,
        (((slIdxOp M0 Tg hM i i').comp (truncateTorusHk hLN)) +
          ((slIdxOp M0 Tz hM i i').comp (truncateTorusHk hLN)))
          (torusHigherScalarCLM N (b i) (torusHigherConstant N E))))‖ ^ 2 ≤
      (c4 x x' β β') ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2) := by
  have key := slIdx (X := ℂ) (Y := ℂ) M0
    (fun x x' β β' hβ hβ' b b' => (slMeanOp n).comp
      ((Tg x x' β β' hβ hβ' b b' + Tz x x' β β' hβ hβ' b b').comp (slConstCLM L)))
    hM c4 h4 l S S' x x' β β' hS hS' (fun i => b i * E)
  rw [slScalar_norm_sq] at key
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun i' _ => ?_
  congr 2
  rw [slMean_sum]
  simp only [slIdxOp, ContinuousLinearMap.comp_apply, add_apply,
    slTrunc_scalar_const]

open Classical in
theorem slIdx_value (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (θ : Vec 2) (r : ℝ) (l : Fin Nw) (n N L : ℕ) (hLN : L ≤ N) (M0 : ℕ)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (Tg Tz : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → TorusHk L ℂ →L[ℝ] TorusHk n ℂ)
    (hvg : ∀ (x x' : ι) (β β' : ℕ × ℕ) (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0)
      (b : Fin (Module.finrank ℝ (h x))) (b' : Fin (Module.finrank ℝ (h x'))) (ψ : TorusHk N ℂ),
      (torusHkValueCLM (Tg x x' β β' hβ hβ' b b' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube]
          letterGfamP true θ (F.letters l)
            (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
              (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
            (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β') b b'
            (torusHigherClassicalValue N ψ))
    (hvz : ∀ (x x' : ι) (β β' : ℕ × ℕ) (hβ : β.1 + β.2 ≤ M0) (hβ' : β'.1 + β'.2 ≤ M0)
      (b : Fin (Module.finrank ℝ (h x))) (b' : Fin (Module.finrank ℝ (h x'))) (ψ : TorusHk N ℂ),
      (torusHkValueCLM (Tz x x' β β' hβ hβ' b b' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube]
          letterGfamP false θ (F.letters l)
            (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
              (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
            (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β') b b'
            (torusHigherClassicalValue N ψ))
    (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (ψ : TorusHk N ℂ) :
    (torusHkValueCLM (((slIdxOp M0 Tg hM i i').comp (truncateTorusHk hLN)) ψ +
        ((slIdxOp M0 Tz hM i i').comp (truncateTorusHk hLN)) ψ) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
        b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          star (b1wLetterTransform F θ i i' r
            (fun y => star (torusHigherClassicalValue N ψ y)) z) := by
  have e1 : (torusHkValueCLM (slIdxOp M0 Tg hM i i' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] _ :=
    hvg i.2.1 i'.2.1 (b1wMom i) (b1wMom i') (hM i) (hM i') i.2.2.2 i'.2.2.2 ψ
  have e2 : (torusHkValueCLM (slIdxOp M0 Tz hM i i' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] _ :=
    hvz i.2.1 i'.2.1 (b1wMom i) (b1wMom i') (hM i) (hM i') i.2.2.2 i'.2.2.2 ψ
  simp only [ContinuousLinearMap.comp_apply]
  rw [map_add]
  filter_upwards [Lp.coeFn_add (torusHkValueCLM (slIdxOp M0 Tg hM i i' (truncateTorusHk hLN ψ)))
    (torusHkValueCLM (slIdxOp M0 Tz hM i i' (truncateTorusHk hLN ψ))), e1, e2] with z ha hb hc
  rw [ha, Pi.add_apply]
  rw [hb, hc, b1wScaleRatio_letter F.π F.ϖ F.ηg F.letters l i i' hi hi',
    ratio_star_letterTransform F θ l i i' hi hi' r _ z, slGfam_split]

open Classical in
theorem slOps_of_blocks (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (θ : Vec 2) (r : ℝ) (l : Fin Nw) (n N L Nmin : ℕ) (hLN : L ≤ N) (hNmin : Nmin ≤ N) (M0 : ℕ)
    (hM : ∀ i : B1WIndex ι h Nw m Ks, (b1wMom i).1 + (b1wMom i).2 ≤ M0)
    (c1 c2 c3 c4 : ι → ι → ℕ × ℕ → ℕ × ℕ → ℝ)
    (hblk : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      SlBlockSplit L n Nmin
        (letterGfamP true θ (F.letters l)
          (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
            (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (letterGfamP false θ (F.letters l)
          (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x)
            (l.castSucc, x')) (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (c1 x x' β β') (c2 x x' β β') (c3 x x' β β') (c4 x x' β β')) :
    ∃ Tg T0 : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
      (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
        (torusHkValueCLM (Tg i i' ψ + T0 i i' ψ) : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
            b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wLetterTransform F θ i i' r
                (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
      ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
        (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
        (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
        (∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
          ∑ i' ∈ S', ‖∑ i ∈ S, Tg i i' (f i)‖ ^ 2 ≤
            (c1 x x' β β') ^ 2 * ∑ i ∈ S, ‖truncateTorusHk hLN (f i)‖ ^ 2) ∧
        (∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
          ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i)))‖ ^ 2 ≤
            (c2 x x' β β') ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) ∧
        (∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ),
          ∑ i' ∈ S', ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 ≤
            (c3 x x' β β') ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)) ∧
        (∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ),
          ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, (Tg i i' + T0 i i')
              (torusHigherScalarCLM N (b i) (torusHigherConstant N E))))‖ ^ 2 ≤
            (c4 x x' β β') ^ 2 * (‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)) := by
  choose Tg Tz hvg hvz h1 h2 h3 h4 using hblk
  refine ⟨fun i i' => (slIdxOp M0 Tg hM i i').comp (truncateTorusHk hLN),
    fun i i' => (slIdxOp M0 Tz hM i i').comp (truncateTorusHk hLN),
    fun i i' hi hi' ψ => slIdx_value F θ r l n N L hLN M0 hM Tg Tz
      (fun x x' β β' hβ hβ' b b' ψ => hvg x x' β β' hβ hβ' N hLN hNmin b b' ψ)
      (fun x x' β β' hβ hβ' b b' ψ => hvz x x' β β' hβ hβ' N hLN hNmin b b' ψ) i i' hi hi' ψ,
    fun S S' x x' β β' hS hS' => ⟨fun f => ?_, fun f => ?_, fun E b => ?_, fun E b => ?_⟩⟩
  · exact slIdx (X := TorusHk L ℂ) (Y := TorusHk n ℂ) M0 Tg hM c1 h1 l S S' x x' β β' hS hS' (fun i => truncateTorusHk hLN (f i))
  · exact slIdx_h2 n L N hLN M0 hM Tz c2 h2 l S S' x x' β β' hS hS' f
  · exact slIdx_h3 n L N hLN M0 hM Tz c3 h3 l S S' x x' β β' hS hS' E b
  · exact slIdx_h4 n L N hLN M0 hM Tg Tz c4 h4 l S S' x x' β β' hS hS' E b

end Core

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the mean of the twisted derivative chain, and the twisted derivative of a constant

The mean of the value of `(∂_k + iθ_k)^m U` is `(iθ_k)^m` times the mean of the value of `U`
(a periodic derivative integrates to zero), hence the mean of `powOp θ n p q U` is
`(iθ_0)^p (iθ_1)^q` times the mean of `U`.  Also `(∂_k + iθ_k)` of a constant is a constant. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

theorem sl86_value_tbDeriv (K : ℕ) (k : Fin 2) (U : TorusHk (K + 1) ℂ) :
    torusHkValueCLM (tbDeriv K k U) =
      cellDerivativeCLM k (truncateTorusHk (Nat.le_add_left 1 K) U) := by
  change (tbDeriv K k U).val (valueIndex2 K) = _
  have := derivativeTorusHk_value_slot (L := K) (r := 1) (fun _ => k) U
  change (derivativeTorusHk (K := K) (r := 1) (fun _ => k) U).val (valueIndex2 K) = _
  rw [this]
  change _ = (truncateTorusHk (Nat.le_add_left 1 K) U).val ⟨⟨1, by decide⟩, fun _ => k⟩
  simp only [truncateTorusHk_apply]
  rfl

theorem sl86_mean_tbDeriv (K : ℕ) (k : Fin 2) (U : TorusHk (K + 1) ℂ) :
    cellMeanCLM (torusHkValueCLM (tbDeriv K k U)) = 0 := by
  rw [sl86_value_tbDeriv, cellMeanCLM_apply]
  exact AVRegularity.CycleDamping.cellDerivative_mean_zero k _

theorem sl86_mean_tbTwist (K : ℕ) (θ : Vec 2) (k : Fin 2) (U : TorusHk (K + 1) ℂ) :
    cellMeanCLM (torusHkValueCLM (tbTwist K θ k U)) =
      Complex.I * (θ k : ℂ) * cellMeanCLM (torusHkValueCLM U) := by
  have he : torusHkValueCLM (tbTwist K θ k U) = torusHkValueCLM (tbDeriv K k U) +
      cellScalarCLM (Complex.I * (θ k : ℂ)) (torusHkValueCLM (tbTrunc K U)) := by
    change torusHkValueCLM (tbDeriv K k U +
      torusHigherScalarCLM K (Complex.I * (θ k : ℂ)) (tbTrunc K U)) = _
    rw [map_add, torusHigherScalarCLM_value]
  rw [he, map_add, sl86_mean_tbDeriv, zero_add, cellMeanCLM_complex_scalar]
  rfl

theorem sl86_mean_twIter (θ : Vec 2) (k : Fin 2) (K : ℕ) :
    ∀ (m : ℕ) (U : TorusHk (K + m) ℂ), cellMeanCLM (torusHkValueCLM (twIter θ k K m U)) =
      (Complex.I * (θ k : ℂ)) ^ m * cellMeanCLM (torusHkValueCLM U)
  | 0, U => by simp [twIter]
  | m + 1, U => by
    change cellMeanCLM (torusHkValueCLM (twIter θ k K m (tbTwist (K + m) θ k U))) = _
    rw [sl86_mean_twIter θ k K m, sl86_mean_tbTwist]
    ring

theorem sl86_mean_powOp (θ : Vec 2) (n p q : ℕ) (U : TorusHk (n + p + q) ℂ) :
    cellMeanCLM (torusHkValueCLM (powOp θ n p q U)) =
      (Complex.I * (θ 0 : ℂ)) ^ p * (Complex.I * (θ 1 : ℂ)) ^ q * cellMeanCLM (torusHkValueCLM U) := by
  change cellMeanCLM (torusHkValueCLM (twIter θ 0 n p (twIter θ 1 (n + p) q U))) = _
  rw [sl86_mean_twIter, sl86_mean_twIter]
  ring

theorem sl86_twist_const (n : ℕ) (θ : Vec 2) (k : Fin 2) (E : ℂ) :
    tbTwist n θ k (torusHigherConstant (n + 1) E) =
      torusHigherConstant n (Complex.I * (θ k : ℂ) * E) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (tbTwist n θ k (torusHigherConstant (n + 1) E)) =
    torusHkValueCLM (torusHigherConstant n (Complex.I * (θ k : ℂ) * E))
  apply Lp.ext
  have hv : (torusHkValueCLM (torusHigherConstant (n + 1) E) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => E := by
    rw [torusHigherConstant_value]; exact cellConstantCLM_ae E
  have hc : (torusHkValueCLM (torusHigherConstant n (Complex.I * (θ k : ℂ) * E)) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => Complex.I * (θ k : ℂ) * E := by
    rw [torusHigherConstant_value]; exact cellConstantCLM_ae _
  filter_upwards [tbTwist_value_ae n θ k (torusHigherConstant (n + 1) E) (fun _ => E)
    contDiff_const hv, hc] with x hx hc'
  rw [hx, hc']
  simp [fibreCovDeriv]

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # realized unit terms with the four bounds

`RQ L n Nmin G B1 B2 B3 B4`: the functional `G` of the classical value is realized, through the
truncation `H^N → H^L` (`N ≥ max L Nmin`), by an operator `A : H^L → H^n` with the bounds
`‖Aψ‖ ≤ B1‖ψ‖`, `|mean Aψ| ≤ B2‖ψ‖`, `‖A (const z)‖ ≤ B3|z|`, `|mean A (const z)|≤ B4|z|`.
`rq_unit0`, `rq_unit1` are the unit terms `κ D_θ^{(p,q)}(c f)` and `κ D_θ^{(p,q)}(c D_{θ,k} f)`;
the mean carries the factor `|θ_0|^p |θ_1|^q` (and `|θ_k|` for the constants and `unit1`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

/-- A functional of the classical value realized with four bounds. -/
def RQ (L n Nmin : ℕ) (G : (Vec 2 → ℂ) → Vec 2 → ℂ) (B1 B2 B3 B4 : ℝ) : Prop :=
  ∃ A : TorusHk L ℂ →L[ℝ] TorusHk n ℂ,
    (∀ (N : ℕ) (hLN : L ≤ N), Nmin ≤ N → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (A (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] G (torusHigherClassicalValue N ψ)) ∧
    (∀ ψ, ‖A ψ‖ ≤ B1 * ‖ψ‖) ∧ (∀ ψ, ‖slMeanOp n (A ψ)‖ ≤ B2 * ‖ψ‖) ∧
    (∀ z : ℂ, ‖A (slConstCLM L z)‖ ≤ B3 * ‖z‖) ∧
    (∀ z : ℂ, ‖slMeanOp n (A (slConstCLM L z))‖ ≤ B4 * ‖z‖)

theorem sl86_mean_le {K : ℕ} (U : TorusHk K ℂ) : ‖slMeanOp K U‖ ≤ ‖U‖ :=
  (cellMeanCLM_norm_le _).trans (sharp_value_norm_le U)

theorem sl86_const_le {K L : ℕ} (h : K ≤ L) (z : ℂ) :
    ‖torusHigherConstant K z‖ ≤ ‖torusHigherConstant L z‖ := by
  rw [← torusHigherConstant_truncate h]
  exact truncateTorusHk_norm_le h _

theorem sl86_const_norm_le {K L : ℕ} (h : K ≤ L) (z : ℂ) :
    ‖torusHigherConstant K z‖ ≤ ‖torusHigherConstant L 1‖ * ‖z‖ := by
  refine (sl86_const_le h z).trans (le_of_eq ?_)
  rw [torusHigherConstant_norm L z]
  ring

/-- The mean of a unit operator carries the factor `|θ_0|^p |θ_1|^q`. -/
theorem sl86_unit_mean (θ : Vec 2) (n p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (V : TorusHk (n + p + q) ℂ) :
    ‖slMeanOp n (unitOp θ n p q hc hp hP V)‖ ≤
      |θ 0| ^ p * |θ 1| ^ q * (cellDriftNativePrice (n + p + q) * P * ‖V‖) := by
  have h1 : slMeanOp n (unitOp θ n p q hc hp hP V) =
      (Complex.I * (θ 0 : ℂ)) ^ p * (Complex.I * (θ 1 : ℂ)) ^ q *
        slMeanOp (n + p + q) (tbMulCLM (n + p + q) hc hp hP V) := by
    change cellMeanCLM (torusHkValueCLM (powOp θ n p q (tbMulCLM (n + p + q) hc hp hP V))) = _
    rw [sl86_mean_powOp]
    rfl
  rw [h1, norm_mul, norm_mul, norm_pow, norm_pow]
  have e0 : ‖Complex.I * (θ 0 : ℂ)‖ = |θ 0| := by simp
  have e1 : ‖Complex.I * (θ 1 : ℂ)‖ = |θ 1| := by simp
  rw [e0, e1]
  exact mul_le_mul_of_nonneg_left ((sl86_mean_le _).trans (tbMulCLM_norm_le (n + p + q) hc hp hP V))
    (by positivity)

theorem sl86_unit_norm' (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (V : TorusHk (n + p + q) ℂ) :
    ‖unitOp θ n p q hc hp hP V‖ ≤
      (1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * ‖V‖ := by
  refine (unitOp_norm θ ρ hθ n p q hc hp hP V).trans ?_
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hle : cellDriftNativePrice (n + p + q) * P ≤ |cellDriftNativePrice (n + p + q)| * P :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hP0
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) (norm_nonneg _)

theorem sl86_unit_mean' (θ : Vec 2) (n p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (V : TorusHk (n + p + q) ℂ) :
    ‖slMeanOp n (unitOp θ n p q hc hp hP V)‖ ≤
      |θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * ‖V‖ := by
  refine (sl86_unit_mean θ n p q hc hp hP V).trans ?_
  have hle : cellDriftNativePrice (n + p + q) * P ≤ |cellDriftNativePrice (n + p + q)| * P :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hP0
  have h0 : 0 ≤ |θ 0| ^ p * |θ 1| ^ q := by positivity
  calc _ ≤ |θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P * ‖V‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) h0
    _ = _ := by ring

theorem rq_unit_bounds (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ)
    (B : TorusHk L ℂ →L[ℝ] TorusHk (n + p + q) ℂ) (b bc : ℝ)
    (hB : ∀ ψ, ‖B ψ‖ ≤ b * ‖ψ‖) (hBc : ∀ z : ℂ, ‖B (slConstCLM L z)‖ ≤ bc * ‖z‖) :
    (∀ ψ, ‖lrSmul κ ((unitOp θ n p q hc hp hP).comp B) ψ‖ ≤
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * b)) * ‖ψ‖) ∧
    (∀ ψ, ‖slMeanOp n (lrSmul κ ((unitOp θ n p q hc hp hP).comp B) ψ)‖ ≤
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * b)) * ‖ψ‖) ∧
    (∀ z : ℂ, ‖lrSmul κ ((unitOp θ n p q hc hp hP).comp B) (slConstCLM L z)‖ ≤
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * bc)) * ‖z‖) ∧
    (∀ z : ℂ, ‖slMeanOp n (lrSmul κ ((unitOp θ n p q hc hp hP).comp B) (slConstCLM L z))‖ ≤
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * bc)) * ‖z‖) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hU : 0 ≤ (1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) := by positivity
  have hM : 0 ≤ |θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) := by positivity
  refine ⟨fun ψ => ?_, fun ψ => ?_, fun z => ?_, fun z => ?_⟩
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [ContinuousLinearMap.comp_apply]
    exact (sl86_unit_norm' θ ρ hθ n p q hc hp hP0 hP _).trans
      (by linarith [mul_le_mul_of_nonneg_left (hB ψ) hU])
  · rw [lrSmul_apply, map_smul, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [ContinuousLinearMap.comp_apply]
    exact (sl86_unit_mean' θ n p q hc hp hP0 hP _).trans
      (by linarith [mul_le_mul_of_nonneg_left (hB ψ) hM])
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [ContinuousLinearMap.comp_apply]
    exact (sl86_unit_norm' θ ρ hθ n p q hc hp hP0 hP _).trans
      (by linarith [mul_le_mul_of_nonneg_left (hBc z) hU])
  · rw [lrSmul_apply, map_smul, norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [ContinuousLinearMap.comp_apply]
    exact (sl86_unit_mean' θ n p q hc hp hP0 hP _).trans
      (by linarith [mul_le_mul_of_nonneg_left (hBc z) hM])


/-- **A unit term from an input operator `B`** with norm bounds `b` (and `bc` on constants). -/
theorem rq_of_unit (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L Nmin p q : ℕ) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ)
    (B : TorusHk L ℂ →L[ℝ] TorusHk (n + p + q) ℂ) (b bc : ℝ)
    (hB : ∀ ψ, ‖B ψ‖ ≤ b * ‖ψ‖) (hBc : ∀ z : ℂ, ‖B (slConstCLM L z)‖ ≤ bc * ‖z‖)
    (g : (Vec 2 → ℂ) → Vec 2 → ℂ)
    (hval : ∀ (N : ℕ) (hLN : L ≤ N), Nmin ≤ N → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (unitOp θ n p q hc hp hP (B (truncateTorusHk hLN ψ))) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g (torusHigherClassicalValue N ψ)) :
    RQ L n Nmin (fun f z => (κ : ℂ) * g f z)
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * b))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * b))
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * bc))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * bc)) := by
  refine ⟨lrSmul κ ((unitOp θ n p q hc hp hP).comp B), fun N hLN hN ψ => ?_,
    rq_unit_bounds θ ρ hθ n L p q hc hp hP0 hP κ B b bc hB hBc⟩
  rw [lrSmul_apply, map_smul]
  filter_upwards [Lp.coeFn_smul κ (torusHkValueCLM (unitOp θ n p q hc hp hP
    (B (truncateTorusHk hLN ψ)))), hval N hLN hN ψ] with z e1 e2
  rw [ContinuousLinearMap.comp_apply, e1]
  simp only [Pi.smul_apply, e2, Complex.real_smul]

theorem rq_unit0 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L Nmin p q : ℕ)
    (h1 : n + p + q ≤ L) (h2 : p + q + 3 ≤ Nmin) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    RQ L n Nmin (fun f z => (κ : ℂ) * fibreCovPow θ (p, q) (fun y => (c y : ℂ) * f y) z)
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * 1))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * 1))
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) *
        ‖torusHigherConstant L 1‖))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) *
        ‖torusHigherConstant L 1‖)) := by
  refine rq_of_unit θ ρ hθ n L Nmin p q hc hp hP0 hP κ (truncateTorusHk h1) 1
    ‖torusHigherConstant L 1‖ (fun ψ => ?_) (fun z => ?_) _ ?_
  · rw [one_mul]; exact truncateTorusHk_norm_le h1 ψ
  · change ‖truncateTorusHk h1 (torusHigherConstant L z)‖ ≤ _
    rw [torusHigherConstant_truncate h1]
    exact sl86_const_norm_le h1 z
  · intro N hLN hN ψ
    have hcd : ContDiff ℝ ((p + q + 1 : ℕ) : ℕ∞) (torusHigherClassicalValue N ψ) :=
      torusHigherClassicalValue_contDiff N (p + q + 1) (by omega) ψ
    have hae : (torusHkValueCLM ψ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        torusHigherClassicalValue N ψ := (torusHigherClassicalValue_ae N (by omega) ψ).symm
    have hv : (torusHkValueCLM (truncateTorusHk (h1.trans hLN) ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hcp : ContDiff ℝ (p + q : ℕ) (fun x => (c x : ℂ) * torusHigherClassicalValue N ψ x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q)))
        (hcd.of_le (by exact_mod_cast (by omega : p + q ≤ p + q + 1)))
    exact unitOp_value θ n p q hc hp hP (truncateTorusHk (h1.trans hLN) ψ) _ hcp hv

theorem rq_unit1 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L Nmin p q : ℕ) (k : Fin 2)
    (h1 : n + p + q + 1 ≤ L) (h2 : p + q + 3 ≤ Nmin) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    RQ L n Nmin (fun f z => (κ : ℂ) * fibreCovPow θ (p, q)
        (fun y => (c y : ℂ) * fibreCovDeriv θ k f y) z)
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) * (1 + ρ)))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) * (1 + ρ)))
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * P) *
        (|θ k| * ‖torusHigherConstant L 1‖)))
      (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * P) *
        (|θ k| * ‖torusHigherConstant L 1‖))) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  refine rq_of_unit θ ρ hθ n L Nmin p q hc hp hP0 hP κ
    ((tbTwist (n + p + q) θ k).comp (truncateTorusHk h1)) (1 + ρ)
    (|θ k| * ‖torusHigherConstant L 1‖) (fun ψ => ?_) (fun z => ?_) _ ?_
  · exact ((tbTwist (n + p + q) θ k).le_opNorm _).trans
      (mul_le_mul ((tbTwist_norm_le _ θ k).trans (by linarith [hθ k]))
        (truncateTorusHk_norm_le h1 ψ) (norm_nonneg _) (by linarith))
  · change ‖tbTwist (n + p + q) θ k (truncateTorusHk h1 (torusHigherConstant L z))‖ ≤ _
    rw [torusHigherConstant_truncate h1, sl86_twist_const, torusHigherConstant_norm]
    have e : ‖Complex.I * (θ k : ℂ) * z‖ = |θ k| * ‖z‖ := by simp
    rw [e]
    have := torusHigherConstant_norm (n + p + q) 1
    have h3 := sl86_const_le (show n + p + q ≤ L by omega) 1
    rw [torusHigherConstant_norm] at h3
    calc |θ k| * ‖z‖ * ‖torusHigherConstant (n + p + q) 1‖
        ≤ |θ k| * ‖z‖ * ‖torusHigherConstant L 1‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using h3
      _ = _ := by ring
  · intro N hLN hN ψ
    have hcd : ContDiff ℝ ((p + q + 1 : ℕ) : ℕ∞) (torusHigherClassicalValue N ψ) :=
      torusHigherClassicalValue_contDiff N (p + q + 1) (by omega) ψ
    have hae : (torusHkValueCLM ψ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        torusHigherClassicalValue N ψ := (torusHigherClassicalValue_ae N (by omega) ψ).symm
    have hv : (torusHkValueCLM (truncateTorusHk (h1.trans hLN) ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hc1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) :=
      hcd.of_le (by exact_mod_cast (by omega : 1 ≤ p + q + 1))
    have hD := tbTwist_value_ae (n + p + q) θ k (truncateTorusHk (h1.trans hLN) ψ) _ hc1 hv
    have hcd' : ContDiff ℝ (p + q : ℕ) (fibreCovDeriv θ k (torusHigherClassicalValue N ψ)) :=
      contDiff_fibreCovDeriv (j := p + q) hcd θ k
    have hcp : ContDiff ℝ (p + q : ℕ)
        (fun x => (c x : ℂ) * fibreCovDeriv θ k (torusHigherClassicalValue N ψ) x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q))) hcd'
    exact unitOp_value θ n p q hc hp hP _ _ hcp hD

end AVRegularity.CycleWords.Assembly
end
end

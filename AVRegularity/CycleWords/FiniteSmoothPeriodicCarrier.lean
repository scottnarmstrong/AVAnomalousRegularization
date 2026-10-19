-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MolecularEnvelopeReadout
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane
import AVRegularity.Weighted.PlaneH1Readouts
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The molecular real price sum is controlled before collapsing any original constituent. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem molecularRealEnvelope_sum_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) (j : ℕ) (hj : j ≤ J) :
    Real.sqrt (π u / π v) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        molecularRealPrice ν ρ (K v) (d - 2)
          (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) ≤
      |C j| * (E ^ j)⁻¹ * b v u := by
  classical
  have hn (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      0 ≤ molecularRealPrice ν ρ (K v) (d - 2)
        (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) :=
    molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ |C j| * (E ^ j)⁻¹ * b v u)).mp
  apply le_trans _ ((henv.2 v u j hj).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self (C j)) (by positivity)) hb)))
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun I _ => hn γ d I))))]
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro γ _
  rw [ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun d _ => Finset.sum_nonneg (fun I _ => hn γ d I))]
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro d hd
  rw [ENNReal.ofReal_sum_of_nonneg (fun I _ => hn γ d I)]
  apply Finset.sum_le_sum
  intro I _
  have hkd : K v + (d - 2) = K v + d - 2 := by
    have hd2 := (Finset.mem_Icc.mp hd).1
    omega
  simpa only [hkd] using molecularRealPrice_ofReal_le ν ρ hν hρ (K v) (d - 2)
    (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))

theorem molecularRealEnvelope_scaled_sum_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (hb : 0 ≤ b v u) (j : ℕ) (hj : j ≤ J) :
    Real.sqrt (π u / π v) * ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        E ^ j * molecularRealPrice ν ρ (K v) (d - 2)
          (molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
            (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) ≤ |C j| * b v u := by
  classical
  have hh := mul_le_mul_of_nonneg_left
    (molecularRealEnvelope_sum_le F π K dom ν e E ρ hν hE hρ C J b henv v u hb j hj)
    (pow_nonneg hE.le j)
  have he : E ^ j * (|C j| * (E ^ j)⁻¹ * b v u) = |C j| * b v u := by
    have hn := (pow_pos hE j).ne'
    field_simp
  rw [he] at hh
  simp_rw [← Finset.mul_sum]
  conv_lhs =>
    arg 2
    arg 2
    intro γ
    rw [mul_left_comm ‖(F.identity v u γ).map‖ (E ^ j)]
  rw [← Finset.mul_sum]
  convert hh using 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter
namespace AVRegularity.CycleWords

/-! Surjectivity of the genuine plane frequency lattice rearrangement. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem planeFrequencyL2Isometry_surjective (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Function.Surjective (planeFrequencyL2Isometry (E := E) a P hP) := by
  intro f
  have hc : IsClosed (Set.range (planeFrequencyL2Isometry (E := E) a P hP)) :=
    (planeFrequencyL2Isometry a P hP).isometry.antilipschitzWith.isClosed_range
      (planeFrequencyL2Isometry a P hP).isometry.uniformContinuous
  exact hc.mem_of_tendsto (tendsto_L2CoordinateProjection f)
    (Eventually.of_forall fun s => planeFrequency_projection_mem_range a P hP f s)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Uniform normalized coefficient jets for the literal integral Taylor remainder. -/

theorem taylorIntegral_coefficient_jet_le (r J K : ℕ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (J + r : ℕ) f) {ϖ ζ t A : ℝ}
    (hϖ : 0 < ϖ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hA : 0 ≤ A)
    (hb : ∀ j ≤ J, ∀ y, ‖iteratedFDeriv ℝ (j + r) f y‖ ≤ A * (ζ * ϖ) ^ (j + r))
    (w : DerivativeWord2 r) (j : ℕ) (hj : j ≤ J) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun x => ((1 - t) ^ K * (ϖ ^ r)⁻¹) *
      iteratedFDeriv ℝ r f ((t / ϖ) • x) (fun i => basisVec (w i))) x‖ ≤ A * ζ ^ r := by
  have hs := norm_scaled_coefficient_word_jet_le r j
    (hf.of_le (by exact_mod_cast Nat.add_le_add_right hj r)) w
    ((1 - t) ^ K * (ϖ ^ r)⁻¹) (t / ϖ) x
  apply hs.trans
  exact (mul_le_mul_of_nonneg_left (hb j hj ((t / ϖ) • x))
    (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) j))).trans
      (taylorIntegral_coefficient_price r j K hϖ hζ hζ1 ht ht1 hA)

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Filter TopologicalSpace
namespace AVRegularity.CycleWords

/-! Norm-preserving interchange of the two variables of actual Bochner L2 fields. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bochnerL2Swap (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] :
    Lp E 2 (μ.prod ν) →ₗᵢ[ℝ] Lp E 2 (ν.prod μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap (Measure.measurePreserving_swap (μ := ν) (ν := μ))

def bochnerL2Transpose (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    [SecondCountableTopology (Lp E 2 μ)] [CompleteSpace E]
    (u : Lp (Lp E 2 ν) 2 μ) : Lp (Lp E 2 μ) 2 ν :=
  bochnerL2Curry ν μ (bochnerL2Swap μ ν (bochnerL2Joint μ ν u))

theorem bochnerL2Transpose_slices (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    [SecondCountableTopology (Lp E 2 μ)] [CompleteSpace E]
    (u : Lp (Lp E 2 ν) 2 μ) :
    ∀ᵐ y ∂ν, (bochnerL2Transpose μ ν u y : X → E) =ᵐ[μ]
      fun x => bochnerL2Joint μ ν u (x, y) := by
  let J := bochnerL2Joint μ ν u
  let F := bochnerL2Swap μ ν J
  have hswap : F =ᵐ[ν.prod μ] fun p => J (p.2, p.1) :=
    Lp.coeFn_compMeasurePreserving J (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have ha := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [bochnerL2Curry_ae ν μ F,
    bochnerL2Product_memLp_slices ν μ (fun y x => F (y, x)) (Lp.memLp F), ha]
    with y hy hm hs
  change (bochnerL2Curry ν μ F y : X → E) =ᵐ[μ] _
  rw [hy]
  filter_upwards [bochnerL2TotalSlice_ae μ (fun y x => F (y, x)) y hm, hs] with x hx hs'
  exact hx.trans hs'

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Order consistency for genuine coupled carriers with equal literal fluxes. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

def coupledStoredFlux (κ : ι → ℕ)
    (A : ∀ i j (d : admissibleOrders κ D i j), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (w : ∀ i, PlaneHk Set.univ (κ i + 1) (h i)) (i : ι) (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j, ∑ d : admissibleOrders κ D i j, A i j d t z
    (WithLp.toLp 2 fun word => (w j).toFunction.jet
      ⟨⟨d.1 - 1, by
        have hd := Finset.mem_filter.mp d.2
        have ho := Finset.mem_Icc.mp hd.1
        omega⟩, word⟩ z)

theorem coupledSolution_truncate (κ κ' : ι → ℕ) (hκ : ∀ i, κ' i ≤ κ i)
    (A : ∀ i j (d : admissibleOrders κ D i j), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (A' : ∀ i j (d : admissibleOrders κ' D i j), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (κ i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (κ i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (κ i + 1) (h i))
    (hflux : ∀ i t z, coupledStoredFlux κ' A'
      (fun j => truncatePlaneHk (Nat.succ_le_succ (hκ j)) (w j t)) i t z =
        coupledStoredFlux κ A (fun j => w j t) i t z)
    (hs : IsCoupledWeakSolutionPlane ν a b v D κ A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D κ' A'
      (fun i => truncatePlaneHk (hκ i) (f i))
      (fun i t => truncatePlaneHk (hκ i) (F i t))
      (fun i t => truncatePlaneHk (hκ i) (g i t))
      (fun i t => truncatePlaneHk (hκ i) (u i t))
      (fun i t => truncatePlaneHk (Nat.succ_le_succ (hκ i)) (w i t)) := by
  rcases hs with ⟨hu, hw, ht, hi, he⟩
  refine ⟨fun i => continuousOn_truncatePlaneHk (hκ i) (hu i),
    fun i => memLp_truncatePlaneHk (Nat.succ_le_succ (hκ i)) (hw i), ?_,
    fun i => initial_truncatePlaneHk (hκ i) (hi i), ?_⟩
  · intro i
    filter_upwards [ht i] with t hh
    exact trace_truncatePlaneHk (hκ i) hh
  · intro i t ht φ
    have hf : (fun s => coupledStoredFlux κ' A'
        (fun j => truncatePlaneHk (Nat.succ_le_succ (hκ j)) (w j s)) i s) =
        (fun s => coupledStoredFlux κ A (fun j => w j s) i s) := by
      funext s z
      exact hflux i s z
    change CoupledWeakIdentity _ ν a t v _ _ _ _ _
      (fun s => coupledStoredFlux κ' A'
        (fun j => truncatePlaneHk (Nat.succ_le_succ (hκ j)) (w j s)) i s) _ _
    rw [hf]
    exact he i t ht φ

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! Positivity of the explicit jet prices requires only positivity of constituent scalar prices. -/

variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def FrequencyNormalPriceStep.nonnegative (s : FrequencyNormalPriceStep I V E) : Prop :=
  match s with
  | .multiply _ Θ C => 0 ≤ Θ ∧ ∀ n, 0 ≤ C n
  | .differentiate _ => True

theorem FrequencyNormalPriceStep.amplitude_nonneg (s : FrequencyNormalPriceStep I V E)
    (hs : s.nonnegative) : 0 ≤ s.amplitude := by
  cases s with
  | multiply A Θ C => exact hs.1
  | differentiate w => exact zero_le_one

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets AVRegularity.ChartTransport
namespace AVRegularity.CycleWords

/-! Operator jets of diagonal samples from graded mixed word budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_diagonal_word_budget {N : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : ContDiff ℝ (N : ℕ) (Function.uncurry W)) (a b ρ B : ℝ) (hρ : 0 ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ N) (x : Vec 2)
    (hb : ∀ p ∈ splitTerms l, ρ ^ l.length * |termCoef a b p| *
      ‖mixL p.1 p.2 W (a⁻¹ • x) (b⁻¹ • x)‖ ≤ B) :
    ρ ^ l.length * ‖odL l (fun y => W (a⁻¹ • y) (b⁻¹ • y)) x‖ ≤ 2 ^ l.length * B := by
  rw [joint_odL_diag_eq hW a b l hl]
  change ρ ^ l.length * ‖((splitTerms l).map fun p => diagTerm W a b p x).sum‖ ≤ _
  rw [list_sum_map_fin]
  calc
    _ ≤ ρ ^ l.length * ∑ k : Fin (splitTerms l).length,
        ‖diagTerm W a b ((splitTerms l).get k) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hρ _)
    _ ≤ ∑ _k : Fin (splitTerms l).length, B := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have hh := hb ((splitTerms l).get k) (List.get_mem _ _)
      simpa only [diagTerm, norm_smul, Real.norm_eq_abs, mul_assoc] using hh
    _ = _ := by simp [splitTerms_card]

theorem joint_diagonal_jet_budget {N : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : ContDiff ℝ (N : ℕ) (Function.uncurry W)) (a b ρ B : ℝ)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hb : ∀ γ δ : List (Fin 2), γ.length + δ.length ≤ N → ∀ X z,
      ρ ^ (γ.length + δ.length) * |termCoef a b (γ, δ)| * ‖mixL γ δ W X z‖ ≤ B)
    (j : ℕ) (hj : j ≤ N) (x : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => W (a⁻¹ • y) (b⁻¹ • y)) x‖ ≤ 4 ^ N * B := by
  have hc : ContDiff ℝ (j : ℕ∞) (fun y => W (a⁻¹ • y) (b⁻¹ • y)) := by
    have hWj : ContDiff ℝ (j : ℕ) (Function.uncurry W) := hW.of_le (by exact_mod_cast hj)
    have hh := hWj.comp
      ((contDiff_id.const_smul a⁻¹).prodMk (contDiff_id.const_smul b⁻¹))
    exact hh.of_le (by exact_mod_cast le_refl j)
  have hword (w : DerivativeWord2 j) :
      ρ ^ j * ‖orderedDerivative w (fun y => W (a⁻¹ • y) (b⁻¹ • y)) x‖ ≤ 2 ^ j * B := by
    have hh := joint_diagonal_word_budget hW a b ρ B hρ (List.ofFn w) (by simpa using hj) x
      (fun p hp => by
        have hs := splitTerms_length_sum (List.ofFn w) p hp
        have hh := hb p.1 p.2 (by simp only [List.length_ofFn] at hs; omega) (a⁻¹ • x) (b⁻¹ • x)
        simpa only [hs, List.length_ofFn] using hh)
    simpa only [List.length_ofFn, orderedDerivative_eq_odL] using hh
  calc
    _ ≤ ρ ^ j * ∑ w : DerivativeWord2 j,
        ‖orderedDerivative w (fun y => W (a⁻¹ • y) (b⁻¹ • y)) x‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sum_words hc x) (pow_nonneg hρ _)
    _ ≤ ∑ _w : DerivativeWord2 j, 2 ^ j * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun w _ => hword w)
    _ = 4 ^ j * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Nonzero original maps have finite molecular coefficient jets at every reserved total order. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem molecularEnvelope_constituent_jet_ne_top (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (_he : 0 < e) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (hf : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (j : ℕ) (hj : j ≤ J)
    : molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) ≠ ⊤ := by
  have hh := molecularEnvelope_constituent_term_le F π K dom ν e E ρ C J b hf v u γ d hd I j hj
  have hroot : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hmap : ENNReal.ofReal ‖(F.identity v u γ).map‖ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hγ)).ne'
  have hscale : ENNReal.ofReal (ν * ρ ^ (d - 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (mul_pos hν (pow_pos hρ _))).ne'
  have hinv : (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hratio : ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (div_pos (by positivity) (by positivity))).ne'
  have hterm := (ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh) (mul_ne_zero hroot hmap)).ne
  have hfirst := (ENNReal.lt_top_of_mul_ne_top_left hterm hratio).ne
  have hm := (ENNReal.lt_top_of_mul_ne_top_left hfirst hinv).ne
  exact hm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Equal coefficient cell classes preserve all row majorant and Taylor norms exactly. -/

theorem fibreRowReplacement_homogeneous_ae
    (a b : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube] b p t)
    (ξ : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    fibreHomogeneous a ξ n t =ᵐ[volume.restrict AVenhance.unitCube] fibreHomogeneous b ξ n t := by
  filter_upwards [ae_all_iff.mpr (fun p => ha p t)] with x hx
  simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [hx p]

theorem fibreRowReplacement_homogeneous_norm_eq
    (a b : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube] b p t)
    (ξ : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    cellL2Norm (fibreHomogeneous a ξ n t) = cellL2Norm (fibreHomogeneous b ξ n t) :=
  eLpNorm_congr_ae (fibreRowReplacement_homogeneous_ae a b ha ξ n t)

theorem fibreRowReplacement_series_correction_norm_eq
    (a b : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube] b p t)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fun x => fibreSeriesFun a ξ t x - 1) =
      cellL2Norm (fun x => fibreSeriesFun b ξ t x - 1) := by
  apply eLpNorm_congr_ae
  filter_upwards [fibreSeriesFun_congr_ae a b ha ξ t] with x hx
  rw [hx]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A uniform polynomial jet constant linear in the actual coefficient jet budget. -/

theorem variableMultilinear_normalized_polynomial_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : Type*}
      (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ),
      (∀ t, ContDiff ℝ (J : ℕ) (a t)) → ∀ (ρ B : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ B →
      (∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => a t x (fun i => basisVec (w i))) x‖ ≤ B) →
      ∀ t j, j ≤ J → ∀ x,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => a t x (fun _ => x)) x‖ ≤ C * B * (1 + ‖x‖) ^ r := by
  have hm (w : DerivativeWord2 r) := Weighted.coordinate_monomial_jet_growth J w 1
  choose A hA hb using hm
  let S : ℝ := 2 ^ J
  let C : ℝ := S * ∑ w, A w
  have hS : 0 ≤ S := by positivity
  refine ⟨C, mul_nonneg hS (Finset.sum_nonneg (fun w _ => hA w)), ?_⟩
  intro T a ha ρ B hρ hρ1 hB hab t j hj x
  let m := fun (w : DerivativeWord2 r) (x : Vec 2) => ∏ i, x (w i)
  let b := fun (w : DerivativeWord2 r) (x : Vec 2) => a t x (fun i => basisVec (w i))
  have hmono (w : DerivativeWord2 r) : ContDiff ℝ (J : ℕ) (m w) :=
    contDiff_prod (fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (w i)).contDiff)
  have hcoef (w : DerivativeWord2 r) : ContDiff ℝ (J : ℕ) (b w) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
      (fun i => basisVec (w i))).contDiff.comp (ha t)
  have hterm (w : DerivativeWord2 r) := normalized_scalar_jet_product_le (A := A w * (1 + ‖x‖) ^ r) (B := B) J
    (m w) (b w) (hmono w) (hcoef w) hρ
    (mul_nonneg (hA w) (by positivity)) hB x
    (by
      intro k hk
      have hh : ‖iteratedFDeriv ℝ k (m w) x‖ ≤ A w * (1 + ‖x‖) ^ r := by
        simpa only [m, one_mul] using hb w k hk x
      calc
        _ ≤ ρ ^ k * (A w * (1 + ‖x‖) ^ r) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg hρ k)
        _ ≤ 1 * (A w * (1 + ‖x‖) ^ r) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hρ hρ1) (mul_nonneg (hA w) (by positivity))
        _ = _ := one_mul _)
    (fun k hk => hab t w k hk x) j hj
  have he : (fun x : Vec 2 => a t x (fun _ => x)) =
      (fun x => ∑ w : DerivativeWord2 r, m w x * b w x) := by
    funext x
    simpa only [one_smul, one_mul, smul_eq_mul] using
      Weighted.multilinear_diagonal_coordinate_expansion (a t x) x 1
  rw [he, iteratedFDeriv_sum (fun w _ => ((hmono w).mul (hcoef w)).of_le (by exact_mod_cast hj))]
  simp only [Finset.sum_apply]
  calc
    _ ≤ ρ ^ j * ∑ w : DerivativeWord2 r,
        ‖iteratedFDeriv ℝ j (fun x => m w x * b w x) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hρ j)
    _ ≤ ∑ w : DerivativeWord2 r, S * (A w * (1 + ‖x‖) ^ r) * B := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun w _ => hterm w)
    _ = C * B * (1 + ‖x‖) ^ r := by
      dsimp only [C]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Molecular dimensional envelopes imply literal normalized cell mixed-jet budgets. -/

theorem molecularNative_ae_mixed_reserve {ι : Type*}
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (K d j a b : ℕ) (hab : a + b ≤ K) (dom : ι → Set (ℝ × Vec 2))
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) (i : ι)
    (hf : ∀ t, (∀ Y : Vec 2, (t, Y) ∈ dom i) → IsBoxSmooth (j + a) b (f i t))
    (hM : molecularJet ρ e K j dom
      (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z) ≠ ⊤) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom i) → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b (f i t X') z) X‖ *
          derivativeReserveFactor (ρ / e) K d ≤
        ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
          ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)))) *
          (molecularJet ρ e K j dom
            (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z)).toReal := by
  filter_upwards [molecularJet_ae_real_term ρ e hρ.le he K j dom
    (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z) hM i a b hab] with t ht
  intro hdom X z
  apply molecular_normalized_reserve_le ν e E ρ hν he hE hρ K d j a b
    (hf t hdom) X z
  have hh := ht (E • X) (hdom (E • X)) z
  rw [Nat.add_comm a j] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Finite classical periodic regularity supplies genuine native ordered Sobolev jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem smoothPlaneRawJet_hasWeakJet_finite (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) :
    HasOrderedWeakJetOn Set.univ (smoothPlaneRawJet K f) := by
  intro j w i e
  have hs : ContDiff ℝ 1 (orderedDerivative w f) :=
    orderedDerivative_contDiff w 1 f (hf.of_le (by exact_mod_cast (by omega : 1 + j.val ≤ K)))
  have he := smoothVector_weak_coordinate hs i e
  have hn : orderedDerivative (Fin.snoc w i) f =
      fun x => (fderiv ℝ (orderedDerivative w f) x) (basisVec i) := by
    rw [orderedDerivative_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (orderedDerivative w f x))
    (fun x => inner ℝ e (orderedDerivative (Fin.snoc w i) f x))
  rw [hn]
  exact he

omit [MeasurableSpace E] [BorelSpace E] in
theorem smoothPlaneRawJet_periodicWeak_finite (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    HasPeriodicOrderedWeakJet (smoothPlaneRawJet K f) := by
  refine ⟨?_, ?_, smoothPlaneRawJet_hasWeakJet_finite K hf⟩
  · intro a
    exact orderedDerivative_periodic a.2 f
      (hf.of_le (by exact_mod_cast Nat.le_of_lt_succ a.1.isLt)) hp
  · intro a
    exact continuous_cell_memLp _ (orderedDerivative_contDiff a.2 0 f
      (hf.of_le (by exact_mod_cast (by omega : 0 + a.1.val ≤ K)))).continuous

def finiteSmoothPeriodicHk (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) : TorusHk K E :=
  (show TorusHkFunction K E from
    ⟨smoothPlaneRawJet K f, smoothPlaneRawJet_periodicWeak_finite K hf hp⟩).toHk

theorem finiteSmoothPeriodicHk_jet_ae (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 K) :
    (finiteSmoothPeriodicHk K f hf hp).val a =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative a.2 f :=
  torusJetToL2_ae (smoothPlaneRawJet K f)
    (smoothPlaneRawJet_periodicWeak_finite K hf hp).2.1 a

end AVRegularity.CycleWords
end

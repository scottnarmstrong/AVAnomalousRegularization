-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleComparison.Coarse.Exists.Cell
public import AVRegularity.CycleComparison.Coarse.Fact.GFBScale
public import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledEnergyTorus
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The factorial norm of the first derivatives of a periodic Sobolev field (`gradNormSq`) is the
gradient factorial norm (`gradFactorialNormSq`) of the same jet at the same order, and is
dominated by the gradient factorial norm of any higher-order field that truncates to it. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The first letter and the remaining word, as one word. -/
def consEquiv (l : ℕ) : (Fin 2 × DerivativeWord2 l) ≃ DerivativeWord2 (1 + l) :=
  ((Equiv.funUnique (Fin 1) (Fin 2)).symm.prodCongr (Equiv.refl _)).trans (wordAppendEquiv 1 l)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The squared derivatives of all first derivatives at level `l` are the squared derivatives of
the field at level `1 + l`. -/
theorem sum_first_derivatives {μ : Measure (Vec 2)} {K : ℕ} (D : JetL2 μ (K + 1) E)
    (l : Fin (K + 1)) :
    ∑ j : Fin 2, ∑ w : DerivativeWord2 l.val,
        ‖D (prefixJetIndex (K := K) (r := 1) (fun _ => j) ⟨l, w⟩)‖ ^ 2 =
      ∑ w : DerivativeWord2 (1 + l.val),
        ‖D ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2 := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (consEquiv l.val) _ _ fun jw => ?_
  rfl

theorem gradNormSq_eq {K : ℕ} (ρ : ℝ) (U : TorusHk (K + 1) E) :
    gradNormSq (K := K) ρ U = ∑ l : Fin (K + 1), factorialWeight ρ l.val *
      ∑ w : DerivativeWord2 (1 + l.val),
        ‖U.val ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2 := by
  unfold gradNormSq factorialNormSq derivativeNormSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum, ← sum_first_derivatives U.val l]
  rfl

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Reindexing a derivative level along an equality of orders. -/
theorem sum_level_congr {μ : Measure (Vec 2)} {K : ℕ} (D : JetL2 μ K E) :
    ∀ {n m : ℕ} (_e : n = m) (h : n < K + 1) (h' : m < K + 1),
      ∑ w : DerivativeWord2 n, ‖D ⟨⟨n, h⟩, w⟩‖ ^ 2 = ∑ w : DerivativeWord2 m, ‖D ⟨⟨m, h'⟩, w⟩‖ ^ 2
  | _, _, rfl, _, _ => rfl

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The weighted level sum equals the gradient factorial norm at the same order. -/
theorem gradFactorialNormSq_eq {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSq ρ D = ∑ l : Fin (K + 1), factorialWeight ρ l.val *
      ∑ w : DerivativeWord2 (1 + l.val),
        ‖D ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2 := by
  unfold gradFactorialNormSq
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact sum_level_congr D (Nat.add_comm _ _) _ _

/-- **Comparison with a higher-order field.** If `Uw` truncates to `U`, the first derivatives of
`U` are controlled by the gradient factorial norm of `Uw`. -/
theorem gradNormSq_le_of_truncate {K M : ℕ} (hKM : K ≤ M) (ρ : ℝ) (U : TorusHk (K + 1) E)
    (Uw : TorusHk (M + 1) E) (h : truncateTorusHk (Nat.succ_le_succ hKM) Uw = U) :
    gradNormSq (K := K) ρ U ≤ gradFactorialNormSq ρ Uw.val := by
  rw [gradNormSq_eq, gradFactorialNormSq_eq]
  have hterm : ∀ l : Fin (K + 1), (∑ w : DerivativeWord2 (1 + l.val),
      ‖U.val ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2) =
      ∑ w : DerivativeWord2 (1 + l.val),
        ‖Uw.val ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2 := by
    intro l
    rw [← h]
    rfl
  simp_rw [hterm]
  let g : Fin (K + 1) → Fin (M + 1) := fun l => ⟨l.val, by have := l.isLt; omega⟩
  have hg : Function.Injective g := fun a b hab => Fin.ext (by simpa [g] using congrArg Fin.val hab)
  calc ∑ l : Fin (K + 1), factorialWeight ρ l.val * ∑ w : DerivativeWord2 (1 + l.val),
        ‖Uw.val ⟨⟨1 + l.val, by have := l.isLt; omega⟩, w⟩‖ ^ 2
      = ∑ l : Fin (K + 1), (fun l' : Fin (M + 1) => factorialWeight ρ l'.val *
          ∑ w : DerivativeWord2 (1 + l'.val),
            ‖Uw.val ⟨⟨1 + l'.val, by have := l'.isLt; omega⟩, w⟩‖ ^ 2) (g l) := rfl
    _ ≤ ∑ l' : Fin (M + 1), factorialWeight ρ l'.val * ∑ w : DerivativeWord2 (1 + l'.val),
          ‖Uw.val ⟨⟨1 + l'.val, by have := l'.isLt; omega⟩, w⟩‖ ^ 2 := by
        exact sum_comp_le_sum_nonneg g hg (fun l' : Fin (M + 1) => factorialWeight ρ l'.val *
          ∑ w : DerivativeWord2 (1 + l'.val),
            ‖Uw.val ⟨⟨1 + l'.val, by have := l'.isLt; omega⟩, w⟩‖ ^ 2)
          fun l' => mul_nonneg (factorialWeight_nonneg ρ _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
end

/-! The pointwise letter bound: a flux which pairs with every smooth periodic test field as the
predecessors pair with the diagonal and edge operators is, by uniqueness, the sum of the gradient
form adjoints applied to the predecessors; hence its factorial norm is bounded by the factorial
norms of the gradients of the predecessors. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  [∀ i, CompleteSpace (F i)]

/-- The value field of a predecessor family, zero when absent. -/
def predV {K' : ℕ} (n : ℕ) (U : ∀ v, ℝ → TorusHk K' (h v)) : ∀ v, ℝ → Vec 2 → h v :=
  if n = 0 then fun _ _ _ => 0 else fun v s x => tval (U v s) x

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The pointwise letter bound.** -/
theorem flux_le_of_gadj {I : Set ℝ} {K m' Kc : ℕ} {ρ CgD : ℝ} {CgE : ι → ι → ℝ}
    (hKc : K + (m' + 1) ≤ Kc) (n1 n2 : ℕ)
    (U' U'' : ∀ v, ℝ → TorusHk (K + (m' + 1)) (h v))
    (TD : ∀ v, ℝ → (Vec 2 → F v) → (Vec 2 → h v))
    (TE : ∀ v u, ℝ → (Vec 2 → F v) → (Vec 2 → h u))
    (GD : ∀ v, ∀ s ∈ I, GAdj (TD v s) m' Kc ρ CgD)
    (GE : ∀ v u, ∀ s ∈ I, GAdj (TE v u s) m' Kc ρ (CgE v u))
    (G : ∀ v, ℝ → TorusHk K (F v))
    (hG : ∀ s ∈ I, ∀ v (ψ : Vec 2 → F v), ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval (G v s)) ψ = cellInner (predV n1 U' v s) (TD v s ψ) +
        ∑ u, cellInner (predV n2 U'' u s) (TE v u s ψ))
    {s : ℝ} (hs : s ∈ I) (v : ι) :
    Real.sqrt (factorialNormSq ρ (G v s).val) ≤
      (if n1 = 0 then 0 else CgD * Real.sqrt (gradNormSq (K := K + m') ρ (U' v s))) +
        ∑ u, (if n2 = 0 then 0 else CgE v u * Real.sqrt (gradNormSq (K := K + m') ρ (U'' u s))) := by
  classical
  -- the candidate
  let XD : TorusHk K (F v) := if n1 = 0 then 0 else (GD v s hs).adj K hKc (U' v s)
  let XE : ι → TorusHk K (F v) := fun u => if n2 = 0 then 0 else (GE v u s hs).adj K hKc (U'' u s)
  have hXD : ∀ ψ : Vec 2 → F v, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval XD) ψ = cellInner (predV n1 U' v s) (TD v s ψ) := by
    intro ψ hψ hp
    by_cases hn : n1 = 0
    · simp only [XD, hn, ↓reduceIte, predV, cellInner_tval_zero]
      simp [cellInner]
    · simp only [XD, hn, ↓reduceIte, predV]
      exact (GD v s hs).ident K hKc (U' v s) ψ hψ hp
  have hXE : ∀ u, ∀ ψ : Vec 2 → F v, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval (XE u)) ψ = cellInner (predV n2 U'' u s) (TE v u s ψ) := by
    intro u ψ hψ hp
    by_cases hn : n2 = 0
    · simp only [XE, hn, ↓reduceIte, predV, cellInner_tval_zero]
      simp [cellInner]
    · simp only [XE, hn, ↓reduceIte, predV]
      exact (GE v u s hs).ident K hKc (U'' u s) ψ hψ hp
  have hsum : ∀ ψ : Vec 2 → F v, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval (∑ u, XE u)) ψ = ∑ u, cellInner (tval (XE u)) ψ := by
    intro ψ hψ _
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp [cellInner_tval_zero]
    | insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, cellInner_tval_add _ _ hψ.continuous, ih]
  -- uniqueness
  have heq : G v s = XD + ∑ u, XE u := by
    refine torusHk_eq_of_cellInner fun ψ hψ hp => ?_
    rw [hG s hs v ψ hψ hp, cellInner_tval_add _ _ hψ.continuous, hsum ψ hψ hp, hXD ψ hψ hp]
    congr 1
    exact Finset.sum_congr rfl fun u _ => (hXE u ψ hψ hp).symm
  -- the bound
  rw [heq]
  refine (sqrt_fNSq_torus_add_le ρ _ _).trans (add_le_add ?_ ?_)
  · by_cases hn : n1 = 0
    · simp only [XD, hn, ↓reduceIte, sqrt_fNSq_torus_zero, le_refl]
    · simp only [XD, hn, ↓reduceIte]
      exact (GD v s hs).gbound K hKc (U' v s)
  · refine (sqrt_fNSq_torus_sum_le ρ _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    by_cases hn : n2 = 0
    · simp only [XE, hn, ↓reduceIte, sqrt_fNSq_torus_zero, le_refl]
    · simp only [XE, hn, ↓reduceIte]
      exact (GE v u s hs).gbound K hKc (U'' u s)
end

/-! The gradient part of the strong energy: `B ∫ ∑ π⁻¹ |∇U|²_ρ ≤ 𝓔²`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The gradient part of the strong energy.** -/
theorem grad_le_strongEnergy_sq {ρ B : ℝ} (hB : 0 ≤ B) {π : ι → ℝ} (hπ : ∀ v, 0 < π v)
    {t₀ t₁ : ℝ} {K : ℕ} (U : ∀ v, ℝ → TorusHk K (h v)) (Uw : ∀ v, ℝ → TorusHk (K + 1) (h v))
    (hUw : ∀ v, MemLp (Uw v) 2 (volume.restrict (Set.Icc t₀ t₁))) :
    ENNReal.ofReal (B * ∫ s in Set.Icc t₀ t₁, ∑ v, (π v)⁻¹ * gradFactorialNormSq ρ (Uw v s).val) ≤
      strongEnergy ρ B π t₀ t₁ U Uw ^ (2 : ℝ) := by
  have hint : ∀ v, Integrable (fun s => gradFactorialNormSq ρ (Uw v s).val)
      (volume.restrict (Set.Icc t₀ t₁)) := fun v => integrable_gradFactorialNormSq_torus (hUw v)
  unfold strongEnergy
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [integral_finsetSum _ fun v _ => (hint v).const_mul _, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg hB (integral_nonneg fun s =>
      mul_nonneg (inv_nonneg.2 (hπ v).le) (gradFactorialNormSq_nonneg ρ _))]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [integral_const_mul, ← ofReal_integral_eq_lintegral_ofReal (hint v)
    (Filter.Eventually.of_forall fun s => gradFactorialNormSq_nonneg ρ _)]
  have h1 : 0 ≤ ∫ s in Set.Icc t₀ t₁, gradFactorialNormSq ρ (Uw v s).val :=
    integral_nonneg fun s => gradFactorialNormSq_nonneg ρ _
  calc ENNReal.ofReal (B * ((π v)⁻¹ * ∫ s in Set.Icc t₀ t₁, gradFactorialNormSq ρ (Uw v s).val))
      = ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal B *
          ENNReal.ofReal (∫ s in Set.Icc t₀ t₁, gradFactorialNormSq ρ (Uw v s).val)) := by
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
        congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left le_add_self zero_le
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The response-flux identity one component at a time: testing the summed identity with a family
of test fields supported in one component isolates the flux of that component. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

theorem cellInner_zero_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : Vec 2 → E) : cellInner g (0 : Vec 2 → E) = 0 := by
  simp [cellInner]

/-- **The response-flux identity for one component.** -/
theorem responseFlux_component {t₀ t₁ : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {K : ℕ}
    {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))} {U' U'' : ∀ v, ℝ → Vec 2 → h v}
    (hG : IsCoarseResponseFlux t₀ t₁ b D H p AD CE Hcov K G U' U'')
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (fun x => (G v s).toFunction.jet (valueIndex2 K) x) ψ =
      cellInner (U' v s) (fun x => -(coarseFluxAdjoint D b AD (Hcov s) p s
          (covPolyQ (Hcov s) p ψ) x)) +
        ∑ u, cellInner (U'' u s) (covPolyP (Hcov s) p (fun x =>
          ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordAdjoint (d.1 - 1)
            (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (covPolyQ (Hcov s) p ψ y)) x)) := by
  let Ψ : ∀ w, Vec 2 → PiLp 2 (fun _ : Fin 2 => h w) := Function.update (fun _ => 0) v ψ
  have hΨs : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ψ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Ψ] using hψ
    · simp only [Ψ, Function.update_of_ne hw]
      exact contDiff_zero_fun
  have hΨp : ∀ w, AVenhance.IsZ2Periodic (Ψ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Ψ] using hp
    · intro n x; simp [Ψ, Function.update_of_ne hw]
  have hI := hG s hs Ψ hΨs hΨp
  -- the left side
  have hL : ∑ w, cellInner (fun x => (G w s).toFunction.jet (valueIndex2 K) x) (Ψ w) =
      cellInner (fun x => (G v s).toFunction.jet (valueIndex2 K) x) ψ := by
    rw [Finset.sum_eq_single v]
    · simp [Ψ]
    · intro w _ hw
      simp only [Ψ, Function.update_of_ne hw]
      exact cellInner_zero_right _
    · intro h; exact absurd (Finset.mem_univ v) h
  -- the diagonal part
  have hD : ∑ w, cellInner (U' w s) (fun x => -(coarseFluxAdjoint D b AD (Hcov s) p s
      (covPolyQ (Hcov s) p (Ψ w)) x)) =
      cellInner (U' v s) (fun x => -(coarseFluxAdjoint D b AD (Hcov s) p s
        (covPolyQ (Hcov s) p ψ) x)) := by
    rw [Finset.sum_eq_single v]
    · simp [Ψ]
    · intro w _ hw
      simp only [Ψ, Function.update_of_ne hw]
      rw [covPolyQ_zero_field, coarseFluxAdjoint_zero_field]
      simp [cellInner]
    · intro h; exact absurd (Finset.mem_univ v) h
  -- the edge part
  have hE : ∀ u, edgeFluxAdjoint D H CE s (fun w => covPolyQ (Hcov s) p (Ψ w)) u =
      fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordAdjoint (d.1 - 1)
        (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (covPolyQ (Hcov s) p ψ y)) x := by
    intro u
    funext x
    unfold edgeFluxAdjoint
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [Ψ]
    · intro w _ hw
      simp only [Ψ, Function.update_of_ne hw]
      rw [covPolyQ_zero_field]
      refine Finset.sum_eq_zero fun d _ => ?_
      have e : (fun y => ContinuousLinearMap.adjoint (CE r w u d s y)
          ((0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => h w)) y)) = fun _ => 0 := by
        funext y; simp
      rw [e, wordAdjoint_zero_field]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hL, hD] at hI
  rw [hI]
  congr 1
  exact Finset.sum_congr rfl fun u _ => by rw [hE u]

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The constants of the letter recursion in terms of the premises of the coarse setting: the
window suprema of the derivative arrays of a coefficient, summed against `ρ^l/l!`, are at most its
coefficient seminorm; the covariance bound is at most four times the sup norm of the covariance
matrix; the explicit drift derivative bound `drift_jets`; and the real form of the
supplied-mean hypothesis. -/

section
section Sup

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The supremum over the window of the `j`-th derivative array of a coefficient. -/
def coeffSup (t₀ t₁ : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) (j : ℕ) : ℝ :=
  (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)).toReal

theorem coeffSup_nonneg (t₀ t₁ : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) (j : ℕ) :
    0 ≤ coeffSup t₀ t₁ A j :=
  ENNReal.toReal_nonneg

theorem coeffSup_term_le {ρ : ℝ} {K : ℕ} {t₀ t₁ : ℝ} (A : ℝ → Vec 2 → E →L[ℝ] F) {j : ℕ}
    (hj : j ≤ K) :
    ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
      (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)) ≤
      coefficientSeminorm ρ K t₀ t₁ A := by
  unfold coefficientSeminorm
  exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
    ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞))
    (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))

/-- The window supremum bounds the derivative array. -/
theorem coeffSup_bound {ρ : ℝ} (hρ : 0 < ρ) {K : ℕ} {t₀ t₁ : ℝ} {A : ℝ → Vec 2 → E →L[ℝ] F}
    (hA : coefficientSeminorm ρ K t₀ t₁ A ≠ ⊤) {j : ℕ} (hj : j ≤ K) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    ‖coefficientDerivativeArray (A t) j x‖ ≤ coeffSup t₀ t₁ A j := by
  set S : ℝ≥0∞ := ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
    (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞) with hS
  have hw : 0 < ρ ^ j / (j.factorial : ℝ) := by positivity
  have hterm := coeffSup_term_le (ρ := ρ) (t₀ := t₀) (t₁ := t₁) A hj
  have hfin : S ≠ ⊤ := by
    intro htop
    rw [← hS, htop, ENNReal.mul_top (by simpa using hw)] at hterm
    exact hA (top_le_iff.1 hterm)
  have h1 : (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞) ≤ S :=
    le_iSup₂_of_le t ht (le_iSup_of_le x le_rfl)
  have h2 := ENNReal.toReal_mono hfin h1
  have h3 : ‖coefficientDerivativeArray (A t) j x‖ ≤ S.toReal := by simpa using h2
  exact h3

/-- **The weighted window suprema are at most the coefficient seminorm.** -/
theorem sum_coeffSup_le {ρ : ℝ} (hρ : 0 < ρ) {K Kc : ℕ} {t₀ t₁ : ℝ}
    {A : ℝ → Vec 2 → E →L[ℝ] F} (hA : coefficientSeminorm ρ K t₀ t₁ A ≠ ⊤) (hKc : Kc ≤ K) :
    ∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * coeffSup t₀ t₁ A l ≤
      (coefficientSeminorm ρ K t₀ t₁ A).toReal := by
  have hterm : ∀ l ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ l / (l.factorial : ℝ)) *
      (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) l x‖₊ : ℝ≥0∞)) ≠
        ⊤ :=
    fun l hl => ne_top_of_le_ne_top hA (coeffSup_term_le A (by
      have := Finset.mem_range.1 hl; omega))
  have heq : (coefficientSeminorm ρ K t₀ t₁ A).toReal =
      ∑ l ∈ Finset.range (K + 1), ρ ^ l / (l.factorial : ℝ) * coeffSup t₀ t₁ A l := by
    unfold coefficientSeminorm
    rw [ENNReal.toReal_sum hterm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  rw [heq]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hl) (by omega))) fun l _ _ => ?_
  exact mul_nonneg (by positivity) (coeffSup_nonneg _ _ _ _)

end Sup

/-- The real form of the sum `∑_d 𝒜_d (B ρ^{d-2})⁻¹` of finite seminorms. -/
theorem toReal_sum_sem_div {D : ℕ} {B ρ : ℝ} (hB : 0 < B) (hρ : 0 < ρ)
    (S : Finset.Icc 2 D → ℝ≥0∞) (hS : ∀ d, S d ≠ ⊤) :
    (∑ d : Finset.Icc 2 D, S d * (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal =
      ∑ d : Finset.Icc 2 D, (S d).toReal / (B * ρ ^ (d.1 - 2)) := by
  have hpos : ∀ d : Finset.Icc 2 D, 0 < B * ρ ^ (d.1 - 2) := fun d => by positivity
  rw [ENNReal.toReal_sum fun d _ => ENNReal.mul_ne_top (hS d)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (hpos d)).ne')]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hpos d).le, div_eq_mul_inv]

/-- The explicit drift derivative bound of the coarse letter constants. -/
def driftB (a B₀ lam : ℝ) (l : ℕ) : ℝ :=
  4 * 2 ^ (l + 1) * (a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) *
    lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)))

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

/-- The covariance bound against the sup norm of the covariance matrix. -/
theorem covBound_le_supNorm {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    covBound (covarianceMatrix Jm B t₀ s) ≤
      4 * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := by
  have hfin : matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top P.cov_small
  have hS : matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁ ≤
      ENNReal.ofReal (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := by
    rw [ENNReal.ofReal_toReal hfin]
  have he : ∀ i j, |covarianceMatrix Jm B t₀ s i j| ≤
      (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := fun i j =>
    abs_entry_le_of_matrixSupNorm ENNReal.toReal_nonneg hS hs i j
  unfold covBound
  calc ∑ i, ∑ j, |covarianceMatrix Jm B t₀ s i j| ≤
        ∑ _i : Fin 2, ∑ _j : Fin 2, (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ = 4 * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := by simp; ring

/-- **The explicit drift derivative bound.** -/
theorem drift_bound_explicit {l : ℕ} (hl : l + 1 ≤ N) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (x : Vec 2) : ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ driftB a B₀ lam l := by
  have hv : ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) (b s) :=
    (P.drift_smooth s hs).of_le (by exact_mod_cast le_top)
  set X : ℝ := a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) * lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ))
  have hX : 0 ≤ X := by
    have := P.a_nonneg
    have := P.lam_pos
    have : 0 ≤ B₀ := zero_le_one.trans P.B₀_ge
    positivity
  have hk : ∀ k : Fin 2, ‖iteratedFDeriv ℝ (l + 1) (fun y => b s y k) x‖ ≤ 2 ^ (l + 1) * X :=
    fun k => (norm_iteratedFDeriv_component_le hv k x).trans
      (mul_le_mul_of_nonneg_left (P.drift_jets (l + 1) (by omega) hl s hs x) (by positivity))
  refine (norm_iteratedFDeriv_le_sum_components hv x).trans ?_
  calc ∑ k : Fin 2, ‖iteratedFDeriv ℝ (l + 1) (fun y => b s y k) x‖ ≤
        ∑ _k : Fin 2, 2 ^ (l + 1) * X := Finset.sum_le_sum fun k _ => hk k
    _ = 2 * (2 ^ (l + 1) * X) := by simp
    _ ≤ driftB a B₀ lam l := by
        have : 0 ≤ 2 ^ (l + 1) * X := by positivity
        unfold driftB
        change 2 * (2 ^ (l + 1) * X) ≤ 4 * 2 ^ (l + 1) * X
        nlinarith

/-- **The supplied-mean hypothesis in real form.** -/
theorem edge_mean_real {r : ℕ} (hr : r ∈ Finset.Icc 1 H) (v u : ι)
    (hx : 0 ≤ Cstar ^ r * (Aedge ^ r) v u) :
    Real.sqrt (π u / π v) * ∑ d : Finset.Icc 2 D,
      (coefficientSeminorm ρ N t₀ t₁ (CE r v u d)).toReal / (B * ρ ^ (d.1 - 2)) ≤
        Cstar ^ r * (Aedge ^ r) v u := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (P.edge_mean r hr v u)
  rw [ENNReal.toReal_ofReal hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    toReal_sum_sem_div P.B_pos P.rho_pos _ fun d => P.CE_fin r hr v u d] at h
  exact h

end Setting
end

/-! The gradient-form adjoints of the diagonal and edge response operators at every time of the
window, with constants uniform in time, and the scale bounds of these constants by the letter
sizes: the diagonal constant against `σ a B₀ + ∑_d 𝒜_{ρ,N}(A_d)/ρ^{d-2}` (`σ` the sup norm of the
covariance matrix) and the mass-weighted Schur sums of the edge constants against
`B ∑_r (C_* Θ)^r`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- Window suprema of the derivative arrays of the diagonal coefficients. -/
def diagSup (t₀ t₁ : ℝ) {D : ℕ}
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (dn l : ℕ) : ℝ :=
  if hd : dn ∈ Finset.Icc 2 D then coeffSup t₀ t₁ (AD ⟨dn, hd⟩) l else 0

/-- Window suprema of the derivative arrays of the edge coefficients. -/
def edgeSup (t₀ t₁ : ℝ) {D : ℕ} (H : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (r dn l : ℕ) : ℝ :=
  if hd : r ∈ Finset.Icc 1 H ∧ dn ∈ Finset.Icc 2 D then
    coeffSup t₀ t₁ (CE r v u ⟨dn, hd.2⟩) l else 0

theorem diagSup_nonneg (dn l : ℕ) : 0 ≤ diagSup t₀ t₁ AD dn l := by
  unfold diagSup; split_ifs
  · exact coeffSup_nonneg _ _ _ _
  · exact le_rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem edgeSup_nonneg (v u : ι) (r dn l : ℕ) : 0 ≤ edgeSup t₀ t₁ H CE v u r dn l := by
  unfold edgeSup; split_ifs
  · exact coeffSup_nonneg _ _ _ _
  · exact le_rfl

/-- The diagonal gradient constant of a cell. -/
def cellCgD (ρ a B₀ σ : ℝ) (Kc D p : ℕ) (t₀ t₁ : ℝ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) : ℝ :=
  gfbD Kc D p * (4 * σ * a * B₀ + ∑ d : Finset.Icc 2 D,
    (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * diagSup t₀ t₁ AD d.1 l) /
      ρ ^ (d.1 - 2))

/-- The edge gradient constant of a cell. -/
def cellCgE (ρ : ℝ) (Kc D H p : ℕ) (t₀ t₁ : ℝ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) : ℝ :=
  gfbE Kc D H p * ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
    (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) * edgeSup t₀ t₁ H CE v u r d.1 l) /
      ρ ^ (d.1 - 2)

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem setting_order_le : 2 * p + D + 3 ≤ N := by
  have hL := P.L_eq
  have hNL : L ≤ N := by rw [P.N_eq]; nlinarith
  omega

/-- **The diagonal gradient adjoint at a time of the window.** -/
def diagGAdj (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {Kc : ℕ} (hKc : Kc + 1 ≤ N)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      fun x => -(AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
        (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ) x)) (4 * p + D - 1) Kc ρ
      (cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal Kc D p t₀ t₁ AD) :=
  (GAdj.coarseFluxF (E := E) (covarianceMatrix Jm B t₀ s) (covBound_le_supNorm P hs) b D p
    (by have := P.D_ge; omega) AD s 1 Kc N le_rfl (by have := setting_order_le P; omega) hKc
    ((P.drift_smooth s hs).of_le (by exact_mod_cast le_top)) (P.drift_per s hs)
    (driftB a B₀ lam) (fun l hl x => drift_bound_explicit P (by omega) hs x)
    (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) (diagSup t₀ t₁ AD)
    (fun d l hl x => by
      simp only [diagSup, d.2, ↓reduceDIte]
      exact coeffSup_bound P.rho_pos (P.AD_fin d) (by omega) hs x)
    ρ P.rho_pos).mono
    (gfbCoarseCg_le P.rho_pos _ Kc D p (covBound_le P hs) (covBound_le_supNorm P hs)
      P.a_nonneg P.B₀_ge P.lam_pos P.drift_scale (fun _ => rfl) diagSup_nonneg)

/-- **The edge gradient adjoint of the pair `(v,u)` at a time of the window.** -/
def edgeGAdj {Kc : ℕ} (hKc : Kc ≤ N) (v u : ι) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (fun x =>
        ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ y)) x)) (4 * p + D - 1) Kc ρ
      (cellCgE ρ Kc D H p t₀ t₁ CE v u) :=
  ((GAdj.edgeFluxPairF (covarianceMatrix Jm B t₀ s) (covBound_le P hs) D H p
    (by have := P.D_ge; omega) (edgeExt H CE) v u s 1 Kc N le_rfl
    (by have := setting_order_le P; omega) hKc
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_smooth r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; exact contDiff_const)
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_per r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; intro n x; rfl)
    (edgeSup t₀ t₁ H CE v u)
    (fun r d l hl x => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · simp only [edgeExt_of_mem hr, edgeSup, hr, d.2, and_self, ↓reduceDIte]
        exact coeffSup_bound P.rho_pos (P.CE_fin r hr v u d) (by omega) hs x
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he, coefficientDerivativeArray_zero_coefficient, ContinuousLinearMap.opNorm_zero]
        exact edgeSup_nonneg v u r d.1 l)
    ρ P.rho_pos).mono
    (gfbEdgeCg_le P.rho_pos _ Kc D H p (covBound_le P hs) (edgeSup_nonneg v u))).ofOp
    (fun ψ _ _ => by
      congr 1
      funext x
      refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun d _ => ?_
      simp only [edgeExt_of_mem hr])

end
end

/-! The scale bounds of the per-cell gradient constants by the letter sizes: the diagonal step
factor `√48 C_D / B` is at most `28 gfbD · (a B₀ σ / B + ∑_d 𝒜_{ρ,N}(A_d)/(Bρ^{d-2}))`, and the
mass-weighted Schur sums of the edge constants are at most `gfbE · B ∑_r (C_* Θ)^r`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

theorem sqrt_48_le : Real.sqrt 48 ≤ 7 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

theorem cellCgD_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (Kc : ℕ) :
    0 ≤ cellCgD ρ a B₀ σ Kc D p t₀ t₁ AD := by
  have := P.a_nonneg
  have : 0 ≤ B₀ := zero_le_one.trans P.B₀_ge
  have := P.rho_pos
  have hS : 0 ≤ ∑ d : Finset.Icc 2 D, (∑ l ∈ Finset.range (Kc + 1),
      ρ ^ l / (l.factorial : ℝ) * diagSup t₀ t₁ AD d.1 l) / ρ ^ (d.1 - 2) :=
    Finset.sum_nonneg fun d _ => div_nonneg (Finset.sum_nonneg fun l _ =>
      mul_nonneg (by positivity) (diagSup_nonneg d.1 l)) (by positivity)
  unfold cellCgD
  exact mul_nonneg (gfbD_nonneg _ _ _) (add_nonneg (by positivity) hS)

theorem cellCgD_le {σ : ℝ} (hσ : 0 ≤ σ) {Kc : ℕ} (hKc : Kc ≤ N) :
    cellCgD ρ a B₀ σ Kc D p t₀ t₁ AD ≤ 4 * gfbD Kc D p * (a * B₀ * σ +
      ∑ d : Finset.Icc 2 D, (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / ρ ^ (d.1 - 2)) := by
  have hρ := P.rho_pos
  have hS : ∑ d : Finset.Icc 2 D, (∑ l ∈ Finset.range (Kc + 1),
      ρ ^ l / (l.factorial : ℝ) * diagSup t₀ t₁ AD d.1 l) / ρ ^ (d.1 - 2) ≤
      ∑ d : Finset.Icc 2 D, (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / ρ ^ (d.1 - 2) :=
    Finset.sum_le_sum fun d _ => div_le_div_of_nonneg_right (by
      simp only [diagSup, d.2, ↓reduceDIte]
      exact sum_coeffSup_le hρ (P.AD_fin d) hKc) (by positivity)
  have hS0 : 0 ≤ ∑ d : Finset.Icc 2 D,
      (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / ρ ^ (d.1 - 2) :=
    Finset.sum_nonneg fun d _ => div_nonneg ENNReal.toReal_nonneg (by positivity)
  have hX : 0 ≤ a * B₀ * σ := by
    have := P.a_nonneg
    have : 0 ≤ B₀ := zero_le_one.trans P.B₀_ge
    positivity
  have hg := gfbD_nonneg Kc D p
  have e : 4 * σ * a * B₀ = 4 * (a * B₀ * σ) := by ring
  unfold cellCgD
  rw [e]
  calc gfbD Kc D p * (4 * (a * B₀ * σ) + ∑ d : Finset.Icc 2 D, (∑ l ∈ Finset.range (Kc + 1),
        ρ ^ l / (l.factorial : ℝ) * diagSup t₀ t₁ AD d.1 l) / ρ ^ (d.1 - 2)) ≤
      gfbD Kc D p * (4 * (a * B₀ * σ + ∑ d : Finset.Icc 2 D,
        (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / ρ ^ (d.1 - 2))) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = _ := by ring

/-- **The diagonal step factor against the diagonal letter size.** -/
theorem letterD_le {σ : ℝ} (hσ : 0 ≤ σ) {Kc : ℕ} (hKc : Kc ≤ N) :
    Real.sqrt 48 * cellCgD ρ a B₀ σ Kc D p t₀ t₁ AD / B ≤
      28 * gfbD Kc D p * (a * B₀ * σ / B + (∑ d : Finset.Icc 2 D,
        coefficientSeminorm ρ N t₀ t₁ (AD d) * (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal) := by
  have hB := P.B_pos
  have hρ := P.rho_pos
  rw [toReal_sum_sem_div hB hρ _ fun d => P.AD_fin d]
  set T := ∑ d : Finset.Icc 2 D, (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / ρ ^ (d.1 - 2)
  have hT : T / B = ∑ d : Finset.Icc 2 D,
      (coefficientSeminorm ρ N t₀ t₁ (AD d)).toReal / (B * ρ ^ (d.1 - 2)) := by
    simp only [T]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun d _ => by rw [div_div, mul_comm (ρ ^ (d.1 - 2)) B]
  have h0 := cellCgD_nonneg P hσ Kc
  have h1 := cellCgD_le P hσ hKc
  calc Real.sqrt 48 * cellCgD ρ a B₀ σ Kc D p t₀ t₁ AD / B ≤
        7 * (4 * gfbD Kc D p * (a * B₀ * σ + T)) / B :=
        div_le_div_of_nonneg_right (mul_le_mul sqrt_48_le h1 h0 (by norm_num)) hB.le
    _ = 28 * gfbD Kc D p * (a * B₀ * σ / B + T / B) := by field_simp; ring
    _ = _ := by rw [hT]

/-- **The mass-weighted edge constant against the supplied means.** -/
theorem edge_weighted_le {Kc : ℕ} (hKc : Kc ≤ N) (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) (v u : ι) :
    Real.sqrt (π u / π v) * cellCgE ρ Kc D H p t₀ t₁ CE v u ≤
      gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * (Aedge ^ r) v u := by
  have hB := P.B_pos
  have hB0 : B ≠ 0 := hB.ne'
  have hρ := P.rho_pos
  have hApos : ∀ r, ∀ v u, 0 ≤ (Aedge ^ r) v u := fun r =>
    (matrix_pow_row_sum_le Aedge P.edge_nonneg hΘ P.edge_row r).1
  have hr : ∀ r ∈ Finset.Icc 1 H, Real.sqrt (π u / π v) * ∑ d : Finset.Icc 2 D,
      (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) *
        edgeSup t₀ t₁ H CE v u r d.1 l) / ρ ^ (d.1 - 2) ≤ B * (Cstar ^ r * (Aedge ^ r) v u) := by
    intro r hr
    have hX : ∑ d : Finset.Icc 2 D, (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) *
        edgeSup t₀ t₁ H CE v u r d.1 l) / ρ ^ (d.1 - 2) ≤
        B * ∑ d : Finset.Icc 2 D,
          (coefficientSeminorm ρ N t₀ t₁ (CE r v u d)).toReal / (B * ρ ^ (d.1 - 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun d _ => ?_
      rw [mul_div_assoc', mul_div_mul_left _ _ hB0]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      simp only [edgeSup, hr, d.2, and_self, ↓reduceDIte]
      exact sum_coeffSup_le hρ (P.CE_fin r hr v u d) hKc
    calc Real.sqrt (π u / π v) * ∑ d : Finset.Icc 2 D, (∑ l ∈ Finset.range (Kc + 1),
          ρ ^ l / (l.factorial : ℝ) * edgeSup t₀ t₁ H CE v u r d.1 l) / ρ ^ (d.1 - 2) ≤
          Real.sqrt (π u / π v) * (B * ∑ d : Finset.Icc 2 D,
            (coefficientSeminorm ρ N t₀ t₁ (CE r v u d)).toReal / (B * ρ ^ (d.1 - 2))) :=
          mul_le_mul_of_nonneg_left hX (Real.sqrt_nonneg _)
      _ = B * (Real.sqrt (π u / π v) * ∑ d : Finset.Icc 2 D,
            (coefficientSeminorm ρ N t₀ t₁ (CE r v u d)).toReal / (B * ρ ^ (d.1 - 2))) := by
          ring
      _ ≤ B * (Cstar ^ r * (Aedge ^ r) v u) :=
          mul_le_mul_of_nonneg_left (edge_mean_real P hr v u
            (mul_nonneg (pow_nonneg hC r) (hApos r v u))) hB.le
  have hg := gfbE_nonneg Kc D H p
  unfold cellCgE
  rw [mul_left_comm, Finset.mul_sum]
  calc gfbE Kc D H p * ∑ r ∈ Finset.Icc 1 H, Real.sqrt (π u / π v) * ∑ d : Finset.Icc 2 D,
        (∑ l ∈ Finset.range (Kc + 1), ρ ^ l / (l.factorial : ℝ) *
          edgeSup t₀ t₁ H CE v u r d.1 l) / ρ ^ (d.1 - 2) ≤
        gfbE Kc D H p * ∑ r ∈ Finset.Icc 1 H, B * (Cstar ^ r * (Aedge ^ r) v u) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hr) hg
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The mass-weighted Schur constant of the edge constants of a cell. -/
def edgeS (Kc D H p : ℕ) (B Cstar Θ : ℝ) : ℝ :=
  gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r

/-- **Row sums.** -/
theorem edge_row_le {Kc : ℕ} (hKc : Kc ≤ N) (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) (v : ι) :
    ∑ u, Real.sqrt (π u / π v) * cellCgE ρ Kc D H p t₀ t₁ CE v u ≤ edgeS Kc D H p B Cstar Θ := by
  have hgB : 0 ≤ gfbE Kc D H p * B := mul_nonneg (gfbE_nonneg _ _ _ _) P.B_pos.le
  calc ∑ u, Real.sqrt (π u / π v) * cellCgE ρ Kc D H p t₀ t₁ CE v u ≤
        ∑ u, gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * (Aedge ^ r) v u :=
        Finset.sum_le_sum fun u _ => edge_weighted_le P hKc hC hΘ v u
    _ = gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * ∑ u, (Aedge ^ r) v u := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
    _ ≤ gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * Θ ^ r :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
          ((matrix_pow_row_sum_le Aedge P.edge_nonneg hΘ P.edge_row r).2 v) (pow_nonneg hC r)) hgB
    _ = edgeS Kc D H p B Cstar Θ := by
        unfold edgeS
        simp only [mul_pow]

/-- **Column sums.** -/
theorem edge_col_le {Kc : ℕ} (hKc : Kc ≤ N) (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ) (u : ι) :
    ∑ v, Real.sqrt (π u / π v) * cellCgE ρ Kc D H p t₀ t₁ CE v u ≤ edgeS Kc D H p B Cstar Θ := by
  have hgB : 0 ≤ gfbE Kc D H p * B := mul_nonneg (gfbE_nonneg _ _ _ _) P.B_pos.le
  calc ∑ v, Real.sqrt (π u / π v) * cellCgE ρ Kc D H p t₀ t₁ CE v u ≤
        ∑ v, gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * (Aedge ^ r) v u :=
        Finset.sum_le_sum fun v _ => edge_weighted_le P hKc hC hΘ v u
    _ = gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * ∑ v, (Aedge ^ r) v u := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
    _ ≤ gfbE Kc D H p * B * ∑ r ∈ Finset.Icc 1 H, Cstar ^ r * Θ ^ r :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
          (matrix_pow_col_sum_le Aedge P.edge_nonneg hΘ P.edge_col r u) (pow_nonneg hC r)) hgB
    _ = edgeS Kc D H p B Cstar Θ := by
        unfold edgeS
        simp only [mul_pow]

end
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleComparison.Coarse

/-! The energy estimate of one component of a coarse response: each component of a zero-coupled
genuine second-order energy solution is a one-component solution, so the coupled energy
estimate `coupled_energy_torus` applies to it alone (with its own mass). This gives the supremum
in time componentwise, as needed by the strong energy. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [DecidableEq ι] in
/-- One component of a zero-coupled solution is a one-component solution. -/
theorem isCoupledWeakSolutionTorus_component {ν : ℝ} {D' : ℕ} {K : ℕ}
    {f₀ : ∀ v, TorusHk K (h v)} {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))}
    {u : ∀ v, ℝ → TorusHk K (h v)} {w : ∀ v, ℝ → TorusHk (K + 1) (h v)}
    (hsol : IsCoupledWeakSolutionTorus ν t₀ t₁ b D' (fun _ => K) (fun _ _ _ _ _ => 0) f₀ G
      (fun _ _ => 0) u w) (v : ι) :
    IsCoupledWeakSolutionTorus (h := fun _ : Unit => h v) ν t₀ t₁ b D' (fun _ => K)
      (fun _ _ _ _ _ => 0) (fun _ => f₀ v) (fun _ => G v) (fun _ _ => 0) (fun _ => u v)
      (fun _ => w v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsol
  refine ⟨fun _ => h1 v, fun _ => h2 v, fun _ => h3 v, fun _ => h4 v, fun _ t ht φ => ?_⟩
  have h5v := h5 v t ht φ
  simp only [zero_apply, Finset.sum_const_zero] at h5v ⊢
  exact h5v

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The energy of one coarse response: the strong energy (componentwise supremum in time plus
`B` times the gradient energy) is at most `√(6 F² + 24/B ∫ ‖G‖²)`, with `F` the mass norm of the
initial datum and `G` the flux. Each component is estimated by the coupled energy theorem
`coupled_energy_torus` applied to it alone. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- The flux mass norm of one time. -/
def fluxMass (ρ : ℝ) (π : ι → ℝ) {K : ℕ}
    (G : ∀ v, TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))) : ℝ :=
  ∑ v, (π v)⁻¹ * factorialNormSq ρ (G v).val

/-- **One component of a coarse response.** -/
theorem response_component_le
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {K : ℕ} (hKN : K ≤ N) {f₀ : ∀ v, TorusHk K (h v)}
    {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))}
    (hG : ∀ v, MemLp (G v) 2 (volume.restrict (Set.Icc t₀ t₁)))
    {u : ∀ v, ℝ → TorusHk K (h v)} {w : ∀ v, ℝ → TorusHk (K + 1) (h v)}
    (hsol : IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => K) (fun _ _ _ _ _ => 0) f₀ G
      (fun _ _ => 0) u w) (v : ι) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    (π v)⁻¹ * factorialNormSq ρ (u v t).val +
        B / 2 * ∫ s in Set.Icc t₀ t₁, (π v)⁻¹ * gradFactorialNormSq ρ (w v s).val ≤
      2 * ((π v)⁻¹ * factorialNormSq ρ (f₀ v).val) +
        8 / B * ∫ s in Set.Icc t₀ t₁, (π v)⁻¹ * factorialNormSq ρ (G v s).val := by
  have hE := (coupled_energy_torus (h := fun _ : Unit => h v) t₀ t₁ P.window ρ P.rho_pos B
    P.B_pos b P.drift_bdd P.drift_meas P.drift_smooth P.drift_div P.drift_per a B₀ lam
    P.a_nonneg P.B₀_ge P.lam_pos N P.drift_jets P.drift_scale P.drift_small 2 (by norm_num)
    (fun _ => π v) (fun _ => P.mass_pos v) (fun _ => K) (fun _ => hKN) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ => by simp [coefficientSeminorm_const_zero])
    (zeroCoupling_schur B ρ (fun _ => π v) (fun _ => K) 2 t₀ t₁) (fun _ => f₀ v)
    (fun _ => G v) (fun _ => hG v) (fun _ _ => 0) (fun _ => timeIntegrable_zero _)).2.2
    (fun _ => u v) (fun _ => w v) (isCoupledWeakSolutionTorus_component hsol v) t ht
  simp only [massNormSq, massGradNormSq, Finset.univ_unique, Finset.sum_singleton] at hE
  have hz : (∫ s in Set.Icc t₀ t₁,
      Real.sqrt ((π v)⁻¹ * factorialNormSq ρ (0 : TorusHk K (h v)).val)) = 0 := by
    simp [factorialNormSq, derivativeNormSq]
  rw [hz] at hE
  simpa using hE

/-- The componentwise strong energy from the energy inequality (abstract form). -/
theorem comp_energy_abstract {I : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ I) {c B : ℝ} (hc : 0 ≤ c)
    (hB : 0 < B) {x : ℝ → ℝ} (hx : ∀ t, 0 ≤ x t) {g : ℝ → ℝ} (hg : ∀ s, 0 ≤ g s)
    (hgi : Integrable g (volume.restrict I)) {R : ℝ}
    (hbound : ∀ t ∈ I, c * x t + B / 2 * ∫ s in I, c * g s ≤ R) :
    ENNReal.ofReal c * ((⨆ t ∈ I, ENNReal.ofReal (x t)) +
        ENNReal.ofReal B * ∫⁻ s in I, ENNReal.ofReal (g s)) ≤ ENNReal.ofReal (3 * R) := by
  have hY : 0 ≤ ∫ s in I, g s := integral_nonneg hg
  have hR : 0 ≤ R := by
    have := hbound t₀ ht₀
    rw [integral_const_mul] at this
    have h1 : 0 ≤ c * x t₀ := mul_nonneg hc (hx t₀)
    have h2 : 0 ≤ B / 2 * (c * ∫ s in I, g s) := by positivity
    linarith
  rw [mul_add]
  have h1 : ENNReal.ofReal c * (⨆ t ∈ I, ENNReal.ofReal (x t)) ≤ ENNReal.ofReal R := by
    rw [ENNReal.mul_iSup]
    refine iSup_le fun t => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun ht => ?_
    rw [← ENNReal.ofReal_mul hc]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hbound t ht
    rw [integral_const_mul] at this
    have h2 : 0 ≤ B / 2 * (c * ∫ s in I, g s) := by positivity
    linarith
  have h2 : ENNReal.ofReal c * (ENNReal.ofReal B * ∫⁻ s in I, ENNReal.ofReal (g s)) ≤
      ENNReal.ofReal (2 * R) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg),
      ← ENNReal.ofReal_mul hB.le, ← ENNReal.ofReal_mul hc]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hbound t₀ ht₀
    rw [integral_const_mul] at this
    have h1 : 0 ≤ c * x t₀ := mul_nonneg hc (hx t₀)
    nlinarith
  calc _ ≤ ENNReal.ofReal R + ENNReal.ofReal (2 * R) := add_le_add h1 h2
    _ = ENNReal.ofReal (3 * R) := by
        rw [← ENNReal.ofReal_add hR (by linarith)]; ring_nf

/-- Square roots of finite sums of componentwise bounds. -/
theorem sum_rpow_half_le {κ : Type*} [Fintype κ] {A : κ → ℝ≥0∞} {R : κ → ℝ} (hR : ∀ c, 0 ≤ R c)
    (hA : ∀ c, A c ≤ ENNReal.ofReal (R c)) :
    (∑ c, A c) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (∑ c, R c)) := by
  have h1 : (∑ c, A c) ≤ ENNReal.ofReal (∑ c, R c) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun c _ => hR c]
    exact Finset.sum_le_sum fun c _ => hA c
  refine (ENNReal.rpow_le_rpow h1 (by norm_num)).trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun c _ => hR c)
    (by norm_num)]

/-- The right side of one component's energy bound. -/
def compRHS (ρ B t₀ t₁ : ℝ) (πv : ℝ) {K : ℕ} {Ev : Type*} [NormedAddCommGroup Ev]
    [InnerProductSpace ℝ Ev] [FiniteDimensional ℝ Ev] [MeasurableSpace Ev] [BorelSpace Ev]
    [CompleteSpace Ev] (f₀v : TorusHk K Ev) (Gv : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => Ev))) : ℝ :=
  3 * (2 * (πv⁻¹ * factorialNormSq ρ f₀v.val) +
    8 / B * ∫ s in Set.Icc t₀ t₁, πv⁻¹ * factorialNormSq ρ (Gv s).val)

/-- **The strong energy of a coarse response.** -/
theorem response_strongEnergy_le
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {K : ℕ} (hKN : K ≤ N) {f₀ : ∀ v, TorusHk K (h v)}
    {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))}
    (hG : ∀ v, MemLp (G v) 2 (volume.restrict (Set.Icc t₀ t₁)))
    {u : ∀ v, ℝ → TorusHk K (h v)} {w : ∀ v, ℝ → TorusHk (K + 1) (h v)}
    (hsol : IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => K) (fun _ _ _ _ _ => 0) f₀ G
      (fun _ _ => 0) u w) :
    strongEnergy ρ B π t₀ t₁ u w ≤
      ENNReal.ofReal (Real.sqrt (∑ v, compRHS ρ B t₀ t₁ (π v) (f₀ v) (G v))) := by
  have hB : 0 < B := P.B_pos
  have hI : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_rfl, P.window⟩
  have hcomp : ∀ v, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u v t).val)) +
        ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁,
          ENNReal.ofReal (gradFactorialNormSq ρ (w v s).val)) ≤
      ENNReal.ofReal (compRHS ρ B t₀ t₁ (π v) (f₀ v) (G v)) := by
    intro v
    have hbd : ∀ t ∈ Set.Icc t₀ t₁, (π v)⁻¹ * factorialNormSq ρ (u v t).val +
        B / 2 * ∫ s in Set.Icc t₀ t₁, (π v)⁻¹ * gradFactorialNormSq ρ (w v s).val ≤
        2 * ((π v)⁻¹ * factorialNormSq ρ (f₀ v).val) +
          8 / B * ∫ s in Set.Icc t₀ t₁, (π v)⁻¹ * factorialNormSq ρ (G v s).val :=
      fun t ht => response_component_le P hKN hG hsol v ht
    exact comp_energy_abstract (x := fun t => factorialNormSq ρ (u v t).val)
      (g := fun s => gradFactorialNormSq ρ (w v s).val) hI (inv_nonneg.2 (P.mass_pos v).le) hB
      (fun t => factorialNormSq_nonneg ρ _) (fun s => gradFactorialNormSq_nonneg ρ _)
      (integrable_gradFactorialNormSq_torus (hsol.2.1 v)) hbd
  have hR0 : ∀ v, 0 ≤ compRHS ρ B t₀ t₁ (π v) (f₀ v) (G v) := by
    intro v
    have hp : 0 ≤ (π v)⁻¹ := inv_nonneg.2 (P.mass_pos v).le
    have h1 : 0 ≤ (π v)⁻¹ * factorialNormSq ρ (f₀ v).val :=
      mul_nonneg hp (factorialNormSq_nonneg ρ _)
    have h2 : 0 ≤ ∫ s in Set.Icc t₀ t₁, (π v)⁻¹ * factorialNormSq ρ (G v s).val :=
      integral_nonneg fun s => mul_nonneg hp (factorialNormSq_nonneg ρ _)
    have h3 : 0 ≤ 8 / B := div_nonneg (by norm_num) hB.le
    have h4 : (0 : ℝ) ≤ 3 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 := by norm_num
    unfold compRHS
    exact mul_nonneg h4 (add_nonneg (mul_nonneg h5 h1) (mul_nonneg h3 h2))
  unfold strongEnergy
  exact sum_rpow_half_le hR0 hcomp

end AVRegularity.CycleComparison.Coarse
end

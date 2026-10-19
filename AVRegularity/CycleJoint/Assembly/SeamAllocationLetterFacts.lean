-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.PatchModelBound
import AVRegularity.CycleWords.Seam.OldNegative
import AVRegularity.CycleComparison.Residual.MixedTail.Energy
import AVRegularity.Proofs.Intermediate.CycleWords.ScalarPackageInterior
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.Proofs.QuietAtlas.QuietPulse
public import AVRegularity.CycleJoint.Assembly.FollowingExplicitEnergyError

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The sum over the allocations**.

The cell model is the sum over the allocations of the seam's kernels applied to the cutoff inputs.
The literal cutoff is exactly linear on square-integrable functions (its kernel is a Schwartz
function, so the convolution integrals converge) and depends only on the a.e. class of its
argument, so the input `seamInput` of a linear family of old endpoints is linear. The weighted jet
norm satisfies the triangle inequality over finite sums, and the bounds of the allocations add up. -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The integrand of the literal cutoff of a square-integrable function is integrable. -/
theorem fourierCutoff_integrand_integrable (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g : Vec 2 → E} (hg : MemLp g 2 volume) (y : Vec 2) :
    Integrable (fun x => cutoffKernel m x • g (y - x)) volume := by
  have hk : MemLp (cutoffKernel m) 2 volume := by
    rw [← CycleWords.seamRealCutoffSchwartz_eq m R hm hs]
    exact (CycleWords.seamRealCutoffSchwartz m R hm hs).memLp 2
  have hg' : MemLp (fun x => g (y - x)) 2 volume :=
    hg.comp_measurePreserving ((volume : Measure (Vec 2)).measurePreserving_sub_left y)
  exact memLp_one_iff_integrable.1 (hk.smul hg')

/-- The literal cutoff depends only on the a.e. class of its argument. -/
theorem fourierCutoff_congr_ae (m : Vec 2 → ℝ) {g₁ g₂ : Vec 2 → E}
    (h : g₁ =ᵐ[volume] g₂) : fourierCutoff m g₁ = fourierCutoff m g₂ := by
  funext y
  unfold fourierCutoff
  apply integral_congr_ae
  have ht : (fun x : Vec 2 => g₁ (y - x)) =ᵐ[volume] fun x => g₂ (y - x) :=
    ((volume : Measure (Vec 2)).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ht] with x hx
  rw [hx]

/-- The literal cutoff is additive on square-integrable functions. -/
theorem fourierCutoff_add_of_memLp (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g₁ g₂ : Vec 2 → E} (h₁ : MemLp g₁ 2 volume) (h₂ : MemLp g₂ 2 volume) :
    fourierCutoff m (fun z => g₁ z + g₂ z) =
      fun z => fourierCutoff m g₁ z + fourierCutoff m g₂ z := by
  funext y
  unfold fourierCutoff
  simp only [smul_add]
  exact integral_add (fourierCutoff_integrand_integrable m R hm hs h₁ y)
    (fourierCutoff_integrand_integrable m R hm hs h₂ y)

/-- The literal cutoff is homogeneous. -/
theorem fourierCutoff_smul (m : Vec 2 → ℝ) (c : ℝ) (g : Vec 2 → E) :
    fourierCutoff m (fun z => c • g z) = fun z => c • fourierCutoff m g z := by
  funext y
  unfold fourierCutoff
  simp only [smul_comm (cutoffKernel m _) c]
  exact integral_smul c _

end Cutoff

section Input

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {K : ι → ℕ}

/-- The seam's input is linear in the old endpoints. -/
theorem seamInput_linear (χm : Vec 2 → ℝ) (η : ℝ) (Υ : Vec 2 → Vec 2) (R : ℝ)
    (hm : ∀ θ, R ≤ Real.sqrt (vecDot θ θ) → χm ((Real.sqrt η)⁻¹ • θ) = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun θ => χm ((Real.sqrt η)⁻¹ • θ))) (c : ℝ)
    (U V : ∀ x, PlaneHk Set.univ (K x) (h x)) :
    seamInput χm η Υ (fun x => c • U x + V x) =
      c • seamInput χm η Υ U + seamInput χm η Υ V := by
  funext x z
  simp only [seamInput, Pi.add_apply, Pi.smul_apply]
  have hae : planeValue (c • U x + V x) =ᵐ[volume]
      fun z => c • planeValue (U x) z + planeValue (V x) z := by
    filter_upwards [planeJetOrder_add_all_ae 0 (fun i => i.elim0) (c • U x) (V x),
      planeJetOrder_smul_ae 0 (fun i => i.elim0) c (U x)] with z h1 h2
    unfold planeValue
    rw [h1, h2]
  have hadd := fourierCutoff_add_of_memLp (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) R hm hs
    (g₁ := fun z => c • planeValue (U x) z) (g₂ := planeValue (V x))
    ((CycleWords.Assembly.planeValue_memLp (U x)).const_smul c)
    (CycleWords.Assembly.planeValue_memLp (V x))
  rw [fourierCutoff_congr_ae _ hae, hadd, fourierCutoff_smul]

end Input

section Norms

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- The weighted jet norm of the zero jets. -/
theorem weightedJetNorm_zero_jets (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) :
    weightedJetNorm π p j s r (fun v a (_ : DerivativeWord2 a) (_ : Vec 2) => (0 : h v)) = 0 := by
  unfold weightedJetNorm
  refine Finset.sum_eq_zero fun a _ => ?_
  simp

/-- The triangle inequality of the weighted jet norm over a finite sum. -/
theorem weightedJetNorm_finset_sum_le {κ : Type*} (S : Finset κ) (π : ι → ℝ) (p : ℝ) (j : ℕ)
    (s r : ℝ) (J : κ → ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ k ∈ S, ∀ v a w, AEStronglyMeasurable (J k v a w) volume) :
    weightedJetNorm π p j s r (fun v a w z => ∑ k ∈ S, J k v a w z) ≤
      ∑ k ∈ S, weightedJetNorm π p j s r (J k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (weightedJetNorm_zero_jets π p j s r).le
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    have hS : ∀ k' ∈ S, ∀ v a w, AEStronglyMeasurable (J k' v a w) volume :=
      fun k' hk' => hJ k' (Finset.mem_insert_of_mem hk')
    refine (CycleWords.Assembly.weightedJetNorm_add_le π p j s r (J k)
      (fun v a w z => ∑ k' ∈ S, J k' v a w z) (hJ k (Finset.mem_insert_self k S))
      (fun v a w => Finset.aestronglyMeasurable_fun_sum S fun k' hk' => hS k' hk' v a w)).trans ?_
    exact add_le_add le_rfl (ih hS)

end Norms

section Sum

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {K : ι → ℕ}

/-- `planeJetOrder` of a finite sum is a.e. the sum. -/
theorem planeJetOrder_finset_sum_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {L : ℕ} {κ : Type*} (S : Finset κ)
    (V : κ → PlaneHk Set.univ L E) (a : ℕ) (w : DerivativeWord2 a) :
    planeJetOrder (∑ k ∈ S, V k) a w =ᵐ[volume] fun z => ∑ k ∈ S, planeJetOrder (V k) a w z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    by_cases ha : a ≤ L
    · exact CycleWords.planeJetOrder_zero_ae ha w
    · exact Filter.Eventually.of_forall fun z => by simp [planeJetOrder, ha]
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [planeJetOrder_add_all_ae a w (V k) (∑ k' ∈ S, V k'), ih] with z h1 h2
    rw [h1, h2]

/-- **The sum of the allocations.** Per-allocation smooth models with weighted jet bounds and
masked error bounds add up to the model `Σ_k Kp k ∘ inp k` with the summed constants. -/
theorem seamSum_bounds {X : Type*} [AddCommGroup X] [Module ℝ X] {κ : Type*} (S : Finset κ)
    (inp : κ → X →ₗ[ℝ] (∀ x, Vec 2 → h x)) (Kp : κ → (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (U : κ → X → ∀ x, PlaneHk Set.univ (K x) (h x)) (π : ι → ℝ) (pout : ℝ) (Mb Kmax : ℕ)
    (ϖ rs : ℝ) (mom : X → ℝ≥0∞) (bM : κ → ℕ → ℝ) (bE : κ → ℝ)
    (hbM : ∀ k ∈ S, ∀ M, 0 ≤ bM k M) (hbE : ∀ k ∈ S, 0 ≤ bE k)
    (hsm : ∀ k ∈ S, ∀ ξ x (M : ℕ), ContDiff ℝ M (Kp k (inp k ξ) x))
    (hmod : ∀ k ∈ S, ∀ ξ, ∀ M ≤ Mb, weightedJetNorm π pout M ϖ ϖ⁻¹
      (fun x _ wd z => orderedDerivative wd (Kp k (inp k ξ) x) z) ≤
        ENNReal.ofReal (bM k M) * mom ξ)
    (herr : ∀ k ∈ S, ∀ ξ, weightedJetNorm π pout Kmax ϖ rs
      (fun x a' wd z => if a' ≤ K x then
        planeJetOrder (U k ξ x) a' wd z - orderedDerivative wd (Kp k (inp k ξ) x) z else 0) ≤
        ENNReal.ofReal (bE k) * mom ξ) :
    (∀ ξ x (M : ℕ), ContDiff ℝ M ((∑ k ∈ S, (Kp k).comp (inp k)) ξ x)) ∧
    (∀ ξ, ∀ M ≤ Mb, weightedJetNorm π pout M ϖ ϖ⁻¹
      (fun x _ wd z => orderedDerivative wd ((∑ k ∈ S, (Kp k).comp (inp k)) ξ x) z) ≤
        ENNReal.ofReal (∑ k ∈ S, bM k M) * mom ξ) ∧
    ∀ ξ, weightedJetNorm π pout Kmax ϖ rs
      (fun x a' wd z => if a' ≤ K x then
        planeJetOrder (∑ k ∈ S, U k ξ x) a' wd z -
          orderedDerivative wd ((∑ k ∈ S, (Kp k).comp (inp k)) ξ x) z else 0) ≤
        ENNReal.ofReal (∑ k ∈ S, bE k) * mom ξ := by
  have hMc : ∀ ξ x, (∑ k ∈ S, (Kp k).comp (inp k)) ξ x = fun z => ∑ k ∈ S, Kp k (inp k ξ) x z := by
    intro ξ x
    funext z
    simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply]
  have hder : ∀ ξ x (a : ℕ) (wd : DerivativeWord2 a),
      orderedDerivative wd ((∑ k ∈ S, (Kp k).comp (inp k)) ξ x) =
        fun z => ∑ k ∈ S, orderedDerivative wd (Kp k (inp k ξ) x) z := by
    intro ξ x a wd
    rw [hMc]
    exact MixedTail.orderedDerivative_sum S wd fun k hk => hsm k hk ξ x a
  refine ⟨fun ξ x M => ?_, fun ξ M hM => ?_, fun ξ => ?_⟩
  · rw [hMc]
    exact ContDiff.sum fun k hk => hsm k hk ξ x M
  · have heq : (fun x a (wd : DerivativeWord2 a) z =>
        orderedDerivative wd ((∑ k ∈ S, (Kp k).comp (inp k)) ξ x) z) =
        fun x a wd z => ∑ k ∈ S, orderedDerivative wd (Kp k (inp k ξ) x) z := by
      funext x a wd z
      rw [hder]
    rw [heq]
    refine (weightedJetNorm_finset_sum_le S π pout M ϖ ϖ⁻¹ _ fun k hk v a w =>
      (CycleWords.Assembly.orderedDerivative_continuous w (hsm k hk ξ v a)).aestronglyMeasurable).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun k hk => hbM k hk M, Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk => hmod k hk ξ M hM
  · have hae : ∀ v a (wd : DerivativeWord2 a),
        (fun z => if a ≤ K v then planeJetOrder (∑ k ∈ S, U k ξ v) a wd z -
          orderedDerivative wd ((∑ k ∈ S, (Kp k).comp (inp k)) ξ v) z else 0) =ᵐ[volume]
        fun z => ∑ k ∈ S, (if a ≤ K v then planeJetOrder (U k ξ v) a wd z -
          orderedDerivative wd (Kp k (inp k ξ) v) z else 0) := by
      intro v a wd
      by_cases ha : a ≤ K v
      · filter_upwards [planeJetOrder_finset_sum_ae S (fun k => U k ξ v) a wd] with z hz
        simp only [ha, ↓reduceIte, hz, hder, Finset.sum_sub_distrib]
      · exact Filter.Eventually.of_forall fun z => by simp [ha]
    rw [CycleWords.Seam.weightedJetNorm_congr_ae π pout Kmax ϖ rs hae]
    refine (weightedJetNorm_finset_sum_le S π pout Kmax ϖ rs _ fun k hk v a w => ?_).trans ?_
    · by_cases ha : a ≤ K v
      · simp only [ha, ↓reduceIte]
        exact (CycleWords.Assembly.planeJetOrder_aestronglyMeasurable (U k ξ v) a w).sub
          (CycleWords.Assembly.orderedDerivative_continuous w
            (hsm k hk ξ v a)).aestronglyMeasurable
      · simp only [ha, ↓reduceIte]
        exact aestronglyMeasurable_const
    · rw [ENNReal.ofReal_sum_of_nonneg hbE, Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk => herr k hk ξ

end Sum

section InputFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- A map with `f (c • x + y) = c • f x + f y` as a linear map. -/
def linearMapOfCombo {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (f : X → Y) (hf : ∀ (c : ℝ) x y, f (c • x + y) = c • f x + f y) : X →ₗ[ℝ] Y where
  toFun := f
  map_add' x y := by simpa using hf 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by
      have := hf 1 0 0
      simp only [smul_zero, add_zero, one_smul] at this
      exact left_eq_add.mp this
    simpa [h0] using hf c x 0

/-- The inputs of the allocations as linear maps (the old word's input; `0` off `W1`). -/
def seamInputFamily {X : Type*} [AddCommGroup X] [Module ℝ X] (W1 : Finset (List Bool))
    (inp : List Bool → X → (∀ x, Vec 2 → h x))
    (hinp : ∀ wo ∈ W1, ∀ (c : ℝ) ξ ξ', inp wo (c • ξ + ξ') = c • inp wo ξ + inp wo ξ')
    (σ : List Bool × List Bool) : X →ₗ[ℝ] (∀ x, Vec 2 → h x) :=
  if hσ : σ.1 ∈ W1 then linearMapOfCombo (inp σ.1) (hinp σ.1 hσ) else 0

theorem seamInputFamily_apply {X : Type*} [AddCommGroup X] [Module ℝ X]
    {W1 : Finset (List Bool)} {inp : List Bool → X → (∀ x, Vec 2 → h x)}
    {hinp : ∀ wo ∈ W1, ∀ (c : ℝ) ξ ξ', inp wo (c • ξ + ξ') = c • inp wo ξ + inp wo ξ'}
    {σ : List Bool × List Bool} (hσ : σ.1 ∈ W1) (ξ : X) :
    seamInputFamily W1 inp hinp σ ξ = inp σ.1 ξ := by
  unfold seamInputFamily
  simp only [hσ, ↓reduceDIte]
  rfl

end InputFamily

section SumProd

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {K : ι → ℕ}

/-- `seamSum_bounds` over the allocations `W1 ×ˢ W2`, with inputs given by functions of the old
word that are linear on `W1`, and with the error of the double sum. -/
theorem seamSum_bounds_prod {X : Type*} [AddCommGroup X] [Module ℝ X]
    (W1 W2 : Finset (List Bool)) (inpF : List Bool → X → (∀ x, Vec 2 → h x))
    (hinp : ∀ wo ∈ W1, ∀ (c : ℝ) ξ ξ', inpF wo (c • ξ + ξ') = c • inpF wo ξ + inpF wo ξ')
    (Kp : List Bool × List Bool → (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x))
    (U : List Bool → List Bool → X → ∀ x, PlaneHk Set.univ (K x) (h x)) (π : ι → ℝ)
    (pout : ℝ) (Mb Kmax : ℕ) (ϖ rs : ℝ) (mom : X → ℝ≥0∞)
    (bM : List Bool × List Bool → ℕ → ℝ) (bE : List Bool × List Bool → ℝ)
    (hbM : ∀ k ∈ W1 ×ˢ W2, ∀ M, 0 ≤ bM k M) (hbE : ∀ k ∈ W1 ×ˢ W2, 0 ≤ bE k)
    (hsm : ∀ k ∈ W1 ×ˢ W2, ∀ ξ x (M : ℕ), ContDiff ℝ M (Kp k (inpF k.1 ξ) x))
    (hmod : ∀ k ∈ W1 ×ˢ W2, ∀ ξ, ∀ M ≤ Mb, weightedJetNorm π pout M ϖ ϖ⁻¹
      (fun x _ wd z => orderedDerivative wd (Kp k (inpF k.1 ξ) x) z) ≤
        ENNReal.ofReal (bM k M) * mom ξ)
    (herr : ∀ k ∈ W1 ×ˢ W2, ∀ ξ, weightedJetNorm π pout Kmax ϖ rs
      (fun x a' wd z => if a' ≤ K x then
        planeJetOrder (U k.1 k.2 ξ x) a' wd z - orderedDerivative wd (Kp k (inpF k.1 ξ) x) z
        else 0) ≤
        ENNReal.ofReal (bE k) * mom ξ) :
    ∃ Mc : X →ₗ[ℝ] (∀ x, Vec 2 → h x),
    (∀ ξ, Mc ξ = ∑ k ∈ W1 ×ˢ W2, Kp k (inpF k.1 ξ)) ∧
    (∀ ξ x (M : ℕ), ContDiff ℝ M (Mc ξ x)) ∧
    (∀ ξ, ∀ M ≤ Mb, weightedJetNorm π pout M ϖ ϖ⁻¹
      (fun x _ wd z => orderedDerivative wd (Mc ξ x) z) ≤
        ENNReal.ofReal (∑ k ∈ W1 ×ˢ W2, bM k M) * mom ξ) ∧
    ∀ ξ, weightedJetNorm π pout Kmax ϖ rs
      (fun x a' wd z => if a' ≤ K x then
        planeJetOrder (∑ wo ∈ W1, ∑ wf ∈ W2, U wo wf ξ x) a' wd z -
          orderedDerivative wd (Mc ξ x) z else 0) ≤
        ENNReal.ofReal (∑ k ∈ W1 ×ˢ W2, bE k) * mom ξ := by
  have happ : ∀ k ∈ W1 ×ˢ W2, ∀ ξ, seamInputFamily W1 inpF hinp k ξ = inpF k.1 ξ :=
    fun k hk ξ => seamInputFamily_apply (Finset.mem_product.1 hk).1 ξ
  obtain ⟨h1, h2, h3⟩ := seamSum_bounds (W1 ×ˢ W2) (seamInputFamily W1 inpF hinp) Kp
    (fun k => U k.1 k.2) π pout Mb Kmax ϖ rs mom bM bE hbM hbE
    (fun k hk ξ => by rw [happ k hk ξ]; exact hsm k hk ξ)
    (fun k hk ξ => by rw [happ k hk ξ]; exact hmod k hk ξ)
    (fun k hk ξ => by rw [happ k hk ξ]; exact herr k hk ξ)
  refine ⟨_, fun ξ => ?_, h1, h2, fun ξ => ?_⟩
  · rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k hk => by rw [LinearMap.comp_apply, happ k hk ξ]
  have hsum : ∀ x, ∑ wo ∈ W1, ∑ wf ∈ W2, U wo wf ξ x = ∑ k ∈ W1 ×ˢ W2, U k.1 k.2 ξ x :=
    fun x => (Finset.sum_product W1 W2 (fun k => U k.1 k.2 ξ x)).symm
  simp only [hsum]
  exact h3 ξ

end SumProd

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The scalar packages of the two renewal blocks**.

`ScalarPackageClause` is the clause of `scalar_package_interior` for fixed scalar
constants `K` and length threshold `Θ₀`. `seamRenewalBlock`: for a cell metric near the identity
and the renewal block of label `l` (`[(l - 1/2) τ'', (l + 1/2) τ'']`), long pulses give the
admissibility (`renewal_block_admissible_of_long_pulses`, with empty marks when `θ_s ≤ 0`), the
`scalar_package_interior` gives regions and a package, the quiet margins at both renewal boundaries give the buffer
bound `τ/(4ℓ²)`, and the buffer is shrunk to exactly `τ/(4ℓ²)`. -/

/-- The clause of `scalar_package_interior` for fixed constants `K` and threshold `Θ₀`. -/
def ScalarPackageClause (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (K : ScalarConstants) (Θ₀ : ℝ) : Prop :=
  ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
    ∀ y₀ : Vec 2, ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ),
      IsCellMetric (fun t _ => G t) → 0 ≤ g → g ≤ K.g0 →
      IsMetricNearIdentity (fun t _ => G t) g →
      IsCellDrift (ocCellDrift α q Λ ζ m ν y₀) ∧
      (∀ t (k : Fin 2),
        cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x k : ℂ)) = 0) ∧
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν y₀ t)) ∧
      (∀ t x, Real.sqrt (ν / B) *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ K.Cw) ∧
      (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
        (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν y₀ t z') z‖ ≤ K.Cvj j) ∧
      ∀ ta T : ℝ, IsOCAdmissibleInterval α q Λ ζ m ν B Θ₀ K.θs ta T →
        ∃ reg : BlockRegions,
          (∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2),
            t ∈ reg.quiet ↔
              ∀ s ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                  (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
                ∀ z, ocCellDrift α q Λ ζ m ν y₀ s z = 0) ∧
          (∀ p, ∃ k : ℤ, Odd k ∧
            (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
              |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
            reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
          ((∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2 - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                (ta / ocEll q Λ m ν ^ 2 + 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) ∪
              Set.Icc ((ta + T) / ocEll q Λ m ν ^ 2 - 7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
                ((ta + T) / ocEll q Λ m ν ^ 2 + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
              ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0) →
            min (ocTau α q Λ m / (4 * ocEll q Λ m ν ^ 2)) (T / ocEll q Λ m ν ^ 2) ≤
              reg.buffer) ∧
          (reg.joins : ℝ) ≤ T / ocTau α q Λ m + 4 ∧
          Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
            (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
            (Real.sqrt ((ν / B) / (T / ocEll q Λ m ν ^ 2))) reg)

/-- `scalar_package_interior` with its clause named. -/
theorem scalarPackage_clause (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ ξ₀ ξmax c Cg : ℝ, 0 < g₀ ∧ 0 < ξmax ∧
      ξmax < ξ₀ ∧ 0 < c ∧ 0 < Cg ∧
      ∀ ξlo : ℝ, 0 < ξlo → 2 * ξlo ≤ ξmax →
      ∃ (K : ScalarConstants) (Θ₀ : ℝ), K.ξlo = ξlo ∧ K.g0 = g₀ ∧ K.ξ0 = ξ₀ ∧ K.Cg = Cg ∧
        K.cGauss = c ∧ 1 ≤ Θ₀ ∧ ScalarPackageClause α q Λ ζ K Θ₀ :=
  Providers.scalar_package_interior α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

section Blocks

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {ν : ℝ}

/-- Admissibility of a renewal block for the scalar constants `K` from long pulses
(`Θlong ≥ Θ₀, 3 max θ_s 1`); for `θ_s ≤ 0` the marks are empty. -/
theorem renewalBlock_admissible_K (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hν : 0 < ν)
    (K : ScalarConstants) {Θ₀ Θlong : ℝ} (hΘ₀ : 1 ≤ Θ₀) (hΘ₀l : Θ₀ ≤ Θlong)
    (hΘ3 : 3 * max K.θs 1 ≤ Θlong) (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (l : ℤ) :
    IsOCAdmissibleInterval α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) Θ₀ K.θs
      (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) (ocTauPP α q Λ m) := by
  by_cases hθ : 0 < K.θs
  · obtain ⟨h1, h2, h3, h4⟩ := CycleDamping.renewal_block_admissible_of_long_pulses (α := α) (q := q)
      (m := m) hΛ hζ hν Θlong K.θs (by linarith) hθ
      (by have := le_max_left K.θs 1; linarith) hlong l
    exact ⟨hΘ₀l.trans h1, hΘ₀l.trans h2, h3, h4⟩
  · obtain ⟨h1, h2, h3, -⟩ := CycleDamping.renewal_block_admissible_of_long_pulses (α := α) (q := q)
      (m := m) hΛ hζ hν Θlong 1 (by linarith) one_pos
      (by have := le_max_right K.θs 1; linarith) hlong l
    refine ⟨hΘ₀l.trans h1, hΘ₀l.trans h2, h3, fun _ => ⟨∅, ?_, by simp, by simp⟩⟩
    rw [Finset.card_empty, Nat.cast_zero]
    have he : 0 < 1 - Real.exp (-2) := by
      have h := Real.exp_lt_exp.2 (show (-2 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at h
      linarith
    have hS : 0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
      div_nonneg (Construction.Stream.ocTauPP_pos hΛ).le (ocEll_sq_pos_of hΛ hν).le
    exact div_nonpos_of_nonneg_of_nonpos (mul_nonneg (div_nonneg he.le (by norm_num)) hS)
      (not_lt.mp hθ)

/-- Cell-time bounds as physical-time bounds. -/
theorem cell_bounds_mul {L t A B : ℝ} (hL : 0 < L) (h1 : A / L ≤ t) (h2 : t ≤ B / L) :
    A ≤ L * t ∧ L * t ≤ B := by
  rw [div_le_iff₀ hL] at h1
  rw [le_div_iff₀ hL] at h2
  constructor <;> linarith

theorem add_div_mul_eq {X Y c L : ℝ} (hL : L ≠ 0) (hc : c ≠ 0) :
    X / L + Y / (c * L) = (X + Y / c) / L := by
  field_simp

theorem sub_div_mul_eq {X Y c L : ℝ} (hL : L ≠ 0) (hc : c ≠ 0) :
    X / L - Y / (c * L) = (X - Y / c) / L := by
  field_simp

/-- A cell time is trimmed quiet: the cell drift vanishes within `τ/(24ℓ²)` of it
(the pin of the packages' quiet regions). -/
def CellTrimmedQuiet (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (ν : ℝ) (yc : Vec 2) (t : ℝ) : Prop :=
  ∀ s ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
      (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
    ∀ z, ocCellDrift α q Λ ζ m ν yc s z = 0

/-- A cell time is trimmed quiet exactly when its physical time is a trimmed quiet time. -/
theorem cellTrimmedQuiet_iff (hΛ : 1 ≤ Λ) (hν : 0 < ν) (yc : Vec 2) (t : ℝ) :
    CellTrimmedQuiet α q Λ m ζ ν yc t ↔
      ocEll q Λ m ν ^ 2 * t ∈ ocTrimmedQuietTimes α q Λ ζ m := by
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have h24 : ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2) =
      (ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2 := by
    field_simp
  rw [Providers.QuietAtlas.mem_ocTrimmedQuietTimes]
  constructor
  · intro h u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hs : u / ocEll q Λ m ν ^ 2 ∈ Set.Icc (t - ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
        (t + ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) := by
      rw [h24]
      have k1 : t - ocTau α q Λ m / 24 / ocEll q Λ m ν ^ 2 =
          (ocEll q Λ m ν ^ 2 * t - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2 := by
        rw [sub_div, mul_div_cancel_left₀ t hl.ne']
      have k2 : t + ocTau α q Λ m / 24 / ocEll q Λ m ν ^ 2 =
          (ocEll q Λ m ν ^ 2 * t + ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2 := by
        rw [add_div, mul_div_cancel_left₀ t hl.ne']
      rw [k1, k2]
      exact ⟨div_le_div_of_nonneg_right hu1 hl.le, div_le_div_of_nonneg_right hu2 hl.le⟩
    have hq := quiet_of_ocCellDrift_eq_zero hΛ hν yc (h _ hs)
    rwa [mul_div_cancel₀ u hl.ne'] at hq
  · intro h s hs z
    apply ocCellDrift_eq_zero_of_quiet
    apply h
    rw [h24] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have e1 := mul_le_mul_of_nonneg_left hs1 hl.le
    have e2 := mul_le_mul_of_nonneg_left hs2 hl.le
    rw [mul_sub, mul_div_cancel₀ _ hl.ne'] at e1
    rw [mul_add, mul_div_cancel₀ _ hl.ne'] at e2
    exact ⟨e1, e2⟩

/-- A physical time whose `τ/24`-neighbourhood lies in a renewal quiet margin is a trimmed quiet time. -/
theorem trimmed_of_quiet_margin (hΛ : 1 ≤ Λ) (l : ℤ) {u : ℝ}
    (h1 : ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m ≤ u - ocTau α q Λ m / 24)
    (h2 : u + ocTau α q Λ m / 24 ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m) :
    u ∈ ocTrimmedQuietTimes α q Λ ζ m := by
  rw [Providers.QuietAtlas.mem_ocTrimmedQuietTimes]
  intro v hv
  apply renewal_boundary_quiet_margin (α := α) (q := q) (m := m) hΛ ζ l
  obtain ⟨hv1, hv2⟩ := hv
  constructor <;> linarith

/-- The renewal boundaries `(l ∓ 1/2) τ''` of the block `l` carry quiet margins of half-width
`τ' ≥ τ`, so the cell drift vanishes on both end strips `[-τ/24, 7τ/24]` of the block (the buffer premise). -/
theorem renewalBlock_ends_quiet (hΛ : 1 ≤ Λ) (hν : 0 < ν) (yc : Vec 2) (l : ℤ) :
    ∀ t ∈ Set.Icc ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 -
          ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
        ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)) ∪
      Set.Icc ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 -
          7 * ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2))
        ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2)),
      ∀ z, ocCellDrift α q Λ ζ m ν yc t z = 0 := by
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hτ := ocTau_le_ocTauP (α := α) (q := q) (m := m) hΛ
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have h24 : (24 : ℝ) ≠ 0 := by norm_num
  intro t ht z
  apply ocCellDrift_eq_zero_of_quiet
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sub_div_mul_eq hl.ne' h24] at h1
    rw [add_div_mul_eq hl.ne' h24] at h2
    obtain ⟨e1, e2⟩ := cell_bounds_mul hl h1 h2
    apply renewal_boundary_quiet_margin (α := α) (q := q) (m := m) hΛ ζ (l - 1)
    push_cast
    constructor <;> linarith
  · rw [sub_div_mul_eq hl.ne' h24] at h1
    rw [add_div_mul_eq hl.ne' h24] at h2
    obtain ⟨e1, e2⟩ := cell_bounds_mul hl h1 h2
    apply renewal_boundary_quiet_margin (α := α) (q := q) (m := m) hΛ ζ l
    constructor <;> linarith

/-- **A renewal block's regions and package** (block `l`, cell metric `G` near the identity), with
the quiet buffer shrunk to `τ/(4ℓ²)`. -/
theorem seamRenewalBlock (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {K : ScalarConstants}
    {Θ₀ Θlong : ℝ} (hcl : ScalarPackageClause α q Λ ζ K Θ₀) (hΘ₀ : 1 ≤ Θ₀) (hΘ₀l : Θ₀ ≤ Θlong)
    (hΘ3 : 3 * max K.θs 1 ≤ Θlong) (hshrink : PackageBufferShrinkStatement)
    {M' : ℕ} {κ : ℕ → ℝ} {B : ℝ} (hband : IsOCBandChain α q Λ ζ M' κ) (hm2 : 2 ≤ m)
    (hmM : m ≤ M') (hνκ : κ m = ν) (hBκ : κ (m - 1) = B) (hν : 0 < ν)
    (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (yc : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (hG : IsCellMetric (fun t _ => G t))
    (hg0 : 0 ≤ g) (hgK : g ≤ K.g0) (hGn : IsMetricNearIdentity (fun t _ => G t) g) (l : ℤ) :
    ∃ reg : BlockRegions,
      (∀ t ∈ Set.Icc ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
          ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2),
        t ∈ reg.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν yc t) ∧
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
          |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
      (reg.joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4 ∧
      reg.buffer = seamBuffer α q Λ m ν ∧
      Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν yc)
        ((((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
        (Real.sqrt ((ν / B) / (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2))) reg) := by
  have hBf : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBκ, ← hνκ]
    exact hband.2 m (by omega) hmM
  obtain ⟨-, -, -, -, -, hblk⟩ := hcl M' κ hband m hm2 hmM ν B hνκ hBκ yc G g hG hg0 hgK hGn
  have hadm := renewalBlock_admissible_K (α := α) (q := q) (m := m) hΛ hζ hν K hΘ₀ hΘ₀l hΘ3
    hlong l
  rw [← hBf] at hadm
  obtain ⟨reg, hq, hp, hbuf, hj, ⟨pkg⟩⟩ := hblk _ _ hadm
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hb : seamBuffer α q Λ m ν ≤ reg.buffer := by
    refine le_trans (le_of_eq ?_) (hbuf (renewalBlock_ends_quiet hΛ hν yc l))
    unfold seamBuffer
    refine (min_eq_left ?_).symm
    rw [← div_div]
    exact div_le_div_of_nonneg_right ((div_le_self hτ.le (by norm_num)).trans
      (ocTau_le_ocTauPP hΛ)) hl.le
  obtain ⟨pkg'⟩ := (hshrink K (ν / B) G _ _ _ _ reg (seamBuffer α q Λ m ν)
    (seamBuffer_nonneg hΛ hν) hb).2 pkg
  exact ⟨{ reg with buffer := seamBuffer α q Λ m ν }, hq, hp, hj, rfl, ⟨pkg'⟩⟩

/-- `seamRenewalBlock` at a given start `t₀` of the block and with `ϖ = ε/√(B τ'')`. -/
theorem seamRenewalBlock_at (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {K : ScalarConstants}
    {Θ₀ Θlong : ℝ} (hcl : ScalarPackageClause α q Λ ζ K Θ₀) (hΘ₀ : 1 ≤ Θ₀) (hΘ₀l : Θ₀ ≤ Θlong)
    (hΘ3 : 3 * max K.θs 1 ≤ Θlong) (hshrink : PackageBufferShrinkStatement)
    {M' : ℕ} {κ : ℕ → ℝ} {B : ℝ} (hband : IsOCBandChain α q Λ ζ M' κ) (hm2 : 2 ≤ m)
    (hmM : m ≤ M') (hνκ : κ m = ν) (hBκ : κ (m - 1) = B) (hν : 0 < ν) (hB : 0 < B)
    (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (yc : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (hG : IsCellMetric (fun t _ => G t))
    (hg0 : 0 ≤ g) (hgK : g ≤ K.g0) (hGn : IsMetricNearIdentity (fun t _ => G t) g) (l : ℤ)
    (t₀ : ℝ) (ht₀ : (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 = t₀) :
    ∃ reg : BlockRegions,
      (∀ t ∈ Set.Icc t₀ (t₀ + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
        t ∈ reg.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν yc t) ∧
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ Set.Icc (reg.lo p) (reg.hi p),
          |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        reg.orient p = (if k % 4 = 3 then 0 else 1)) ∧
      (reg.joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4 ∧
      reg.buffer = seamBuffer α q Λ m ν ∧
      Nonempty (ScalarPackage K (ν / B) G (ocCellDrift α q Λ ζ m ν yc) t₀
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) reg) := by
  subst ht₀
  rw [← seamVarpi_eq hΛ hν hB, ← add_div]
  exact seamRenewalBlock hΛ hζ hcl hΘ₀ hΘ₀l hΘ3 hshrink hband hm2 hmM hνκ hBκ hν hlong yc G g hG
    hg0 hgK hGn l

/-- The drift clauses of `scalar_package_interior` for the cell drift centred at `yc`. -/
theorem seamDrift_facts {K : ScalarConstants} {Θ₀ : ℝ} (hcl : ScalarPackageClause α q Λ ζ K Θ₀)
    {M' : ℕ} {κ : ℕ → ℝ} {B : ℝ} (hband : IsOCBandChain α q Λ ζ M' κ) (hm2 : 2 ≤ m)
    (hmM : m ≤ M') (hνκ : κ m = ν) (hBκ : κ (m - 1) = B)
    (yc : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (hG : IsCellMetric (fun t _ => G t))
    (hg0 : 0 ≤ g) (hgK : g ≤ K.g0) (hGn : IsMetricNearIdentity (fun t _ => G t) g) :
    IsCellDrift (ocCellDrift α q Λ ζ m ν yc) ∧
      (∀ t (k : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν yc t x k : ℂ)) = 0) ∧
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν yc t)) ∧
      (∀ t x, Real.sqrt (ν / B) *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν yc t x i ^ 2) ≤ K.Cw) ∧
      (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j
        (fun z' => Real.sqrt (ν / B) • ocCellDrift α q Λ ζ m ν yc t z') z‖ ≤ K.Cvj j) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hcl M' κ hband m hm2 hmM ν B hνκ hBκ yc G g hG hg0 hgK hGn
  exact ⟨h1, h2, h3, h4, h5⟩

end Blocks

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The window objects of the seam on the two blocks**.

From the joint premises (`JointPremisesGen`): the clamped frozen metrics of the two charts, the
regions and packages of the two renewal blocks with the future buffer `τ/(4ℓ²)` and the quiet
quiet margin `τ'/ℓ²` at the seam (`scalar_package_interior`), and the transition `Υ` at the seam
(`BlockTransitionStatement`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Window

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- `ℓ²` times a cell time is the physical time. -/
theorem ocEll_sq_mul_cellTime (hΛ : 1 ≤ Λ) (hν : 0 < ν) (t : ℝ) :
    ocEll q Λ m ν ^ 2 * cellTime q Λ m ν t = t := by
  rw [cellTime_eq_div hΛ hν]
  exact mul_div_cancel₀ t (ocEll_sq_pos_of hΛ hν).ne'

/-- **The clamped metrics of the two blocks**. -/
theorem JointPremisesGen.seamMetrics
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hclamp : ClampedMetricStatement) (hΛ : 1 ≤ Λ) (hg : g ≤ 1 / 2) :
    ∃ GO GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      IsCellMetric (fun t _ => GO t) ∧ IsMetricNearIdentity (fun t _ => GO t) g ∧
      (∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
        GO t = twoGpre hp t 0) ∧
      IsCellMetric (fun t _ => GF t) ∧ IsMetricNearIdentity (fun t _ => GF t) g ∧
      (∀ t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoTp α q Λ m l₀)), GF t = twoGpost hp t 0) := by
  have hw := hp.windows hΛ
  obtain ⟨h1, h2, h3⟩ := hclamp hΛ hφ hp.cov (windowCoverReferenceChartIndex P) _ _ hw.ab.le
    hw.windowPre hg
  obtain ⟨h4, h5, h6⟩ := hclamp hΛ hφ hp.cov (windowCoverFollowingChartIndex P hp.cov.P_pos) _ _
    hw.bd.le hw.windowPost hg
  exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩

/-- **The transition at the seam**:`Υ` acts on the slot-`K` endpoints (and, for a family
without edges, on the slot-`0` endpoints) by composition, is a
centred transition of order `Jchart + 1`, and has a smooth inverse. -/
theorem JointPremisesGen.seamTransition
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) {CU : ℝ}
    (hT : BlockTransitionBody.{u, v, w, x, v} Kmax Jchart Cchart CG Cpad Cage CU)
    (hg0 : g₀ ≤ 1 / 4) :
    ∃ Υ Υinv : Vec 2 → Vec 2,
      (∀ (U : ∀ x, PlaneHk Set.univ (K x) (h x)) x,
        planeValue (twoTransit hp hΛ hchart x (U x)) =ᵐ[volume] fun z => planeValue (U x) (Υ z)) ∧
      (∀ (hedge : ∀ v u, IsEmpty (F.Γ v u)) (U : ∀ x, PlaneHk Set.univ 0 (h x)) x,
        planeValue (twoTransit (hp.slotZero hedge) hΛ hchart x (U x)) =ᵐ[volume]
          fun z => planeValue (U x) (Υ z)) ∧
      IsCenteredTransition Υ Υinv (g + ocA α q Λ (m - 1) * ocTauPP α q Λ m)
        (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) CU (Jchart + 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) Υinv := by
  have hw := hp.windows hΛ
  have hν := hp.cov.pos.1
  have hts : ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)) =
      twoSeam α q Λ m l₀ := by
    have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
    unfold cellTime
    field_simp
  have htblock : ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m ≤
        ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)) ∧
      ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)) ≤
        ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m := by
    rw [hts]
    have := (Velocity.Jets.ocTauP_pos (α := α) (q := q) (m := m) hΛ).le
    unfold twoSeam
    constructor <;> linarith
  obtain ⟨Υ, Υinv, htr, hcent, hs⟩ := hT α q Λ m ζ Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Npad l₀
    P ν B r g g₀ a B₀ lam Cb qJ y₀ hp.cov hΛ (ocA_nonneg_of hΛ (m - 1)) hg0 F hp.hprep
    hp.hcover hw.next _ hw.seamMem htblock
  exact ⟨Υ, Υinv, fun U x => htr (K x) (slot_le_chart hp.hK hchart x) (U x),
    fun hedge U x => htr 0 (slot_le_chart (hp.slotZero hedge).hK hchart x) (U x), hcent, hs⟩

/-- **The two renewal blocks** (`scalar_package_interior`): regions and packages of the old
block `l₀` (start `(l₀ - 1/2) τ''/ℓ²`) and of the future block `l₀ + 1` (start at the seam's cell
time `b`), the joins and buffers of both blocks (`≤ τ''/τ + 4`, `= τ/(4ℓ²)`), the future buffer inside
the old block's quiet times before `b`, and the trimmed quiet margin `[b, b + (τ' - τ/24)/ℓ²]` of the future block. -/
theorem JointPremisesGen.seamBlocks
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {Kc : ScalarConstants}
    {Θ₀ Θlong : ℝ} (hcl : ScalarPackageClause α q Λ ζ Kc Θ₀) (hΘ₀ : 1 ≤ Θ₀) (hΘ₀l : Θ₀ ≤ Θlong)
    (hΘ3 : 3 * max Kc.θs 1 ≤ Θlong) (hshrink : PackageBufferShrinkStatement)
    (hlong : Θlong ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2)
    (GO GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hGmO : IsCellMetric (fun t _ => GO t)) (hGnO : IsMetricNearIdentity (fun t _ => GO t) g)
    (hGmF : IsCellMetric (fun t _ => GF t)) (hGnF : IsMetricNearIdentity (fun t _ => GF t) g)
    (hgK : g ≤ Kc.g0) :
    ∃ regO regF : BlockRegions,
      Nonempty (ScalarPackage Kc (ν / B) GO (ocCellDrift α q Λ ζ m ν (twoYc hp))
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) regO) ∧
      Nonempty (ScalarPackage Kc (ν / B) GF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) regF) ∧
      (∀ t ∈ Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
          ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
            ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
        t ∈ regO.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν (twoYc hp) t) ∧
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ Set.Icc (regO.lo p) (regO.hi p),
          |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        regO.orient p = (if k % 4 = 3 then 0 else 1)) ∧
      (∀ t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
          (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
        t ∈ regF.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν (twoYcPost hp) t) ∧
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ Set.Icc (regF.lo p) (regF.hi p),
          |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        regF.orient p = (if k % 4 = 3 then 0 else 1)) ∧
      (regO.joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4 ∧
      regO.buffer = seamBuffer α q Λ m ν ∧
      (regF.joins : ℝ) ≤ ocTauPP α q Λ m / ocTau α q Λ m + 4 ∧
      regF.buffer = seamBuffer α q Λ m ν ∧
      Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀) - regF.buffer)
          (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ⊆
        regO.quiet ∩ Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
          ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
            ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ∧
      Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
          (cellTime q Λ m ν (twoSeam α q Λ m l₀) +
            (ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2) ⊆ regF.quiet := by
  obtain ⟨hν, hB, -⟩ := hp.cov.pos
  have hl := ocEll_sq_pos_of (q := q) (m := m) hΛ hν
  have hg0 := hp.cov.g_range.1
  have hb := cellTime_twoSeam (α := α) (q := q) (m := m) hΛ hν l₀
  have hend : (((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
      ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 = cellTime q Λ m ν (twoSeam α q Λ m l₀) := by
    rw [hb, ← add_div]
    ring_nf
  have hstart : ((((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 =
      cellTime q Λ m ν (twoSeam α q Λ m l₀) := by
    rw [hb]
    push_cast
    ring_nf
  obtain ⟨regO, hqO, hpO, hjO, hbO, pkgO⟩ := seamRenewalBlock_at hΛ hζ hcl hΘ₀ hΘ₀l hΘ3 hshrink
    hp.hband hp.hm2 hp.hmM hp.hν hp.hB hν hB hlong (twoYc hp) GO g hGmO hg0 hgK hGnO l₀ _ rfl
  obtain ⟨regF, hqF, hpF, hjF, hbF, pkgF⟩ := seamRenewalBlock_at hΛ hζ hcl hΘ₀ hΘ₀l hΘ3 hshrink
    hp.hband hp.hm2 hp.hmM hp.hν hp.hB hν hB hlong (twoYcPost hp) GF g hGmF hg0 hgK hGnF
    (l₀ + 1) _ hstart
  have hseamT : ocEll q Λ m ν ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀) =
      ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m := ocEll_sq_mul_cellTime hΛ hν _
  have hl1 : ocEll q Λ m ν ≠ 0 := fun h0 => by simp [h0] at hl
  have hbufT : ocEll q Λ m ν ^ 2 * seamBuffer α q Λ m ν = ocTau α q Λ m / 4 := by
    unfold seamBuffer
    field_simp
  have hcolT : ocEll q Λ m ν ^ 2 * ((ocTauP α q Λ m - ocTau α q Λ m / 24) / ocEll q Λ m ν ^ 2) =
      ocTauP α q Λ m - ocTau α q Λ m / 24 :=
    mul_div_cancel₀ _ hl.ne'
  have hτ := ocTau_le_ocTauP (α := α) (q := q) (m := m) hΛ
  have hτ0 := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hbS : seamBuffer α q Λ m ν ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 :=
    (seamBuffer_le_quiet_margin hΛ hν).trans (quietMargin_le_seamS hΛ hν)
  refine ⟨regO, regF, pkgO, pkgF, hqO, hpO, hqF, hpF, hjO, hbO, hjF, hbF, ?_, ?_⟩
  · intro t ht
    rw [hbF] at ht
    have htw : t ∈ Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) := by
      rw [hend]
      refine ⟨?_, ht.2⟩
      linarith [ht.1, hend, hbS]
    have h1 := mul_le_mul_of_nonneg_left ht.1 hl.le
    rw [mul_sub, hseamT, hbufT] at h1
    have h2 := mul_le_mul_of_nonneg_left ht.2 hl.le
    rw [hseamT] at h2
    refine ⟨(hqO t htw).2 ((cellTrimmedQuiet_iff hΛ hν _ t).2
      (trimmed_of_quiet_margin hΛ l₀ ?_ ?_)), htw⟩
    · linarith
    · linarith
  · intro t ht
    have htw : t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) :=
      ⟨ht.1, ht.2.trans (by linarith [trimmedQuietMargin_le_seamS (α := α) (q := q) (m := m) hΛ hν])⟩
    have h1 := mul_le_mul_of_nonneg_left ht.1 hl.le
    rw [hseamT] at h1
    have h2 := mul_le_mul_of_nonneg_left ht.2 hl.le
    rw [mul_add, hseamT, hcolT] at h2
    refine (hqF t htw).2 ((cellTrimmedQuiet_iff hΛ hν _ t).2 (trimmed_of_quiet_margin hΛ l₀ ?_ ?_))
    · linarith
    · linarith

end Window

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The four letters of the two blocks for the seam**.

From `BlockLettersBody`, the metric and source letters of the old block (reference chart, label
`l₀`, cell window `[a, b]`) and of the future block (following chart, label `l₀ + 1`, cell window
`[b, b + S]`) satisfy the seam's letter hypotheses (`SeamLetterOK`) at every reserve `R ≤ Jstar`,
for regions whose pulses lie in the enlarged odd pulses and whose quiet times are the trimmed quiet
cell times of the block: their physical times are trimmed quiet times
(`cellTrimmedQuiet_iff`), where the family is fast independent (`hquiet`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Letters

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The physical time of a cell time is `ℓ² t`. -/
theorem nu_inv_eps_sq_mul (hν : 0 < ν) (t : ℝ) :
    ν⁻¹ * ocEpsilon q Λ m ^ 2 * t = ocEll q Λ m ν ^ 2 * t := by
  rw [CycleReference.ocEll_sq_eq hν]
  ring

/-- **The four letters satisfy the seam's letter hypotheses.** -/
theorem JointPremisesGen.seamLetterFacts
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) {Jstar : ℕ} {CL : ℝ}
    (hL : BlockLettersBody.{u, v, w, x} D Kmax Ks Ls Jm Jchart qJ Jstar Ca Cm Cchart CG CL)
    (hD : 2 ≤ D) (hg0 : g₀ ≤ 1 / 4) (hθ : 0 ≤ Cth * Θ)
    (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1)) (R : ℕ) (hR : R ≤ Jstar)
    (regO regF : BlockRegions)
    (hpO : ∀ p, ∃ k : ℤ, Odd k ∧
      (∀ t ∈ Set.Icc (regO.lo p) (regO.hi p),
        |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
      regO.orient p = (if k % 4 = 3 then 0 else 1))
    (hpF : ∀ p, ∃ k : ℤ, Odd k ∧
      (∀ t ∈ Set.Icc (regF.lo p) (regF.hi p),
        |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
      regF.orient p = (if k % 4 = 3 then 0 else 1))
    (hqO : ∀ t ∈ Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
      t ∈ regO.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν (twoYc hp) t)
    (hqF : ∀ t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
      t ∈ regF.quiet ↔ CellTrimmedQuiet α q Λ m ζ ν (twoYcPost hp) t) :
    SeamLetterOK π K (twoMpre hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ)
      R H regO (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) ∧
    SeamLetterOK π K (twoSpre hp (CL * (Cth * Θ))
        (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
      (Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ×ˢ Set.univ)
      R H regO (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (Set.Icc ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
        ((((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2 +
          ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) ∧
    SeamLetterOK π K (twoMpost hp (CL * g) (fun v u => if v = u then CL * g else 0))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ×ˢ
        Set.univ)
      R H regF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) ∧
    SeamLetterOK π K (twoSpost hp (CL * (Cth * Θ))
        (fun v u => CL * (Real.sqrt (π u / π v) * A v u)))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) ×ˢ
        Set.univ)
      R H regF (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
      (Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
        (cellTime q Λ m ν (twoSeam α q Λ m l₀) + ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)) := by
  have hw := hp.windows hΛ
  have hν := hp.cov.pos.1
  have hd := cellTime_twoTp (α := α) (q := q) (m := m) hΛ hν l₀
  have htr0 : 0 ≤ ocTau α q Λ m / (24 * ocEll q Λ m ν ^ 2) :=
    div_nonneg (Construction.Stream.ocTau_pos hΛ).le
      (mul_nonneg (by norm_num) (ocEll_sq_pos_of hΛ hν).le)
  obtain ⟨hcSO, hcMO, htrO, hqlO, hmSO, hmMO⟩ := hL α q Λ m ζ Φ hφ tS
    (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B r g g₀ a B₀ lam Cb y₀ hp.cov hΛ heE
    (ocA_nonneg_of hΛ (m - 1)) hg0 hD F hp.hmeas hp.hwmeas π hp.hπ K hp.hK actual A Θ Cth H hθ
    hp.hprep hp.hcover hp.henv hp.hdepth hp.htrans (ocTrimmedQuietTimes α q Λ ζ m) hp.hquiet
    (windowCoverReferenceChartIndex P) _ _ hw.ab.le hw.windowPre l₀ _ rfl (Or.inl rfl)
    hw.blockPre
  have hwinF := hw.windowPost
  have hblkF := hw.blockPost
  rw [hd] at hwinF hblkF
  obtain ⟨hcSF, hcMF, htrF, hqlF, hmSF, hmMF⟩ := hL α q Λ m ζ Φ hφ tS
    (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B r g g₀ a B₀ lam Cb y₀ hp.cov hΛ heE
    (ocA_nonneg_of hΛ (m - 1)) hg0 hD F hp.hmeas hp.hwmeas π hp.hπ K hp.hK actual A Θ Cth H hθ
    hp.hprep hp.hcover hp.henv hp.hdepth hp.htrans (ocTrimmedQuietTimes α q Λ ζ m) hp.hquiet
    (windowCoverFollowingChartIndex P hp.cov.P_pos) _ _
    (le_add_of_nonneg_right (div_nonneg (Construction.Stream.ocTauPP_pos hΛ).le
      (ocEll_sq_pos_of hΛ hν).le)) hwinF (l₀ + 1) _ rfl (Or.inr hw.next) hblkF
  obtain ⟨hqSO, hqMO⟩ := hqlO (regO.quiet ∩ _)
    (fun t ht => by
      rw [nu_inv_eps_sq_mul hν]
      exact (cellTrimmedQuiet_iff hΛ hν _ t).1 ((hqO t ht.2).1 ht.1))
    (fun t ht z => (hqO t ht.2).1 ht.1 t ⟨by linarith [htr0], by linarith [htr0]⟩ z)
  obtain ⟨hqSF, hqMF⟩ := hqlF (regF.quiet ∩ _)
    (fun t ht => by
      rw [nu_inv_eps_sq_mul hν]
      exact (cellTrimmedQuiet_iff hΛ hν _ t).1 ((hqF t ht.2).1 ht.1))
    (fun t ht z => (hqF t ht.2).1 ht.1 t ⟨by linarith [htr0], by linarith [htr0]⟩ z)
  obtain ⟨htSO, htMO⟩ := htrO (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p))
    regO.orient hpO
  obtain ⟨htSF, htMF⟩ := htrF (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p))
    regF.orient hpF
  refine ⟨⟨CycleWords.Assembly.isCycleLetter_reserve_mono hcMO hR, htMO, hqMO, hmMO,
      fun x y o hne => metricEdges_slots K _ _ _ x y o hne⟩,
    ⟨CycleWords.Assembly.isCycleLetter_reserve_mono hcSO hR, htSO, hqSO, hmSO,
      fun x y o hne => blockSourceEdges_slots F K hp.hdesc _ _ hφ _ _ _ _ _ _ _ x y o hne⟩,
    ⟨CycleWords.Assembly.isCycleLetter_reserve_mono hcMF hR, htMF, hqMF, hmMF,
      fun x y o hne => metricEdges_slots K _ _ _ x y o hne⟩,
    ⟨CycleWords.Assembly.isCycleLetter_reserve_mono hcSF hR, htSF, hqSF, hmSF,
      fun x y o hne => blockSourceEdges_slots F K hp.hdesc _ _ hφ _ _ _ _ _ _ _ x y o hne⟩⟩

end Letters

end AVRegularity.CycleJointProofs.Assembly
end
end

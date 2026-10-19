-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.ActualMeans.PulseFlux
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedMean
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.ActualMeans

/-! The Eulerian presentation of the glued mean:
on each pulse the mean is the label-frame divergence of the chart flux, exact Piola transport
turns it into the Eulerian divergence of `(DΦ F)∘Φ⁻¹`, and the partition glues the pulses. Any
letters whose classical grade flux is minus the glued Piola flux therefore present the glued
mean. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem sum_smul_sum_smul_comm {A : Type*} [AddCommMonoid A] [Module ℝ A] (S : Finset ℕ)
    (J : Fin 2 → ℝ) (cn : ℕ → ℝ) (X : ℕ → Fin 2 → A) :
    ∑ l : Fin 2, J l • ∑ n ∈ S, cn n • X n l = ∑ n ∈ S, cn n • ∑ l : Fin 2, J l • X n l := by
  calc ∑ l : Fin 2, J l • ∑ n ∈ S, cn n • X n l
      = ∑ l : Fin 2, ∑ n ∈ S, cn n • (J l • X n l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun n _ => smul_comm _ _ _
    _ = ∑ n ∈ S, ∑ l : Fin 2, cn n • (J l • X n l) := Finset.sum_comm
    _ = ∑ n ∈ S, cn n • ∑ l : Fin 2, J l • X n l :=
        Finset.sum_congr rfl fun n _ => Finset.smul_sum.symm

/-- The Eulerian flux of one pulse: the Piola transport `(DΦ F)∘Ψ` of the chart flux. -/
def eulerFlux (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2) (Lbk : ℕ → MeanCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (s : ℝ) (v : ι) (y : Vec 2) (k' : Fin 2) : h v :=
  ∑ l : Fin 2, jacMatrix chart (label y) k' l • chartFlux c ρ εc M Lbk g s (label y) l v

theorem eulerFlux_eq (c ρ εc : ℝ) (M : ℕ) (chart label : Vec 2 → Vec 2)
    (Lbk : ℕ → MeanCoeff ι h) (g : Vec 2 → ∀ i, h i) (s : ℝ) (v : ι) (y : Vec 2) (k' : Fin 2) :
    eulerFlux c ρ εc M chart label Lbk g s v y k' =
      ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix chart (label y) k' l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
          Lbk n d α s (ρ⁻¹ • label y) l v u (orderedDerivative α g (label y) u) :=
  sum_smul_sum_smul_comm (Finset.Icc 2 M) (fun l => jacMatrix chart (label y) k' l)
    (fun n => c⁻¹ * εc ^ n) (fun n l => ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
      ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
        Lbk n d α s (ρ⁻¹ • label y) l v u (orderedDerivative α g (label y) u))

theorem differentiable_eulerFlux (c ρ εc : ℝ) (M : ℕ) {chart label : Vec 2 → Vec 2}
    (hchart : ContDiff ℝ (⊤ : ℕ∞) chart) (hlabel : Differentiable ℝ label)
    (Lbk : ℕ → MeanCoeff ι h) (g : Vec 2 → ∀ i, h i) (s : ℝ) (v : ι)
    (hF : ∀ l : Fin 2, Differentiable ℝ (fun y => chartFlux c ρ εc M Lbk g s y l v))
    (k' : Fin 2) : Differentiable ℝ (fun y => eulerFlux c ρ εc M chart label Lbk g s v y k') := by
  intro y
  unfold eulerFlux
  refine DifferentiableAt.fun_sum fun l _ => ?_
  have h1 : DifferentiableAt ℝ (fun y' => jacMatrix chart (label y') k' l) y :=
    (Charts.differentiable_jacMatrix_entry hchart k' l (label y)).comp y (hlabel y)
  have h2 : DifferentiableAt ℝ (fun y' => chartFlux c ρ εc M Lbk g s (label y') l v) y :=
    (hF l (label y)).comp y (hlabel y)
  exact h1.fun_smul h2

/-- Exact Piola transport: the Eulerian divergence of the Eulerian flux is the label-frame
divergence of the chart flux. -/
theorem div_eulerFlux (c ρ εc : ℝ) (M : ℕ) {chart label : Vec 2 → Vec 2}
    (hchart : ContDiff ℝ (⊤ : ℕ∞) chart) (hlabel : Differentiable ℝ label)
    (hlc : ∀ y, label (chart y) = y) (hcl : ∀ x, chart (label x) = x)
    (hdet : ∀ y, (jacMatrix chart y).det = 1)
    (Lbk : ℕ → MeanCoeff ι h) (g : Vec 2 → ∀ i, h i) (s : ℝ) (v : ι)
    (hF : ∀ l : Fin 2, Differentiable ℝ (fun y => chartFlux c ρ εc M Lbk g s y l v))
    (x : Vec 2) :
    ∑ k' : Fin 2, fderiv ℝ (fun y => eulerFlux c ρ εc M chart label Lbk g s v y k') x
        (basisVec k') =
      ∑ l : Fin 2, fderiv ℝ (fun y => chartFlux c ρ εc M Lbk g s y l v) (label x) (basisVec l) :=
  Charts.piola_forward_vector hchart hlabel hlc hcl hdet
    (F := fun y l => chartFlux c ρ εc M Lbk g s y l v) hF x

variable {D : ℕ}

/-- **The glued mean is presented by any letters with the glued Piola flux.** -/
theorem isMeanPresentation_of_flux (I : Set ℝ) (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ εc : ℝ) (hc : c ≠ 0) (hρ : ρ ≠ 0) (N r : ℕ) (Q : ℤ → LiftOperatorData ι h D)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (AD : ∀ d : Finset.Icc 2 (N + D), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (N + D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsupp : ∀ k ∈ kset, ∀ t ∈ I, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (hlc : ∀ k ∈ kset, ∀ t y, label k t (chart k t y) = y)
    (hcl : ∀ k ∈ kset, ∀ t x, chart k t (label k t x) = x)
    (hdet : ∀ k ∈ kset, ∀ t y, (jacMatrix (chart k t) y).det = 1)
    (hchart : ∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hlabel : ∀ k ∈ kset, ∀ t, Differentiable ℝ (label k t))
    (hpres : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D →
      ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          liftMean (Q k) (Cc k) (fun _ => a₀) r n s X =
            meanApply n (Lb k r n) (fun _ => a₀) s X)
    (hLb : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ContDiff ℝ 1 (fun X => Lb k r n d α s X k₀ v u))
    (hflux : ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
      ∀ t ∈ I, ∀ x (v : ι) (k' : Fin 2),
        classicalGradeFlux (N + D) r AD CE Jm a v t x k' =
          -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 (N + D), (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
            jacMatrix (chart k t) (label k t x) k' l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
              ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
                Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
                  (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u)) :
    IsMeanPresentation I (N + D) r AD CE Jm (gluedMean kset ϖ c ρ εc N r Q Cc chart label) := by
  intro a ha _ t ht x v
  -- the flux, as a function of the position, is minus the glued Eulerian flux
  have hfun : ∀ k' : Fin 2, (fun y => classicalGradeFlux (N + D) r AD CE Jm a v t y k') =
      fun y => -∑ k ∈ kset, ϖ k t • eulerFlux c ρ εc (N + D) (chart k t) (label k t) (Lb k r)
        (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k' := by
    intro k'
    funext y
    rw [hflux a ha t ht y v k']
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eulerFlux_eq]
  -- one pulse
  have hpulse : ∀ k ∈ kset,
      ϖ k t • pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x v =
        ∑ k' : Fin 2, fderiv ℝ (fun y => ϖ k t • eulerFlux c ρ εc (N + D) (chart k t)
          (label k t) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k') x
            (basisVec k') ∧
      ∀ k' : Fin 2, DifferentiableAt ℝ (fun y => ϖ k t • eulerFlux c ρ εc (N + D) (chart k t)
        (label k t) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k') x := by
    intro k hk
    by_cases hϖ : ϖ k t = 0
    · refine ⟨?_, fun k' => ?_⟩
      · simp only [hϖ, zero_smul, fderiv_fun_const, Pi.zero_apply, zero_apply,
          Finset.sum_const_zero]
      · simp only [hϖ, zero_smul]
        exact differentiableAt_const _
    · have hwin := hsupp k hk t ht hϖ
      have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y' => a t (chart k t y')) :=
        (ha t).comp (hchart k hk t)
      have hF : ∀ l : Fin 2, Differentiable ℝ (fun y => chartFlux c ρ εc (N + D) (Lb k r)
          (fun y' => a t (chart k t y')) (c⁻¹ * t) y l v) := fun l =>
        differentiable_chartFlux c ρ εc (N + D) (Lb k r) _ hg (c⁻¹ * t)
          (fun n hn hnM d hd hdn α k₀ v u =>
            hLb k hk n hn hnM d hd hdn α k₀ v u (c⁻¹ * t) hwin) l v
      have hE : ∀ k' : Fin 2, Differentiable ℝ (fun y => eulerFlux c ρ εc (N + D) (chart k t)
          (label k t) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k') := fun k' =>
        differentiable_eulerFlux c ρ εc (N + D) (hchart k hk t) (hlabel k hk t) (Lb k r) _
          (c⁻¹ * t) v hF k'
      have hmean := pulseMeanField_eq_div_chartFlux c ρ εc hc hρ N r (Q k) (Cc k) (chart k)
        (label k) (Lb k r) (s₀ k) (s₁ k) (hpres k hk) (hLb k hk) a t (ha t) (hchart k hk t)
        hwin x v
      have hdiv := div_eulerFlux c ρ εc (N + D) (hchart k hk t) (hlabel k hk t) (hlc k hk t)
        (hcl k hk t) (hdet k hk t) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v hF x
      refine ⟨?_, fun k' => (hE k' x).const_smul _⟩
      rw [hmean, ← hdiv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [fderiv_fun_const_smul (hE k' x), smul_apply]
  -- glue the pulses
  have hglue : gluedMean kset ϖ c ρ εc N r Q Cc chart label a t x v =
      ∑ k ∈ kset, ϖ k t • pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x v := by
    simp only [gluedMean, Finset.sum_apply, Pi.smul_apply]
  rw [hglue, Finset.sum_congr rfl fun k hk => (hpulse k hk).1, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [hfun k', fderiv_fun_neg, neg_apply, neg_neg,
    fderiv_fun_sum fun k hk => (hpulse k hk).2 k', _root_.sum_apply]

end AVRegularity.CycleComparison.ActualMeans
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.ActualMeans

/-! The actual means in the Eulerian frame (the glued Piola mean flux `M_m` of Definition 9.8 of
the paper). The letters are `adLetter` and `ceLetter`; the scalar letters of the diagonal means are
read off the grade-zero chart-frame letters through a unit vector of a nontrivial component (if
every component is trivial, every field vanishes and the scalar letters are a supplied fallback). -/

/-- The scalar letters `Lsc` read the diagonal chart-frame letters `Lb0` through a functional `φ`
of norm at most one with `φ(a • id) = a` on one component `v₀`, or they are the fallback `Lfb`
(the case of trivial components). The reading transfers jet bounds and pairings with the
identity from the letters to the scalar letters. -/
def IsScalarReading {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Lb0 : ℤ → ℕ → MeanCoeff ι h)
    (Lsc Lfb : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ) : Prop :=
  (∃ (v₀ : ι) (φ : (h v₀ →L[ℝ] h v₀) →L[ℝ] ℝ), ‖φ‖ ≤ 1 ∧
      (∀ a : ℝ, φ (a • ContinuousLinearMap.id ℝ (h v₀)) = a) ∧
      ∀ k n d α l s X, Lsc k n d α l s X = φ (Lb0 k n d α s X l v₀ v₀)) ∨ Lsc = Lfb

/-- The scalar letters of the diagonal chart-frame means, with their regularity. If every
component space is trivial the letters carry no information; the scalar letters are then the
supplied fallback `Lfb`. -/
theorem exists_scalarLetter {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    (kset : Finset ℤ) (M Kt : ℕ) (ρ : ℝ) (s₀ s₁ : ℤ → ℝ) (Lb0 : ℤ → ℕ → MeanCoeff ι h)
    (Ls : ℤ → ℕ → (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ)
    (hC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ContDiff ℝ (Kt : ℕ∞) (fun X => Lb0 k n d α s X k₀ v u))
    (hMeas : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
        Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lb0 k n d α s X k₀ v u))
    (hP : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ∀ (p : Fin 2 → ℤ) (X : Vec 2),
          Lb0 k n d α s (X + ρ⁻¹ • AVenhance.latticeShift p) k₀ v u = Lb0 k n d α s X k₀ v u)
    (hLs : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
        (∀ v, Lb0 k n d α s X k₀ v v = Ls k n d α s X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
        (∀ v u, v ≠ u → Lb0 k n d α s X k₀ v u = 0))
    (Lfb : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
    (hfC : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ContDiff ℝ (Kt : ℕ∞) (Lfb k n d α l s))
    (hfM : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2),
        Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lfb k n d α l s X))
    (hfP : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
        ∀ (p : Fin 2 → ℤ) (X : Vec 2),
          Lfb k n d α l s (X + ρ⁻¹ • AVenhance.latticeShift p) = Lfb k n d α l s X) :
    ∃ Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ,
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          (∀ (v : ι) (ξ : h v), Lb0 k n d α s X l v v ξ = Lsc k n d α l s X • ξ) ∧
          (∀ v u : ι, v ≠ u → Lb0 k n d α s X l v u = 0)) ∧
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ContDiff ℝ (Kt : ℕ∞) (Lsc k n d α l s)) ∧
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2),
          Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lsc k n d α l s X)) ∧
      (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
        ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
          ∀ (p : Fin 2 → ℤ) (X : Vec 2),
            Lsc k n d α l s (X + ρ⁻¹ • AVenhance.latticeShift p) = Lsc k n d α l s X) ∧
      ((∀ v : ι, Subsingleton (h v)) → Lsc = Lfb) ∧ IsScalarReading Lb0 Lsc Lfb := by
  by_cases hne : ∃ v₀ : ι, Nontrivial (h v₀)
  · obtain ⟨v₀, hv₀⟩ := hne
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : h v₀)
    have he : ‖‖x₀‖⁻¹ • x₀‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀)]
    let φ : (h v₀ →L[ℝ] h v₀) →L[ℝ] ℝ :=
      (innerSL ℝ (‖x₀‖⁻¹ • x₀)).comp (ContinuousLinearMap.apply ℝ (h v₀) (‖x₀‖⁻¹ • x₀))
    have hφ : ∀ s : ℝ, φ (s • ContinuousLinearMap.id ℝ (h v₀)) = s := by
      intro s
      show inner ℝ (‖x₀‖⁻¹ • x₀) ((s • ContinuousLinearMap.id ℝ (h v₀)) (‖x₀‖⁻¹ • x₀)) = s
      rw [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_right,
        real_inner_self_eq_norm_sq, he]
      ring
    have hφn : ‖φ‖ ≤ 1 := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [innerSL_apply_norm, he, one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
      show ‖T (‖x₀‖⁻¹ • x₀)‖ ≤ 1 * ‖T‖
      rw [one_mul]
      calc ‖T (‖x₀‖⁻¹ • x₀)‖ ≤ ‖T‖ * ‖‖x₀‖⁻¹ • x₀‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [he, mul_one]
    refine ⟨fun k n d α l s X => φ (Lb0 k n d α s X l v₀ v₀), ?_, ?_, ?_, ?_,
      fun hsub => absurd (hsub v₀) (not_subsingleton_iff_nontrivial.mpr hv₀),
      Or.inl ⟨v₀, φ, hφn, hφ, fun _ _ _ _ _ _ _ => rfl⟩⟩
    · intro k hk n hn hnM d hd hdn α l s hs X
      obtain ⟨hdiag, hoff⟩ := hLs k hk n hn hnM d hd hdn α l s hs X
      refine ⟨fun v ξ => ?_, hoff⟩
      show Lb0 k n d α s X l v v ξ = φ (Lb0 k n d α s X l v₀ v₀) • ξ
      rw [hdiag v, hdiag v₀, hφ, smul_apply, ContinuousLinearMap.id_apply]
    · intro k hk n hn hnM d hd hdn α l s hs
      exact φ.contDiff.comp (hC k hk n hn hnM d hd hdn α l v₀ v₀ s hs)
    · intro k hk n hn hnM d hd hdn α l X
      exact φ.continuous.measurable.comp (hMeas k hk n hn hnM d hd hdn α l v₀ v₀ X)
    · intro k hk n hn hnM d hd hdn α l s hs p X
      exact congrArg φ (hP k hk n hn hnM d hd hdn α l v₀ v₀ s hs p X)
  · have hsub : ∀ v : ι, Subsingleton (h v) := fun v =>
      not_nontrivial_iff_subsingleton.mp fun hn => hne ⟨v, hn⟩
    refine ⟨Lfb, ?_, hfC, hfM, hfP, fun _ => rfl, Or.inr rfl⟩
    intro k hk n hn hnM d hd hdn α l s hs X
    refine ⟨fun v ξ => ?_, (hLs k hk n hn hnM d hd hdn α l s hs X).2⟩
    have := hsub v
    exact Subsingleton.elim _ _

/-- **The flux identity of the Eulerian letters**, for every grade. -/
theorem flux_identity {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) {M : ℕ}
    (hM : 2 ≤ M) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
    (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hinv : ∀ k ∈ kset, ∀ x, chart k t (label k t x) = x)
    (hsupp : ∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (hsc : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ M → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
        (∀ (v : ι) (ξ : h v), Lb k 0 n d α s X l v v ξ = Lsc k n d α l s X • ξ) ∧
        (∀ v u : ι, v ≠ u → Lb k 0 n d α s X l v u = 0))
    (x : Vec 2) (v : ι) (k' : Fin 2) :
    classicalGradeFlux M r (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm)
        (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb) Jm a v t x k' =
      -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 M, (c⁻¹ * εc ^ n) •
        ∑ l : Fin 2, jacMatrix (chart k t) (label k t x) k' l •
          ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
            Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
              (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u) := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · exact classicalGradeFlux_diag kset ϖ c ρ εc hM chart label s₀ s₁ Lb Lsc Jm
      (ceLetter kset ϖ c ρ εc M chart label s₀ s₁ Lb) a t ha hchart hinv hsupp
      (fun k hk hwin n hn d hd α l X => hsc k hk n (Finset.mem_Icc.1 hn).1
        (Finset.mem_Icc.1 hn).2 d (Finset.mem_Icc.1 hd).1 (Finset.mem_Icc.1 hd).2 α l
        (c⁻¹ * t) hwin X) x v k'
  · exact classicalGradeFlux_edge kset ϖ c ρ εc M chart label s₀ s₁ Lb
      (adLetter kset ϖ c ρ εc M chart label s₀ s₁ Lsc Jm) Jm (Nat.pos_iff_ne_zero.mp hrpos) a t
      ha hchart hinv hsupp x v k'

/-- The conclusions of `cycle_comparison_actual_means` as a predicate on the letters
`(AD, CE)`: (1) the presentation of the glued means, (2) the flux identity, (3), (3') the
regularity of the letters, (4) the entrywise transfer bound with the constant `C`. -/
def IsActualMeans {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] (N D H Kt : ℕ) (C : ℝ)
    (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (T₀ T₁ c ρ εc lam Rχ : ℝ)
    (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (AD : ∀ d : Finset.Icc 2 (N + D), ℝ → Vec 2 →
            PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (N + D)), ℝ → Vec 2 →
            (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
              (PiLp 2 (fun _ : Fin 2 => h v))) : Prop :=
        -- (1) the Eulerian presentation of the glued mean of every grade
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc T₀ T₁) (N + D) r AD CE Jm
          (gluedMean kset ϖ c ρ εc N r Q Cc chart label)) ∧
        -- (2) the flux identity: the letters are the glued Piola transports of the
        --     dimensional chart-frame fluxes (at `r = 0`, minus the `Jm` part)
        (∀ r, r ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
          ∀ t ∈ Set.Icc T₀ T₁, ∀ x (v : ι) (k' : Fin 2),
            classicalGradeFlux (N + D) r AD CE Jm a v t x k' =
              -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 (N + D), (c⁻¹ * εc ^ n) •
                ∑ l : Fin 2, jacMatrix (chart k t) (label k t x) k' l •
                  ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
                    Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
                      (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u)) ∧
        -- (3) regularity of the diagonal letters
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, ContDiff ℝ (Kt : ℕ∞) (AD d t)) ∧
        (∀ d, Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => AD d q.1 q.2) ∧
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, AVenhance.IsZ2Periodic (AD d t)) ∧
        -- (3') regularity of the edge letters
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          ContDiff ℝ (Kt : ℕ∞) (CE r v u d t)) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d,
          Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => CE r v u d q.1 q.2) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          AVenhance.IsZ2Periodic (CE r v u d t)) ∧
        -- (4) the entrywise transfer bound through the chart jets
        (∀ r, 1 ≤ r → r ≤ H → ∀ (v u : ι) (M : ℝ), 0 ≤ M →
          (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
            ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ i, i ≤ Kt →
              ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
                ‖iteratedFDeriv ℝ i (fun X' => Lb k r n d α s X' k₀ v u) X‖ ≤
                  M * lam ^ (n - d + i)) →
          ∀ (d : Finset.Icc 2 (N + D)) (j : ℕ), j ≤ Kt → ∀ t ∈ Set.Icc T₀ T₁, ∀ x,
            ‖coefficientDerivativeArray (CE r v u d t) j x‖ ≤
              C * M * (∑ k ∈ kset, |ϖ k t|) *
                ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1))

/-- **The actual means, with explicit letters.** The letters are `adLetter` (built on scalar
letters `Lsc` of the diagonal chart-frame means) and `ceLetter`. -/
theorem actual_means_explicit (N D H Kt : ℕ) (hD : 2 ≤ D) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (T₀ T₁ c ρ εc lam Rχ : ℝ)
        (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
        (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
        (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Ls : ℤ → ℕ → (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ)
        (Lfb : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
        1 ≤ Kt → 0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ →
        (∀ i j, Measurable fun t => Jm t i j) →
        -- the time partition: measurable, and active only inside the lift windows
        (∀ k ∈ kset, Measurable (ϖ k)) →
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
        -- exact volume-preserving, lattice-equivariant, smooth charts (qualitative)
        (∀ k ∈ kset, ∀ t y, label k t (chart k t y) = y) →
        (∀ k ∈ kset, ∀ t x, chart k t (label k t x) = x) →
        (∀ k ∈ kset, ∀ t (p : Fin 2 → ℤ) y,
          chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p) →
        (∀ k ∈ kset, ∀ t y, (jacMatrix (chart k t) y).det = 1) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2)) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2)) →
        -- normalized chart jets at the chart scale `Rχ` (`oc_flow_jets`), on the lift window of the pulse
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
          ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
          ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        -- the chart-frame mean letters of every pulse
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
              liftMean (Q k) (Cc k) (fun _ => a₀) r n s X =
                meanApply n (Lb k r n) (fun _ => a₀) s X) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
              ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
            Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ (p : Fin 2 → ℤ) (X : Vec 2),
              Lb k r n d α s (X + ρ⁻¹ • AVenhance.latticeShift p) k₀ v u =
                Lb k r n d α s X k₀ v u) →
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            (∀ v, Lb k 0 n d α s X k₀ v v = Ls k n d α s X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
            (∀ v u, v ≠ u → Lb k 0 n d α s X k₀ v u = 0)) →
        -- the fallback scalar letters, used only if every component space is trivial
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
            ContDiff ℝ (Kt : ℕ∞) (Lfb k n d α l s)) →
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2),
            Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lfb k n d α l s X)) →
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
            ∀ (p : Fin 2 → ℤ) (X : Vec 2),
              Lfb k n d α l s (X + ρ⁻¹ • AVenhance.latticeShift p) = Lfb k n d α l s X) →
      ∃ Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ,
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            (∀ (v : ι) (ξ : h v), Lb k 0 n d α s X l v v ξ = Lsc k n d α l s X • ξ) ∧
            (∀ v u : ι, v ≠ u → Lb k 0 n d α s X l v u = 0)) ∧
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
            ContDiff ℝ (Kt : ℕ∞) (Lsc k n d α l s)) ∧
        IsScalarReading (fun k n => Lb k 0 n) Lsc Lfb ∧
        IsActualMeans N D H Kt C kset ϖ T₀ T₁ c ρ εc lam Rχ Q Cc chart label s₀ s₁ Lb Jm
          (adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm)
          (ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb) := by
  obtain ⟨C, hC, htr⟩ := ceLetter_transfer N D Kt Cχ
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ kset ϖ T₀ T₁ c ρ εc lam Rχ Q Cc chart label s₀ s₁ Lb Ls Lfb Jm hKt hc hρ
    hεc hRχ hlam hJm hϖm hsupp hlc hcl hequiv hdet hchartJ hlabelJ hjets hpres hLbC hLbM hLbP
    hLs hfC hfM hfP
  have hM2 : 2 ≤ N + D := by omega
  have hchart_t : ∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart k t) := fun k hk t =>
    (hchartJ k hk).comp ((contDiff_const (c := t)).prodMk contDiff_id)
  have hlabel_t : ∀ k ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (label k t) := fun k hk t =>
    (hlabelJ k hk).comp ((contDiff_const (c := t)).prodMk contDiff_id)
  have hlequiv : ∀ k ∈ kset, ∀ t (p : Fin 2 → ℤ) (x : Vec 2),
      label k t (x + AVenhance.latticeShift p) = label k t x + AVenhance.latticeShift p :=
    fun k hk t => label_latticeShift (hlc k hk t) (hcl k hk t) (hequiv k hk t)
  obtain ⟨Lsc, hsc, hscC, hscM, hscP, -, hdeg⟩ := exists_scalarLetter kset (N + D) Kt ρ s₀ s₁
    (fun k n => Lb k 0 n) Ls
    (fun k hk n hn hnM d hd hdn α k₀ v u s hs =>
      hLbC k hk 0 (Nat.zero_le H) n hn hnM d hd hdn α k₀ v u s hs)
    (fun k hk n hn hnM d hd hdn α k₀ v u X =>
      hLbM k hk 0 (Nat.zero_le H) n hn hnM d hd hdn α k₀ v u X)
    (fun k hk n hn hnM d hd hdn α k₀ v u s hs p X =>
      hLbP k hk 0 (Nat.zero_le H) n hn hnM d hd hdn α k₀ v u s hs p X)
    (fun k hk n hn hnM d hd hdn α k₀ s hs X => hLs k hk n hn hnM d hd hdn α k₀ s hs X)
    Lfb hfC hfM hfP
  refine ⟨Lsc, hsc, hscC, hdeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the presentation
    intro r hr
    exact isMeanPresentation_of_flux (Set.Icc T₀ T₁) kset ϖ c ρ εc hc.ne' hρ.ne' N r Q Cc chart
      label s₀ s₁ Lb (adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm)
      (ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb) Jm hsupp hlc hcl hdet hchart_t
      (fun k hk t => (hlabel_t k hk t).differentiable (by simp))
      (fun k hk n hn hnM a₀ ha₀ s hs X => hpres k hk r hr n hn hnM a₀ ha₀ s hs X)
      (fun k hk n hn hnM d hd hdn α k₀ v u s hs =>
        (hLbC k hk r hr n hn hnM d hd hdn α k₀ v u s hs).of_le (by exact_mod_cast hKt))
      (fun a ha t ht x v k' => flux_identity kset ϖ c ρ εc hM2 chart label s₀ s₁ Lb Lsc Jm r a t
        (ha t) (fun k hk => hchart_t k hk t) (fun k hk => hcl k hk t)
        (fun k hk => hsupp k hk t ht) hsc x v k')
  · -- (2) the flux identity
    intro r _ a ha t ht x v k'
    exact flux_identity kset ϖ c ρ εc hM2 chart label s₀ s₁ Lb Lsc Jm r a t (ha t)
      (fun k hk => hchart_t k hk t) (fun k hk => hcl k hk t) (fun k hk => hsupp k hk t ht) hsc
      x v k'
  · -- (3) the diagonal letters are smooth
    intro d t _
    exact contDiff_adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm Kt d t
      (fun k hk => hchart_t k hk t) (fun k hk => hlabel_t k hk t) hscC
  · -- the diagonal letters are measurable
    intro d
    exact measurable_adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm T₀ T₁ d hJm hϖm
      hchartJ hlabelJ hscM
      (fun k hk n hn hnM d' hd hdn α l s hs => (hscC k hk n hn hnM d' hd hdn α l s hs).continuous)
  · -- the diagonal letters are periodic
    intro d t _
    exact isZ2Periodic_adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm d t
      (fun k hk => hequiv k hk t) (fun k hk => hlequiv k hk t) hscP
  · -- (3') the edge letters are smooth
    intro r hr v u d t _
    exact contDiff_ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb Kt r v u d t
      (fun k hk => hchart_t k hk t) (fun k hk => hlabel_t k hk t)
      (fun k hk n hn hnM d' hd hdn α l s hs =>
        hLbC k hk r (Finset.mem_Icc.1 hr).2 n hn hnM d' hd hdn α l v u s hs)
  · -- the edge letters are measurable
    intro r hr v u d
    exact measurable_ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb T₀ T₁ r v u d hϖm
      hchartJ hlabelJ
      (fun k hk n hn hnM d' hd hdn α l X =>
        hLbM k hk r (Finset.mem_Icc.1 hr).2 n hn hnM d' hd hdn α l v u X)
      (fun k hk n hn hnM d' hd hdn α l s hs =>
        (hLbC k hk r (Finset.mem_Icc.1 hr).2 n hn hnM d' hd hdn α l v u s hs).continuous)
  · -- the edge letters are periodic
    intro r hr v u d t _
    exact isZ2Periodic_ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb r v u d t
      (fun k hk => hequiv k hk t) (fun k hk => hlequiv k hk t)
      (fun k hk n hn hnM d' hd hdn α l s hs p X =>
        hLbP k hk r (Finset.mem_Icc.1 hr).2 n hn hnM d' hd hdn α l v u s hs p X)
  · -- (4) the transfer bound
    intro r _ hrH v u Mb hMb hLjet d j hj t ht x
    exact htr kset ϖ c ρ εc lam Rχ chart label s₀ s₁ Lb r v u Mb t hc hρ hεc hRχ hlam hMb
      (fun k hk => hchart_t k hk t) (fun k hk => hlabel_t k hk t)
      (fun k hk hwin p hp1 hpN y => hjets k hk t ht hwin p hp1 hpN y)
      (fun k hk n hn hnM d' hd hdn α k₀ s hs => hLbC k hk r hrH n hn hnM d' hd hdn α k₀ v u s hs)
      (fun k hk n hn hnM d' hd hdn α k₀ i hi s hs X =>
        hLjet k hk n hn hnM d' hd hdn α k₀ i hi s hs X) d j hj x

/-- **The actual means in the Eulerian frame** (the mean flux `M_m` of Definition 9.8 of the
paper). -/
theorem actual_means (N D H Kt : ℕ) (hD : 2 ≤ D) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (T₀ T₁ c ρ εc lam Rχ : ℝ)
        (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
        (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
        (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Ls : ℤ → ℕ → (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ)
        (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
        1 ≤ Kt → 0 < c → 0 < ρ → 0 ≤ εc → 0 < Rχ → lam = ρ / Rχ →
        (∀ i j, Measurable fun t => Jm t i j) →
        -- the time partition: measurable, and active only inside the lift windows
        (∀ k ∈ kset, Measurable (ϖ k)) →
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k)) →
        -- exact volume-preserving, lattice-equivariant, smooth charts (qualitative)
        (∀ k ∈ kset, ∀ t y, label k t (chart k t y) = y) →
        (∀ k ∈ kset, ∀ t x, chart k t (label k t x) = x) →
        (∀ k ∈ kset, ∀ t (p : Fin 2 → ℤ) y,
          chart k t (y + AVenhance.latticeShift p) = chart k t y + AVenhance.latticeShift p) →
        (∀ k ∈ kset, ∀ t y, (jacMatrix (chart k t) y).det = 1) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k q.1 q.2)) →
        (∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k q.1 q.2)) →
        -- normalized chart jets at the chart scale `Rχ` (`oc_flow_jets`), on the lift window of the pulse
        (∀ k ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k) →
          ∀ p, 1 ≤ p → p ≤ Kt + N + D → ∀ y,
          ‖iteratedFDeriv ℝ p (chart k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (label k t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        -- the chart-frame mean letters of every pulse
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
              liftMean (Q k) (Cc k) (fun _ => a₀) r n s X =
                meanApply n (Lb k r n) (fun _ => a₀) s X) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k),
              ContDiff ℝ (Kt : ℕ∞) (fun X => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
            Measurable (fun s : Set.Icc (s₀ k) (s₁ k) => Lb k r n d α s X k₀ v u)) →
        (∀ k ∈ kset, ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
            ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ (p : Fin 2 → ℤ) (X : Vec 2),
              Lb k r n d α s (X + ρ⁻¹ • AVenhance.latticeShift p) k₀ v u =
                Lb k r n d α s X k₀ v u) →
        (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
            (∀ v, Lb k 0 n d α s X k₀ v v = Ls k n d α s X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
            (∀ v u, v ≠ u → Lb k 0 n d α s X k₀ v u = 0)) →
      ∃ (AD : ∀ d : Finset.Icc 2 (N + D), ℝ → Vec 2 →
            PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
        (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 (N + D)), ℝ → Vec 2 →
            (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
              (PiLp 2 (fun _ : Fin 2 => h v))),
        -- (1) the Eulerian presentation of the glued mean of every grade
        (∀ r, r ≤ H → IsMeanPresentation (Set.Icc T₀ T₁) (N + D) r AD CE Jm
          (gluedMean kset ϖ c ρ εc N r Q Cc chart label)) ∧
        -- (2) the flux identity: the letters are the glued Piola transports of the
        --     dimensional chart-frame fluxes (at `r = 0`, minus the `Jm` part)
        (∀ r, r ≤ H → ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
          ∀ t ∈ Set.Icc T₀ T₁, ∀ x (v : ι) (k' : Fin 2),
            classicalGradeFlux (N + D) r AD CE Jm a v t x k' =
              -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 (N + D), (c⁻¹ * εc ^ n) •
                ∑ l : Fin 2, jacMatrix (chart k t) (label k t x) k' l •
                  ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u : ι,
                    Lb k r n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
                      (orderedDerivative α (fun y => a t (chart k t y)) (label k t x) u)) ∧
        -- (3) regularity of the diagonal letters
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, ContDiff ℝ (Kt : ℕ∞) (AD d t)) ∧
        (∀ d, Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => AD d q.1 q.2) ∧
        (∀ d, ∀ t ∈ Set.Icc T₀ T₁, AVenhance.IsZ2Periodic (AD d t)) ∧
        -- (3') regularity of the edge letters
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          ContDiff ℝ (Kt : ℕ∞) (CE r v u d t)) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d,
          Measurable fun q : Set.Icc T₀ T₁ × Vec 2 => CE r v u d q.1 q.2) ∧
        (∀ r ∈ Finset.Icc 1 H, ∀ v u d, ∀ t ∈ Set.Icc T₀ T₁,
          AVenhance.IsZ2Periodic (CE r v u d t)) ∧
        -- (4) the entrywise transfer bound through the chart jets
        (∀ r, 1 ≤ r → r ≤ H → ∀ (v u : ι) (M : ℝ), 0 ≤ M →
          (∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
            ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2), ∀ i, i ≤ Kt →
              ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
                ‖iteratedFDeriv ℝ i (fun X' => Lb k r n d α s X' k₀ v u) X‖ ≤
                  M * lam ^ (n - d + i)) →
          ∀ (d : Finset.Icc 2 (N + D)) (j : ℕ), j ≤ Kt → ∀ t ∈ Set.Icc T₀ T₁, ∀ x,
            ‖coefficientDerivativeArray (CE r v u d t) j x‖ ≤
              C * M * (∑ k ∈ kset, |ϖ k t|) *
                ∑ n ∈ Finset.Icc d.1 (N + D), c⁻¹ * (εc * ρ) ^ n * Rχ⁻¹ ^ (n + j - d.1)) := by
  obtain ⟨C, hC, hex⟩ := actual_means_explicit N D H Kt hD Cχ
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ kset ϖ T₀ T₁ c ρ εc lam Rχ Q Cc chart label s₀ s₁ Lb Ls Jm hKt hc hρ hεc
    hRχ hlam hJm hϖm hsupp hlc hcl hequiv hdet hchartJ hlabelJ hjets hpres hLbC hLbM hLbP hLs
  obtain ⟨Lsc, -, -, -, hL⟩ := hex kset ϖ T₀ T₁ c ρ εc lam Rχ Q Cc chart label s₀ s₁ Lb Ls
    (fun _ _ _ _ _ _ _ => 0) Jm hKt hc hρ hεc hRχ hlam hJm hϖm hsupp hlc hcl hequiv hdet hchartJ
    hlabelJ hjets hpres hLbC hLbM hLbP hLs
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => contDiff_const) (fun _ _ _ _ _ _ _ _ _ _ _ => measurable_const)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
  exact ⟨adLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lsc Jm,
    ceLetter kset ϖ c ρ εc (N + D) chart label s₀ s₁ Lb, hL⟩

end AVRegularity.CycleComparison.ActualMeans
end

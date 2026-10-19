-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
public import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.CycleComparison.Lift.CellScalarSourceSeries
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleJoint.TransitionAffineSampling
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The chain rule behind the physical edge coefficient, finite smoothness**.

Finite-order versions of the chain rule and of the flux identity. The charts `χ`, `ψ` stay
smooth (renewal charts); the field `V` is only `C^n`. A word of length `m ≤ n` needs only `C^n`:

* `orderedListDerivative_perm_of_contDiff`: permuting a word of length `≤ n` does not change the
  ordered derivative of a `C^n` field (symmetry of second derivatives of `C²` fields,
  `ContDiffAt.isSymmSndFDerivAt`, applied to the intermediate `C^{n-k}` derivatives);
* `outerListDeriv_contDiff_of`, `outerListDeriv_ofFn_of_contDiff`: regularity of the outer-first
  derivatives and their identification with `orderedDerivative`;
* `outerListDeriv_chain_of_contDiff`, `transitionT_chain_of_contDiff`: the chain rule for words
  of length `m ≤ n`;
* `transportedCoeff_flux_of_contDiff`, `transportedCoeff_flux_orders_of_contDiff`: the flux
  identity for `Dγ ≤ n + 1` (the words have length `≤ Dγ - 1`). -/

section Coordinate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate derivative of a `C^{m+1}` field is `C^m`. -/
theorem coordinateDerivative_contDiff_of_succ (k : Fin 2) {f : Vec 2 → E} {m : ℕ}
    (hf : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) f) :
    ContDiff ℝ (m : ℕ∞) (coordinateDerivative k f) := by
  have hd : ContDiff ℝ (m : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by exact_mod_cast (show m + 1 ≤ m + 1 by rfl))
  show ContDiff ℝ (m : ℕ∞) (fun X => fderiv ℝ f X (basisVec k))
  exact hd.clm_apply contDiff_const

/-- Two coordinate derivatives of a `C²` field commute. -/
theorem coordinateDerivative_commute_of_contDiff (i j : Fin 2) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) :
    coordinateDerivative j (coordinateDerivative i f) =
      coordinateDerivative i (coordinateDerivative j f) := by
  funext X
  rw [coordinateDerivative_second i j f hf X, coordinateDerivative_second j i f hf X]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (basisVec j) (basisVec i)

/-- **Finite-order symmetry of ordered derivatives.** Permuting a word of length `≤ n` does not
change the ordered derivative of a `C^n` field. -/
theorem orderedListDerivative_perm_of_contDiff {w w' : List (Fin 2)} (hw : w.Perm w') :
    ∀ (n : ℕ) (f : Vec 2 → E), ContDiff ℝ (n : ℕ∞) f → w.length ≤ n →
      orderedListDerivative w f = orderedListDerivative w' f := by
  induction hw with
  | nil => exact fun _ _ _ _ => rfl
  | cons k _ ih =>
    intro n f hf hlen
    rw [List.length_cons] at hlen
    have hf' : ContDiff ℝ ((n - 1 + 1 : ℕ) : ℕ∞) f :=
      hf.of_le (by exact_mod_cast (show n - 1 + 1 ≤ n by omega))
    exact ih (n - 1) (coordinateDerivative k f) (coordinateDerivative_contDiff_of_succ k hf')
      (by omega)
  | swap i j l =>
    intro n f hf hlen
    simp only [List.length_cons] at hlen
    have h2n : ((2 : ℕ) : WithTop ℕ∞) ≤ ((n : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 2 ≤ n by omega)
    have h2 : ContDiff ℝ 2 f := hf.of_le h2n
    change orderedListDerivative l (coordinateDerivative i (coordinateDerivative j f)) =
      orderedListDerivative l (coordinateDerivative j (coordinateDerivative i f))
    rw [coordinateDerivative_commute_of_contDiff j i h2]
  | trans h₁ _ ih₁ ih₂ =>
    intro n f hf hlen
    exact (ih₁ n f hf hlen).trans (ih₂ n f hf (by rw [← h₁.length_eq]; exact hlen))

end Coordinate

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The outer-first derivative along a list of length `l` of a `C^n` field is `C^k` for
`l + k ≤ n`. -/
theorem outerListDeriv_contDiff_of (l : List (Fin 2)) {g : Vec 2 → E} {n : ℕ}
    (hg : ContDiff ℝ (n : ℕ∞) g) :
    ∀ k : ℕ, l.length + k ≤ n → ContDiff ℝ (k : ℕ∞) (outerListDeriv l g) := by
  induction l with
  | nil =>
    intro k hk
    rw [List.length_nil] at hk
    exact hg.of_le (by exact_mod_cast (show k ≤ n by omega))
  | cons i l ih =>
    intro k hk
    rw [List.length_cons] at hk
    have h1 : ContDiff ℝ ((k + 1 : ℕ) : ℕ∞) (outerListDeriv l g) := ih (k + 1) (by omega)
    have hd : ContDiff ℝ (k : ℕ∞) (fderiv ℝ (outerListDeriv l g)) :=
      h1.fderiv_right (by exact_mod_cast (show k + 1 ≤ k + 1 by rfl))
    show ContDiff ℝ (k : ℕ∞) (fun x => fderiv ℝ (outerListDeriv l g) x (basisVec i))
    exact hd.clm_apply contDiff_const

/-- For a `C^n` field and a word of length `m ≤ n`, the outer-first derivative along the word is
its `orderedDerivative`. -/
theorem outerListDeriv_ofFn_of_contDiff {g : Vec 2 → E} {n : ℕ} (hg : ContDiff ℝ (n : ℕ∞) g)
    {m : ℕ} (A : DerivativeWord2 m) (hm : m ≤ n) :
    outerListDeriv (List.ofFn A) g = orderedDerivative A g := by
  have h := orderedListDerivative_perm_of_contDiff (List.reverse_perm (List.ofFn A)) n g hg
    (by rw [List.length_reverse, List.length_ofFn]; exact hm)
  rw [outerListDeriv_eq_reverse]
  exact h

/-- The Leibniz rule for a word-indexed sum, with differentiability required only on the
indices of the sum. -/
theorem transition_fderiv_wordSum_apply_of (s : Finset ℕ)
    (c : ∀ r, DerivativeWord2 r → Vec 2 → ℝ) (f : ∀ r, DerivativeWord2 r → Vec 2 → E)
    (hc : ∀ r ∈ s, ∀ A, Differentiable ℝ (c r A)) (hf : ∀ r ∈ s, ∀ A, Differentiable ℝ (f r A))
    (x v : Vec 2) :
    fderiv ℝ (fun y => ∑ r ∈ s, ∑ A : DerivativeWord2 r, c r A y • f r A y) x v =
      ∑ r ∈ s, ∑ A : DerivativeWord2 r,
        (c r A x • fderiv ℝ (f r A) x v + fderiv ℝ (c r A) x v • f r A x) := by
  have hA : ∀ r ∈ s, ∀ A : DerivativeWord2 r,
      DifferentiableAt ℝ (fun y => c r A y • f r A y) x :=
    fun r hr A => ((hc r hr A) x).fun_smul ((hf r hr A) x)
  have hr : ∀ r ∈ s,
      DifferentiableAt ℝ (fun y => ∑ A : DerivativeWord2 r, c r A y • f r A y) x :=
    fun r hrs => DifferentiableAt.fun_sum fun A _ => hA r hrs A
  rw [fderiv_fun_sum hr, _root_.sum_apply]
  refine Finset.sum_congr rfl fun r hrs => ?_
  rw [fderiv_fun_sum fun A _ => hA r hrs A, _root_.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [fderiv_fun_smul ((hc r hrs A) x) ((hf r hrs A) x)]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply]

/-- The right side of the chain rule for a list of length `l` is differentiable if the physical
field is `C^n` with `l + 1 ≤ n`. -/
theorem transitionSum_differentiable_of {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x a i)) (I : List (Fin 2)) {u : Vec 2 → E}
    {n : ℕ} (hu : ContDiff ℝ (n : ℕ∞) u) (hI : I.length + 1 ≤ n) :
    Differentiable ℝ (transitionSum K I u) := fun x => by
  unfold transitionSum
  refine DifferentiableAt.fun_sum fun r hr => DifferentiableAt.fun_sum fun A _ => ?_
  have hr' : List.length (List.ofFn A) + 1 ≤ n := by
    rw [List.length_ofFn]
    simp only [Finset.mem_range] at hr
    omega
  exact ((AVRegularity.CycleJointProofs.transitionT_spatial_smooth K hK I
    (List.ofFn A)).differentiable (by simp) x).fun_smul
    ((outerListDeriv_contDiff_of (List.ofFn A) hu 1 hr').differentiable (by simp) x)

/-- **Chain rule, outer-first form, finite smoothness.** As `outerListDeriv_chain`, for a `C^n`
field `V` and a list `I` of length `≤ n`. -/
theorem outerListDeriv_chain_of_contDiff {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : ∀ x a i, K x a i = fderiv ℝ χ (ψ x) (basisVec i) a)
    (hKs : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x a i))
    {n : ℕ} {V : Vec 2 → E} (hV : ContDiff ℝ (n : ℕ∞) V) (I : List (Fin 2))
    (hI : I.length ≤ n) :
    (fun x => outerListDeriv I V (ψ x)) = transitionSum K I (V ∘ ψ) := by
  have hu : ContDiff ℝ (n : ℕ∞) (V ∘ ψ) := hV.comp (hψ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  induction I with
  | nil =>
    funext x
    show V (ψ x) = ∑ r ∈ Finset.range 1, ∑ A : DerivativeWord2 r,
      transitionT K [] (List.ofFn A) x • outerListDeriv (List.ofFn A) (V ∘ ψ) x
    rw [Finset.sum_range_one]
    simp only [Fintype.sum_unique, List.ofFn_zero]
    exact (one_smul ℝ (V (ψ x))).symm
  | cons i I ih =>
    rw [List.length_cons] at hI
    have hSd : Differentiable ℝ (transitionSum K I (V ∘ ψ)) :=
      transitionSum_differentiable_of hKs I hu hI
    -- the label derivative `∂^I V` read through the chart
    have h1 : outerListDeriv I V = transitionSum K I (V ∘ ψ) ∘ χ := by
      funext y
      have hy : outerListDeriv I V (ψ (χ y)) = transitionSum K I (V ∘ ψ) (χ y) :=
        congrFun (ih (by omega)) (χ y)
      rw [hψχ y] at hy
      exact hy
    funext x
    have hdT : ∀ (r : ℕ) (A : DerivativeWord2 r),
        Differentiable ℝ (transitionT K I (List.ofFn A)) := fun _ A =>
      (AVRegularity.CycleJointProofs.transitionT_spatial_smooth K hKs I
        (List.ofFn A)).differentiable (by simp)
    have hdD : ∀ r ∈ Finset.range (I.length + 1), ∀ A : DerivativeWord2 r,
        Differentiable ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) := fun r hr A =>
      (outerListDeriv_contDiff_of (List.ofFn A) hu 1 (by
        rw [List.length_ofFn]
        simp only [Finset.mem_range] at hr
        omega)).differentiable (by simp)
    have hderiv : ∀ b : Fin 2, fderiv ℝ (transitionSum K I (V ∘ ψ)) x (basisVec b) =
        ∑ r ∈ Finset.range (I.length + 1), ∑ A : DerivativeWord2 r,
          (transitionT K I (List.ofFn A) x •
              fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) +
            fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) •
              outerListDeriv (List.ofFn A) (V ∘ ψ) x) := fun b =>
      transition_fderiv_wordSum_apply_of (Finset.range (I.length + 1))
        (fun _ A => transitionT K I (List.ofFn A))
        (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ)) (fun r _ A => hdT r A) hdD x
        (basisVec b)
    -- one label derivative: `∂_{y_i} = ∑_b K_{bi} ∂_{x_b}`
    have hchain : outerListDeriv (i :: I) V (ψ x) =
        ∑ b : Fin 2, K x b i • ∑ r ∈ Finset.range (I.length + 1), ∑ A : DerivativeWord2 r,
          (transitionT K I (List.ofFn A) x •
              fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) +
            fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) •
              outerListDeriv (List.ofFn A) (V ∘ ψ) x) := by
      rw [outerListDeriv_cons_apply, h1, fderiv_comp (ψ x) (hSd (χ (ψ x))) (hχd (ψ x)),
        ContinuousLinearMap.comp_apply, hχψ x,
        transition_clm_apply_eq_sum (fderiv ℝ (transitionSum K I (V ∘ ψ)) x)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hK x b i, hderiv b]
    -- the top order of the derivative part vanishes
    have hp : ∀ A : DerivativeWord2 (I.length + 1),
        ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) = 0 := by
      intro A
      rw [AVRegularity.CycleJointProofs.transitionT_zero_above_native_order K I (List.ofFn A)
        (by rw [List.length_ofFn]; omega)]
      simp
    -- the empty output word has no order-lowering part
    have h0 : ∀ A : DerivativeWord2 0, transitionT K (i :: I) (List.ofFn A) x =
        ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b) := by
      intro A
      rw [List.ofFn_zero, transitionT_cons_nil_apply]
    -- the order-lowering part of `T_{(i,I),(a,A₀)}` is `K_{ai} T_{I,A₀}`
    have hj : ∀ s : ℕ, ∑ A : DerivativeWord2 (s + 1),
        (transitionT K (i :: I) (List.ofFn A) x -
            ∑ b : Fin 2, K x b i * fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b)) •
          outerListDeriv (List.ofFn A) (V ∘ ψ) x =
        ∑ b : Fin 2, ∑ A : DerivativeWord2 s, (K x b i * transitionT K I (List.ofFn A) x) •
          fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b) := by
      intro s
      rw [transition_sum_word_succ]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      simp only [List.ofFn_cons]
      rw [transitionT_cons_cons_apply, outerListDeriv_cons_apply]
      congr 1
      ring
    exact hchain.trans ((transition_sum_regroup (m := I.length + 1) (fun b => K x b i)
      (fun _ A => transitionT K I (List.ofFn A) x)
      (fun b _ A => fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b))
      (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ) x)
      (fun b _ A => fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b))).trans
      (transition_sum_peel (m := I.length + 1)
        (fun _ A => transitionT K (i :: I) (List.ofFn A) x)
        (fun _ A => ∑ b : Fin 2, K x b i *
          fderiv ℝ (transitionT K I (List.ofFn A)) x (basisVec b))
        (fun _ A => outerListDeriv (List.ofFn A) (V ∘ ψ) x)
        (fun s => ∑ b : Fin 2, ∑ A : DerivativeWord2 s,
          (K x b i * transitionT K I (List.ofFn A) x) •
            fderiv ℝ (outerListDeriv (List.ofFn A) (V ∘ ψ)) x (basisVec b))
        hp h0 hj).symm)

/-- **The chain rule, finite smoothness** (`transitionT_chain` for a `C^n` field `V` and a word
`I` of length `m ≤ n`): `(∂^I V)(ψ x) = ∑_{r ≤ m} ∑_{|A| = r} T_{I,A}(x) (∂^A (V ∘ ψ))(x)`. -/
theorem transitionT_chain_of_contDiff {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {n : ℕ} {V : Vec 2 → E} (hV : ContDiff ℝ (n : ℕ∞) V) {m : ℕ} (I : DerivativeWord2 m)
    (hm : m ≤ n) (x : Vec 2) :
    orderedDerivative I V (ψ x) =
      ∑ r ∈ Finset.range (m + 1), ∑ A : DerivativeWord2 r,
        transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x •
          orderedDerivative A (V ∘ ψ) x := by
  have hu : ContDiff ℝ (n : ℕ∞) (V ∘ ψ) := hV.comp (hψ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hmain : outerListDeriv (List.ofFn I) V (ψ x) =
      transitionSum (chartInvJacobian ψ) (List.ofFn I) (V ∘ ψ) x :=
    congrFun (outerListDeriv_chain_of_contDiff hχ hψ hψχ hχψ
      (chartInvJacobian_apply_of_inverse (hχ.differentiable (by simp))
        (hψ.differentiable (by simp)) hψχ hχψ)
      (chartInvJacobian_entry_contDiff hχ hψ hψχ hχψ) hV (List.ofFn I)
      (by rw [List.length_ofFn]; exact hm)) x
  rw [outerListDeriv_ofFn_of_contDiff hV I hm] at hmain
  rw [hmain]
  simp only [transitionSum, List.length_ofFn]
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun A _ => ?_
  rw [outerListDeriv_ofFn_of_contDiff hu A (by
    simp only [Finset.mem_range] at hr
    omega)]

end ChainRule

section Flux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Flux identity for the transported coefficient, finite smoothness.** As
`transportedCoeff_flux`, for a `C^n` field `V` and `Dγ ≤ n + 1` (the label words have length
`≤ Dγ - 1`). -/
theorem transportedCoeff_flux_of_contDiff {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {n : ℕ} {V : Vec 2 → E} (hV : ContDiff ℝ (n : ℕ∞) V) (Dγ : ℕ) (hDn : Dγ ≤ n + 1)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (x : Vec 2) (a₀ : Fin 2) :
    ∑ r ∈ Finset.range Dγ, ∑ A : DerivativeWord2 r,
        transportedCoeff (chartInvJacobian ψ) Dγ B r A x a₀ • orderedDerivative A (V ∘ ψ) x =
      ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        (chartInvJacobian ψ x a₀ i₀ * B d I i₀) • orderedDerivative I V (ψ x) := by
  calc _ = ∑ r ∈ Finset.range Dγ, ∑ A : DerivativeWord2 r, ∑ d ∈ Finset.Icc (r + 1) Dγ,
          ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
            (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
              transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
              orderedDerivative A (V ∘ ψ) x := by
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        simp only [transportedCoeff, Finset.sum_smul]
    _ = ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
          ∑ r ∈ Finset.range (d - 1 + 1), ∑ A : DerivativeWord2 r,
            (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
              transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
              orderedDerivative A (V ∘ ψ) x :=
        transition_flux_reindex Dγ fun _ A d I i₀ =>
          (chartInvJacobian ψ x a₀ i₀ * B d I i₀ *
            transitionT (chartInvJacobian ψ) (List.ofFn I) (List.ofFn A) x) •
            orderedDerivative A (V ∘ ψ) x
    _ = _ := by
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun _ _ => ?_
        have hdn : d - 1 ≤ n := by
          simp only [Finset.mem_Icc] at hd
          omega
        rw [transitionT_chain_of_contDiff hχ hψ hψχ hχψ hV I hdn x]
        simp only [Finset.smul_sum, smul_smul]

/-- `transportedCoeff_flux_of_contDiff` indexed by the orders `d ∈ [1, Dγ]`, as
`constituentPhysical` indexes the physical coefficient. -/
theorem transportedCoeff_flux_orders_of_contDiff {χ ψ : Vec 2 → Vec 2}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y)
    (hχψ : ∀ x, χ (ψ x) = x) {n : ℕ} {V : Vec 2 → E} (hV : ContDiff ℝ (n : ℕ∞) V) (Dγ : ℕ)
    (hDn : Dγ ≤ n + 1) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (x : Vec 2)
    (a₀ : Fin 2) :
    ∑ d ∈ Finset.Icc 1 Dγ, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ψ) Dγ B (d - 1) A x a₀ •
          orderedDerivative A (V ∘ ψ) x =
      ∑ d ∈ Finset.Icc 1 Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        (chartInvJacobian ψ x a₀ i₀ * B d I i₀) • orderedDerivative I V (ψ x) := by
  refine Eq.trans (transition_sum_Icc_one Dγ _) ?_
  exact transportedCoeff_flux_of_contDiff hχ hψ hψχ hχψ hV Dγ hDn B x a₀

end Flux

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Slice norms of finite sums and the pull-back energy density at one time.** The mass-weighted
cell norms of a flux and a scalar at one time (`ChartTransport.fluxInt`, `scalInt`) of a finite
sum of `n` continuous fields are at most `n` times the sum of the norms
(`fluxInt_sum_le`, `scalInt_sum_le`; Cauchy-Schwarz). The gradient energy density
(`ResidualTimeData.gradDensity`) of the pull-back of a periodic field by an exact chart is at
most a constant times that of the field (`gradDensity_comp_le`, the pointwise-in-time form of
`cycle_residual_chart_transport` (2)). These are the time-slice estimates of the reconstruction:
the residual of the glued lift is bounded at every time, before the time integration.
-/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- A finite sum in `ℝ≥0∞`-norm squared. -/
theorem enorm_sum_sq_le {E : Type*} [NormedAddCommGroup E] {κ : Type*} (S : Finset κ)
    (y : κ → E) : ‖∑ i ∈ S, y i‖ₑ ^ 2 ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, ‖y i‖ₑ ^ 2 := by
  calc ‖∑ i ∈ S, y i‖ₑ ^ 2 ≤ (∑ i ∈ S, ‖y i‖ₑ) ^ 2 := by
        gcongr
        exact enorm_sum_le S y
    _ ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, ‖y i‖ₑ ^ 2 :=
        AVRegularity.ennreal_sq_sum_le_card_mul_sum_sq S fun i => ‖y i‖ₑ

/-- **The flux slice norm of a finite sum of continuous fluxes.** -/
theorem fluxInt_sum_le {κ : Type*} (S : Finset κ) (G : κ → Vec 2 → Fin 2 → ∀ i, h i)
    (hG : ∀ i ∈ S, ∀ k, Continuous (fun x => G i x k)) (π : ι → ℝ) :
    fluxInt π (fun x k => ∑ i ∈ S, G i x k) ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, fluxInt π (G i) := by
  have hm : ∀ i ∈ S, ∀ v, Measurable (fun x => ∑ k : Fin 2, ‖G i x k v‖ₑ ^ 2) :=
    fun i hi v => Finset.measurable_sum _ fun k _ =>
      ((continuous_apply v).comp (hG i hi k)).enorm.measurable.pow_const 2
  have hpt : ∀ v x, ∑ k : Fin 2, ‖(∑ i ∈ S, G i x k) v‖ₑ ^ 2 ≤
      (S.card : ℝ≥0∞) * ∑ i ∈ S, ∑ k : Fin 2, ‖G i x k v‖ₑ ^ 2 := by
    intro v x
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.sum_apply]
    exact enorm_sum_sq_le S fun i => G i x k v
  unfold fluxInt
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ k : Fin 2, ‖(∑ i ∈ S, G i x k) v‖ₑ ^ 2
      ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ((S.card : ℝ≥0∞) *
          ∑ i ∈ S, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖G i x k v‖ₑ ^ 2) := by
        refine Finset.sum_le_sum fun v _ => ?_
        gcongr
        refine (lintegral_mono fun x => hpt v x).trans_eq ?_
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
          lintegral_finsetSum' _ fun i hi => (hm i hi v).aemeasurable]
    _ = (S.card : ℝ≥0∞) * ∑ i ∈ S, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖G i x k v‖ₑ ^ 2 := by
        simp only [Finset.mul_sum]
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by ring

/-- **The scalar slice norm of a finite sum of continuous scalars.** -/
theorem scalInt_sum_le {κ : Type*} (S : Finset κ) (q : κ → Vec 2 → ∀ i, h i)
    (hq : ∀ i ∈ S, Continuous (q i)) (π : ι → ℝ) :
    scalInt π (fun x => ∑ i ∈ S, q i x) ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, scalInt π (q i) := by
  have hm : ∀ i ∈ S, ∀ v, Measurable (fun x => ‖q i x v‖ₑ ^ 2) :=
    fun i hi v => ((continuous_apply v).comp (hq i hi)).enorm.measurable.pow_const 2
  have hpt : ∀ v x, ‖(∑ i ∈ S, q i x) v‖ₑ ^ 2 ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, ‖q i x v‖ₑ ^ 2 := by
    intro v x
    rw [Finset.sum_apply]
    exact enorm_sum_sq_le S fun i => q i x v
  unfold scalInt
  calc ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ‖(∑ i ∈ S, q i x) v‖ₑ ^ 2
      ≤ ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ((S.card : ℝ≥0∞) *
          ∑ i ∈ S, ∫⁻ x in AVenhance.unitCube, ‖q i x v‖ₑ ^ 2) := by
        refine Finset.sum_le_sum fun v _ => ?_
        gcongr
        refine (lintegral_mono fun x => hpt v x).trans_eq ?_
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
          lintegral_finsetSum' _ fun i hi => (hm i hi v).aemeasurable]
    _ = (S.card : ℝ≥0∞) * ∑ i ∈ S, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ x in AVenhance.unitCube, ‖q i x v‖ₑ ^ 2 := by
        simp only [Finset.mul_sum]
        conv_lhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by ring

/-- **The gradient energy density of a pull-back by an exact chart** at one time. -/
theorem gradDensity_comp_le [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    {Φ : ℝ → Vec 2 → Vec 2} {Ψt : Vec 2 → Vec 2} {t : ℝ} (hC : IsChart (Φ t) Ψt)
    {m : ℕ} (a : ℝ → Vec 2 → ∀ i, h i) (ha : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (a t))
    (hap : AVenhance.IsZ2Periodic (a t)) (hΦ : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (Φ t))
    {D Rχ ρ : ℝ} (hD : 1 ≤ D) (hρ : 0 < ρ) (hρR : ρ ≤ Rχ) (hJ : JetBound (Φ t) (m + 1) D Rχ)
    (π : ι → ℝ) :
    ResidualTimeData.gradDensity π ρ m (fun s y => a s (Φ s y)) t ≤
      ENNReal.ofReal (ChartTransport.densConst m 1 1 ((m + 1).factorial * D ^ (m + 1))) *
        ResidualTimeData.gradDensity π ρ m a t := by
  unfold ResidualTimeData.gradDensity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  have hau : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun x => a t x u) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha
  have hapu : AVenhance.IsZ2Periodic (fun x => a t x u) := fun n x => congrFun (hap n x) u
  have hcomp : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun y => a t (Φ t y) u) := hau.comp hΦ
  rw [classicalGradFactorialSq_eq_fsum ρ m hau, classicalGradFactorialSq_eq_fsum ρ m hcomp,
    mul_left_comm]
  gcongr
  exact fsum_comp_le hC (M := m) (e := 1) (N := m + 1) le_rfl le_rfl hau hapu hΦ hD hρ hρR hJ

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public section
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The label-frame operators in physical coordinates** (exact Piola transports flux by
`(DΦR)∘Φ⁻¹` and preserves the divergence pairing). Let `χ` be a chart (labels to physical points)
with unit Jacobian determinant and inverse `ψ`, and `G = (Dχ)⁻¹ (Dχ)⁻ᵀ` its material metric. For a
field `V` of the labels and its physical reading `u = V ∘ ψ`:

* the physical gradient is the push-forward of the metric gradient,
  `∂_k u(x) = ∑_l Dχ(ψ x)_{kl} (G ∇V)_l(ψ x)` (`chart_grad`);
* the physical Laplacian is the label diffusion, `Δu(x) = div(G ∇V)(ψ x)` (`chart_laplacian`, by the
  Piola identity `Charts.piola_forward_vector`);
* a label drift `w` pushed forward by the chart, `Dχ(ψ x) w(ψ x) = b(x)`, is the physical drift,
  `(w·∇V)(ψ x) = (b·∇u)(x)` (`chart_drift`).

These are pointwise identities; they turn the label density of the lift (`labelDensity`) into
physical operators applied to the physical lift. -/

/-- A vector of the plane is the combination of the coordinate vectors. -/
theorem vec_eq_sum_smul_basisVec (v : Vec 2) : v = ∑ j, v j • basisVec j := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The Jacobian of the labels is a left inverse of the Jacobian of the chart. -/
theorem jacMatrix_label_mul_chart {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (x : Vec 2) :
    jacMatrix ψ x * jacMatrix χ (ψ x) = 1 := by
  have hcomp := CycleReference.jacMatrix_comp (f := ψ) (g := χ) (ψ x) (hψ _) (hχ _)
  have he : ψ ∘ χ = id := funext hψχ
  rw [he, CycleReference.jacMatrix_identity, hχψ] at hcomp
  exact hcomp.symm

/-- The Jacobian of the chart is a left inverse of the Jacobian of the labels. -/
theorem jacMatrix_chart_mul_label {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (x : Vec 2) :
    jacMatrix χ (ψ x) * jacMatrix ψ x = 1 :=
  mul_eq_one_comm.1 (jacMatrix_label_mul_chart hχ hψ hψχ hχψ x)

/-- The Jacobian of the labels is the inverse of the Jacobian of the chart. -/
theorem jacMatrix_label_eq_inv {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (x : Vec 2) :
    jacMatrix ψ x = (jacMatrix χ (ψ x))⁻¹ :=
  (Matrix.inv_eq_left_inv (jacMatrix_label_mul_chart hχ hψ hψχ hχψ x)).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate chain rule for a field read through the labels. -/
theorem fderiv_comp_label_basis {V : Vec 2 → E} {ψ : Vec 2 → Vec 2} {x : Vec 2}
    (hV : DifferentiableAt ℝ V (ψ x)) (hψ : DifferentiableAt ℝ ψ x) (k : Fin 2) :
    fderiv ℝ (fun x' => V (ψ x')) x (basisVec k) =
      ∑ j, jacMatrix ψ x j k • fderiv ℝ V (ψ x) (basisVec j) := by
  rw [fderiv_fun_comp x hV hψ, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [vec_eq_sum_smul_basisVec (fderiv ℝ ψ x (basisVec k))]
  simp only [map_sum, map_smul, jacMatrix, Matrix.of_apply]

/-- **The physical gradient is the push-forward of the metric gradient.** -/
theorem chart_grad {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ) (hψ : Differentiable ℝ ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ y, G y = (jacMatrix χ y)⁻¹ * ((jacMatrix χ y)⁻¹)ᵀ)
    {V : Vec 2 → E} (hV : Differentiable ℝ V) (x : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun x' => V (ψ x')) x (basisVec k) =
      ∑ l, jacMatrix χ (ψ x) k l • ∑ j, G (ψ x) l j • fderiv ℝ V (ψ x) (basisVec j) := by
  rw [fderiv_comp_label_basis (hV _) (hψ x) k]
  have hinv := jacMatrix_label_eq_inv hχ hψ hψχ hχψ x
  have hGx : G (ψ x) = jacMatrix ψ x * (jacMatrix ψ x)ᵀ := by rw [hG, hinv]
  have hJ := jacMatrix_chart_mul_label hχ hψ hψχ hχψ x
  have hcoef : ∀ j, ∑ l, jacMatrix χ (ψ x) k l * G (ψ x) l j = jacMatrix ψ x j k := by
    intro j
    have hm : jacMatrix χ (ψ x) * G (ψ x) = (jacMatrix ψ x)ᵀ := by
      rw [hGx, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    have := congrFun (congrFun hm k) j
    rwa [Matrix.mul_apply, Matrix.transpose_apply] at this
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, hcoef j]

/-- **The physical Laplacian is the label diffusion** (Piola). -/
theorem chart_laplacian {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ y, G y = (jacMatrix χ y)⁻¹ * ((jacMatrix χ y)⁻¹)ᵀ)
    (hGd : ∀ i j, Differentiable ℝ (fun y => G y i j))
    {V : Vec 2 → E} (hV : ContDiff ℝ 2 V) (x : Vec 2) :
    ∑ k, fderiv ℝ (fun x' => fderiv ℝ (fun x'' => V (ψ x'')) x' (basisVec k)) x (basisVec k) =
      ∑ i, fderiv ℝ (fun y => ∑ j, G y i j • fderiv ℝ V y (basisVec j)) (ψ x) (basisVec i) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hV1 : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hdV : ∀ j, Differentiable ℝ (fun y => fderiv ℝ V y (basisVec j)) := fun j =>
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const _)
  have hF : ∀ l, Differentiable ℝ (fun y => ∑ j, G y l j • fderiv ℝ V y (basisVec j)) :=
    fun l => Differentiable.fun_sum fun j _ => (hGd l j).smul (hdV j)
  have hfun : ∀ k, (fun x' => fderiv ℝ (fun x'' => V (ψ x'')) x' (basisVec k)) =
      fun x' => ∑ l, jacMatrix χ (ψ x') k l •
        (fun y => fun l' => ∑ j, G y l' j • fderiv ℝ V y (basisVec j)) (ψ x') l :=
    fun k => funext fun x' => chart_grad hχd hψ hψχ hχψ G hG hV1 x' k
  simp only [hfun]
  exact Charts.piola_forward_vector hχ hψ hψχ hχψ hd
    (F := fun y l => ∑ j, G y l j • fderiv ℝ V y (basisVec j)) hF x

/-- **A pushed-forward label drift is the physical drift.** -/
theorem chart_drift {χ ψ : Vec 2 → Vec 2} (hχ : Differentiable ℝ χ) (hψ : Differentiable ℝ ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    {V : Vec 2 → E} (hV : Differentiable ℝ V) (w b : Vec 2 → Vec 2)
    (hwb : ∀ x, (jacMatrix χ (ψ x)).mulVec (w (ψ x)) = b x) (x : Vec 2) :
    ∑ k, w (ψ x) k • fderiv ℝ V (ψ x) (basisVec k) =
      ∑ k, b x k • fderiv ℝ (fun x' => V (ψ x')) x (basisVec k) := by
  have hw : (jacMatrix ψ x).mulVec (b x) = w (ψ x) := by
    rw [← hwb x, Matrix.mulVec_mulVec, jacMatrix_label_mul_chart hχ hψ hψχ hχψ x,
      Matrix.one_mulVec]
  simp only [fderiv_comp_label_basis (hV _) (hψ x), Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← hw]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! Slow jets of a time-dependent field of integral type in time: if `Ψ(s, ·)` has the time
derivative `Ψ'(s, ·)` at every time of `[a, b]` and the slow derivatives of `Ψ'` are bounded
uniformly, then every ordered slow derivative `∂^α Ψ(s, ·)(X)` is of integral type on `[a, b]`
with density `∂^α Ψ'(s, ·)(X)` (the derivatives commute with the time integral,
`orderedDerivative_parameter_intervalIntegral`). This is the time regularity of the jets of the
coarse field read in the moving chart, for a coarse field that depends on time. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A function with a continuous derivative on `[a, b]` is of integral type there. -/
theorem isPrimOn_of_hasDerivAt {a b : ℝ} (hab : a ≤ b) {g g' : ℝ → E}
    (hd : ∀ s ∈ Icc a b, HasDerivAt g (g' s) s) (hc : ContinuousOn g' (Icc a b)) :
    IsPrimOn a b g g' := by
  have hint : IntervalIntegrable g' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc
  refine ⟨hint, fun s hs => ?_⟩
  have hsub : uIcc a s ⊆ Icc a b := by
    rw [uIcc_of_le hs.1]
    exact Icc_subset_Icc le_rfl hs.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx))
    (hint.mono_set (by rw [uIcc_of_le hab]; exact hsub))]
  abel

/-- **Slow jets of integral type.** -/
theorem jet_prim_of_timeDeriv {a b : ℝ} (hab : a ≤ b) (n : ℕ) (Ψ Ψ' : ℝ → Vec 2 → E)
    (hΨ : ∀ s ∈ Icc a b, ∀ X, HasDerivAt (fun s' => Ψ s' X) (Ψ' s X) s)
    (hcont : ∀ X, ContinuousOn (fun s => Ψ' s X) (Icc a b))
    (hsm : ∀ s ∈ Icc a b, ContDiff ℝ (n : ℕ∞) (Ψ s))
    (hsm' : ∀ s ∈ Icc a b, ContDiff ℝ (n : ℕ∞) (Ψ' s))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ j (Ψ' s) x‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) (X : Vec 2) :
    IsPrimOn a b (fun s => orderedDerivative α (Ψ s) X)
      (fun s => orderedDerivative α (Ψ' s) X) := by
  classical
  have hn0 : ∀ j ≤ n, 0 ≤ C j := fun j hj =>
    (norm_nonneg _).trans (hb j hj a (left_mem_Icc.2 hab) 0)
  -- the truncated time derivative, smooth and bounded at every time
  let f : ℝ → Vec 2 → E := fun s x => (Icc a b).piecewise (fun s => Ψ' s x) (fun _ => 0) s
  have hf_in : ∀ s ∈ Icc a b, f s = Ψ' s := fun s hs => by
    funext x; simp only [f, Set.piecewise_eq_of_mem _ _ _ hs]
  have hf_out : ∀ s ∉ Icc a b, f s = fun _ => 0 := fun s hs => by
    funext x; simp only [f, Set.piecewise_eq_of_notMem _ _ _ hs]
  have hfm : ∀ x, Measurable (fun s => f s x) := fun x =>
    (hcont x).measurable_piecewise continuousOn_const measurableSet_Icc
  have hfs : ∀ s, ContDiff ℝ (n : ℕ∞) (f s) := fun s => by
    by_cases hs : s ∈ Icc a b
    · rw [hf_in s hs]; exact hsm' s hs
    · rw [hf_out s hs]; exact contDiff_const
  have hfb : ∀ j ≤ n, ∀ s x, ‖iteratedFDeriv ℝ j (f s) x‖ ≤ C j := fun j hj s x => by
    by_cases hs : s ∈ Icc a b
    · rw [hf_in s hs]; exact hb j hj s hs x
    · rw [hf_out s hs, iteratedFDeriv_fun_zero]
      simpa using hn0 j hj
  have hint : IntervalIntegrable (fun s => orderedDerivative α (Ψ' s) X) volume a b := by
    have hmeas : Measurable (fun s => orderedDerivative α (f s) X) :=
      Lift.orderedDerivative_parameter_measurable f n hfm hfs q hq α X
    have hbound : ∀ s, ‖orderedDerivative α (f s) X‖ ≤ C q := fun s => by
      rw [AVRegularity.orderedDerivative_eq_iteratedFDeriv α
        ((hfs s).of_le (by exact_mod_cast hq))]
      refine ((iteratedFDeriv ℝ q (f s) X).le_opNorm _).trans ?_
      have h1 : ∏ i : Fin q, ‖basisVec (α (Fin.rev i))‖ = 1 :=
        Finset.prod_eq_one fun i _ => by simp [basisVec, Pi.norm_single]
      rw [h1, mul_one]
      exact hfb q hq s X
    have hI : IntervalIntegrable (fun s => orderedDerivative α (f s) X) volume a b :=
      (intervalIntegrable_const (c := C q)).mono_fun' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hbound)
    refine hI.congr fun s hs => ?_
    rw [uIoc_of_le hab] at hs
    rw [hf_in s (Ioc_subset_Icc_self hs)]
  refine ⟨hint, fun s hs => ?_⟩
  have hsub : uIcc a s ⊆ Icc a b := by
    rw [uIcc_of_le hs.1]
    exact Icc_subset_Icc le_rfl hs.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hval : Ψ s = fun Y => Ψ a Y + ∫ σ in a..s, f σ Y := by
    funext Y
    have hp := (isPrimOn_of_hasDerivAt hab (fun σ hσ => hΨ σ hσ Y) (hcont Y)).2 s hs
    beta_reduce at hp
    rw [hp]
    congr 1
    exact intervalIntegral.integral_congr fun σ hσ => (congrFun (hf_in σ (hsub hσ)) Y).symm
  have hsmI : ContDiff ℝ (q : ℕ∞) (fun Y => ∫ σ in a..s, f σ Y) := by
    have he : (fun Y => ∫ σ in a..s, f σ Y) = fun Y => Ψ s Y - Ψ a Y := by
      funext Y
      rw [hval]
      beta_reduce
      abel
    rw [he]
    exact ((hsm s hs).sub (hsm a ha)).of_le (by exact_mod_cast hq)
  beta_reduce
  rw [hval, AVRegularity.orderedDerivative_add α ((hsm a ha).of_le (by exact_mod_cast hq)) hsmI,
    Lift.orderedDerivative_parameter_intervalIntegral n f hfm hfs C hfb a s q hq α]
  beta_reduce
  congr 1
  exact intervalIntegral.integral_congr fun σ hσ => by
    simp only [hf_in σ (hsub hσ)]

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Bill bookkeeping of the physical reconstruction: energies and the residual norm**. The
residual norm is `𝔑_ν(R,q) = ν^{-1/2}‖R‖_{L²(I;L²_π)} + ‖q‖_{L¹(I;L²_π)}`.

* Energy conversions: the strong energy `𝓔^B_{ρ,m;π}(W) ≤ X` bounds the time integral of the
  mass-weighted gradient density by `X²/B` (`lintegral_grad_le_of_strongEnergyUpTo_le`, and
  `integral_grad_le_of_strongEnergyUpTo_le` for the Bochner integral under componentwise time
  measurability); the coarse-flux bound `B^{-1/2}(∫_I ‖F‖²)^{1/2} ≤ Y` of
  `cycle_coarse_defect_bound` gives `∫_I ‖F‖² ≤ B Y²` (`integral_mass_le_of_coarse_bound`).
* The residual norm of the value jets of two torus Sobolev families `(R, q)` is at most
  `(ν⁻¹ ∫_I ‖R‖²_{ρ,K;π})^{1/2} + ∫_I ‖q‖_{ρ,K;π}` for every radius `ρ`
  (`residualNorm_le_of_mass`): the value component is one summand of the factorial norm. -/

section Energy

/-- The truncated gradient factorial norm is nonnegative. -/
theorem gradUpTo_nonneg {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (m : ℕ) (X : JetL2 μ K E) :
    0 ≤ gradFactorialNormSqUpTo ρ m X := by
  unfold gradFactorialNormSqUpTo
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
  · exact le_rfl

/-- **The strong energy controls the gradient density** (lower integral form): from
`𝓔^B_{ρ,m;π}(W) ≤ X`, `∑_v π_v⁻¹ ∫⁻_I |∇W_v|²_{ρ,m} ≤ X²/B`. -/
theorem lintegral_grad_le_of_strongEnergyUpTo_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {ρ B X : ℝ} {π : ι → ℝ} {t₀ t₁ : ℝ} {m K : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)}
    (hB : 0 < B) (hX : 0 ≤ X) (hE : strongEnergyUpTo ρ B π t₀ t₁ m W ≤ ENNReal.ofReal X) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val) ≤
      ENNReal.ofReal (X ^ 2 / B) := by
  have hdef : strongEnergyUpTo ρ B π t₀ t₁ m W =
      (∑ v, ENNReal.ofReal (π v)⁻¹ *
        ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSqUpTo ρ m (W v t).val))
          + ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁,
              ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val))) ^ (1 / 2 : ℝ) := rfl
  have h12 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  have h2 := ENNReal.rpow_le_rpow hE (by norm_num : (0 : ℝ) ≤ 2)
  rw [hdef, ← ENNReal.rpow_mul, h12, ENNReal.rpow_one, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow hX] at h2
  have hB' : ENNReal.ofReal B * ∑ v, ENNReal.ofReal (π v)⁻¹ *
      ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val) ≤
        ENNReal.ofReal (X ^ 2) := by
    refine le_trans ?_ h2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [mul_left_comm]
    exact mul_le_mul_right le_add_self _
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val)
      = ENNReal.ofReal B⁻¹ * (ENNReal.ofReal B * ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hB.le), inv_mul_cancel₀ hB.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal B⁻¹ * ENNReal.ofReal (X ^ 2) := mul_le_mul_right hB' _
    _ = ENNReal.ofReal (X ^ 2 / B) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hB.le), div_eq_inv_mul]

/-- **The strong energy controls the gradient density** (Bochner form): from
`𝓔^B_{ρ,m;π}(W) ≤ X` and the time measurability of every component density,
`∫_I ∑_v π_v⁻¹ |∇W_v|²_{ρ,m} ≤ X²/B`. -/
theorem integral_grad_le_of_strongEnergyUpTo_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {ρ B X : ℝ} {π : ι → ℝ} {t₀ t₁ : ℝ} {m K : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)}
    (hB : 0 < B) (hX : 0 ≤ X) (hπ : ∀ v, 0 < π v)
    (hmeas : ∀ v, AEStronglyMeasurable (fun s => gradFactorialNormSqUpTo ρ m (W v s).val)
      (volume.restrict (Set.Icc t₀ t₁)))
    (hE : strongEnergyUpTo ρ B π t₀ t₁ m W ≤ ENNReal.ofReal X) :
    ∫ s in Set.Icc t₀ t₁, ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m (W v s).val ≤
      X ^ 2 / B := by
  have hc : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  have hg : ∀ v s, 0 ≤ gradFactorialNormSqUpTo ρ m (W v s).val := fun v s =>
    gradUpTo_nonneg ρ m _
  have hsm : AEStronglyMeasurable
      (fun s => ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m (W v s).val)
      (volume.restrict (Set.Icc t₀ t₁)) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun v _ => (hmeas v).const_mul (π v)⁻¹
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc t₀ t₁)]
      (fun s => ∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m (W v s).val) :=
    Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun v _ => mul_nonneg (hc v) (hg v s)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hsm]
  refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (sq_nonneg X) hB.le) ?_
  refine le_trans (le_of_eq ?_) (lintegral_grad_le_of_strongEnergyUpTo_le hB hX hE)
  calc ∫⁻ s in Set.Icc t₀ t₁,
        ENNReal.ofReal (∑ v, (π v)⁻¹ * gradFactorialNormSqUpTo ρ m (W v s).val)
      = ∫⁻ s in Set.Icc t₀ t₁, ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val) := by
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (hc v) (hg v s)]
        exact Finset.sum_congr rfl fun v _ => ENNReal.ofReal_mul (hc v)
    _ = ∑ v, ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (π v)⁻¹ *
          ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val) :=
        lintegral_finsetSum' _ fun v _ =>
          ((hmeas v).aemeasurable.ennreal_ofReal).const_mul (ENNReal.ofReal (π v)⁻¹)
    _ = ∑ v, ENNReal.ofReal (π v)⁻¹ *
          ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSqUpTo ρ m (W v s).val) :=
        Finset.sum_congr rfl fun v _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- From `B^{-1/2} (∫⁻_I M)^{1/2} ≤ Y` for an integrable nonnegative `M`: `∫_I M ≤ B Y²`. -/
theorem integral_le_of_coarse_lintegral_bound {I : Set ℝ} {M : ℝ → ℝ} {B Y : ℝ} (hB : 0 < B)
    (hY : 0 ≤ Y) (hM : ∀ s, 0 ≤ M s) (hMi : IntegrableOn M I)
    (h : ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in I, ENNReal.ofReal (M s)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Y) :
    ∫ s in I, M s ≤ B * Y ^ 2 := by
  have hX : 0 ≤ ∫ s in I, M s := integral_nonneg hM
  have hMnn : 0 ≤ᵐ[volume.restrict I] M := Filter.Eventually.of_forall hM
  rw [← ofReal_integral_eq_lintegral_ofReal hMi hMnn,
    ENNReal.ofReal_rpow_of_nonneg hX (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg B)),
    ENNReal.ofReal_le_ofReal_iff hY] at h
  exact sq_le_of_inv_sqrt_mul_sqrt_le hB hX h

/-- **The coarse flux in `L²(I; H)`** from the second conclusion of `cycle_coarse_defect_bound`:
`B^{-1/2} (∫⁻_I ‖F_coarse‖²_{ρ,k;π})^{1/2} ≤ Y` gives `∫_I ‖F_coarse‖²_{ρ,k;π} ≤ B Y²`. -/
theorem integral_mass_le_of_coarse_bound {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {k : ℕ} {ρ B Y : ℝ} {π : ι → ℝ} {I : Set ℝ}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hB : 0 < B) (hY : 0 ≤ Y) (hπ : ∀ v, 0 < π v)
    (hint : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (Fc v s).val)) I)
    (hFc : ENNReal.ofReal (Real.sqrt B)⁻¹ * (∫⁻ s in I, ENNReal.ofReal
        (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
          (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y) :
    ∫ s in I, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π
        (fun v => (Fc v s).val) ≤ B * Y ^ 2 :=
  integral_le_of_coarse_lintegral_bound hB hY
    (fun _ => CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _) hint hFc

end Energy

section Residual

/-- The squared extended norm is the extended real of the squared norm. -/
theorem enorm_sq_eq_ofReal_sq {F : Type*} [NormedAddCommGroup F] (w : F) :
    ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The squared extended norm of a pair in `F²` is the sum of those of its entries. -/
theorem sum_enorm_sq_pair {F : Type*} [NormedAddCommGroup F]
    (z : PiLp 2 (fun _ : Fin 2 => F)) : ∑ k : Fin 2, ‖z k‖ₑ ^ 2 = ‖z‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal_sq z, PiLp.norm_sq_eq_of_L2,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun k _ => enorm_sq_eq_ofReal_sq (z k)

/-- The square of the `L²` norm on the cell of a square integrable field is the lower integral of
its squared norm. -/
theorem ofReal_eLpNorm_sq_cell {F : Type*} [NormedAddCommGroup F] {g : Vec 2 → F}
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) :
    ENNReal.ofReal ((eLpNorm g 2 (volume.restrict AVenhance.unitCube)).toReal ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ 2 := by
  have hne := hg.eLpNorm_ne_top
  have he : eLpNorm g 2 (volume.restrict AVenhance.unitCube) =
      (∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by simp)
      hg.aestronglyMeasurable]
    norm_num
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne, he,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The squared norm of the value component of a torus Sobolev element is the lower integral on
the cell of the squared norm of its value jet. -/
theorem ofReal_value_norm_sq_eq_lintegral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (U : TorusHk K E) :
    ENNReal.ofReal (‖U.val (valueIndex2 K)‖ ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖U.toFunction.jet (valueIndex2 K) x‖ₑ ^ 2 := by
  have hae := AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae U (valueIndex2 K)
  have hm : MemLp (U.toFunction.jet (valueIndex2 K)) 2 (volume.restrict AVenhance.unitCube) :=
    (Lp.memLp (U.val (valueIndex2 K))).ae_eq hae.symm
  have hn : ‖U.val (valueIndex2 K)‖ =
      (eLpNorm (U.toFunction.jet (valueIndex2 K)) 2
        (volume.restrict AVenhance.unitCube)).toReal := by
    rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
  rw [hn]
  exact ofReal_eLpNorm_sq_cell hm

/-- **The value jet is one summand of the factorial norm**: the lower integral on the cell of
the squared value jet is at most `|U|²_{ρ,K}`, for every radius `ρ`. -/
theorem lintegral_value_jet_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (ρ : ℝ) (U : TorusHk K E) :
    ∫⁻ x in AVenhance.unitCube, ‖U.toFunction.jet (valueIndex2 K) x‖ₑ ^ 2 ≤
      ENNReal.ofReal (factorialNormSq ρ U.val) := by
  rw [← ofReal_value_norm_sq_eq_lintegral U]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← AVRegularity.CycleJointProofs.derivativeNormSq_zero_eq_value]
  exact AVRegularity.CoupledEnergy.Variational.derivativeNormSq_zero_le_factorial ρ U.val

/-- The mass-weighted cell `L²` density of the value jets of a family is at most its mass norm
`‖U‖²_{ρ,K;π}`. -/
theorem sum_value_lintegral_le_massNormSq {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (U : ∀ v, TorusHk (K v) (E v)) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ‖(U v).toFunction.jet (valueIndex2 (K v)) x‖ₑ ^ 2 ≤
      ENNReal.ofReal (massNormSq (E := E) (K := K) ρ π (fun v => (U v).val)) := by
  have hmass : massNormSq (E := E) (K := K) ρ π (fun v => (U v).val) =
      ∑ v, (π v)⁻¹ * factorialNormSq ρ (U v).val := rfl
  rw [hmass, ENNReal.ofReal_sum_of_nonneg fun v _ =>
    mul_nonneg (inv_nonneg.2 (hπ v).le) (factorialNormSq_nonneg ρ (U v).val)]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  exact mul_le_mul_right (lintegral_value_jet_sq_le ρ (U v)) _

/-- The mass-weighted cell `L²` density of the value jets of a flux family (values in `𝗁_v ⊗ ℝ²`,
summed over the two directions) is at most its mass norm `‖U‖²_{ρ,K;π}`. -/
theorem sum_flux_lintegral_le_massNormSq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (U : ∀ v, TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ k : Fin 2, ‖((U v).toFunction.jet (valueIndex2 (K v)) x) k‖ₑ ^ 2 ≤
      ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρ π
        (fun v => (U v).val)) := by
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ k : Fin 2, ‖((U v).toFunction.jet (valueIndex2 (K v)) x) k‖ₑ ^ 2
      = ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
          ‖(U v).toFunction.jet (valueIndex2 (K v)) x‖ₑ ^ 2 :=
        Finset.sum_congr rfl fun v _ => by
          rw [lintegral_congr fun x =>
            sum_enorm_sq_pair ((U v).toFunction.jet (valueIndex2 (K v)) x)]
    _ ≤ _ := sum_value_lintegral_le_massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        ρ π hπ U

/-- The two parts of a residual norm from pointwise-in-time bounds by nonnegative integrable
densities: `ν^{-1/2}(∫⁻_I A)^{1/2} + ∫⁻_I Q^{1/2} ≤ (ν⁻¹ ∫_I M_R)^{1/2} + ∫_I M_q^{1/2}` when
`A ≤ M_R` and `Q ≤ M_q` at every time. -/
theorem residual_split_le {ν : ℝ} {I : Set ℝ} {A Q : ℝ → ℝ≥0∞} {MR Mq : ℝ → ℝ}
    (hA : ∀ t, A t ≤ ENNReal.ofReal (MR t)) (hQ : ∀ t, Q t ≤ ENNReal.ofReal (Mq t))
    (hMR : ∀ t, 0 ≤ MR t) (hMq : ∀ t, 0 ≤ Mq t) (hRi : IntegrableOn MR I)
    (hqi : IntegrableOn (fun t => Real.sqrt (Mq t)) I) :
    ENNReal.ofReal (Real.sqrt ν)⁻¹ * (∫⁻ t in I, A t) ^ (1 / 2 : ℝ)
        + ∫⁻ t in I, Q t ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (ν⁻¹ * ∫ t in I, MR t))
        + ENNReal.ofReal (∫ t in I, Real.sqrt (Mq t)) := by
  have hX : 0 ≤ ∫ t in I, MR t := integral_nonneg hMR
  have hRnn : 0 ≤ᵐ[volume.restrict I] MR := Filter.Eventually.of_forall hMR
  have hsq0 : ∀ t, 0 ≤ Real.sqrt (Mq t) := fun t => Real.sqrt_nonneg (Mq t)
  have hqnn : 0 ≤ᵐ[volume.restrict I] (fun t => Real.sqrt (Mq t)) :=
    Filter.Eventually.of_forall hsq0
  have h1 : ∫⁻ t in I, A t ≤ ENNReal.ofReal (∫ t in I, MR t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hRi hRnn]
    exact lintegral_mono hA
  refine add_le_add ?_ ?_
  · calc ENNReal.ofReal (Real.sqrt ν)⁻¹ * (∫⁻ t in I, A t) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Real.sqrt ν)⁻¹ * ENNReal.ofReal (∫ t in I, MR t) ^ (1 / 2 : ℝ) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow h1 (by norm_num)) _
      _ = ENNReal.ofReal (Real.sqrt (ν⁻¹ * ∫ t in I, MR t)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hX (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg ν)),
            Real.sqrt_mul' _ hX, Real.sqrt_inv]
  · rw [ofReal_integral_eq_lintegral_ofReal hqi hqnn]
    refine lintegral_mono fun t => ?_
    calc Q t ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Mq t) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hQ t) (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (Mq t)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (hMq t) (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ← Real.sqrt_eq_rpow]

/-- **The residual norm from the mass norms of the residual families**. For flux and scalar
torus Sobolev families `R_v(t) ∈ H^{K_v}(𝗁_v ⊗ ℝ²)`, `q_v(t) ∈ H^{K_v}(𝗁_v)` whose mass norms
at a radius `ρ` are integrable in time (`‖R‖²` and `‖q‖`), the residual norm of their value jets
is at most `(ν⁻¹ ∫_I ‖R‖²_{ρ,K;π})^{1/2} + ∫_I ‖q‖_{ρ,K;π}`. -/
theorem residualNorm_le_of_mass {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {K : ι → ℕ} (ν ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (I : Set ℝ) (R : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk (K v) (h v))
    (hR : IntegrableOn (fun s => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K) ρ π (fun v => (R v s).val)) I)
    (hq : IntegrableOn (fun s => Real.sqrt (massNormSq (E := h) (K := K) ρ π
      (fun v => (q v s).val))) I) :
    residualNorm ν π I (fun t x k v => ((R v t).toFunction.jet (valueIndex2 (K v)) x) k)
        (fun t x v => (q v t).toFunction.jet (valueIndex2 (K v)) x) ≤
      ENNReal.ofReal (Real.sqrt (ν⁻¹ * ∫ s in I, massNormSq
          (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρ π (fun v => (R v s).val)))
        + ENNReal.ofReal (∫ s in I, Real.sqrt (massNormSq (E := h) (K := K) ρ π
          (fun v => (q v s).val))) := by
  have hdef : residualNorm ν π I
        (fun t x k v => ((R v t).toFunction.jet (valueIndex2 (K v)) x) k)
        (fun t x v => (q v t).toFunction.jet (valueIndex2 (K v)) x) =
      ENNReal.ofReal (Real.sqrt ν)⁻¹ *
          (∫⁻ t in I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
            ∑ k : Fin 2, ‖((R v t).toFunction.jet (valueIndex2 (K v)) x) k‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        + ∫⁻ t in I, (∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
            ‖(q v t).toFunction.jet (valueIndex2 (K v)) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := rfl
  rw [hdef]
  refine residual_split_le ?_ ?_ ?_ ?_ hR hq
  · exact fun t => sum_flux_lintegral_le_massNormSq ρ π hπ (fun v => R v t)
  · exact fun t => sum_value_lintegral_le_massNormSq (E := h) ρ π hπ (fun v => q v t)
  · exact fun t => CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _
  · exact fun t => CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _

end Residual

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Tested identities of integral type.** Pointwise identities of integral type in time
integrate in space (Fubini): if `s ↦ G(s, y)` is of integral type with density `g(s, y)` at every
point `y` and `g` is integrable in space-time, then `s ↦ ∫ G(s, y) dy` is of integral type with
density `s ↦ ∫ g(s, y) dy`. Together with the product rule for `C¹` test functions this turns the
pointwise (time-integrated) lift identity into the tested identity of the weak formulation
(`CoupledWeakIdentity`). -/

/-- **Integration in space.** -/
theorem IsPrimOn.integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {a b : ℝ} (hab : a ≤ b) {G g : ℝ → α → ℝ}
    (hG : ∀ y, IsPrimOn a b (fun s => G s y) (fun s => g s y))
    (hg : Integrable (Function.uncurry g) ((volume.restrict (Ioc a b)).prod μ))
    (hGa : Integrable (G a) μ) :
    IsPrimOn a b (fun s => ∫ y, G s y ∂μ) (fun s => ∫ y, g s y ∂μ) := by
  have hint : IntervalIntegrable (fun s => ∫ y, g s y ∂μ) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hg.integral_prod_left
  refine ⟨hint, fun s hs => ?_⟩
  have hsub : (volume.restrict (uIoc a s)).prod μ ≤ (volume.restrict (Ioc a b)).prod μ := by
    refine Measure.prod_mono ?_ le_rfl
    rw [uIoc_of_le hs.1]
    exact Measure.restrict_mono (Ioc_subset_Ioc_right hs.2) le_rfl
  have hgs : Integrable (Function.uncurry g) ((volume.restrict (uIoc a s)).prod μ) :=
    hg.mono_measure hsub
  have hG' : (fun y => G s y) = fun y => G a y + ∫ σ in a..s, g σ y := by
    funext y
    exact (hG y).2 s hs
  have hprim : Integrable (fun y => ∫ σ in a..s, g σ y) μ := by
    have h := hgs.integral_prod_right
    rw [uIoc_of_le hs.1] at h
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [intervalIntegral.integral_of_le hs.1]
    rfl
  beta_reduce
  rw [hG', integral_add hGa hprim, ← intervalIntegral_integral_swap hgs]

/-- **Pairing with a `C¹` test.** If `G` is of integral type with density `g` and `φ` has the
continuous derivative `φ'` on `[a, b]`, then `s ↦ ⟪G s, φ s⟫` is of integral type with density
`⟪g s, φ s⟫ + ⟪G s, φ' s⟫`. -/
theorem IsPrimOn.inner_C1 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {a b : ℝ} (hab : a ≤ b) {G g φ φ' : ℝ → F}
    (hG : IsPrimOn a b G g) (hφ : ∀ s ∈ Icc a b, HasDerivAt φ (φ' s) s)
    (hφ' : ContinuousOn φ' (Icc a b)) :
    IsPrimOn a b (fun s => inner ℝ (G s) (φ s))
      (fun s => inner ℝ (g s) (φ s) + inner ℝ (G s) (φ' s)) := by
  let e := stdOrthonormalBasis ℝ F
  have hP : IsPrimOn a b φ φ' := isPrimOn_of_hasDerivAt hab hφ hφ'
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ F))), IsPrimOn a b
      (fun s => inner ℝ (e j) (G s) * inner ℝ (e j) (φ s))
      (fun s => inner ℝ (e j) (g s) * inner ℝ (e j) (φ s) +
        inner ℝ (e j) (G s) * inner ℝ (e j) (φ' s)) := fun j _ =>
    IsPrimOn.mul hab (by simpa using hG.map_clm (innerSL ℝ (e j)))
      (by simpa using hP.map_clm (innerSL ℝ (e j)))
  refine (IsPrimOn.sum Finset.univ hterm).congr hab (fun s _ => ?_) (fun s _ => ?_)
  · simp_rw [real_inner_comm (G s) (e _)]
    exact e.sum_inner_mul_inner (G s) (φ s)
  · simp_rw [real_inner_comm (g s) (e _), real_inner_comm (G s) (e _)]
    rw [Finset.sum_add_distrib, e.sum_inner_mul_inner (g s) (φ s),
      e.sum_inner_mul_inner (G s) (φ' s)]

end AVRegularity.CycleComparison.Reconstruction
end
end

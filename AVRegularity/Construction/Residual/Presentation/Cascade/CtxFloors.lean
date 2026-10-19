-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Meas.Pairing
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

section
section
/-! **The algebra of the dominations** (cascade side of the bill residual).

The five dominations of the window's bill by `C₁` times the cascade bill
`E^{-qγ}·𝔱 + e^N(1 + R) + G` (`succReconBill`), in terms of abstract nonnegative numbers.

For `𝔱 = 0` only the second term of the bill remains. -/

@[expose] public section

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The five dominations of the cascade bill, for abstract nonnegative terms: `Eq = E^{-qγ} ≥ 1`
dominates the contrast `s` up to `C₁`, `e₀ ≤ e ≤ ` and `e₀, Rf ≤ 1`. -/
theorem dominations (Eq P e e₀ R Rf s G C₁ : ℝ) (N : ℕ) (hEq : 1 ≤ Eq) (hP : 0 ≤ P)
    (he₀ : 0 ≤ e₀) (he₀e : e₀ ≤ e) (hR : 0 ≤ R) (hRf0 : 0 ≤ Rf) (hRf : Rf ≤ R) (hG : 0 ≤ G)
    (hC : 1 ≤ C₁) (hs : s ≤ C₁ * Eq) (he₀1 : e₀ ≤ 1) (hRf1 : Rf ≤ 1) :
    e₀ ^ N ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) ∧
    s * P ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) ∧
    e₀ ^ 2 * P ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) ∧
    e₀ ^ N * Rf ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) ∧
    e₀ ^ 2 * Rf * P ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) := by
  have he : 0 ≤ e := he₀.trans he₀e
  have hEq0 : 0 ≤ Eq := by linarith
  have hC0 : 0 ≤ C₁ := by linarith
  have hA : 0 ≤ Eq * P := mul_nonneg hEq0 hP
  have hB : 0 ≤ e ^ N * (1 + R) := mul_nonneg (pow_nonneg he N) (by linarith)
  have hbill : 0 ≤ Eq * P + e ^ N * (1 + R) + G := by linarith
  have hCb : Eq * P + e ^ N * (1 + R) + G ≤ C₁ * (Eq * P + e ^ N * (1 + R) + G) := by
    nlinarith
  have hpN : e₀ ^ N ≤ e ^ N := pow_le_pow_left₀ he₀ he₀e N
  have hRfR : e₀ ^ N * Rf ≤ e ^ N * R :=
    mul_le_mul hpN hRf hRf0 (pow_nonneg he N)
  have he₀2 : e₀ ^ 2 ≤ 1 := pow_le_one₀ he₀ he₀1
  have hP1 : P ≤ Eq * P := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (pow_nonneg he N) hR]
  · have : s * P ≤ C₁ * Eq * P := by nlinarith
    nlinarith
  · have : e₀ ^ 2 * P ≤ P := by nlinarith [sq_nonneg e₀]
    nlinarith
  · nlinarith [mul_nonneg (pow_nonneg he N) hR]
  · have h1 : e₀ ^ 2 * Rf ≤ 1 := by
      have := mul_le_mul he₀2 hRf1 hRf0 zero_le_one
      linarith
    have h2 : e₀ ^ 2 * Rf * P ≤ P := by
      have := mul_le_mul_of_nonneg_right h1 hP
      linarith
    nlinarith

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **K4.1, step 2: strong measurability in time from the order-0 joint measurability.**

A `TorusHk K`-valued trajectory `W` whose value is, at every time of a window, a.e. a function
`f t` with `(t, x) ↦ f t x` measurable on the window, is a.e. strongly measurable on the window.
Proof: `aestronglyMeasurable_of_weak` (the pairings with smooth periodic tests suffice), and the
pairing is `t ↦ ∫_{cell} ⟨f t x, ψ x⟩ dx`, measurable by Fubini. No derivative of `f` is used. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem aesm_of_value {K : ℕ} (a b : ℝ) (W : ℝ → TorusHk K F) (f : ℝ → Vec 2 → F)
    (hf : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc a b} => f z.1.1 z.1.2))
    (hval : ∀ t ∈ Set.Icc a b, (W t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict
      AVenhance.unitCube] f t) :
    AEStronglyMeasurable W (volume.restrict (Set.Icc a b)) := by
  classical
  apply CycleComparison.Coarse.aestronglyMeasurable_of_weak
  intro ψ hψ _
  let f0 : ℝ × Vec 2 → F := fun p => if p.1 ∈ Set.Icc a b then f p.1 p.2 else 0
  have hf0 : Measurable f0 :=
    Measurable.dite (s := {p : ℝ × Vec 2 | p.1 ∈ Set.Icc a b}) (f := fun z => f z.1.1 z.1.2)
      (g := fun _ => (0 : F)) hf measurable_const (measurableSet_Icc.preimage measurable_fst)
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hg : StronglyMeasurable (fun p : ℝ × Vec 2 => inner ℝ (f0 p) (ψ p.2)) :=
    (hf0.inner (hψm.comp measurable_snd)).stronglyMeasurable
  have hint : StronglyMeasurable (fun t => ∫ x in AVenhance.unitCube,
      inner ℝ (f0 (t, x)) (ψ x)) :=
    hg.integral_prod_right' (ν := volume.restrict AVenhance.unitCube)
  refine hint.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  show (∫ x in AVenhance.unitCube, inner ℝ (f0 (t, x)) (ψ x)) =
    cellInner (CycleComparison.Coarse.tval (W t)) ψ
  unfold cellInner
  apply integral_congr_ae
  filter_upwards [hval t ht] with x hx
  have h0 : f0 (t, x) = f t x := by simp only [f0, ht, ↓reduceIte]
  rw [h0]
  exact congrArg (fun y => inner ℝ y (ψ x)) hx.symm

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **Stability of the kernel weak solution under a null set of times in the gradient
carrier.**

`kernelWeakSolution_congr_w`: if `(u, w, y)` solves the kernel system on `[t₀, t₁]` and
`w'` agrees with `w` for almost every time of the window, then `(u, w', y)` is a solution too,
provided the drift `v(s)` is continuous and bounded on the cell at each time of the window (the
only place where the exceptional times of `w'` could spoil the weak identity is the integrability
of `v · ∇w' φ` at those times).

* `coupledWeakIdentity_congr_du`: the coupled weak identity is stable under a change of the
  gradient `du` on a null set of times, given the integrability of the modified integrand at every
  time of `(t₀, t]`.

For `w' = w` everything is the hypothesis, and for `t₀ = t₁` the weak identity is the trivial
integral over `Ioc t₀ t₀ = ∅`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The coupled weak identity is stable under a change of the gradient `du` on a null set of
times, given integrability of the modified integrand at every time. -/
theorem coupledWeakIdentity_congr_du {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {μ : Measure (Vec 2)} {ν a t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du du' : ℝ → Fin 2 → Vec 2 → H}
    {Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H}
    (hI : CoupledWeakIdentity μ ν a t v u₀ f φ dφ du Q F g)
    (hdu : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)), du' s = du s)
    (hint : ∀ s ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ k : Fin 2, v s x k * inner ℝ (du' s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du' s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (Q s x k + F s x k) (dφ k x) + inner ℝ (g s x) (φ x)) μ) :
    CoupledWeakIdentity μ ν a t v u₀ f φ dφ du' Q F g := by
  dsimp only [CoupledWeakIdentity] at hI ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hcongr : (fun s => ∫ x, (-(∑ k : Fin 2, v s x k * inner ℝ (du' s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du' s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (Q s x k + F s x k) (dφ k x) + inner ℝ (g s x) (φ x)) ∂μ)
      =ᵐ[volume.restrict (Set.Ioc a t)] fun s => ∫ x, (-(∑ k : Fin 2, v s x k *
        inner ℝ (du s k x) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
        - ∑ k : Fin 2, inner ℝ (Q s x k + F s x k) (dφ k x) + inner ℝ (g s x) (φ x)) ∂μ := by
    filter_upwards [hdu] with s hs
    rw [hs]
  refine ⟨h1, h2, hint, h4.congr_fun_ae hcongr.symm, ?_⟩
  rw [h5]
  exact (integral_congr_ae hcongr).symm


/-- The part of the integrand that sees the gradient `J`: integrable as soon as the pairings of
`J` with the test and its gradient are, and the drift is continuous and bounded. -/
theorem gradTerm_integrable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} {ν : ℝ} {w : Vec 2 → Vec 2} {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H}
    {J : Fin 2 → Vec 2 → H} (hwc : Continuous w) (hwb : ∃ M, ∀ x, ‖w x‖ ≤ M)
    (hJφ : ∀ k, Integrable (fun x => inner ℝ (J k x) (φ x)) μ)
    (hJd : ∀ k, Integrable (fun x => inner ℝ (J k x) (dφ k x)) μ) :
    Integrable (fun x => -(∑ k : Fin 2, w x k * inner ℝ (J k x) (φ x))
      - ν * ∑ k : Fin 2, inner ℝ (J k x) (dφ k x)) μ := by
  obtain ⟨M, hM⟩ := hwb
  have h1 : Integrable (fun x => ∑ k : Fin 2, w x k * inner ℝ (J k x) (φ x)) μ := by
    refine integrable_finsetSum _ fun k _ => ?_
    refine (hJφ k).bdd_mul (c := M) ?_ ?_
    · exact ((continuous_apply k).comp hwc).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have := norm_le_pi_norm (w x) k
      rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact this.trans (hM x)
  have h2 : Integrable (fun x => ∑ k : Fin 2, inner ℝ (J k x) (dφ k x)) μ :=
    integrable_finsetSum _ fun k _ => hJd k
  exact h1.neg.sub (h2.const_mul ν)


/-- Two jets of torus Sobolev elements pair to an integrable function on the cell. -/
theorem torusJet_inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K K' : ℕ} (W : TorusHk K E)
    (W' : TorusHk K' E) (a : JetIndex2 K) (b : JetIndex2 K') :
    Integrable (fun x => inner ℝ (W.toFunction.jet a x) (W'.toFunction.jet b x))
      (volume.restrict AVenhance.unitCube) := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (W.val a) (W'.val b)).congr ?_
  filter_upwards [periodicJetRepresentative_ae W.val a, periodicJetRepresentative_ae W'.val b]
    with x h1 h2
  exact congrArg₂ (fun p q => inner ℝ p q) h1.symm h2.symm

section Solution

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- **Route A, the stability lemma.** A kernel weak solution stays a kernel weak solution when its
gradient carrier `w` is changed on a null set of times of the window, if the drift is continuous
and bounded on the cell at each time of the window. -/
theorem kernelWeakSolution_congr_w {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {k D : ℕ}
    {B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α}
    {S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    {f : ∀ i, TorusHk k (h i)} {F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → TorusHk k (h i)} {u : ∀ i, ℝ → TorusHk k (h i)}
    {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hsol : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y)
    (w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hww : ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), w' i s = w i s)
    (hvc : ∀ s ∈ Set.Icc t₀ t₁, Continuous (v s))
    (hvb : ∀ s ∈ Set.Icc t₀ t₁, ∃ M, ∀ x, ‖v s x‖ ≤ M) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w' y := by
  classical
  obtain ⟨hu, hw, htr, hinit, hyM, hyV, hweak⟩ := hsol
  refine ⟨hu, fun i => (hw i).ae_eq (show w' i =ᵐ[volume.restrict (Set.Icc t₀ t₁)] w i from hww i).symm, fun i => ?_, hinit, hyM, fun i j α => ?_, ?_⟩
  · filter_upwards [htr i, hww i] with s hs hs'
    rw [hs']
    exact hs
  · filter_upwards [hyV i j α, hww j] with s hs hs'
    rw [hs']
    exact hs
  · intro i t ht φ
    have hI := hweak i t ht φ
    have hsub : Set.Ioc t₀ t ⊆ Set.Icc t₀ t₁ := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
    refine coupledWeakIdentity_congr_du hI ?_ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hww i)] with s hs
      funext m
      rw [hs]
    · intro s hs
      have hs' : s ∈ Set.Icc t₀ t₁ := hsub hs
      have hR := hI.2.2.1 s hs
      have hG : ∀ W : TorusHk (k + 1) (h i), Integrable (fun x =>
          -(∑ q : Fin 2, v s x q * inner ℝ (W.toFunction.jet
              ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩ x)
              (φ.toFunction.jet (valueIndex2 1) x))
            - ν * ∑ q : Fin 2, inner ℝ (W.toFunction.jet
              ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩ x)
              (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩ x))
          (volume.restrict AVenhance.unitCube) := fun W =>
        gradTerm_integrable (hvc s hs') (hvb s hs')
          (fun q => torusJet_inner_integrable W φ _ _)
          (fun q => torusJet_inner_integrable W φ _ _)
      refine ((hR.sub (hG (w i s))).add (hG (w' i s))).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring

end Solution

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The scales of a level of a band chain** (cascade side of the bill residual).

At a level `m₀ ≤ m < M` of a band chain, above the separation threshold `Λ₀`, with `ν = κ_m`,
`B = κ_{m-1}`, `R = √(Bτ_m'')`, `ℓ = ε_m/√ν`, `E = ε_{m-1}`:
`0 < ν`, `0 < B`, `ε_m ≤ R ≤ E`, `√(B/ν) ≤ C₁E^{-qγ}`, `d_*/R ≤ 1`, and, for every window length
`T ≤ T₀`, `√T/ℓ·(ε_m/R)^{A_cl} ≤ 1` (the cleanup order `A_cl` of the schedule,
`(qγ + 3δ)A_cl ≥ 2 - β + 8δ`). The constants `Λ₀, C₁, m₀` are chosen from `(α, s, q, ζ)`,
`A_cl` and `T₀` only.

The case `A_cl = 0` is excluded by the schedule inequality (`2 - β + 8δ > 0`). -/

@[expose] public section

open AVenhance AVRegularity

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The lower bound of `τ''_m` by a power of `E = ε_{m-1}`: `τ'' ≥ E^{2-β+2δ}/2^{26}`. -/
theorem tauPP_lower {α q : ℝ} {Λ m : ℕ} (hE0 : 0 < ocEpsilon q Λ (m - 1))
    (hE1 : ocEpsilon q Λ (m - 1) ≤ 1) (hx : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q) :
    ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) / 2 ^ 26 ≤ ocTauPP α q Λ m := by
  set E := ocEpsilon q Λ (m - 1) with hE
  set x := 2 - (1 + α) + 2 * ocDelta α q with hxdef
  have hy1 : 1 ≤ E ^ (-x) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE0 hE1 (by linarith)
  have hypos : 0 < E ^ (-x) := by linarith
  have hceil : ((⌈E ^ (-x)⌉₊ : ℕ) : ℝ) ≤ 2 * E ^ (-x) := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ E ^ (-x))
    linarith
  have hcpos : (0 : ℝ) < ((⌈E ^ (-x)⌉₊ : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.ceil_pos.2 hypos)
  have hinv : E ^ x = (E ^ (-x))⁻¹ := by rw [Real.rpow_neg hE0.le]; simp
  have hdef : ocTauPP α q Λ m = (2 : ℝ) ^ (-25 : ℤ) / ((⌈E ^ (-x)⌉₊ : ℕ) : ℝ) := rfl
  rw [hdef, hinv, zpow_neg, zpow_ofNat]
  rw [div_le_div_iff₀ (by norm_num) hcpos]
  have : (2 : ℝ) ^ 25 ≠ 0 := by positivity
  have h26 : (2 : ℝ) ^ 26 = 2 * 2 ^ 25 := by ring
  rw [h26]
  have key : (((⌈E ^ (-x)⌉₊ : ℕ) : ℝ)) * (E ^ (-x))⁻¹ ≤ 2 := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hypos]
    linarith
  field_simp
  nlinarith [key]

/-- The cell length is bounded below algebraically: `ℓ⁻¹ ≤ K E^{-(2-β+8δ)/2}` at a level `m < M`
of a band chain, with `τ''/ℓ² ≤ C E^{-6δ}` (the diffusivity ledger). -/
theorem ell_inv {α q : ℝ} {Λ m : ℕ} {C ν : ℝ} (hC : 1 ≤ C) (hν : 0 < ν)
    (hE0 : 0 < ocEpsilon q Λ (m - 1)) (hE1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hx : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q) (he : 0 < ocEpsilon q Λ m)
    (hasy : ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 ≤
      C * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q))) :
    (ocEll q Λ m ν)⁻¹ ≤ Real.sqrt (2 ^ 26 * C) *
      ocEpsilon q Λ (m - 1) ^ (-((2 - (1 + α) + 8 * ocDelta α q) / 2)) := by
  set E := ocEpsilon q Λ (m - 1) with hE
  set l := ocEll q Λ m ν with hl
  have hl0 : 0 < l := div_pos he (Real.sqrt_pos.2 hν)
  have hl2 : 0 < l ^ 2 := pow_pos hl0 2
  have hτ := tauPP_lower (α := α) (Λ := Λ) (m := m) hE0 hE1 hx
  set p := 2 - (1 + α) + 8 * ocDelta α q with hp
  have h1 : ocTauPP α q Λ m ≤ C * E ^ (-(6 * ocDelta α q)) * l ^ 2 :=
    (div_le_iff₀ hl2).1 hasy
  have h2 : E ^ (2 - (1 + α) + 2 * ocDelta α q) / 2 ^ 26 ≤ C * E ^ (-(6 * ocDelta α q)) * l ^ 2 :=
    hτ.trans h1
  have hmul : E ^ (2 - (1 + α) + 2 * ocDelta α q) * E ^ (6 * ocDelta α q) = E ^ p := by
    rw [← Real.rpow_add hE0]; congr 1; rw [hp]; ring
  have hcancel : E ^ (-(6 * ocDelta α q)) * E ^ (6 * ocDelta α q) = 1 := by
    rw [← Real.rpow_add hE0]; simp
  have h3 : E ^ p / 2 ^ 26 ≤ C * l ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hE0.le (6 * ocDelta α q))
    calc E ^ p / 2 ^ 26 = E ^ (2 - (1 + α) + 2 * ocDelta α q) / 2 ^ 26 *
          E ^ (6 * ocDelta α q) := by rw [← hmul]; ring
      _ ≤ C * E ^ (-(6 * ocDelta α q)) * l ^ 2 * E ^ (6 * ocDelta α q) := this
      _ = C * l ^ 2 * (E ^ (-(6 * ocDelta α q)) * E ^ (6 * ocDelta α q)) := by ring
      _ = C * l ^ 2 := by rw [hcancel, mul_one]
  have hEp : 0 < E ^ p := Real.rpow_pos_of_pos hE0 _
  have h4 : (l⁻¹) ^ 2 ≤ 2 ^ 26 * C * E ^ (-p) := by
    have hEn : E ^ (-p) = (E ^ p)⁻¹ := Real.rpow_neg hE0.le p
    rw [inv_pow, hEn, ← div_eq_mul_inv, inv_eq_one_div, div_le_iff₀ hl2]
    have : E ^ p ≤ 2 ^ 26 * C * l ^ 2 := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 26)).1 h3
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hEp]
    linarith
  have hK : 0 ≤ Real.sqrt (2 ^ 26 * C) := Real.sqrt_nonneg _
  have hpow : (E ^ (-(p / 2))) ^ 2 = E ^ (-p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE0.le]; congr 1; push_cast; ring
  have hsq : (Real.sqrt (2 ^ 26 * C) * E ^ (-(p / 2))) ^ 2 = 2 ^ 26 * C * E ^ (-p) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hpow]
  have hnn : 0 ≤ Real.sqrt (2 ^ 26 * C) * E ^ (-(p / 2)) :=
    mul_nonneg hK (Real.rpow_nonneg hE0.le _)
  have := (sq_le_sq₀ (inv_nonneg.2 hl0.le) hnn).1 (by rw [hsq]; exact h4)
  simpa [hp] using this

/-- **The scales of a level** (see the module docstring). -/
theorem levels {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (Acl : ℕ) (T₀ : ℝ),
      2 - (1 + α) + 8 * ocDelta α q ≤ (q * ocGamma α q + 3 * ocDelta α q) * Acl →
      ∃ (C₁ : ℝ) (m₀ : ℕ), 1 ≤ C₁ ∧ 2 ≤ m₀ ∧
      ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m < M →
        0 < κ m ∧ 0 < κ (m - 1) ∧
        ocEpsilon q Λ m ≤ Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) ∧
        Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1) ∧
        Real.sqrt (κ (m - 1) / κ m) ≤ C₁ * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
        ocDStar q Λ m (κ m) (κ (m - 1)) / Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) ≤ 1 ∧
        ∀ T : ℝ, 0 ≤ T → T ≤ T₀ →
          Real.sqrt T / ocEll q Λ m (κ m) *
            (ocEpsilon q Λ m / Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)) ^ Acl ≤ 1 := by
  obtain ⟨C₁, hC₁, Λ₁, hΛ₁, hsl⟩ := AVRegularity.CycleComparison.Assembly.scale_laws α s hα0 hα1
    hs0 hs1 q hq ζ hζ
  obtain ⟨CL, hCL, Λ₂, hΛ₂, hled⟩ := AVRegularity.CycleReference.bandChain_uniform_ledger hα0 hα1
    hs0 hs1 hq hζ
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hγ : 0 < ocGamma α q := hexp.1
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hq1 : 1 < q := hq.1
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have ha : 0 < q * ocGamma α q + 3 * ocDelta α q := by positivity
  have hp : 0 < 2 - (1 + α) + 8 * ocDelta α q := by linarith
  have hx : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q := by linarith
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun Λ hΛ Acl T₀ hAcl => ?_⟩
  have hΛ1 : Λ₁ ≤ Λ := le_trans (le_max_left _ _) hΛ
  have hΛ2 : Λ₂ ≤ Λ := le_trans (le_max_right _ _) hΛ
  have h128 : 128 ≤ Λ := le_trans hΛ₁ hΛ1
  have hΛone : 1 ≤ Λ := by omega
  have hC0 : 0 < C₁ := by linarith
  -- the three smallness thresholds
  obtain ⟨η₁, hη₁, hs₁⟩ := Applications.exists_small_pow (K := C₁) (e := 3 * ocDelta α q)
    (target := 1) hC0.le (by positivity) one_pos
  obtain ⟨η₂, hη₂, hs₂⟩ := Applications.exists_small_pow (K := C₁)
    (e := q * ocGamma α q + 3 * ocDelta α q) (target := 1) hC0.le ha one_pos
  set K : ℝ := Real.sqrt T₀ * Real.sqrt (2 ^ 26 * CL) * C₁ ^ Acl with hKdef
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨η₃, hη₃, hs₃⟩ := Applications.exists_small_pow (K := K)
    (e := (2 - (1 + α) + 8 * ocDelta α q) / 2) (target := 1) hK0 (by positivity) one_pos
  obtain ⟨N, hN⟩ := Applications.eps_eventually_le hq1 h128
    (lt_min hη₁ (lt_min hη₂ hη₃))
  refine ⟨C₁, N + 2, hC₁, by omega, fun M κ hband m hm hmM => ?_⟩
  have hm2 : 2 ≤ m := by omega
  have hlaws := hsl Λ hΛ1 M κ hband m hm2 hmM.le (κ m) (κ (m - 1)) rfl rfl
  have hE0 : 0 < ocEpsilon q Λ (m - 1) := Applications.eps_pos hq1 h128
  have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 := Applications.eps_le_one hq1 h128
  have hEsmall := hN (m - 1) (by omega)
  have hEη₁ : ocEpsilon q Λ (m - 1) ≤ η₁ := hEsmall.trans (min_le_left _ _)
  have hEη₂ : ocEpsilon q Λ (m - 1) ≤ η₂ :=
    hEsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEη₃ : ocEpsilon q Λ (m - 1) ≤ η₃ :=
    hEsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hκB : 0 < κ (m - 1) :=
    AVRegularity.CycleReference.bandChain_pos hΛone hζ hband (by omega)
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛone
  have hR : 0 < Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) := Real.sqrt_pos.2 (mul_pos hκB hτ)
  have he : 0 < ocEpsilon q Λ m := Applications.eps_pos hq1 h128
  have hr1 : ocEpsilon q Λ m / Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) ≤ 1 :=
    hlaws.eR_le.trans (by simpa using hs₂ _ hE0.le hEη₂)
  have hr0 : 0 ≤ ocEpsilon q Λ m / Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) :=
    (div_pos he hR).le
  refine ⟨hlaws.ν_pos, hκB, ?_, hlaws.radius_le, hlaws.contrast_le, ?_, ?_⟩
  · exact (div_le_one hR).1 hr1
  · exact hlaws.εc_le.trans (by simpa using hs₁ _ hE0.le hEη₁)
  · intro T hT0 hT
    have hlt := ((hled Λ hΛ2 M (by omega) κ hband).2 m hm2 hmM.le (κ m) (κ (m - 1)) rfl rfl)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hblk, -, -⟩ := hlt
    obtain ⟨-, -, -, -, hasy, -⟩ := hblk hmM
    have hell := ell_inv (α := α) (q := q) (Λ := Λ) (m := m) hCL hlaws.ν_pos hE0 hE1 hx he
      hasy.2
    set E := ocEpsilon q Λ (m - 1) with hE
    set p := 2 - (1 + α) + 8 * ocDelta α q with hpdef
    set r := ocEpsilon q Λ m / Real.sqrt (κ (m - 1) * ocTauPP α q Λ m) with hrdef
    have hrC : r ≤ C₁ * E ^ (q * ocGamma α q + 3 * ocDelta α q) := hlaws.eR_le
    have hrpow : r ^ Acl ≤ C₁ ^ Acl * E ^ p := by
      have h1 : r ^ Acl ≤ (C₁ * E ^ (q * ocGamma α q + 3 * ocDelta α q)) ^ Acl :=
        pow_le_pow_left₀ hr0 hrC Acl
      have h2 : (E ^ (q * ocGamma α q + 3 * ocDelta α q)) ^ Acl =
          E ^ ((q * ocGamma α q + 3 * ocDelta α q) * Acl) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0.le]
      have h3 : E ^ ((q * ocGamma α q + 3 * ocDelta α q) * Acl) ≤ E ^ p :=
        Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hAcl
      calc r ^ Acl ≤ (C₁ * E ^ (q * ocGamma α q + 3 * ocDelta α q)) ^ Acl := h1
        _ = C₁ ^ Acl * E ^ ((q * ocGamma α q + 3 * ocDelta α q) * Acl) := by
          rw [mul_pow, h2]
        _ ≤ C₁ ^ Acl * E ^ p := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hell0 : 0 < ocEll q Λ m (κ m) :=
      div_pos he (Real.sqrt_pos.2 hlaws.ν_pos)
    have hTs : Real.sqrt T ≤ Real.sqrt T₀ := Real.sqrt_le_sqrt hT
    have hz1 : Real.sqrt T / ocEll q Λ m (κ m) ≤
        Real.sqrt T₀ * (Real.sqrt (2 ^ 26 * CL) * E ^ (-(p / 2))) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hTs hell (inv_nonneg.2 hell0.le) (Real.sqrt_nonneg _)
    have hz0 : 0 ≤ Real.sqrt T / ocEll q Λ m (κ m) :=
      div_nonneg (Real.sqrt_nonneg _) hell0.le
    have hEpow : E ^ (-(p / 2)) * E ^ p = E ^ (p / 2) := by
      rw [← Real.rpow_add hE0]; congr 1; ring
    calc Real.sqrt T / ocEll q Λ m (κ m) * r ^ Acl
        ≤ Real.sqrt T₀ * (Real.sqrt (2 ^ 26 * CL) * E ^ (-(p / 2))) * (C₁ ^ Acl * E ^ p) :=
          mul_le_mul hz1 hrpow (pow_nonneg hr0 _) (by positivity)
      _ = K * E ^ (p / 2) := by
          rw [hKdef, ← hEpow]; ring
      _ ≤ 1 := hs₃ _ hE0.le hEη₃

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The kernels of a stage do not see the readout exponent `η₀` of the tag parameters** (at
every context).

`FrontierAnalyticProductionDataStatement` (`Construction/Preservation/Frontier/UniformAssembly.lean`)
states the edge inputs `yom` through `G'.sysS (succProvParams D Cw k_I.c_r σ₀ (succEta0 α q s) N p)`
inside `∀ᵐ s ∂ …`, where the time variable `s` shadows the exponent `s` of the statement. The
kernel of an identity (`GenStage.kernelOf`) is read from the `kernel` field of its tags, and that
field is the same for tag parameters with the same fresh widths `r_b`, whatever `η₀` (and `C`, `Rb`)
are: only the `witness` field sees `η₀`. Hence the two readings of the hypothesis agree.

* `tags_agree`: width and kernel of the tags of a provenance agree for parameters with the
  same `r_b`;
* `kernelOf_eq'`, `sysS_eq`: the kernel and the system operator of a stage agree for such
  parameters;
* `sysS_succProvParams_eta`: the case of `succProvParams` with two values of `η₀`.

For a seed identity the kernel is `seed k` for every parameter. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The relation `width` and `kernel` agree. -/
def TagsAgree (a b : ProvTags) : Prop := a.width = b.width ∧ a.kernel = b.kernel

theorem widest_agree {l l' : List ProvTags} (h : List.Forall₂ TagsAgree l l') :
    Option.Rel TagsAgree (widestTags l) (widestTags l') := by
  induction h with
  | nil => exact Option.Rel.none
  | @cons a b as bs hab hs ih =>
    simp only [widestTags]
    cases h1 : widestTags as with
    | none =>
      cases h2 : widestTags bs with
      | none => exact Option.Rel.some hab
      | some t2 => rw [h1, h2] at ih; cases ih
    | some t1 =>
      cases h2 : widestTags bs with
      | none => rw [h1, h2] at ih; cases ih
      | some t2 =>
        rw [h1, h2] at ih
        cases ih with
        | some h12 =>
          simp only [hab.1, h12.1]
          split_ifs
          · exact Option.Rel.some h12
          · exact Option.Rel.some hab

mutual
theorem tags_agree {P P' : ProvParams} (hrb : P.rb = P'.rb) :
    ∀ pr : Prov, TagsAgree (pr.tags P) (pr.tags P')
  | .seed k tag => ⟨rfl, rfl⟩
  | .dir m src => by
    have := tags_agree hrb src
    exact this
  | .quad m path => by
    have hp := pathTags_agree hrb path
    have hw := widest_agree hp
    simp only [Prov.tags]
    cases h1 : widestTags (Prov.pathTags P path) with
    | none =>
      cases h2 : widestTags (Prov.pathTags P' path) with
      | none => exact ⟨by simp [hrb], rfl⟩
      | some t2 => rw [h1, h2] at hw; cases hw
    | some t1 =>
      cases h2 : widestTags (Prov.pathTags P' path) with
      | none => rw [h1, h2] at hw; cases hw
      | some t2 =>
        rw [h1, h2] at hw
        cases hw with
        | some h12 => exact h12
  | .letter m l path => ⟨by simp [Prov.tags, hrb], rfl⟩

theorem pathTags_agree {P P' : ProvParams} (hrb : P.rb = P'.rb) :
    ∀ path : List (Comp × Comp × Prov),
      List.Forall₂ TagsAgree (Prov.pathTags P path) (Prov.pathTags P' path)
  | [] => List.Forall₂.nil
  | (_, _, x) :: rest =>
    List.Forall₂.cons (tags_agree hrb x) (pathTags_agree hrb rest)
end

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The kernel of an identity depends on the tag parameters only through `r_b`. -/
theorem kernelOf_eq' {P P' : ProvParams} (hrb : P.rb = P'.rb)
    (seedK freshK : ℕ → KernelSpec) (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) : G.kernelOf P seedK freshK v u γ = G.kernelOf P' seedK freshK v u γ := by
  have h := (tags_agree hrb (G.prov v u γ)).2
  unfold GenStage.kernelOf
  rw [h]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The system operator of an identity depends on the tag parameters only through `r_b`. -/
theorem sysS_eq {P P' : ProvParams} (hrb : P.rb = P'.rb)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (t : ℝ) :
    G.sysS P seedK freshK φ₀ hφ₀ v u γ t = G.sysS P' seedK freshK φ₀ hφ₀ v u γ t := by
  unfold GenStage.sysS
  rw [kernelOf_eq' hrb seedK freshK G v u γ]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- The case of the tag parameters of the construction: two values of the readout exponent. -/
theorem sysS_succProvParams_eta (Cw cr σ₀ η η' : ℝ) (N p : ℕ)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (t : ℝ) :
    G.sysS (succProvParams D Cw cr σ₀ η N p) seedK freshK φ₀ hφ₀ v u γ t =
      G.sysS (succProvParams D Cw cr σ₀ η' N p) seedK freshK φ₀ hφ₀ v u γ t :=
  sysS_eq (P := succProvParams D Cw cr σ₀ η N p) (P' := succProvParams D Cw cr σ₀ η' N p)
    rfl seedK freshK φ₀ hφ₀ G v u γ t

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
/-! **The prefix of the successor statements, once** (cascade side of the bill
residual).

Every statement of the preservation step chooses its constants in the same order:
`Λ₀ → c₀max →` kernel template, carrier width `→ Q, T₀ →` seed bounds `→` orders (the schedule,
the reserves, the order floor of the reconstruction, the seed allocation, the lift
floors) `→` thresholds `thr, C_H, Υ → k_I →` ledger thresholds `→ C_I, C_w, j₀ → C_Q, C_pr →`
the constants of the statement, and then the data. `SuccPrefix α s q Data` is that prefix around a
predicate `Data` on the choices and on the constants `x : X` chosen last.

* `SuccPrefix.and`: two statements in prefix form give their conjunction, with the pair of
  constants (the thresholds are joined by `certificateThresholdJoin`, the carrier and ledger
  thresholds by maxima, `c₀max` by a minimum, `Λ₀` by a maximum). No monotonicity of the data in
  the constants is asked: each statement keeps its own constants and its own starting level.
* `SuccPrefix.imp`: a consequence at fixed choices, with the hypotheses of the prefix available
  as `SuccPrefixFacts`.
* `SuccPrefix₀`, `SuccPrefix.of_tail`: the proved library statements have the prefix without the
  reconstruction order floor around their own tail (`∀ C_Q C_pr, ∃ C m_*, …`, or `∀ k, …` first,
  or no `C_Q`); each is definitionally `SuccPrefix₀ α s q Tail`, and `of_tail` brings it to the common
  form.
* `SuccPrefix.of_scale`: a statement with the short prefix `∃ Λ₀, ∀ Λ ≥ Λ₀, …` (an at-form of a
  cascade piece that chooses only `Λ₀` and a starting level) in the common form.
* `successorBillResidual_of_prefix`: the bill residual from its data statement in prefix form.

The cascade pieces are stated at a frame with their inputs as hypotheses; the proved library
statements are brought to this form one by one and joined here, so that the prefix is opened
once.

For `X = Unit` the statement has no constants, and `SuccPrefix.and` of a statement with itself
chooses the constants twice, independently. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- A data statement of the successor: a predicate on the choices of the prefix, in
their order `Λ, φ₀, b, Q, T₀, C_e, τ_e, k_S, r₀, D₀, H, J, N, p, n_k, L_c, L_f, L_pr, A_cl, N_aux,
N_out, K_res, n_pad, s_X, s_Z, σ₀, a, σ, k_I, C_I, C_w, j₀, C_Q, C_pr`, and on the constants `x`
chosen last. -/
abbrev SuccData (X : Type) : Type :=
  ℕ → (φ₀ : Vec 2 → ℝ) → Integrable φ₀ → ℝ → ℝ → ℝ → ℝ → ℝ → InvConsts → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → InvConsts → ℝ → ℝ → ℕ → ℝ → ℝ → X → Prop

/-- **The prefix around a data statement.** -/
def SuccPrefix (α s q : ℝ) {X : Type} (Data : SuccData X) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ x : X,
      Data Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
        σ₀ a σ kI CI Cw j₀ CQ Cpr x

/-- The hypotheses of the prefix at fixed choices (the thresholds, which are chosen
by the statement, appear existentially). -/
structure SuccPrefixFacts (α s q : ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (bw Q T₀ Ce τe : ℝ)
    (kS : InvConsts) (r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ a σ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) : Prop where
  hΛ : 128 ≤ Λ
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ₀
  nonneg : ∀ z, 0 ≤ φ₀ z
  mass : ∫ z, φ₀ z = 1
  support : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  hbw : 0 < bw
  hbw_le : bw ≤ 1 / 10000
  hQ : 0 < Q
  hT₀ : 0 < T₀
  hCe : 1 ≤ Ce
  hτe : 0 < τe
  hc₀ : 0 < kS.c₀
  hcr : 0 < kS.cr
  hcr_le : kS.cr ≤ 1
  hσf : 0 < kS.σf
  hlamC : 0 < kS.lamC
  sched : IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk
    Lc Lf Lpr Acl Naux Nout
  hNaux : Naux ≤ Kres
  hNout : Kres + 2 * p ≤ Nout
  recon : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux
  alloc : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf
  hsX : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX
  hsZ : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ
  admissible : ∃ thr : InvConsts,
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q)
  ledger : ∃ CIthr Cwthr : ℝ, IsLedgerAdmissible Ce CI Cw CIthr Cwthr
  start : ∃ CH Υ : ℝ, 1 ≤ CH ∧ 0 < Υ ∧ IsCarrierStart α q Λ bw CH Υ j₀

/-- A tail of the prefix: a predicate on the choices up to `j₀`. -/
abbrev SuccTail : Type :=
  ℕ → (φ₀ : Vec 2 → ℝ) → Integrable φ₀ → ℝ → ℝ → ℝ → ℝ → ℝ → InvConsts → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → InvConsts → ℝ → ℝ → ℕ → Prop

/-- **The prefix without the reconstruction order floor** around an
arbitrary tail: the form of the proved library statements of the preservation step. -/
def SuccPrefix₀ (α s q : ℝ) (Tail : SuccTail) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
      Tail Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
        σ₀ a σ kI CI Cw j₀

variable {α s q : ℝ} {X₁ X₂ : Type}

/-- **A proved library statement in the common form**: the prefix without the reconstruction order
floor around a tail, and a passage from the tail to the constants and the data at fixed choices. -/
theorem SuccPrefix.of_tail {Tail : SuccTail} {D : SuccData X₁} (h : SuccPrefix₀ α s q Tail)
    (ht : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ Ce τe : ℝ)
      (kS : InvConsts) (r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ)
      (σ₀ a σ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      SuccPrefixFacts α s q Λ φ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad sX sZ σ₀ a σ kI CI Cw j₀ →
      Tail Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ a σ kI CI Cw j₀ →
        ∀ CQ Cpr : ℝ, ∃ x : X₁, D Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux
          Nout Kres npad sX sZ σ₀ a σ kI CI Cw j₀ CQ Cpr x) :
    SuccPrefix α s q D := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  exact ht Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀
    { hΛ := hΛ₀.trans hΛ, smooth := hφsmooth, nonneg := hφpos, mass := hφint,
      support := hφsupport, hbw := hbw, hbw_le := hbwupper, hQ := hQ, hT₀ := hT₀, hCe := hCe,
      hτe := hτe, hc₀ := hc₀, hcr := hcr, hcr_le := hcrupper, hσf := hσf, hlamC := hlamC,
      sched := hsched, hNaux := hNaux, hNout := hNout, recon := hrecon, alloc := halloc,
      hsX := hsX, hsZ := hsZ, admissible := ⟨thr, hkI⟩, ledger := ⟨CIthr, Cwthr, hledger⟩,
      start := ⟨CH, Υ, hCH, hΥ, hstart⟩ }
    (h CI Cw j₀ hledger hstart)

/-- **A statement with the short prefix `∃ Λ₀, ∀ Λ ≥ Λ₀, …` in the common form** (the at-forms
of the cascade pieces that choose only `Λ₀` and a starting level): the remaining thresholds are
trivial (`c₀max = 1`, `thr = k_S`, `C_H = Υ = 1`, ledger thresholds `0`). -/
theorem SuccPrefix.of_scale {P : ℕ → Prop} {D : SuccData X₁}
    (h : ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → P Λ)
    (ht : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ Ce τe : ℝ)
      (kS : InvConsts) (r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ)
      (σ₀ a σ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      SuccPrefixFacts α s q Λ φ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad sX sZ σ₀ a σ kI CI Cw j₀ →
      P Λ →
        ∀ CQ Cpr : ℝ, ∃ x : X₁, D Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux
          Nout Kres npad sX sZ σ₀ a σ kI CI Cw j₀ CQ Cpr x) :
    SuccPrefix α s q D := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ _hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  exact ht Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀
    { hΛ := hΛ₀.trans hΛ, smooth := hφsmooth, nonneg := hφpos, mass := hφint,
      support := hφsupport, hbw := hbw, hbw_le := hbwupper, hQ := hQ, hT₀ := hT₀, hCe := hCe,
      hτe := hτe, hc₀ := hc₀, hcr := hcr, hcr_le := hcrupper, hσf := hσf, hlamC := hlamC,
      sched := hsched, hNaux := hNaux, hNout := hNout, recon := hrecon, alloc := halloc,
      hsX := hsX, hsZ := hsZ, admissible := ⟨kS, hkI⟩, ledger := ⟨0, 0, hledger⟩,
      start := ⟨1, 1, le_rfl, one_pos, hstart⟩ }
    (h Λ hΛ)

/-- `SuccPrefix.of_scale` with the bound `k_S.c₀ ≤ 1` of the seed's radius factor (the choice
`c₀max = 1`) passed to the tail, for the at-forms that ask `c₀ ≤ 1`. -/
theorem SuccPrefix.of_scale_radius {P : ℕ → Prop} {D : SuccData X₁}
    (h : ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → P Λ)
    (ht : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ Ce τe : ℝ)
      (kS : InvConsts) (r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ)
      (σ₀ a σ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      SuccPrefixFacts α s q Λ φ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad sX sZ σ₀ a σ kI CI Cw j₀ → kS.c₀ ≤ 1 →
      P Λ →
        ∀ CQ Cpr : ℝ, ∃ x : X₁, D Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux
          Nout Kres npad sX sZ σ₀ a σ kI CI Cw j₀ CQ Cpr x) :
    SuccPrefix α s q D := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  exact ht Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀
    { hΛ := hΛ₀.trans hΛ, smooth := hφsmooth, nonneg := hφpos, mass := hφint,
      support := hφsupport, hbw := hbw, hbw_le := hbwupper, hQ := hQ, hT₀ := hT₀, hCe := hCe,
      hτe := hτe, hc₀ := hc₀, hcr := hcr, hcr_le := hcrupper, hσf := hσf, hlamC := hlamC,
      sched := hsched, hNaux := hNaux, hNout := hNout, recon := hrecon, alloc := halloc,
      hsX := hsX, hsZ := hsZ, admissible := ⟨kS, hkI⟩, ledger := ⟨0, 0, hledger⟩,
      start := ⟨1, 1, le_rfl, one_pos, hstart⟩ }
    hc₀upper (h Λ hΛ)

/-- **Two statements in prefix form give their conjunction**, each with its own constants. -/
theorem SuccPrefix.and {D₁ : SuccData X₁} {D₂ : SuccData X₂}
    (h₁ : SuccPrefix α s q D₁) (h₂ : SuccPrefix α s q D₂) :
    SuccPrefix α s q (X := X₁ × X₂)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
          σ₀ a σ kI CI Cw j₀ CQ Cpr x =>
        D₁ Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
            σ₀ a σ kI CI Cw j₀ CQ Cpr x.1 ∧
          D₂ Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
            σ₀ a σ kI CI Cw j₀ CQ Cpr x.2) := by
  obtain ⟨Λa, hΛa, ha⟩ := h₁
  obtain ⟨Λb, hΛb, hb⟩ := h₂
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  obtain ⟨xa, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart) CQ Cpr
  obtain ⟨xb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cpr
  exact ⟨(xa, xb), ha, hb⟩

/-- **A consequence at fixed choices**, with the hypotheses of the prefix available. -/
theorem SuccPrefix.imp {D₁ : SuccData X₁} {D₂ : SuccData X₂} (h : SuccPrefix α s q D₁)
    (himp : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ Ce τe : ℝ)
      (kS : InvConsts) (r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ)
      (σ₀ a σ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ),
      SuccPrefixFacts α s q Λ φ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        npad sX sZ σ₀ a σ kI CI Cw j₀ →
      ∀ x : X₁, D₁ Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
          sX sZ σ₀ a σ kI CI Cw j₀ CQ Cpr x →
        ∃ y : X₂, D₂ Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
          sX sZ σ₀ a σ kI CI Cw j₀ CQ Cpr y) :
    SuccPrefix α s q D₂ := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨x, hx⟩ := h CI Cw j₀ hledger hstart CQ Cpr
  exact himp Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr
    { hΛ := hΛ₀.trans hΛ, smooth := hφsmooth, nonneg := hφpos, mass := hφint,
      support := hφsupport, hbw := hbw, hbw_le := hbwupper, hQ := hQ, hT₀ := hT₀, hCe := hCe,
      hτe := hτe, hc₀ := hc₀, hcr := hcr, hcr_le := hcrupper, hσf := hσf, hlamC := hlamC,
      sched := hsched, hNaux := hNaux, hNout := hNout, recon := hrecon, alloc := halloc,
      hsX := hsX, hsZ := hsZ, admissible := ⟨thr, hkI⟩, ledger := ⟨CIthr, Cwthr, hledger⟩,
      start := ⟨CH, Υ, hCH, hΥ, hstart⟩ } x hx

/-- **The bill residual from its data statement in prefix form**: the constants are the triple
`(C, c, m_*)` with `0 < c`. -/
theorem successorBillResidual_of_prefix {ζ : ℝ → ℝ}
    (h : SuccPrefix α s q (X := ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf _Lpr Acl Naux Nout _Kres npad sX sZ
          σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 < x.2.1 ∧
          SuccessorBillResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf
            Acl Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ x.1 x.2.1 x.2.2)) :
    SuccessorBillResidualStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨x, hc, hx⟩ := h CI Cw j₀ hledger hstart CQ Cpr
  exact ⟨x.1, x.2.1, x.2.2, hc, hx⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **Level floors and threshold choices of the cascade pieces** (cascade side of the bill
residual).

Two statements in the common prefix form that carry no analysis, only choices of the
prefix that the pieces at a frame ask as hypotheses:

* `succPrefix_ckerPos`: the kernel derivative constants of the invariant are `≥ 1` (the
  threshold `thr.cker = 1`; hypothesis `hcpos` of the fine defect);
* `succPrefix_levelFloor`: a level `m_*`, chosen after `(k_I, C_I)`, from which the kernel price
  bound of the invariant is `≤ 1/8` and the width factor is `≤ 1`
  (`C_I·ε_{m-1}^{q·min(δ/4, τ_e)} ≤ 1/8`: hypothesis `hθ` of the fine defect and of the stage scale;
  `C_wid·ε_m^{σ_f} ≤ 1`: hypothesis `hsmall` of the fine defect).

For `C_I ≤ 0` or `C_wid ≤ 0` the floors hold at every level; the thresholds are
lower bounds only, so the choice `thr.cker = 1` does not restrict the seed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter
open scoped Topology

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- **The kernel derivative constants of the invariant are at least `1`** (common prefix form,
threshold `thr.cker = 1`). -/
theorem succPrefix_ckerPos (α s q : ℝ) :
    SuccPrefix α s q (X := Unit)
      (fun _Λ _φ₀ _hφ₀ _bw _Q _T₀ _Ce _τe _kS _r₀ _D₀ _H _J _N _p _nk _Lc _Lf _Lpr _Acl _Naux
          _Nout _Kres _npad _sX _sZ _σ₀ _a _σ kI _CI _Cw _j₀ _CQ _Cpr _x => ∀ j, 1 ≤ kI.cker j) := by
  refine ⟨128, le_rfl, fun Λ _ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ Q T₀ _ _ Ce τe kS r₀ D₀ _ _ _ _ _ _ _ _
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ _ _ _ _ _ _ _
  refine ⟨{ kS with cker := fun _ => 1 }, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _ CQ Cpr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hck, -⟩ := hkI
  exact ⟨(), fun j => (hck j).2⟩

/-- A power of the parent wavelength is eventually below any positive bound. -/
theorem billCtx_parentPower_eventually_le {q e b : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (he : 0 < e) (C : ℝ) (hb : 0 < b) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → C * ocEpsilon q Λ (m - 1) ^ e ≤ b := by
  have hlim : Tendsto (fun m : ℕ => C * ocEpsilon q Λ (m - 1) ^ e) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (Construction.Preservation.Buffer.preparation_parent_power_tendsto_zero hq hΛ he)
  exact eventually_atTop.mp (hlim.eventually (eventually_le_nhds hb))

/-- **The smallness conditions of the invariant's constants from the level `m_*` on.** -/
def LevelFloorAt (α q : ℝ) (Λ : ℕ) (τe : ℝ) (kI : InvConsts) (CI : ℝ) (mStar : ℕ) : Prop :=
  ∀ m, mStar ≤ m →
    CI * ocEpsilon q Λ (m - 1) ^ (q * min (ocDelta α q / 4) τe) ≤ 1 / 8 ∧
      kI.Cwid * ocEpsilon q Λ m ^ kI.σf ≤ 1

/-- **The level floor in the common prefix form**; the constant is the level `m_*`, chosen after
`(k_I, C_I)`. -/
theorem succPrefix_levelFloor (α s : ℝ) (hα₀ : 0 < α) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ _φ₀ _hφ₀ _bw _Q _T₀ _Ce τe _kS _r₀ _D₀ _H _J _N _p _nk _Lc _Lf _Lpr _Acl _Naux _Nout
          _Kres _npad _sX _sZ _σ₀ _a _σ kI CI _Cw _j₀ _CQ _Cpr x =>
        LevelFloorAt α q Λ τe kI CI x) := by
  refine SuccPrefix.of_scale (P := fun _ => True) ⟨128, le_rfl, fun _ _ => trivial⟩ ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts _ CQ Cpr
  have hq1 : 1 < q := hq.1
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα₀ hq
  have hμ : 0 < q * min (ocDelta α q / 4) τe :=
    mul_pos (by linarith) (lt_min (by linarith) hfacts.hτe)
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  obtain ⟨-, -, -, -, -, hσ₀, ha, haσ, -⟩ := hfacts.sched
  have hσ₀pos : 0 < σ₀ := by rw [hσ₀]; linarith
  have hσf : 0 < kI.σf := by
    rw [hkI.2.2.2.2.2.2.1]
    exact lt_min hfacts.hσf (by linarith)
  obtain ⟨m₁, h₁⟩ := billCtx_parentPower_eventually_le hq1 hfacts.hΛ hμ CI
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨m₂, h₂⟩ := billCtx_parentPower_eventually_le hq1 hfacts.hΛ hσf kI.Cwid one_pos
  refine ⟨max m₁ m₂, fun m hm => ⟨h₁ m (le_trans (le_max_left _ _) hm), ?_⟩⟩
  have h := h₂ (m + 1) (le_trans (le_trans (le_max_right _ _) hm) (Nat.le_succ m))
  rwa [Nat.add_sub_cancel] at h

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

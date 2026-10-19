-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.TorusEnergy.StreamFacts
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Proofs.Results.Finite.TraceClosure.TestSeparation
public import AVRegularity.Applications.Limits.WindowWeak
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus
public import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The root bound of the raw energy: `‖θ(t)‖² ≤ ‖f‖²` for every weak solution**.

`IsWeakSolutionOn` does not assume `f ∈ L²`. The energy bound `l2NormSq_le_of_weakSolutionOnWith`
does. The bridge: `θ(t₁) ∈ L²` pairs with every smooth periodic test like `f`
(`initial_pairing`), so `θ` is a weak solution with datum `θ(t₁)`, whence
`‖θ(t)‖² ≤ ‖θ(t₁)‖²`. Then either `f` is integrable on the cell and `f = θ(t₁)` almost everywhere
(`ae_eq_of_cellInner_eq`), or it is not, and `θ(t₁) = 0` (the pairings of `θ(t₁)` with the tests `ψ`
and `ψ + 1` both vanish, since one of `f ψ`, `f (ψ + 1)` is not integrable and its junk integral
is `0`). -/

open AVRegularity.Applications

/-- The actual stream drift is a window drift. -/
theorem isWindowDrift_of_isContDrift {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) (t₁ t₂ : ℝ) :
    IsWindowDrift b t₁ t₂ := by
  obtain ⟨B, -, hB⟩ := hb.bounded
  exact ⟨hb.continuous.measurable, ⟨B, fun t _ x => hB t x⟩, fun t _ => hb.periodic t,
    fun t _ φ hφ hc => hb.divFree t φ hφ hc⟩

/-- The datum of a weak solution can be replaced by `θ(t₁)`. -/
theorem rawEnergy_withInitialTrace {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (h12 : t₁ < t₂)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsWeakSolutionOnWith b κ t₁ t₂ (θ t₁) θ Dθ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun φ hφ => ?_⟩
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (φ t₁) := hφ.1.comp (contDiff_const.prodMk contDiff_id)
  rw [h8 φ hφ]
  exact (initial_pairing h12 ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hψ (hφ.2.1 t₁)).symm

theorem rawEnergy_trace_le {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (h12 : t₁ < t₂)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) : l2NormSq (θ t₁) ≤ l2NormSq f := by
  have hg : MemL2On unitCube (θ t₁) := (h.1 t₁ ⟨le_rfl, h12.le⟩).2
  have hpair := fun ψ (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : IsZ2Periodic ψ) =>
    initial_pairing h12 h hψ hp
  have hgi : IntegrableOn (θ t₁) unitCube := by
    have : IsFiniteMeasure (volume.restrict unitCube) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono (fun x hx => fun i _ => Set.Ioo_subset_Icc_self (hx i
        (Set.mem_univ i)) : unitCube ⊆ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))
        (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top⟩
    exact hg.integrable (by norm_num)
  by_cases hfi : IntegrableOn f unitCube
  · have hae : θ t₁ =ᵐ[volume.restrict unitCube] f := by
      refine InitialValue.ae_eq_of_cellInner_eq hgi hfi fun φ hφ hp => ?_
      unfold cellInner
      simp only [RCLike.inner_apply, conj_trivial]
      simp_rw [mul_comm (φ _)]
      exact hpair φ hφ hp
    unfold l2NormSq
    exact (integral_congr_ae (hae.mono fun x hx => by rw [hx])).le
  · have hgz : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
        ∫ x in unitCube, θ t₁ x * ψ x = 0 := by
      have hone : ∫ x in unitCube, f x * (fun _ => (1 : ℝ)) x = 0 := by
        simp only [mul_one]
        exact integral_undef hfi
      have hgone : ∫ x in unitCube, θ t₁ x * (fun _ => (1 : ℝ)) x = 0 := by
        rw [hpair _ contDiff_const (fun _ _ => rfl), hone]
      intro ψ hψ hp
      by_cases hfψ : IntegrableOn (fun x => f x * ψ x) unitCube
      · have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x + 1) := hψ.add contDiff_const
        have hp' : IsZ2Periodic (fun x => ψ x + 1) := fun k x => by simp [hp k x]
        have hnot : ¬ IntegrableOn (fun x => f x * (ψ x + 1)) unitCube := by
          intro h
          apply hfi
          have := h.sub hfψ
          refine this.congr_fun (fun x _ => ?_) measurableSet_unitCube'
          simp only [Pi.sub_apply]
          ring
        have h0 : ∫ x in unitCube, f x * (ψ x + 1) = 0 := integral_undef hnot
        have h1 := hpair _ hψ' hp'
        have i1 := integrable_mul_memL2 hg (memL2_continuous hψ.continuous)
        simp only [mul_add, mul_one] at h1 h0 hgone
        rw [integral_add i1 hgi, hgone, h0] at h1
        linarith
      · rw [hpair ψ hψ hp]
        exact integral_undef hfψ
    have hz := Providers.TraceClosure.ae_eq_zero_of_smooth_periodic_tests hg hgz
    have : l2NormSq (θ t₁) = 0 := by
      unfold l2NormSq
      have h0 : (fun x => θ t₁ x ^ 2) =ᵐ[volume.restrict unitCube] fun _ => (0 : ℝ) :=
        hz.mono fun x hx => by simp [hx]
      rw [integral_congr_ae h0]
      simp
    rw [this]
    exact integral_nonneg fun x => sq_nonneg _

/-- **The root bound**: `‖θ(t)‖² ≤ ‖f‖²` for every weak solution on a window with a window drift
(no `L²` hypothesis on the datum). -/
theorem rawEnergy_l2NormSq_le {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} (hκ : 0 ≤ κ) (h12 : t₁ < t₂)
    (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolutionOn b κ t₁ t₂ f θ) : ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ l2NormSq f := by
  obtain ⟨Dθ, h⟩ := hθ
  have h' := rawEnergy_withInitialTrace h12 h
  have hg : MemL2On unitCube (θ t₁) := (h.1 t₁ ⟨le_rfl, h12.le⟩).2
  intro t ht
  exact ((l2NormSq_le_of_weakSolutionOnWith hκ h12 hb hg h').1 t ht).trans
    (rawEnergy_trace_le h12 h)

end AVRegularity.Providers.WeakGen.Reduction
end
end

section
@[expose] public noncomputable section

section
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! The numerical passage from a square-root trace estimate to a squared
ENNReal time-supremum bound. The positive price also covers an infinite sup. -/

/-- Square the smoothing estimate after taking the finite time supremum.
No measurability or attainment of that supremum is required. -/
theorem weak_entry_high_trace_supremum (a b C : ℝ) (I : Set ℝ) (F : ℝ → ℝ)
    (hb : 0 ≤ b) (hab : a ≤ b) (hC : 0 < C)
    (hsmooth : ∀ bound : ℝ, (∀ t ∈ I, Real.sqrt (F t) ≤ bound) →
      Real.sqrt b ≤ C * bound) :
    ENNReal.ofReal a ≤ ENNReal.ofReal (C ^ 2) * ⨆ t ∈ I, ENNReal.ofReal (F t) := by
  let S : ℝ≥0∞ := ⨆ t ∈ I, ENNReal.ofReal (F t)
  change _ ≤ ENNReal.ofReal (C ^ 2) * S
  by_cases htop : S = ⊤
  · rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hC)))]
    exact le_top
  have hbound (t : ℝ) (ht : t ∈ I) : Real.sqrt (F t) ≤ Real.sqrt S.toReal := by
    apply Real.sqrt_le_sqrt
    have hs : ENNReal.ofReal (F t) ≤ S := le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hs
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) (hsmooth _ hbound)
  rw [Real.mul_self_sqrt hb, mul_mul_mul_comm,
    Real.mul_self_sqrt ENNReal.toReal_nonneg, ← pow_two] at hsq
  apply (ENNReal.ofReal_le_ofReal (hab.trans hsq)).trans_eq
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal htop]

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **Order-zero norms of jets**: the order-zero part of the factorial norm does not depend
on the radius, it is bounded by the factorial norm at every radius (truncation), and for a scalar
element of `TorusHk` it is `∫_{unitCube} g²` for any representative `g` of the value class. -/

section Norms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_orderZero_eq {μ : Measure (Vec 2)} (ρ ρ' : ℝ) (D : JetL2 μ 0 E) :
    factorialNormSq ρ D = factorialNormSq ρ' D := by
  simp [factorialNormSq, factorialWeight]

/-- The order-zero norm (at radius `1`) is at most the factorial norm at every radius. -/
theorem factorialNormSq_orderZero_le {K : ℕ} (ρ : ℝ) (U : TorusHk K E) :
    factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) U).val ≤ factorialNormSq ρ U.val :=
  (factorialNormSq_orderZero_eq 1 ρ _).le.trans
    (CycleComparison.Error.factorialNormSq_truncateTorusHk_le (Nat.zero_le K) ρ U)

end Norms

/-- **The order-zero norm of a scalar element is the `L²` norm of its value class.** -/
theorem factorialNormSq_orderZero_value {K : ℕ} (U : TorusHk K ℝ) (g : Vec 2 → ℝ)
    (hg : U.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict unitCube] g) :
    factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) U).val = ∫ x in unitCube, g x ^ 2 := by
  have h1 : factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) U).val =
      ∑ w : DerivativeWord2 0, ‖(truncateTorusHk (Nat.zero_le K) U).val ⟨0, w⟩‖ ^ 2 := by
    simp [factorialNormSq, factorialWeight, derivativeNormSq]
  rw [h1]
  rw [Fintype.sum_subsingleton _ (Fin.elim0 : DerivativeWord2 0)]
  have h2 : ((truncateTorusHk (Nat.zero_le K) U).val.ofLp ⟨0, Fin.elim0⟩) = U.val.ofLp (valueIndex2 K) :=
    rfl
  rw [h2, ← Applications.LocalEnergy.integral_sq_lp]
  refine integral_congr_ae ?_
  filter_upwards [hg, periodicJetRepresentative_ae U.val (valueIndex2 K)] with x hx hx'
  rw [← hx', ← hx]
  rfl

/-! ### Sum of suprema against the supremum of the sum -/

theorem rawEnergy_sum_lintegral_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ≥0∞)
    (μ : Measure ℝ) : ∑ v ∈ s, ∫⁻ t, f v t ∂μ ≤ ∫⁻ t, ∑ v ∈ s, f v t ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add_right ih _).trans (le_lintegral_add _ _)

/-- **The strong energy expression is at most `(#components + 2)` times the bound of the
supremum of the sum plus half the gradient integral.** The time supremum of each component is
at most the supremum of the sum; `κ ∫ = 2 (κ/2) ∫`. -/
theorem rawEnergy_inner_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ κ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (t₀ t₁ : ℝ) {K : ι → ℕ}
    (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v)) (X : ℝ≥0∞)
    (hX : ∀ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (massNormSq ρ π (fun v => (u v t).val)) +
      ENNReal.ofReal (κ / 2) * ∫⁻ τ in Set.Icc t₀ t₁,
        ENNReal.ofReal (massGradNormSq ρ π (fun v => (w v τ).val)) ≤ X) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u v t).val)) +
        ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal (gradFactorialNormSq ρ (w v τ).val))) ≤
      ((Fintype.card ι : ℝ≥0∞) + 2) * X := by
  have hπi : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  have hG : ENNReal.ofReal (κ / 2) * ∫⁻ τ in Set.Icc t₀ t₁,
      ENNReal.ofReal (massGradNormSq ρ π (fun v => (w v τ).val)) ≤ X := by
    by_cases hle : t₀ ≤ t₁
    · exact le_trans le_add_self (hX t₁ ⟨hle, le_rfl⟩)
    · rw [Set.Icc_eq_empty hle]
      simp
  have hfn : ∀ v t, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (factorialNormSq ρ (u v t).val) ≤
      ENNReal.ofReal (massNormSq ρ π (fun v => (u v t).val)) := fun v t => by
    rw [← ENNReal.ofReal_mul (hπi v)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold massNormSq
    exact Finset.single_le_sum (f := fun i => (π i)⁻¹ * factorialNormSq ρ (u i t).val)
      (fun i _ => mul_nonneg (hπi i) (factorialNormSq_nonneg _ _)) (Finset.mem_univ v)
  have hsup : ∀ v, ENNReal.ofReal (π v)⁻¹ *
      (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u v t).val)) ≤ X := by
    intro v
    simp only [ENNReal.mul_iSup]
    refine iSup₂_le fun t ht => (hfn v t).trans ((le_self_add).trans (hX t ht))
  have hgrad : ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
      ENNReal.ofReal (gradFactorialNormSq ρ (w v τ).val)) ≤ 2 * X := by
    have h1 : ∀ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
        ENNReal.ofReal (gradFactorialNormSq ρ (w v τ).val)) =
        ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal ((π v)⁻¹ * gradFactorialNormSq ρ (w v τ).val) := by
      intro v
      rw [mul_left_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      refine lintegral_congr fun τ => ?_
      rw [ENNReal.ofReal_mul (hπi v)]
    simp_rw [h1]
    rw [← Finset.mul_sum]
    have h2 := rawEnergy_sum_lintegral_le Finset.univ (fun v τ =>
      ENNReal.ofReal ((π v)⁻¹ * gradFactorialNormSq ρ (w v τ).val)) (volume.restrict (Set.Icc t₀ t₁))
    have h3 : ∀ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹ * gradFactorialNormSq ρ (w v τ).val) =
        ENNReal.ofReal (massGradNormSq ρ π (fun v => (w v τ).val)) := fun τ => by
      unfold massGradNormSq
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro v _
      exact mul_nonneg (hπi v) (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
    simp_rw [h3] at h2
    calc ENNReal.ofReal κ * ∑ v, ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal ((π v)⁻¹ * gradFactorialNormSq ρ (w v τ).val)
        ≤ ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal (massGradNormSq ρ π (fun v => (w v τ).val)) :=
          mul_le_mul_right h2 _
      _ = 2 * (ENNReal.ofReal (κ / 2) * ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal (massGradNormSq ρ π (fun v => (w v τ).val))) := by
          rw [← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ 2 * X := mul_le_mul_right hG _
  calc _ = ∑ v, (ENNReal.ofReal (π v)⁻¹ * (⨆ t ∈ Set.Icc t₀ t₁,
          ENNReal.ofReal (factorialNormSq ρ (u v t).val)) +
        ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal κ * ∫⁻ τ in Set.Icc t₀ t₁,
          ENNReal.ofReal (gradFactorialNormSq ρ (w v τ).val))) := by
          simp_rw [mul_add]
    _ = _ := Finset.sum_add_distrib
    _ ≤ ∑ v : ι, X + 2 * X := add_le_add (Finset.sum_le_sum fun v _ => hsup v) hgrad
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul]

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **From a coupled solution at large reserves to a width-zero kernel solution** (weak reduction,
step 1).

* `triangular_coupled_exists_from`: `triangular_coupled_exists` with initial data.
* `coupledWeakIdentity_congr_ae`: a coupled weak identity transfers to data, gradients, total
  fluxes and forcings that agree almost everywhere in space at every time.
* `kernel_of_coupled`: a coupled solution at reserves `K ≥ k` with `k + D - 1 ≤ K + 1`, whose
  coefficients are the sums of order-`n` coefficients vanishing at the non-admissible orders, is
  a solution of the kernel class at the common order `k`, with identity kernels, after truncation:
  the lift of the input `S C U_j` is the truncation of `w_j` to order `k + D - 1`. This is the
  converse of `kernel_solution_identified`, with the same flux bookkeeping
  (`kernel_orders_sum_eq`). -/

open Comparison

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **A triangular coupled system has a solution from every datum** at every reserve vector. -/
theorem triangular_coupled_exists_from {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax) (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν)
    {D : ℕ} (hD : 2 ≤ D) (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hA_meas : ∀ i i' d, Measurable fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2)
    (hA_smooth : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hA_per : ∀ i i' d, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A i i' d t))
    (hA_fin : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (r : ι → ℕ) (htri : ∀ v u, ¬ r u < r v → ∀ d, A v u d = 0)
    (f : ∀ i, TorusHk (K i) (h i)) :
    ∃ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w := by
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hab'⟩ := hd.jets
  set c := schurMatrix ν ρ (fun _ : ι => (1 : ℝ)) K D a b A with hcdef
  set S := ∑ v, ∑ u, c v u with hS
  have hc0 : ∀ v u, 0 ≤ c v u := CoupledEnergy.schurMatrix_nonneg ν ρ hν hρ _
    (fun _ => one_pos) K D a b A hA_fin
  have hrow : ∀ v, ∑ u, c v u ≤ S := fun v =>
    Finset.single_le_sum (f := fun v => ∑ u, c v u)
      (fun v _ => Finset.sum_nonneg fun u _ => hc0 v u) (Finset.mem_univ v)
  have hcol : ∀ u, ∑ v, c v u ≤ S := fun u => by
    rw [hS, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun u => ∑ v, c v u)
      (fun u _ => Finset.sum_nonneg fun v _ => hc0 v u) (Finset.mem_univ u)
  set L := max 1 (8 * S) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hschur := CycleComparison.Error.schurCondition_rankScaledMass ν ρ hν hρ (fun _ => 1)
    (fun _ => one_pos) K D a b A hA_fin r htri L hL1 c S (fun _ _ => le_rfl) hrow hcol
    (le_max_right _ _)
  have hgate := coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div hd.per
    a' B₀ lam ha hB₀ hlam Kmax hjets hB hab' D hD
    (CycleComparison.Error.rankScaledMass (fun _ => 1) r L)
    (CycleComparison.Error.rankScaledMass_pos (fun _ => one_pos) (lt_of_lt_of_le one_pos hL1))
    K hK A hA_meas hA_smooth hA_per hA_fin hschur f (fun _ _ => 0)
    (fun _ => torusHk_memLp_zero _ _) (fun _ _ => 0) (fun _ => torusHk_integrable_zero _ _)
  exact hgate.1

end Generic

/-- **Congruence of the coupled weak identity**: data, gradients, total fluxes and forcings that
agree almost everywhere in space at every time give the same identity. -/
theorem coupledWeakIdentity_congr_ae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} {ν a t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ u₀' f f' φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du du' : ℝ → Fin 2 → Vec 2 → H}
    {Q F Q' F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g g' : ℝ → Vec 2 → H}
    (hI : CoupledWeakIdentity μ ν a t v u₀ f φ dφ du Q F g)
    (hu : u₀ =ᵐ[μ] u₀') (hf : f =ᵐ[μ] f')
    (hr : ∀ r ∈ Set.Ioc a t, ∀ᵐ x ∂μ, (∀ q, du r q x = du' r q x) ∧
      Q r x + F r x = Q' r x + F' r x ∧ g r x = g' r x) :
    CoupledWeakIdentity μ ν a t v u₀' f' φ dφ du' Q' F' g' := by
  let R (du : ℝ → Fin 2 → Vec 2 → H) (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
      (g : ℝ → Vec 2 → H) (r : ℝ) (x : Vec 2) : ℝ :=
    -(∑ q : Fin 2, v r x q * inner ℝ (du r q x) (φ x)) -
      ν * ∑ q : Fin 2, inner ℝ (du r q x) (dφ q x) -
      ∑ q : Fin 2, inner ℝ (Q r x q + F r x q) (dφ q x) + inner ℝ (g r x) (φ x)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a t, Integrable (R du Q F g r) μ) ∧
    IntegrableOn (fun r => ∫ x, R du Q F g r x ∂μ) (Set.Ioc a t) ∧ _ at hI
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a t, Integrable (R du' Q' F' g' r) μ) ∧
    IntegrableOn (fun r => ∫ x, R du' Q' F' g' r x ∂μ) (Set.Ioc a t) ∧ _
  have he (r : ℝ) (hr' : r ∈ Set.Ioc a t) : R du Q F g r =ᵐ[μ] R du' Q' F' g' r := by
    filter_upwards [hr r hr'] with x ⟨h1, h2, h3⟩
    change _ - _ - (∑ q : Fin 2, inner ℝ ((Q r x + F r x) q) (dφ q x)) + _ =
      _ - _ - (∑ q : Fin 2, inner ℝ ((Q' r x + F' r x) q) (dφ q x)) + _
    simp only [h1, h2, h3]
  have ht : (fun r => ∫ x, R du Q F g r x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun r => ∫ x, R du' Q' F' g' r x ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr'
    exact integral_congr_ae (he r hr')
  have hu' : (fun x => inner ℝ (u₀ x) (φ x)) =ᵐ[μ] fun x => inner ℝ (u₀' x) (φ x) := by
    filter_upwards [hu] with x hx
    rw [hx]
  have hf' : (fun x => inner ℝ (f x) (φ x)) =ᵐ[μ] fun x => inner ℝ (f' x) (φ x) := by
    filter_upwards [hf] with x hx
    rw [hx]
  refine ⟨hI.1.congr hu', hI.2.1.congr hf', fun r hr' => (hI.2.2.1 r hr').congr (he r hr'),
    hI.2.2.2.1.congr ht, ?_⟩
  rw [← integral_congr_ae hu', ← integral_congr_ae hf', hI.2.2.2.2]
  exact integral_congr_ae ht

/-- The jets of the zero carrier vanish almost everywhere. -/
theorem torusHk_zero_jet_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) (a : JetIndex2 k) :
    (0 : TorusHk k E).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  filter_upwards [periodicJetRepresentative_ae (0 : TorusHk k E).val a,
    Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube)] with x h1 h2
  change periodicJetRepresentative (0 : TorusHk k E).val a x = 0
  rw [h1]
  exact h2

section Kernel

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D D' k : ℕ} {K : ι → ℕ}
  {P : ∀ i j (_ : Γ i j) (n : ℕ), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (n - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {A : ∀ i j, (d : admissibleOrders K D' i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {S : ∀ i j (_ : Γ i j), ℝ → Lp (h j) 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
    Lp (h j) 2 (volume.restrict AVenhance.unitCube)}

/-- The kernel flux of the truncated lifts equals the coupled flux, almost everywhere in space at
every time. -/
theorem kernel_of_coupled_flux_ae (hD : D' ≤ D) (hlift : ∀ j, k + D - 1 ≤ K j + 1)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)) (i : ι) (r : ℝ) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      (∑ j : ι, ∑ d : admissibleOrders K D' i j,
        A i j d r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (w j r).toFunction.jet ⟨⟨d.1 - 1, by
            have h := Finset.mem_filter.1 d.2
            have := Finset.mem_Icc.1 h.1
            omega⟩, word⟩ x)) =
      ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        P i j α d.1 r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (truncateTorusHk (hlift j) (w j r)).toFunction.jet ⟨⟨d.1 - 1, by
            have := Finset.mem_Icc.1 d.2
            omega⟩, word⟩ x) := by
  have hjet : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j (n : ℕ)
      (h₁ : n < k + D - 1 + 1) (h₂ : n < K j + 1 + 1) (word : DerivativeWord2 n),
      (truncateTorusHk (hlift j) (w j r)).toFunction.jet ⟨⟨n, h₁⟩, word⟩ x =
        (w j r).toFunction.jet ⟨⟨n, h₂⟩, word⟩ x :=
    ae_all_iff.2 fun j => torusHk_jet_ae_of_value_eq _ _ rfl
  filter_upwards [hjet] with x hx
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hA, _root_.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact (kernel_orders_sum_eq K hD i j (L₁ := k + D - 1) (L₂ := K j + 1) (by omega)
    (fun n => P i j α n r x) (fun n hn hna => hP i j α n hn hna r x)
    (fun a => (truncateTorusHk (hlift j) (w j r)).toFunction.jet a x)
    (fun a => (w j r).toFunction.jet a x) (hx j)
    (fun d => by have := Finset.mem_Icc.1 d.2; omega)
    (fun d => by
      have h := Finset.mem_filter.1 d.2
      have := Finset.mem_Icc.1 h.1
      omega)).symm

/-- A truncated square-integrable trajectory is square integrable. -/
theorem truncate_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {m n : ℕ} (hmn : m ≤ n)
    {μ : Measure ℝ} {w : ℝ → TorusHk n E} (hw : MemLp w 2 μ) :
    MemLp (fun t => truncateTorusHk hmn (w t)) 2 μ :=
  (truncateTorusHk hmn).comp_memLp' hw

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i j, Fintype (Γ i j)] in
/-- The input lifts of `kernel_of_coupled` are square integrable (the field of the kernel class,
stated at its own instance path). -/
theorem kernel_of_coupled_lift_memLp (hlift : ∀ j, k + D - 1 ≤ K j + 1)
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    ∀ i j (_ : Γ i j), MemLp (fun t => truncateTorusHk (hlift j) (w j t)) 2
      (volume.restrict (Set.Icc a b)) :=
  fun _ j _ => truncate_memLp (hlift j) (hw j)

/-- **A coupled solution at large reserves is a width-zero kernel solution at order `k`**, after
truncation; the input lifts are the truncations of `w`. -/
theorem kernel_of_coupled (hD : D' ≤ D) (hkK : ∀ i, k ≤ K i) (hlift : ∀ j, k + D - 1 ≤ K j + 1)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    {f : ∀ i, TorusHk (K i) (h i)} {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v k D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S
      (fun i => truncateTorusHk (hkK i) (f i)) (fun _ _ => 0) (fun _ _ => 0)
      (fun i t => truncateTorusHk (hkK i) (u i t))
      (fun i t => truncateTorusHk (Nat.succ_le_succ (hkK i)) (w i t))
      (fun _ j _ t => truncateTorusHk (hlift j) (w j t)) := by
  refine ⟨fun i => (truncateTorusHk (hkK i)).continuous.comp_continuousOn (hc.1 i),
    fun i => (truncateTorusHk (Nat.succ_le_succ (hkK i))).comp_memLp' (hc.2.1 i), fun i => ?_,
    fun i => ?_, kernel_of_coupled_lift_memLp hlift hc.2.1,
    fun i j α => ?_, fun i t ht φ => ?_⟩
  · filter_upwards [hc.2.2.1 i] with s hs
    rw [← hs]
    rfl
  · change truncateTorusHk (hkK i) (u i a) = truncateTorusHk (hkK i) (f i)
    rw [hc.2.2.2.1 i]
  · refine Filter.Eventually.of_forall fun s => ?_
    simp only [hS, ContinuousLinearMap.id_apply, id_compLp_eq]
    rfl
  · have hI := hc.2.2.2.2 i t ht φ
    refine coupledWeakIdentity_congr_ae hI
      (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (u i t) (valueIndex2 k)).symm
      (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (f i) (valueIndex2 k)).symm
      fun r _ => ?_
    have hdu : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ q : Fin 2,
        (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => q⟩ x =
          (truncateTorusHk (Nat.succ_le_succ (hkK i)) (w i r)).toFunction.jet
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩ x :=
      ae_all_iff.2 fun q => (KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (hkK i)) (w i r) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩,
          fun _ => q⟩).symm
    filter_upwards [hdu, kernel_of_coupled_flux_ae hD hlift hA hP w i r,
      torusHk_zero_jet_ae (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) (valueIndex2 (K i)),
      torusHk_zero_jet_ae (E := PiLp 2 (fun _ : Fin 2 => h i)) k (valueIndex2 k),
      torusHk_zero_jet_ae (E := h i) (K i) (valueIndex2 (K i)),
      torusHk_zero_jet_ae (E := h i) k (valueIndex2 k)] with x h1 h2 h3 h4 h5 h6
    refine ⟨h1, ?_, ?_⟩
    · rw [h3, h4]
      simp only [Pi.zero_apply, add_zero]
      exact h2
    · rw [h5, h6]

end Kernel

end AVRegularity.Providers.WeakGen.Reduction
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **From a forced coupled solution at large reserves to a width-zero kernel solution**.

`kernel_of_coupled_forced` is `kernel_of_coupled` with a forcing: a coupled solution at reserves
`K ≥ k` with `k + D - 1 ≤ K + 1`, forced by a flux `R` and a scalar `q` at the reserves, whose
coefficients are the sums of order-`n` coefficients vanishing at the non-admissible orders, is a
solution of the kernel class at the common order `k` forced by the truncations of `R` and `q`.
The physical lift of a reconstruction window returns its residual `(R_res, q_res)` as such a
forcing; the comparison error of a weak passage solves the kernel system at order zero.

The degenerate cases are included: `R = 0`, `q = 0` is `kernel_of_coupled` (the truncation of zero
is zero); `k = K i` on every row is no truncation of the value, the forcing and the initial
datum. -/

open Comparison

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D D' k : ℕ} {K : ι → ℕ}
  {P : ∀ i j (_ : Γ i j) (n : ℕ), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (n - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {A : ∀ i j, (d : admissibleOrders K D' i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {S : ∀ i j (_ : Γ i j), ℝ → Lp (h j) 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
    Lp (h j) 2 (volume.restrict AVenhance.unitCube)}

/-- **A forced coupled solution at large reserves is a width-zero kernel solution at order `k`**,
after truncation, with the truncated forcing; the input lifts are the truncations of `w`. -/
theorem kernel_of_coupled_forced (hD : D' ≤ D) (hkK : ∀ i, k ≤ K i)
    (hlift : ∀ j, k + D - 1 ≤ K j + 1)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    {f : ∀ i, TorusHk (K i) (h i)}
    {R : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {q : ∀ i, ℝ → TorusHk (K i) (h i)} {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f R q u w) :
    IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v k D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S
      (fun i => truncateTorusHk (hkK i) (f i))
      (fun i t => truncateTorusHk (hkK i) (R i t))
      (fun i t => truncateTorusHk (hkK i) (q i t))
      (fun i t => truncateTorusHk (hkK i) (u i t))
      (fun i t => truncateTorusHk (Nat.succ_le_succ (hkK i)) (w i t))
      (fun _ j _ t => truncateTorusHk (hlift j) (w j t)) := by
  refine ⟨fun i => (truncateTorusHk (hkK i)).continuous.comp_continuousOn (hc.1 i),
    fun i => (truncateTorusHk (Nat.succ_le_succ (hkK i))).comp_memLp' (hc.2.1 i), fun i => ?_,
    fun i => ?_, kernel_of_coupled_lift_memLp hlift hc.2.1,
    fun i j α => ?_, fun i t ht φ => ?_⟩
  · filter_upwards [hc.2.2.1 i] with s hs
    rw [← hs]
    rfl
  · change truncateTorusHk (hkK i) (u i a) = truncateTorusHk (hkK i) (f i)
    rw [hc.2.2.2.1 i]
  · refine Filter.Eventually.of_forall fun s => ?_
    simp only [hS, ContinuousLinearMap.id_apply, id_compLp_eq]
    rfl
  · have hI := hc.2.2.2.2 i t ht φ
    refine coupledWeakIdentity_congr_ae hI
      (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (u i t) (valueIndex2 k)).symm
      (KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (f i) (valueIndex2 k)).symm
      fun r _ => ?_
    have hdu : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ q' : Fin 2,
        (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => q'⟩ x =
          (truncateTorusHk (Nat.succ_le_succ (hkK i)) (w i r)).toFunction.jet
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q'⟩ x :=
      ae_all_iff.2 fun q' => (KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (hkK i)) (w i r) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩,
          fun _ => q'⟩).symm
    filter_upwards [hdu, kernel_of_coupled_flux_ae hD hlift hA hP w i r,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (R i r) (valueIndex2 k),
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (hkK i) (q i r) (valueIndex2 k)]
      with x h1 h2 h3 h4
    refine ⟨h1, ?_, h4.symm⟩
    rw [h3]
    exact congrArg (· + (R i r).toFunction.jet (valueIndex2 (K i)) x) h2

/-- **The same, at given data**: an initial value and a forcing at the order `k` that are the
truncations of those of the coupled solution. Stated here, for abstract components, so that the
substitution is made before the system is specialized. -/
theorem kernel_of_coupled_forced_eq (hD : D' ≤ D) (hkK : ∀ i, k ≤ K i)
    (hlift : ∀ j, k + D - 1 ≤ K j + 1)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    {f : ∀ i, TorusHk (K i) (h i)}
    {R : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {q : ∀ i, ℝ → TorusHk (K i) (h i)} {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    {f₀ : ∀ i, TorusHk k (h i)} {F₀ : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g₀ : ∀ i, ℝ → TorusHk k (h i)}
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f R q u w)
    (hf : ∀ i, truncateTorusHk (hkK i) (f i) = f₀ i)
    (hF : ∀ i t, truncateTorusHk (hkK i) (R i t) = F₀ i t)
    (hg : ∀ i t, truncateTorusHk (hkK i) (q i t) = g₀ i t) :
    IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v k D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀
      (fun i t => truncateTorusHk (hkK i) (u i t))
      (fun i t => truncateTorusHk (Nat.succ_le_succ (hkK i)) (w i t))
      (fun _ j _ t => truncateTorusHk (hlift j) (w j t)) := by
  obtain rfl : f₀ = fun i => truncateTorusHk (hkK i) (f i) := funext fun i => (hf i).symm
  obtain rfl : F₀ = fun i t => truncateTorusHk (hkK i) (R i t) :=
    funext fun i => funext fun t => (hF i t).symm
  obtain rfl : g₀ = fun i t => truncateTorusHk (hkK i) (q i t) :=
    funext fun i => funext fun t => (hg i t).symm
  exact kernel_of_coupled_forced hD hkK hlift hA hP hS hc

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **The row recursion of a coupled solution with initial data** (rows with data).

`coupledRow_energy` and `coupledRow_recursion` assume zero initial data. Here the initial
datum `f_v` is carried: with
* `X_v = 2 |f_v|² + 8/ν ∫|Q_v|² + 10 (∫|g_v|)²` (`rowDataBound`), `Q_v` the row's forcing plus its
  incoming flux, in the factorial norms of radius `r`, and
* `Φ_v = 2 |f_v|² + 16/ν ∫|F_v|² + 10 (∫|g_v|)²`,

`|u_v(t)|² + ν/2 ∫|∇w_v|² ≤ X_v` (`coupledRowData_energy`), and under the same coupling
hypotheses as `coupledRow_recursion`, `X_v ≤ Φ_v + 32 S C² ∑_u β_vu (π_v/π_u) X_u`
(`coupledRowData_recursion`). The proofs are those of the zero-data case with the term `2|f_v|²` of
`torusForcedRow_energy` kept. -/

open CycleJointProofs CycleJointProofs.PathReduction CoupledEnergy.Variational

section System

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν r a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D Kmax : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))} {g u : ∀ i, ℝ → TorusHk (K i) (h i)}
  {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}

/-- The energy bound of a row with initial datum `f`. -/
def rowDataBound (ν r a b : ℝ) (f : ∀ i, TorusHk (K i) (h i))
    (Q : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i)) (i : ι) : ℝ :=
  2 * factorialNormSq r (f i).val + rowEnergyBound ν r a b Q g i

omit [Fintype ι] in
theorem rowDataBound_nonneg (ν r a b : ℝ) (hν : 0 < ν) (f : ∀ i, TorusHk (K i) (h i))
    (Q : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i)) (i : ι) : 0 ≤ rowDataBound ν r a b f Q g i := by
  have h1 := integral_nonneg (μ := volume.restrict (Set.Icc a b))
    (f := fun s => factorialNormSq r (Q i s).val) fun s => factorialNormSq_nonneg r (Q i s).val
  have h2 : 0 ≤ factorialNormSq r (f i).val := factorialNormSq_nonneg r _
  have h3 : 0 ≤ (∫ s in Set.Icc a b, Real.sqrt (factorialNormSq r (g i s).val)) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ 8 / ν := div_nonneg (by norm_num) hν.le
  unfold rowDataBound rowEnergyBound
  exact add_nonneg (mul_nonneg (by norm_num) h2)
    (add_nonneg (mul_nonneg h4 h1) (mul_nonneg (by norm_num) h3))

/-- **The energy of a row of a coupled solution with initial data.** -/
theorem coupledRowData_energy (Rd : TorusCoefficientData (h := h) r K D a b A)
    (hd : TorusDriftData ν r a b v Kmax) (hν : 0 < ν) (hD : 2 ≤ D) (hK : ∀ i, K i ≤ Kmax)
    (hA_meas : ∀ i j d, Measurable fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    {f : ∀ i, TorusHk (K i) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    factorialNormSq r (u i t).val + ν / 2 * ∫ s in Set.Icc a b, gradFactorialNormSq r (w i s).val ≤
      rowDataBound ν r a b f (rowForcingFlux Rd F w) g i := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hQ : MemLp (rowForcingFlux Rd F w i) 2 (volume.restrict (Set.Icc a b)) :=
    torusHk_memLp_add (hF i) (torusHk_memLp_finset_sum Finset.univ _ fun j _ =>
      edgeFlux_memLp Rd hab hA_meas w (fun j => hs.2.1 j) i j)
  have he := torusForcedRow_energy hd hab Rd.radius_pos hν hD (hK i) hQ (hg i)
    (torusWeakSolution_forcedRow Rd f F g u w hs i) t ht
  unfold rowDataBound rowEnergyBound
  linarith

/-- **The row recursion of a coupled solution with initial data.** -/
theorem coupledRowData_recursion (Rd : TorusCoefficientData (h := h) r K D a b A)
    (hd : TorusDriftData ν r a b v Kmax) (hν : 0 < ν) (hD : 2 ≤ D) (hK : ∀ i, K i ≤ Kmax)
    (hab : a ≤ b)
    (hA_meas : ∀ i j d, Measurable fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    {f : ∀ i, TorusHk (K i) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C S : ℝ) (β : ι → ι → ℝ)
    (hβ : ∀ i j, 0 ≤ β i j) (hS : ∀ i, ∑ j, β i j ≤ S)
    (hc : ∀ i j, ∑ d : admissibleOrders K D i j,
      (coefficientSeminorm r (K i) a b (A i j d)).toReal *
        derivativeReserveFactor r (K i) (d.1 - 2) ≤ ν * C * Real.sqrt (π i / π j) * β i j)
    (i : ι) :
    rowDataBound ν r a b f (rowForcingFlux Rd F w) g i ≤
      (2 * factorialNormSq r (f i).val + 16 / ν * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) +
        10 * (∫ s in Set.Icc a b, Real.sqrt (factorialNormSq r (g i s).val)) ^ 2) +
      32 * S * C ^ 2 * ∑ j, β i j * (π i / π j) *
        rowDataBound ν r a b f (rowForcingFlux Rd F w) g j := by
  classical
  set μ := volume.restrict (Set.Icc a b) with hμ
  set cc : ι → ℝ := fun j => ∑ d : admissibleOrders K D i j,
    (coefficientSeminorm r (K i) a b (A i j d)).toReal *
      derivativeReserveFactor r (K i) (d.1 - 2) with hcc
  have hcc0 : ∀ j, 0 ≤ cc j := fun j => Finset.sum_nonneg fun d _ => by
    unfold derivativeReserveFactor
    have := Rd.radius_pos
    positivity
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun j _ => hβ i j).trans (hS i)
  have hpt : ∀ s ∈ Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val ≤
      2 * factorialNormSq r (F i s).val + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * gradFactorialNormSq r (w j s).val) := by
    intro s hs'
    have hle : Real.sqrt (factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
        Real.sqrt (factorialNormSq r (F i s).val) +
          ∑ j, cc j * Real.sqrt (gradFactorialNormSq r (w j s).val) := by
      refine (CycleComparison.Coarse.sqrt_fNSq_torus_add_le r _ _).trans (add_le_add le_rfl ?_)
      exact (CycleComparison.Coarse.sqrt_fNSq_torus_sum_le r Finset.univ _).trans
        (Finset.sum_le_sum fun j _ => edgeFlux_sqrt_le Rd i j s hs' (w j s))
    have hb := row_sq_bound Finset.univ _ _ S (ν * C)
      (fun j => Real.sqrt (gradFactorialNormSq r (w j s).val)) cc (β i)
      (fun j => Real.sqrt (π i / π j)) (Real.sqrt_nonneg _) (fun j _ => Real.sqrt_nonneg _)
      (fun j _ => hβ i j) (fun j _ => by simpa only [cc, mul_assoc] using hc i j)
      (fun j _ => hcc0 j) (hS i) hle
    rw [Real.sq_sqrt (factorialNormSq_nonneg r _), Real.sq_sqrt (factorialNormSq_nonneg r _)]
      at hb
    refine hb.trans (le_of_eq ?_)
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt (div_nonneg (hπ i).le (hπ j).le),
      Real.sq_sqrt (CycleComparison.Coarse.gradFactorialNormSq_nonneg r _)]
  have hFi := CycleComparison.Coarse.integrable_factorialNormSq_torus (ρ := r) (hF i)
  have hwi := fun j => CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (ρ := r)
    (hs.2.1 j)
  have hQi : Integrable (fun s => factorialNormSq r (rowForcingFlux Rd F w i s).val) μ :=
    CycleComparison.Coarse.integrable_factorialNormSq_torus (torusHk_memLp_add (hF i)
      (torusHk_memLp_finset_sum Finset.univ _ fun j _ =>
        edgeFlux_memLp Rd hab hA_meas w (fun j => hs.2.1 j) i j))
  have hint : (∫ s in Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
      2 * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * ∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) := by
    have hrhs : Integrable (fun s => 2 * factorialNormSq r (F i s).val + 2 * S * (ν * C) ^ 2 *
        ∑ j, β i j * ((π i / π j) * gradFactorialNormSq r (w j s).val)) μ :=
      (hFi.const_mul 2).add ((integrable_finsetSum Finset.univ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)).const_mul _)
    refine (setIntegral_mono_on hQi hrhs measurableSet_Icc hpt).trans (le_of_eq ?_)
    rw [integral_add (hFi.const_mul 2) ((integrable_finsetSum Finset.univ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ =>
        ((hwi j).const_mul (π i / π j)).const_mul (β i j)]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul]
  -- the gradients of the sources, now against the bound with data
  have hgrad : ∀ j, (∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) ≤
      2 / ν * rowDataBound ν r a b f (rowForcingFlux Rd F w) g j := by
    intro j
    have he := coupledRowData_energy Rd hd hν hD hK hA_meas hF hg hs j a ⟨le_rfl, hab⟩
    have h0 := factorialNormSq_nonneg r (u j a).val
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    nlinarith
  have hsum : ∑ j, β i j * ((π i / π j) * ∫ s in Set.Icc a b, gradFactorialNormSq r (w j s).val) ≤
      ∑ j, β i j * ((π i / π j) *
        (2 / ν * rowDataBound ν r a b f (rowForcingFlux Rd F w) g j)) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgrad j)
      (div_nonneg (hπ i).le (hπ j).le)) (hβ i j)
  have hkey : 8 / ν * (∫ s in Set.Icc a b, factorialNormSq r (rowForcingFlux Rd F w i s).val) ≤
      16 / ν * (∫ s in Set.Icc a b, factorialNormSq r (F i s).val) +
        32 * S * C ^ 2 * ∑ j, β i j * (π i / π j) *
          rowDataBound ν r a b f (rowForcingFlux Rd F w) g j := by
    have h8 : 0 ≤ 8 / ν := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hint.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsum (by positivity)))) h8
    refine hstep.trans (le_of_eq ?_)
    have hre : ∑ j, β i j * ((π i / π j) *
        (2 / ν * rowDataBound ν r a b f (rowForcingFlux Rd F w) g j)) =
        2 / ν * ∑ j, β i j * (π i / π j) *
          rowDataBound ν r a b f (rowForcingFlux Rd F w) g j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hre]
    generalize (∑ j, β i j * (π i / π j) *
      rowDataBound ν r a b f (rowForcingFlux Rd F w) g j) = X
    field_simp
    ring
  unfold rowDataBound rowEnergyBound at hkey ⊢
  linarith

end System

end AVRegularity.Providers.WeakGen.Comparison
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **Stage coefficients of every order at a fixed level** (weak reduction).

The reduction lifts the source rows to `L²(H^{K_w + D_m - 1})` with `D_m` chosen after the level
threshold, so it needs the physical coefficients of the passage stages at every order, at a level
fixed before `D_m`. The productions give a fixed order only above an order-dependent threshold.
Here every order comes from holomorphic generation:

* `scaled_contextCertified_of_weakCertified`: a weakly certified stage whose records are no
  longer than its wavelength, with record sizes inflated by `2^N (C + 1)` (`scaleWeakSeedStage`,
  which leaves every flux, piece, weight and order unchanged), is `IsContextCertified` at the
  auxiliary constants `weakReductionConsts L H` (reserves in `[0, 1]`, fast weight `L`);
* `weakData_physCoeff_allOrder`: for the stages of a weak construction below the root, on a
  carrier start at `(1, 400)` above the common plan's thresholds, every physical coefficient is
  jointly measurable on every window, `C^n` and periodic at every time, and has finite seminorms
  of every order at every radius `ρ ≤ ε_{i-1}`: the native lemmas of the construction applied
  to the inflated stage, whose physical coefficients are those of the stage, and the shift
  invariance of the weak construction. It is stated on the raw data, for the weak entry and for a
  passage instance;
* `weakEntry_physCoeff_allOrder`: the same for the stages of `WeakEntryStages`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Construction.Preservation.FullLift

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Auxiliary invariant constants: fast weight `L`, grade offset zero, top grade `H`. -/
def weakReductionConsts (L H : ℕ) : InvConsts :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0, L, 0, H⟩

theorem compReserve_weakReductionConsts_le_one (L H : ℕ) (c : Comp) :
    compReserve (weakReductionConsts L H) c ≤ 1 := by
  unfold compReserve
  have h : 0 ≤ (((weakReductionConsts L H).G0 + compGrade c : ℕ) : ℝ) /
      (((weakReductionConsts L H).Hprod : ℝ) + 1) := by positivity
  linarith

theorem compReserve_weakReductionConsts_nonneg (L H : ℕ) (c : Comp) (hc : compGrade c ≤ H) :
    0 ≤ compReserve (weakReductionConsts L H) c := by
  unfold compReserve
  change 0 ≤ 1 - (((0 + compGrade c : ℕ) : ℝ)) / ((H : ℝ) + 1)
  rw [sub_nonneg, div_le_one (by positivity), zero_add]
  have hc' : ((compGrade c : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hc
  linarith

/-- The records of a passage stage of a weak construction have the length `ε_{i+1}`. -/
theorem weakConstruction_stage_record_length {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] (P : ProvParams) (Mn : WeakMenu) (M J r : ℕ) (rW : ℝ)
    (stage : ℕ → GenStage D hr Dm b j₀) (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hMi : M ≤ i) (hi : i < M + J) (v u : CompIn (stage i).comps)
    (γ : (stage i).fam.Γ v u) :
    ((stage i).fam.identity v u γ).record.length = D.eps (i + 1) := by
  have hp := hc.2.2 (i + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hp
  have hl := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc
    (i + 1) (by omega) (by omega)
  have hrec := weakPassage_record_lengths P Mn rW (1 + (M + J - (i + 1)) * Mn.N)
    (stage (i + 1)) (stage i) hp.1 hp.2 v u γ
  rw [hl] at hrec
  exact hrec.1

/-- **A weakly certified stage, inflated, is context certified.** The record lengths must be at
most the wavelength of the stage and the orders at most `N`; the reserve of the weak certificate
is at least one. -/
theorem scaled_contextCertified_of_weakCertified {G : GenStage D ScalarH Dm b j₀} {C mres : ℝ}
    {L N : ℕ} (hC : 0 ≤ C) (hW : Providers.WeakGen.WeakCertified C mres L G) (hb : 0 ≤ b)
    (hε : ∀ k, 0 ≤ D.eps k) (hm : 1 ≤ mres) (hεl : 0 < D.eps G.level)
    (hlen : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.length ≤ D.eps G.level)
    (hord : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N) (H : ℕ) :
    (scaleWeakSeedStage G (2 ^ N * (C + 1)) (by positivity)).IsContextCertified
      (weakReductionConsts L H) := by
  intro v u γ
  set s := (G.fam.identity v u γ).record.size with hs
  set n := (G.fam.identity v u γ).maxOrder with hn
  set ρ := (G.fam.identity v u γ).record.length / D.eps G.level with hρ
  have hs0 : 0 ≤ s := (G.fam.identity v u γ).record.size_nonneg
  have hρ0 : 0 < ρ := div_pos (G.fam.identity v u γ).record.length_pos hεl
  have hρ1 : ρ ≤ 1 := (div_le_one hεl).2 (hlen v u γ)
  set θ₀ := C * s * ρ ^ (n - 2) with hθ₀
  have hθ₀0 : 0 ≤ θ₀ := mul_nonneg (mul_nonneg hC hs0) (pow_nonneg hρ0.le _)
  refine ⟨fun _ _ _ => θ₀, fun _ _ _ => hθ₀0, fun d hd hdn => ?_, fun d α c => ?_⟩
  · have hsum : ∑ _α : DerivativeWord2 (d - 1), ∑ _k : Fin 2, θ₀ = 2 ^ d * θ₀ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        DerivativeWord2, DerivativeWord, Fintype.card_fun]
      push_cast
      rw [← mul_assoc, ← pow_succ]
      congr 2
      omega
    have hratio : D.eps G.level / (G.fam.identity v u γ).record.length = ρ⁻¹ := by
      rw [hρ, inv_div]
    change (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
        ∑ _α : DerivativeWord2 (d - 1), ∑ _k : Fin 2, θ₀ ≤ 2 ^ N * (C + 1) * s
    rw [hsum, hratio]
    calc ρ⁻¹ ^ (d - 2) * (2 ^ d * θ₀) ≤ 2 ^ N * C * s :=
          witness_algebra hρ0 hρ1 hC hs0 hd hdn (hord v u γ)
      _ ≤ 2 ^ N * (C + 1) * s := by gcongr; linarith
  · obtain ⟨f, F, hf, hco, hsz⟩ := hW v u γ d α c
    refine ⟨f, F, fun p => ⟨isGeneratedCtxFrom_of_noExports (hf p).1, (hf p).2, hco p⟩, ?_⟩
    exact (ctxSize_mono_reserve hb hε
      ((compReserve_weakReductionConsts_le_one L H v.1).trans hm) L).trans hsz

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The stages of a weak construction have physical coefficients of every order**, on the raw
data: a carrier start at `(1, 400)`, the base and level thresholds of the common plan, and the
construction. Jointly measurable on every window, `C^n` and periodic at every time, with finite
seminorms of every order at every radius `ρ ≤ ε_{i-1}`. It serves the weak entry and a passage
instance. -/
theorem weakData_physCoeff_allOrder {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ)
    (h128 : 128 ≤ A.Λ) (j₀ : ℕ) (hcar : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀) (M : ℕ)
    (hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ M)
    (D : OCData) (hDα : D.α = B.α) (hDq : D.q = B.q) (hDΛ : D.Λ = A.Λ) (hDζ : D.ζ = B.ζ)
    (hstream : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ) (hband0 : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ)
    (hterm : D.term = M) (Dm : ℕ) (hDm : 1 + A.Jw * A.Nw ≤ Dm) (P : ProvParams)
    (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (hcons : IsWeakConstruction D P (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu)
      M A.Jw (D.termRW A.σw M) 0 stage)
    (i : ℕ) (hMi : M ≤ i) (hi : i < M + A.Jw)
    (v u : CompIn (stage i).comps) (γ : (stage i).fam.Γ v u) (n d : ℕ) (a b : ℝ) :
    Measurable (fun z : Set.Icc a b × Vec 2 => (stage i).physCoeff v u γ d z.1 z.2) ∧
      (∀ t, ContDiff ℝ (n : ℕ) ((stage i).physCoeff v u γ d t)) ∧
      (∀ t, AVenhance.IsZ2Periodic ((stage i).physCoeff v u γ d t)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps (i - 1) →
        coefficientSeminorm ρ n a b ((stage i).physCoeff v u γ d) ≠ ⊤ := by
  let c := weakCommonCase R hbase j₀ hcar M hlev D hDα hDq hDΛ
    hDζ hstream hband0 hterm Dm hDm P stage hcons
  obtain ⟨Cm, hC0, hW⟩ : ∃ Cm : ℝ, 0 ≤ Cm ∧ Providers.WeakGen.WeakCertified Cm
      (weakReserve c.inst i) (weakWeight c.inst i) (stage i) := by
    have h := weakCommonCase_certified R hbase j₀ hcar M hlev D hDα
      hDq hDΛ hDζ hstream hband0 hterm Dm hDm P stage
      hcons (M + A.Jw - i) (by omega)
    rw [show M + A.Jw - (M + A.Jw - i) = i by omega] at h
    exact ⟨_, h.1, h.2⟩
  have hlevel : (stage i).level = i :=
    EntryWeakProofs.weakConstruction_level P _ M A.Jw 0 _ stage hcons i hMi hi.le
  have hj2 : j₀ + 2 ≤ M :=
    ((weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext).2
      (weakCoeffRequestOne R) j₀).trans hlev
  have hepos : ∀ k, 0 < D.eps k := fun k => case_eps_pos c.inst k
  have hq : 1 < D.q := by rw [hDq]; exact B.hq.1
  have hΛ : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hres : 1 ≤ weakReserve c.inst i := by
    unfold weakReserve
    have : (0 : ℝ) ≤ ((i - c.inst.M : ℕ) : ℝ) / (c.inst.physical.Jw : ℝ) := by positivity
    linarith
  have hlen : ∀ v u (γ : (stage i).fam.Γ v u),
      ((stage i).fam.identity v u γ).record.length ≤ D.eps (stage i).level := by
    intro v u γ
    rw [weakConstruction_stage_record_length P _ M A.Jw 0 _ stage hcons i hMi hi,
      hlevel]
    exact Applications.eps_antitone hq hΛ (Nat.le_succ i)
  have hord : ∀ v u (γ : (stage i).fam.Γ v u),
      ((stage i).fam.identity v u γ).maxOrder ≤ 1 + A.Jw * A.Nw :=
    fun v u γ => EntryWeakProofs.weakConstruction_output_maxOrder_bound P _ M A.Jw _ 0
      stage hcons i hMi hi v u γ
  set H := ∑ c' ∈ (stage i).comps, compGrade c' with hH
  have hgrade : ∀ v : CompIn (stage i).comps, compGrade v.1 ≤ H := fun v =>
    Finset.single_le_sum (f := compGrade) (fun _ _ => Nat.zero_le _) v.2
  have hb : 0 < A.bw := A.bw_pos
  have hcert := scaled_contextCertified_of_weakCertified (N := 1 + A.Jw * A.Nw) hC0 hW hb.le
    (fun k => (hepos k).le) hres (by rw [hlevel]; exact hepos i) hlen hord H
  have hCs : 0 < 2 ^ (1 + A.Jw * A.Nw) * (Cm + 1) := by positivity
  set G' := scaleWeakSeedStage (stage i) (2 ^ (1 + A.Jw * A.Nw) * (Cm + 1)) hCs.le with hG'
  have hpar : G'.IsSlotTransverse := scaleWeakSeedStage_isSlotTransverse _ _ _
    (weakGen_stage_slot_laws weakCommonCoeffPlan (fun R => le_trans (by norm_num)
      ((le_max_left _ _).trans ((weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan)
        weakBasePlan_complexContext).1 R).2)) weakBasePlan_gen c i hMi hi.le)
  have hnat : G'.IsNatural (M + A.Jw) := scaleWeakSeedStage_isNatural _ _ hCs _
    (EntryWeakProofs.weakConstruction_output_natural P _ M A.Jw 0 _ stage hcons
      i hMi hi)
  have hi1 : 1 ≤ G'.level := by change 1 ≤ (stage i).level; rw [hlevel]; omega
  have hj : j₀ ≤ G'.level := by change j₀ ≤ (stage i).level; rw [hlevel]; omega
  have hε : 0 < D.eps (G'.level - 1) := hepos _
  have hm0 : ∀ v : CompIn G'.comps, 0 ≤ compReserve (weakReductionConsts (weakWeight c.inst i) H) v.1 :=
    fun v => compReserve_weakReductionConsts_nonneg _ _ _ (hgrade v)
  have hm2 : ∀ v : CompIn G'.comps, compReserve (weakReductionConsts (weakWeight c.inst i) H) v.1 ≤ 2 :=
    fun v => (compReserve_weakReductionConsts_le_one _ _ _).trans (by norm_num)
  have hΛ1 : 1 ≤ D.Λ := le_trans (by norm_num) hΛ
  have hζ : IsFastProfile D.ζ := by rw [hDζ]; exact B.hζ
  have hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]
    exact hband0
  have hshift := weakConstruction_shiftInvariant P _ M A.Jw 0 _ stage hcons hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ1) (fun _ => Construction.Stream.ocEpsilon_pos hΛ1)
    (fun m _ _ => (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ1 hζ hband m).le) i hMi hi.le
  refine ⟨Construction.Preservation.FullLift.native_physCoeff_joint_measurable_of_context hcert
      hpar hnat hΛ1 hi1 hj hb hε a b hm0 hm2 v u γ d,
    fun t => native_physCoeff_all_order_smooth hcert hpar hnat hi1 hj hb hε t t v u γ (hm0 v)
      (hm2 v) n d t ⟨le_rfl, le_rfl⟩,
    fun t => Construction.Preservation.Buffer.native_physCoeff_periodic
      (EntryWeakProofs.weakConstruction_output_natural P _ M A.Jw 0 _ stage hcons
        i hMi hi) hshift v u γ d t,
    fun ρ hρ hρε => native_physCoeff_all_order_seminorm_finite hcert hpar hnat hi1 hj hb hε a b
      v u γ (hm0 v) (hm2 v) ρ hρ
      (by change ρ ≤ D.eps ((stage i).level - 1); rw [hlevel]; exact hρε) n d⟩


/-- **The passage stages of the weak entry have physical coefficients of every order**: jointly
measurable on every window, `C^n` and periodic at every time, with finite seminorms of every
order at every radius `ρ ≤ ε_{i-1}`. -/
theorem weakEntry_physCoeff_allOrder (hcommon : WeakEntryCommonOK plan) {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (i : ℕ) (hMi : x.M ≤ i) (hi : i < x.M + A.Jw)
    (v u : CompIn (g.stage i).comps) (γ : (g.stage i).fam.Γ v u) (n d : ℕ) (a b : ℝ) :
    Measurable (fun z : Set.Icc a b × Vec 2 => (g.stage i).physCoeff v u γ d z.1 z.2) ∧
      (∀ t, ContDiff ℝ (n : ℕ) ((g.stage i).physCoeff v u γ d t)) ∧
      (∀ t, AVenhance.IsZ2Periodic ((g.stage i).physCoeff v u γ d t)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ x.D.eps (i - 1) →
        coefficientSeminorm ρ n a b ((g.stage i).physCoeff v u γ d) ≠ ⊤ :=
  weakData_physCoeff_allOrder R ((hcommon.1 B).trans x.base_ge) x.base128 x.j₀ x.carrier400 x.M
    ((hcommon.2 R C x.j₀).trans x.level_ge) x.D x.alpha x.q_eq x.base_eq x.profile_eq x.streams
    x.band x.terminal x.Dm x.order_ge x.P g.stage g.construction i hMi hi v u γ n d a b

end AVRegularity.Providers.WeakGen.Reduction
end
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.QuietDecay.Partition.Main
public import AVRegularity.CycleComparison.ActualMeans.Main
public import AVRegularity.CycleComparison.Coarse.Defect.Final
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Coarse.Energy.Cell

section
section
/-! **Density extension with an integrable majorant** (step (iv) of the conversion).

The `L¹`-in-time version of `AVRegularity.CycleComparison.Coarse.integrated_identity_of_tendsto`:
the right side `R s` is bounded by `m s * ‖φ‖` with an integrable (not constant) majorant `m`. -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **Density extension of an integrated identity, integrable majorant.** -/
theorem IntegratedIdentityOfTendsto {X : Type*} [SeminormedAddCommGroup X]
    {t₀ t : ℝ} (L : X → ℝ) (R : ℝ → X → ℝ)
    (hLsub : ∀ φ φ', L (φ - φ') = L φ - L φ') {c : ℝ} (hLb : ∀ φ, |L φ| ≤ c * ‖φ‖)
    (hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ φ φ', R s (φ - φ') = R s φ - R s φ') (m : ℝ → ℝ)
    (hm : IntegrableOn m (Set.Ioc t₀ t))
    (hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ φ, |R s φ| ≤ m s * ‖φ‖)
    {φ : X} {φN : ℕ → X} (hconv : Tendsto φN atTop (𝓝 φ))
    (hN : ∀ n, IntegrableOn (fun s => R s (φN n)) (Set.Ioc t₀ t) ∧
      L (φN n) = ∫ s in Set.Ioc t₀ t, R s (φN n)) :
    IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) ∧ L φ = ∫ s in Set.Ioc t₀ t, R s φ := by
  have hdist : Tendsto (fun n => ‖φN n - φ‖) atTop (𝓝 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.1 hconv)
  have hpt : ∀ s ∈ Set.Ioc t₀ t, Tendsto (fun n => R s (φN n)) atTop (𝓝 (R s φ)) := by
    intro s hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul (m s))
    rw [Real.norm_eq_abs, ← hRsub s hs]
    exact hRb s hs _
  have hmeas : AEStronglyMeasurable (fun s => R s φ) (volume.restrict (Set.Ioc t₀ t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hN n).1.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt))
  have hint : IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) :=
    Integrable.mono' (hm.mul_const ‖φ‖) hmeas
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]; exact hRb s hs φ))
  refine ⟨hint, ?_⟩
  have hL : Tendsto (fun n => L (φN n)) atTop (𝓝 (L φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul |c|)
    rw [Real.norm_eq_abs, ← hLsub]
    exact (hLb _).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _))
  have hI : Tendsto (fun n => ∫ s in Set.Ioc t₀ t, R s (φN n)) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, R s φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => (∫ s in Set.Ioc t₀ t, m s) * ‖φN n - φ‖)
      (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul (∫ s in Set.Ioc t₀ t, m s))
    rw [← integral_sub (hN n).1 hint]
    have hb : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)), ‖R s (φN n) - R s φ‖ ≤ m s * ‖φN n - φ‖ :=
      (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs, ← hRsub s hs]
        exact hRb s hs _)
    have := norm_integral_le_of_norm_le (hm.mul_const ‖φN n - φ‖) hb
    rw [integral_mul_const] at this
    linarith
  have hL' : Tendsto (fun n => L (φN n)) atTop (𝓝 (∫ s in Set.Ioc t₀ t, R s φ)) :=
    hI.congr fun n => ((hN n).2).symm
  exact tendsto_nhds_unique hL hL'

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Pointwise algebra of the transfer step** (step (vi) of the conversion).

At one time, the integrand of the weak equation of the coarse side and the integrand `wIntegrand` of the
defect differ by the pairings of the macro flux and of the coarse defect flux (equal integrals by
the swap) after the a.e. replacements of the derivatives (jets) and of the mean flux. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The two integrands at one time.** -/
theorem TransferPoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} (ν : ℝ) (b : Vec 2 → Vec 2) (ψ : Vec 2 → H) (dψ : Fin 2 → Vec 2 → H)
    (du du' : Fin 2 → Vec 2 → H) (Fm Fcd Fmean FcJ : Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (hdu : ∀ᵐ x ∂μ, ∀ k, du k x = du' k x) (hF : ∀ᵐ x ∂μ, FcJ x = Fmean x)
    (hrhs : Integrable (fun x => -(∑ k : Fin 2, b x k * inner ℝ (du k x) (ψ x))
      - ν * ∑ k : Fin 2, inner ℝ (du k x) (dψ k x)
      - ∑ k : Fin 2, inner ℝ (Fm x k + Fmean x k) (dψ k x) + inner ℝ (0 : H) (ψ x)) μ)
    (hPm : Integrable (fun x => ∑ k : Fin 2, inner ℝ (Fm x k) (dψ k x)) μ)
    (hPc : Integrable (fun x => ∑ k : Fin 2, inner ℝ (Fcd x k) (dψ k x)) μ)
    (hint : ∫ x, ∑ k : Fin 2, inner ℝ (Fm x k) (dψ k x) ∂μ =
      ∫ x, ∑ k : Fin 2, inner ℝ (Fcd x k) (dψ k x) ∂μ) :
    Integrable (fun x => -(∑ k : Fin 2, b x k * inner ℝ (du' k x) (ψ x))
      - ν * ∑ k : Fin 2, inner ℝ (du' k x) (dψ k x)
      - ∑ k : Fin 2, inner ℝ (Fcd x k + FcJ x k) (dψ k x)) μ ∧
    ∫ x, (-(∑ k : Fin 2, b x k * inner ℝ (du' k x) (ψ x))
      - ν * ∑ k : Fin 2, inner ℝ (du' k x) (dψ k x)
      - ∑ k : Fin 2, inner ℝ (Fcd x k + FcJ x k) (dψ k x)) ∂μ =
    ∫ x, (-(∑ k : Fin 2, b x k * inner ℝ (du k x) (ψ x))
      - ν * ∑ k : Fin 2, inner ℝ (du k x) (dψ k x)
      - ∑ k : Fin 2, inner ℝ (Fm x k + Fmean x k) (dψ k x) + inner ℝ (0 : H) (ψ x)) ∂μ := by
  have hae : (fun x => -(∑ k : Fin 2, b x k * inner ℝ (du' k x) (ψ x))
      - ν * ∑ k : Fin 2, inner ℝ (du' k x) (dψ k x)
      - ∑ k : Fin 2, inner ℝ (Fcd x k + FcJ x k) (dψ k x)) =ᵐ[μ]
      fun x => (-(∑ k : Fin 2, b x k * inner ℝ (du k x) (ψ x))
        - ν * ∑ k : Fin 2, inner ℝ (du k x) (dψ k x)
        - ∑ k : Fin 2, inner ℝ (Fm x k + Fmean x k) (dψ k x) + inner ℝ (0 : H) (ψ x))
        + ∑ k : Fin 2, inner ℝ (Fm x k) (dψ k x) - ∑ k : Fin 2, inner ℝ (Fcd x k) (dψ k x) := by
    filter_upwards [hdu, hF] with x h1 h2
    simp only [h1, h2, inner_add_left, inner_zero_left, Finset.sum_add_distrib]
    ring
  refine ⟨((hrhs.add hPm).sub hPc).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  have h1 := integral_sub (hrhs.add hPm) hPc
  have h2 := integral_add hrhs hPm
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2, hint]
  ring

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The grade-zero tail: the generic lemma** (glued mean, step (i)).

For a lift sequence with `C_n = 0` for `n > N` and `1 ≤ N`, the cell mean of the grade-zero slow
flux `liftFluxX` of degree `n ≥ N + 2` vanishes: the first two terms contain `C_{n-1}` with
`n - 1 > N`, the source term is absent at grade zero, and the third term is `-η G ∂_X` of a field
of cell mean zero. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftApply_eq_zero_of_coeff (n : ℕ) (c : LiftCoeff ι h)
    (hc : ∀ m α t X z v u, c m α t X z v u = 0) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    liftApply n c a t = fun _ _ => 0 := by
  funext X z
  funext v
  simp [liftApply, hc]

theorem gradeZero_meanFluxX_zero (Q Q' : LiftOperatorData ι h D) (sX sZ : ℕ)
    (t₀ t₁ : ℝ) (N : ℕ) (H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q' sX sZ t₀ t₁ N H Cc) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (hN : 1 ≤ N)
    (n : ℕ) (hn : N + 2 ≤ n) (a₀ : Vec 2 → ∀ i, h i) (ha : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (X : Vec 2) (k : Fin 2) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => a₀) 0 n t X z k) = 0 := by
  have h1 : liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => a₀) t = fun _ _ => 0 :=
    liftApply_eq_zero_of_coeff _ _ (fun m α t X z v u => hseq.2.2.1 0 (Nat.zero_le H) (n - 1)
      (by omega) m α t X z v u) _ _
  set Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => a₀) t with hΨ
  have hbox : IsBoxSmooth sX sZ Ψ := by
    refine CycleComparison.Lift.isBoxSmooth_pi sX sZ _ fun v => ?_
    exact QuietDecay.Partition.isBoxSmooth_liftApply (n - 2) sX sZ (Cc 0 (n - 2)) _ t
      (fun m α v u => (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) (n - 2) m α v u t ht).1)
      (ha.of_le (by exact_mod_cast le_top)) v
  have hC1 : ContDiff ℝ ((1 : ℕ) : ℕ∞) (Function.uncurry Ψ) := hbox.contDiff_uncurry hX hZ
  have hmean : ∀ X', fieldCellMean (Ψ X') = 0 := by
    intro X'
    by_cases hnN : n - 2 ≤ N
    · exact liftApply_fieldCellMean_eq_zero Q' sX sZ t₀ t₁ N H Cc hseq 0 (Nat.zero_le H)
        (n - 2) (by omega) hnN a₀ ha t ht X'
    · have : Ψ = fun _ _ => 0 := liftApply_eq_zero_of_coeff _ _
        (fun m α t X z v u => hseq.2.2.1 0 (Nat.zero_le H) (n - 2) (by omega) m α t X z v u) _ _
      rw [this]; exact fieldCellMean_zero
  have hslow : ∀ j : Fin 2, fieldCellMean (fun z => slowPartial j Ψ X z) = 0 := by
    intro j
    rw [fieldCellMean_slowPartial hC1 X j]
    have : (fun X' => fieldCellMean (Ψ X')) = fun _ => 0 := funext hmean
    rw [this]; simp
  have hcont : ∀ j : Fin 2, Continuous (fun z => slowPartial j Ψ X z) := by
    intro j
    have := continuous_fderiv_slow_of_contDiff hC1
    exact (this.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have heq : (fun z => liftFluxX Q Cc (fun _ => a₀) 0 n t X z k) =
      fun z => -(Q.η • ∑ j : Fin 2, Q.G t X k j • slowPartial j Ψ X z) := by
    funext z
    simp [liftFluxX, h1, fastPartial, hΨ, show 2 ≤ n by omega]
  have hs := fieldCellMean_sum (Finset.univ : Finset (Fin 2))
    (f := fun j z => Q.G t X k j • slowPartial j Ψ X z)
    (fun j _ => continuous_const.fun_smul (hcont j))
  rw [heq, fieldCellMean_neg, fieldCellMean_smul, hs]
  simp [fieldCellMean_smul, hslow]

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The generic gluing step of the core** (glued mean, step (i)).

`gluedMean_eq_neg_div`: the glued mean of pulse lifts with the divergence form of the pulse
means (`liftMean = meanApply n (Lb n)` on the window) is minus the Eulerian divergence of any
pulse fluxes `PF k` equal to minus the Piola transport of the chart flux. This is the body of
`isMeanPresentation_of_flux`, with the classical grade flux
replaced by an abstract pulse flux and the flux hypothesis taken pointwise at one time. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.ActualMeans

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem gluedMean_eq_neg_div (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ εc : ℝ) (hc : c ≠ 0) (hρ : ρ ≠ 0) (N r : ℕ) (Q : ℤ → LiftOperatorData ι h D)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a t))
    (PF : ℤ → ℝ → Vec 2 → ∀ v : ι, Fin 2 → h v)
    (hsupp : ∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (hlc : ∀ k ∈ kset, ∀ y, label k t (chart k t y) = y)
    (hcl : ∀ k ∈ kset, ∀ x, chart k t (label k t x) = x)
    (hdet : ∀ k ∈ kset, ∀ y, (jacMatrix (chart k t) y).det = 1)
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hlabel : ∀ k ∈ kset, Differentiable ℝ (label k t))
    (hpres : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D →
      ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ∀ X,
          liftMean (Q k) (Cc k) (fun _ => a₀) r n s X =
            meanApply n (Lb k r n) (fun _ => a₀) s X)
    (hLb : ∀ k ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ∀ s ∈ Set.Icc (s₀ k) (s₁ k), ContDiff ℝ 1 (fun X => Lb k r n d α s X k₀ v u))
    (hPF : ∀ k ∈ kset, ϖ k t ≠ 0 → ∀ (v : ι) (y : Vec 2) (j : Fin 2),
      PF k t y v j = -eulerFlux c ρ εc (N + D) (chart k t) (label k t) (Lb k r)
        (fun y' => a t (chart k t y')) (c⁻¹ * t) v y j)
    (x : Vec 2) (v : ι) :
    gluedMean kset ϖ c ρ εc N r Q Cc chart label a t x v =
      -divE (fun y => ∑ k ∈ kset, ϖ k t • PF k t y v) x := by
  classical
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
    · have hwin := hsupp k hk hϖ
      have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y' => a t (chart k t y')) := ha.comp (hchart k hk)
      have hF : ∀ l : Fin 2, Differentiable ℝ (fun y => chartFlux c ρ εc (N + D) (Lb k r)
          (fun y' => a t (chart k t y')) (c⁻¹ * t) y l v) := fun l =>
        differentiable_chartFlux c ρ εc (N + D) (Lb k r) _ hg (c⁻¹ * t)
          (fun n hn hnM d hd hdn α k₀ v u =>
            hLb k hk n hn hnM d hd hdn α k₀ v u (c⁻¹ * t) hwin) l v
      have hE : ∀ k' : Fin 2, Differentiable ℝ (fun y => eulerFlux c ρ εc (N + D) (chart k t)
          (label k t) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k') := fun k' =>
        differentiable_eulerFlux c ρ εc (N + D) (hchart k hk) (hlabel k hk) (Lb k r) _
          (c⁻¹ * t) v hF k'
      have hmean := pulseMeanField_eq_div_chartFlux c ρ εc hc hρ N r (Q k) (Cc k) (chart k)
        (label k) (Lb k r) (s₀ k) (s₁ k) (hpres k hk) (hLb k hk) a t ha (hchart k hk)
        hwin x v
      have hdiv := div_eulerFlux c ρ εc (N + D) (hchart k hk) (hlabel k hk) (hlc k hk)
        (hcl k hk) (hdet k hk) (Lb k r) (fun y' => a t (chart k t y')) (c⁻¹ * t) v hF x
      refine ⟨?_, fun k' => (hE k' x).const_smul _⟩
      rw [hmean, ← hdiv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [fderiv_fun_const_smul (hE k' x), smul_apply]
  have hglue : gluedMean kset ϖ c ρ εc N r Q Cc chart label a t x v =
      ∑ k ∈ kset, ϖ k t • pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x v := by
    simp only [gluedMean, Finset.sum_apply, Pi.smul_apply]
  have hfun : ∀ k' : Fin 2, (fun y => (∑ k ∈ kset, ϖ k t • PF k t y v) k') =
      fun y => -∑ k ∈ kset, ϖ k t • eulerFlux c ρ εc (N + D) (chart k t) (label k t) (Lb k r)
        (fun y' => a t (chart k t y')) (c⁻¹ * t) v y k' := by
    intro k'
    funext y
    rw [← Finset.sum_neg_distrib, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hϖ : ϖ k t = 0
    · simp [hϖ]
    · rw [Pi.smul_apply, hPF k hk hϖ v y k', smul_neg]
  rw [hglue, Finset.sum_congr rfl fun k hk => (hpulse k hk).1, Finset.sum_comm]
  unfold divE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [hfun k', fderiv_fun_neg, neg_apply, neg_neg,
    fderiv_fun_sum fun k hk => (hpulse k hk).2 k', _root_.sum_apply]

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Bound of the defect integrand with a time-dependent `Fc`** (step (iv) of the conversion).

A version of `defIntegrand_bound` in which the uniform
bound of the retained field is a hypothesis and the bound of `Fc` is its norm at the time `s`:
`|∫ defIntegrand φ s| ≤ (C + 2 ‖Fc v s‖) ‖φ‖`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

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

/-- **Bound of the defect integrand, `L¹` majorant.** -/
theorem DefIntegrandBound
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))} {MW : ℝ}
    (hMW : ∀ s ∈ Set.Icc t₀ t₁, ∀ v, ‖W v s‖ ≤ MW) (v : ι) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc t₀ t₁, ∀ φ : TorusHk 1 (h v),
      Integrable (defIntegrand B b D H AD CE Jm W Fc v φ s)
          (volume.restrict AVenhance.unitCube) ∧
        |∫ x in AVenhance.unitCube, defIntegrand B b D H AD CE Jm W Fc v φ s x| ≤
          (C + 2 * ‖Fc v s‖) * ‖φ‖ := by
  obtain ⟨Cb, hCb⟩ := P.drift_bdd
  obtain ⟨Mj, hMj⟩ := jm_bound P
  set CA : ℝ := ∑ d : Finset.Icc 2 D, coeffSup t₀ t₁ (AD d) 0
  set CC : ℝ := ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
    coeffSup t₀ t₁ (CE r v u d) 0
  refine ⟨2 * Cb * MW + 2 * |B| * MW +
    2 * (dfConst D H (Fintype.card ι) CA CC (Mj + |B|) * MW), fun s hs φ => ?_⟩
  set MF : ℝ := ‖Fc v s‖
  set MZ : ℝ := dfConst D H (Fintype.card ι) CA CC (Mj + |B|) * MW + MF
  have hAD : ∀ d x, ‖AD d s x‖ ≤ CA := fun d x => by
    have h1 : ‖AD d s x‖ ≤ ‖coefficientDerivativeArray (AD d s) 0 x‖ :=
      norm_ordered_le_array (AD d s) 0 Fin.elim0 x
    refine h1.trans ((coeffSup_bound P.rho_pos (P.AD_fin d) (Nat.zero_le _) hs x).trans ?_)
    exact Finset.single_le_sum (f := fun d => coeffSup t₀ t₁ (AD d) 0)
      (fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ d)
  have hCE : ∀ r ∈ Finset.Icc 1 H, ∀ u d x, ‖CE r v u d s x‖ ≤ CC := fun r hr u d x => by
    have h1 : ‖CE r v u d s x‖ ≤ ‖coefficientDerivativeArray (CE r v u d s) 0 x‖ :=
      norm_ordered_le_array (CE r v u d s) 0 Fin.elim0 x
    refine h1.trans ((coeffSup_bound P.rho_pos (P.CE_fin r hr v u d) (Nat.zero_le _) hs x).trans
      ?_)
    have e1 := Finset.single_le_sum (f := fun d => coeffSup t₀ t₁ (CE r v u d) 0)
      (fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ d)
    have e2 := Finset.single_le_sum (f := fun u => ∑ d : Finset.Icc 2 D,
      coeffSup t₀ t₁ (CE r v u d) 0)
      (fun u _ => Finset.sum_nonneg fun d _ => coeffSup_nonneg _ _ _ _) (Finset.mem_univ u)
    have e3 := Finset.single_le_sum (f := fun r => ∑ u : ι, ∑ d : Finset.Icc 2 D,
      coeffSup t₀ t₁ (CE r v u d) 0)
      (fun r _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun d _ =>
        coeffSup_nonneg _ _ _ _) hr
    exact e1.trans (e2.trans e3)
  have hJ : ∀ k' l, |Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l| ≤ Mj + |B| :=
    fun k' l => by
      refine (abs_sub _ _).trans (add_le_add (hMj s hs k' l) ?_)
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg B) ?_
      by_cases hkl : k' = l
      · rw [hkl, Matrix.one_apply_eq, abs_one]
      · rw [Matrix.one_apply_ne hkl, abs_zero]; exact zero_le_one
  obtain ⟨hDFm, hDFb⟩ := coarseDefectFlux_memLp_bound W (by have := P.D_ge; omega)
    (by omega) B AD CE Jm v s hAD hCE hJ (fun w => hMW s hs w)
    (fun d => (P.AD_smooth d s hs).continuous)
    (fun r hr u d => (P.CE_smooth r hr v u d s hs).continuous)
  have hFcm : MemLp (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) 2
      (volume.restrict AVenhance.unitCube) := memLp_jet (Fc v s) _
  have hFcb : (eLpNorm (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ MF :=
    eLpNorm_jet_le (Fc v s) _
  have hcomp : ∀ {G : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {M : ℝ},
      MemLp G 2 (volume.restrict AVenhance.unitCube) →
      (eLpNorm G 2 (volume.restrict AVenhance.unitCube)).toReal ≤ M → ∀ k',
      MemLp (fun x => G x k') 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => G x k') 2 (volume.restrict AVenhance.unitCube)).toReal ≤ M :=
    fun {G M} hG hGb k' => by
      have hm := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => h v) k').comp_memLp' hG
      refine ⟨hm, le_trans (ENNReal.toReal_mono hG.eLpNorm_lt_top.ne
        (eLpNorm_mono hm.aestronglyMeasurable fun x => PiLp.norm_apply_le (G x) k')) hGb⟩
  have hZ : ∀ k', MemLp (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k' +
      (Fc v s).toFunction.jet (valueIndex2 k) x k') 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k' +
        (Fc v s).toFunction.jet (valueIndex2 k) x k') 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ MZ := fun k' => by
    obtain ⟨m1, b1⟩ := hcomp hDFm hDFb k'
    obtain ⟨m2, b2⟩ := hcomp hFcm hFcb k'
    refine ⟨m1.add m2, ?_⟩
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_lt_top.ne, m2.eLpNorm_lt_top.ne⟩)
      (eLpNorm_add_le (by norm_num))).trans ?_
    rw [ENNReal.toReal_add m1.eLpNorm_lt_top.ne m2.eLpNorm_lt_top.ne]
    exact add_le_add b1 b2
  have hK : 1 ≤ k + 1 + D := by omega
  have hJm : ∀ k', MemLp (torusJetOrder (W v s) 1 (fun _ => k')) 2
      (volume.restrict AVenhance.unitCube) := fun k' => memLp_torusJetOrder _ hK _
  have hJb : ∀ k', (eLpNorm (torusJetOrder (W v s) 1 (fun _ => k')) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ MW := fun k' =>
    (eLpNorm_torusJetOrder_le _ hK _).trans (hMW s hs v)
  have hbm : ∀ k', AEStronglyMeasurable (fun x => b s x k')
      (volume.restrict AVenhance.unitCube) := fun k' =>
    ((continuous_apply k').comp (P.drift_smooth s hs).continuous).aestronglyMeasurable
  have hb : ∀ k' x, |b s x k'| ≤ Cb := fun k' x =>
    (norm_le_pi_norm (b s x) k').trans (hCb s hs x)
  rw [defIntegrand_eq_weak]
  obtain ⟨hI, hB⟩ := weakIntegrand_integrable_and_bound hbm hb B hJm hJb (fun k' => (hZ k').1)
    (fun k' => (hZ k').2) (memLp_jet φ _) (eLpNorm_jet_le φ _) (fun k' => memLp_jet φ _)
    (fun k' => eLpNorm_jet_le φ _)
  refine ⟨hI, hB.trans (le_of_eq ?_)⟩
  simp only [MZ]
  ring

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

section
section
/-! **Smoothness of the two readouts of the mean flux split.** At every time of the window
the readout of `rootFluxDefect` (on `c.Gw, c.Gt', x.aZ`) and of `omittedFluxClassical` (on `c.Gt'`,
the retained family, `x.aY`) are `C^{2 p_T}`: the smoothness clause of `MenuMeanFluxSplitStatement`.
Stated generically in `(c, x)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- The readouts that the split of the mean flux uses are `C^{2p_T}` (the smoothness clause of
`MenuMeanFluxSplitStatement`). -/
def ReconReadoutSmoothAt (x : TermResAux c) : Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((2 * A.pT : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux (S := c.Gw.comps) M
      (c.D.eps (M - 1)) A.η₀ (fun _ => True)
      (fun v' s y' => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gw c.Gt' x.aZ v' s y') v t y)) ∧
    ContDiff ℝ ((2 * A.pT : ℕ) : ℕ∞) (fun y => WithLp.ofLp (readoutFlux (S := c.Gw.comps) M
      (c.D.eps (M - 1)) A.η₀ (fun c' => ¬ IsRetained M 1 A.RT c')
      (fun v' s y' => omittedFluxClassical (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr)
        A.φ₀ c.Gt' (c.Gt'.retained M 1 A.RT) x.aY v' s y') v t y))


/-- **Readout smoothness with the prefix.** -/
def TermReconReadoutSmoothStatement : Prop :=
  ReconPrefix (κ := Unit) fun c x _ _ _ => ReconReadoutSmoothAt c x

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The conversion to the coarse defect, in steps**.

From the coarse equation, the letters and the realizations, the defect
`IsCoarseDefect` of the window holds. The route, with one named statement per step:
- `ReconJetsAt` (v): the classical representative `aRep` of `P_pZ` carries the torus jets of
  `reconW` (and of the truncated initial value) up to order `N_T + D_t`;
- `ReconGluedMeanAt` (i): the window's `gluedMean` of grade `r` is `-div` of the menu's glued mean
  flux of grade `r`;
- `ReconMacroSwapAt` (ii): the macro flux of the menu is replaced by the letters' flux against smooth
  periodic tests (equal divergences, `IsMeanPresentation`, integration by parts on the torus);
- `ReconMeanFluxAt` (iii): `F_mean = F_cov - F_filter - F_front` (`menuMeanFluxSplit`) and the
  realizations, almost everywhere on the cell;
- `ReconTransferAt`: the coarse equation, with (v), (ii), (iii), is the smooth-test form of the
  defect of `reconW`;
- `ReconDensityAt` (iv): smooth periodic tests are extended to first-order tests by Galerkin density
  (as in `coarseDefect_of_witness`).

Degenerate cases:
- `p_T = 0`: `P_p = I`, the split of (iii) is the definition.
- A weak stage without edges: `CE = 0`, only the diagonal part enters (ii).
- `F1 = F2 = F3 = 0` with zero flux pieces: (iii) reads `F_mean = 0` almost everywhere. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section Steps

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **(v) The jets of `aRep`.** On the window `[t_p, a + T₀]` the classical representative `aRep`
of `P_pZ` is a classical representative of `reconW` to the order `N_T + D_t`, and at `t_p` of the
truncated initial value (order `0`, when the window is not empty). -/
def ReconJetsAt (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    IsClassicalRep (reconW c kc hW v t) (fun y => c.aRep t y v) (A.NT + A.Dt)) ∧
  (c.tp ≤ c.a + A.T₀ →
    ∀ v, IsClassicalRep (truncateTorusHk hf (c.PZ v c.tp)) (fun y => c.aRep c.tp y v) 0)

/-- **(i) The glued mean of grade `r` is the divergence of the menu's glued mean flux**: for
smooth periodic fields, `t` in the window, with the degrees `2..N_T + 1` at grade `0` and
`2..N_T + D_t` at the grades `r ≥ 1`. -/
def ReconGluedMeanAt (r : ℕ) : Prop :=
  ∀ a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root,
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
    ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ (y : Vec 2) (v : CompIn c.Gw.comps),
      gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
        (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT r
        (fun k => rLiftData c k) c.CcT
        (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)) a t y v =
        -divE (fun z => menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {r}
          (if r = 0 then Finset.Icc 2 (A.NT + 1) else Finset.Icc 2 (A.NT + A.Dt)) c.CcT a t z v) y

/-- The conclusion of (ii): the macro flux of the menu on `aRep` and the letters' flux on `reconW`
are integrable against every smooth periodic test and have the same pairing, at every time of the
window. -/
def ReconMacroSwapConc (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) : Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c),
    ∀ φ : Vec 2 → ScalarH v.1.root, ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
    let Pm : Vec 2 → ℝ := fun y => ∑ k : Fin 2, inner ℝ (toFluxL (menuMacroFlux
      (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep v s y) k) (gradE φ y k)
    let Pc : Vec 2 → ℝ := fun y => ∑ k : Fin 2, inner ℝ (AVRegularity.coarseDefectFlux
      (c.D.κ (M - 1)) (A.NT + A.Dt) A.dW AD CE (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (reconW c kc hW) v s y k) (gradE φ y k)
    Integrable Pm (volume.restrict unitCube) ∧ Integrable Pc (volume.restrict unitCube) ∧
      ∫ y in unitCube, Pm y = ∫ y in unitCube, Pc y

/-- **(ii) The macro flux is replaced by the letters' flux** (equal divergences by
`IsMeanPresentation` and (i), integration by parts on the torus; the field `aRep` has finite
regularity, the mean presentation is for smooth fields: approximation in `C^{N_T + D_t}`). -/
def ReconMacroSwapAt (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT) : Prop :=
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc →
    (∀ r ∈ Finset.range (A.dW + 1), ReconGluedMeanAt c r) → ReconJetsAt c kc hW hf →
    ReconMacroSwapConc c kc hW AD CE

/-- The conclusion of (iii): the coarse flux `F_c` is the mean flux of the menu a.e. on the cell. -/
def ReconMeanFluxConc (x : TermResAux c) (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    (reconFc c F1 F2 F3 v t).toFunction.jet (valueIndex2 kc) =ᵐ[volume.restrict unitCube]
      fun y => toFluxL (menuMeanFluxF (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ
        (upsilonFlux (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt'
          (c.Gt'.retained M 1 A.RT) M 1 A.RT (c.D.eps (M - 1)) A.η₀ x.aZ x.aY) v t y)

/-- **(iii) The split of the mean flux and the realizations.** -/
def ReconMeanFluxAt (x : TermResAux c) (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ReconFluxRealizations c x kc F1 F2 F3 → ReconReadoutSmoothAt c x →
    ReconMeanFluxConc c x kc F1 F2 F3

/-- The smooth-test form of the defect of `reconW`: the integrated identity of `IsCoarseDefect`
against smooth periodic tests, in the form of `CycleComparison/Coarse/Defect`. -/
def ReconSmoothDefect (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) : Prop :=
  ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
    ∀ ψ : Vec 2 → ScalarH v.1.root, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    IntegrableOn (fun s => ∫ y in unitCube, wIntegrand (c.D.κ (M - 1))
        (streamVel (c.D.Φ (M - 1))) (A.NT + A.Dt) A.dW AD CE
        (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (reconW c kc hW) (reconFc c F1 F2 F3)
        v ψ s y) (Set.Ioc c.tp t) ∧
    cellInner (tval (reconW c kc hW v t)) ψ -
        cellInner (fun y => (truncateTorusHk hf (c.PZ v c.tp)).toFunction.jet
          (valueIndex2 (rNc A kc)) y) ψ =
      ∫ s in Set.Ioc c.tp t, ∫ y in unitCube, wIntegrand (c.D.κ (M - 1))
        (streamVel (c.D.Φ (M - 1))) (A.NT + A.Dt) A.dW AD CE
        (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (reconW c kc hW) (reconFc c F1 F2 F3)
        v ψ s y

/-- **(vi) The transfer.** The coarse equation, the jets (v), the swap (ii) and the mean flux
(iii) give the smooth-test defect of `reconW` (a.e. rewriting of the integrands; the integrability
of the letters' flux terms comes from the coarse setting). -/
def ReconTransferAt (x : TermResAux c) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc →
    TermCoarseWeakAt c x → ReconJetsAt c kc hW hf → ReconMacroSwapConc c kc hW AD CE →
    ReconMeanFluxConc c x kc F1 F2 F3 → ReconSmoothDefect c kc hW hf F1 F2 F3 AD CE

/-- **(iv) Density.** Smooth periodic tests are extended to first-order tests (the Galerkin
projections converge, both sides are bounded in the test: the argument of
`coarseDefect_of_witness`, with the bounds taken from the coarse setting). -/
def ReconDensityAt (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ReconTimeRegAt c kc hW F1 F2 F3 →
  ∀ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ) (Cstar Θc : ℝ),
    ReconLettersBody c kc aC B₀C lamC AD CE Aedge Cstar Θc →
    ReconSmoothDefect c kc hW hf F1 F2 F3 AD CE →
    IsCoarseDefect c.tp (c.tp + rTobs c) (c.D.κ (M - 1)) (streamVel (c.D.Φ (M - 1)))
      (A.NT + A.Dt) A.dW kc (kc + (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4)) AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (fun v => truncateTorusHk hf (c.PZ v c.tp)) (reconW c kc hW) (reconFc c F1 F2 F3)

/-- The steps of the conversion at a context. -/
def ReconDefectStepsAt (x : TermResAux c) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ReconJetsAt c kc hW hf ∧ (∀ r ∈ Finset.range (A.dW + 1), ReconGluedMeanAt c r) ∧
    ReconMacroSwapAt c kc hW hf ∧ ReconMeanFluxAt c x kc F1 F2 F3 ∧
    ReconTransferAt c x kc hW hf F1 F2 F3 ∧ ReconDensityAt c kc hW hf F1 F2 F3

/-- **The conversion with two extra hypotheses** (readout smoothness, time regularity):
the statement `ReconDefectConvAt` that is used. -/
def ReconDefectConvPlusAt (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    Prop :=
  ReconReadoutSmoothAt c x → ReconDefectConvAt c x kc ℓ hW hf F1 F2 F3

/-- **The conversion (plus) at a context from its steps.** -/
theorem reconDefectConvPlusAt_of_steps (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (h : ReconDefectStepsAt c x kc hW hf F1 F2 F3) :
    ReconDefectConvPlusAt c x kc ℓ hW hf F1 F2 F3 := by
  obtain ⟨hV, hG, hS, hM, hT, hDn⟩ := h
  intro hRs hWk hreal hTR _ _ _ _ _ _ _ aC B₀C lamC AD CE Aedge Cstar Θc hlet
  exact hDn hTR aC B₀C lamC AD CE Aedge Cstar Θc hlet
    (hT aC B₀C lamC AD CE Aedge Cstar Θc hlet hWk hV
      (hS aC B₀C lamC AD CE Aedge Cstar Θc hlet hG hV) (hM hreal hRs))

end Steps

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The glued mean (step (i)), split**.

`ReconGluedMeanAt` needs two premises that the context does not carry: the menu
`A.Mt M sXT sZT c.tp cr` has slow length factor `cr`, the window's `gluedMean` has the factor `1` (`rRho c`), and
`cr = 1` is a field of `TermResAux c` (`x.one`), not of the context; moreover the grade-zero degree
range `2..N_T + 1` is the full range `2..N_T + D_t` only if the degree-`(N_T + 2)` flux vanishes,
which needs `1 ≤ N_T` (mean-zero correctors).

The statement `ReconGluedMeanFix` has the premises `cr = 1`, `1 ≤ N_T`; it is assembled
from
- `ReconGluedMeanCore c r`: the identity over the full degrees `2..N_T + D_t`, at every grade (the
  divergence form of the pulse means, with the lift data of the window against the family's);
- `ReconGradeZeroTail c`: the glued mean flux of grade `0` has no degrees `N_T + 2..N_T + D_t`.

Degenerate cases:
- `r ≥ 1`: the core is the statement.
- `D_t = 1`: the tail is empty. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section GluedMean

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The core of (i)**: at `cr = 1` the glued mean of the window of grade `r` is
`-div` of the menu's glued mean flux over the full degrees `2..N_T + D_t`. -/
def ReconGluedMeanCore (r : ℕ) : Prop :=
  cr = 1 →
  ∀ a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root,
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
    ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ (y : Vec 2) (v : CompIn c.Gw.comps),
      gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
        (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT r
        (fun k => rLiftData c k) c.CcT
        (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)) a t y v =
        -divE (fun z => menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {r}
          (Finset.Icc 2 (A.NT + A.Dt)) c.CcT a t z v) y

/-- **The grade-zero tail**: for `1 ≤ N_T` the degrees `N_T + 2..N_T + D_t` of the
grade-zero glued mean flux vanish (`C_n = 0` for `n > N_T` by `IsLiftSequence`; the degree
`N_T + 2` flux is `-η G ∇ P₀ C_{N_T} a`, and `P₀ C_{N_T} a = 0`). -/
def ReconGradeZeroTail : Prop :=
  1 ≤ A.NT →
  ∀ a : ℝ → Vec 2 → ∀ v : CompIn c.Gw.comps, ScalarH v.1.root,
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
    ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ (z : Vec 2) (v : CompIn c.Gw.comps),
      menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0} (Finset.Icc 2 (A.NT + A.Dt))
          c.CcT a t z v =
        menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0} (Finset.Icc 2 (A.NT + 1))
          c.CcT a t z v

/-- **(i) with the premises** `cr = 1` and `1 ≤ N_T`. -/
def ReconGluedMeanFix (r : ℕ) : Prop :=
  cr = 1 → 1 ≤ A.NT → ReconGluedMeanAt c r

/-- **(i) from the core and the tail.** -/
theorem reconGluedMeanFix_of_core (r : ℕ) (hcore : ReconGluedMeanCore c r)
    (htail : ReconGradeZeroTail c) : ReconGluedMeanFix c r := by
  intro hcr hN
  unfold ReconGluedMeanAt
  intro a ha hper t ht y v
  have h := hcore hcr a ha hper t ht y v
  rw [h]
  by_cases hr : r = 0
  · subst hr
    simp only [ite_true]
    have hf : (fun z => menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0}
        (Finset.Icc 2 (A.NT + A.Dt)) c.CcT a t z v) = fun z =>
        menuGluedMeanFlux (A.Mt M sXT sZT c.tp cr) c.Gw M {0} (Finset.Icc 2 (A.NT + 1)) c.CcT a t z v :=
      funext fun z => htail hN a ha hper t ht z v
    rw [hf]
  · simp only [hr, ite_false]

end GluedMean

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Step (v) of the conversion: the jets of `aRep`.** The classical representative `aRep` of `P_pZ`
(`c.lift`, third clause of `IsTerminalLiftedField`) is a classical representative of every
truncation of `P_pZ`, to the order of the truncation (`classicalRep_truncate`).

Degenerate cases:
- `kc = 0`, `N_T + D_t = 0`: orders `1` and `0`.
- `hW` and `hf` at equality: no loss of order. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- A classical representative to a lower order. -/
theorem rdJets_classicalRep_mono {K r r' : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {W : TorusHk K E}
    {a : Vec 2 → E} (h : IsClassicalRep W a r) (hr : r' ≤ r) : IsClassicalRep W a r' :=
  ⟨hr.trans h.1, h.2.1.of_le (by exact_mod_cast hr), h.2.2.1,
    fun m hm w => h.2.2.2 m (hm.trans hr) w⟩

/-- **Step (v) at every context.** -/
theorem reconJetsAt_of_ctx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT) :
    ReconJetsAt c kc hW hf := by
  refine ⟨fun v t ht => ?_, fun hle v => ?_⟩
  · exact Construction.Preservation.FullLift.classicalRep_truncate hW (by omega) (c.PZ v t)
      (fun y => c.aRep t y v)
      (rdJets_classicalRep_mono (c.lift.2.1 v t ht).2 (by omega))
  · refine Construction.Preservation.FullLift.classicalRep_truncate hf (Nat.zero_le _) (c.PZ v c.tp)
      (fun y => c.aRep c.tp y v)
      (rdJets_classicalRep_mono (c.lift.2.1 v c.tp ⟨le_rfl, hle⟩).2 (Nat.zero_le _))

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end

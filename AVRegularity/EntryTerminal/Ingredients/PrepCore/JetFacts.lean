-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Entry.TerminalResidualClauses

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.EntryTerminal.Ingredients

/-! **Congruence of the coupled weak identity** (E2, `PrepCorePart`). The identity is a statement
about its data `u₀, f` and the time integral of its right-hand side. If two right-hand sides agree at
almost every time of `(t₀, t]` and the new one is integrable in space at every time, the identity
transfers.

Special cases:
- Equal right-hand sides: the identity itself.
- `t = t₀`: an empty time interval. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The right-hand side of `CoupledWeakIdentity` (its `let`). -/
def cwiRhs (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) : ℝ → Vec 2 → ℝ := fun s x =>
  -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
    - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
    - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
    + inner ℝ (g s x) (φ x)

theorem coupledWeakIdentity_iff {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H} :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g ↔
      (Integrable (fun x => inner ℝ (u₀ x) (φ x)) μ ∧
        Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
        (∀ s ∈ Set.Ioc t₀ t, Integrable (cwiRhs ν v φ dφ du flux F g s) μ) ∧
        IntegrableOn (fun s => ∫ x, cwiRhs ν v φ dφ du flux F g s x ∂μ) (Set.Ioc t₀ t) ∧
        ∫ x, inner ℝ (u₀ x) (φ x) ∂μ - ∫ x, inner ℝ (f x) (φ x) ∂μ =
          ∫ s in Set.Ioc t₀ t, ∫ x, cwiRhs ν v φ dφ du flux F g s x ∂μ) :=
  Iff.rfl

/-- **Transfer of the coupled weak identity** to a right-hand side equal at almost every time and
integrable at every time. -/
theorem coupledWeakIdentity_congr {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du du' : ℝ → Fin 2 → Vec 2 → H}
    {flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g g' : ℝ → Vec 2 → H}
    (h : CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g)
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)),
      cwiRhs ν v φ dφ du' flux' F' g' s = cwiRhs ν v φ dφ du flux F g s)
    (hint : ∀ s ∈ Set.Ioc t₀ t, Integrable (cwiRhs ν v φ dφ du' flux' F' g' s) μ) :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du' flux' F' g' := by
  rw [coupledWeakIdentity_iff] at h ⊢
  obtain ⟨h1, h2, -, h4, h5⟩ := h
  have hae' : (fun s => ∫ x, cwiRhs ν v φ dφ du' flux' F' g' s x ∂μ) =ᵐ[volume.restrict
      (Set.Ioc t₀ t)] fun s => ∫ x, cwiRhs ν v φ dφ du flux F g s x ∂μ := by
    filter_upwards [hae] with s hs
    rw [hs]
  refine ⟨h1, h2, hint, h4.congr_fun_ae hae'.symm, ?_⟩
  rw [h5]
  exact (integral_congr_ae hae').symm

/-- Pointwise equal data at one time give equal right-hand sides there. -/
theorem cwiRhs_congr_at {ν : ℝ} {v : ℝ → Vec 2 → Vec 2} {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H}
    {du du' : ℝ → Fin 2 → Vec 2 → H} {flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)}
    {g g' : ℝ → Vec 2 → H} (s : ℝ) (hdu : ∀ m x, du' s m x = du s m x)
    (hflux : ∀ x, flux' s x = flux s x) (hF : ∀ x, F' s x = F s x) (hg : ∀ x, g' s x = g s x) :
    cwiRhs ν v φ dφ du' flux' F' g' s = cwiRhs ν v φ dφ du flux F g s := by
  funext x
  simp only [cwiRhs, hdu, hflux, hF, hg]

/-- A right-hand side whose data vanish almost everywhere at one time is integrable there. -/
theorem cwiRhs_integrable_of_ae_zero {μ : Measure (Vec 2)} {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H} (s : ℝ)
    (hdu : ∀ m, du s m =ᵐ[μ] 0) (hflux : flux s =ᵐ[μ] 0) (hF : F s =ᵐ[μ] 0) (hg : g s =ᵐ[μ] 0) :
    Integrable (cwiRhs ν v φ dφ du flux F g s) μ := by
  refine (integrable_zero (Vec 2) ℝ μ).congr ?_
  filter_upwards [hdu 0, hdu 1, hflux, hF, hg] with x h0 h1 hfl hF' hg'
  have hdx : ∀ m : Fin 2, du s m x = 0 := fun m => by
    fin_cases m
    · exact h0
    · exact h1
  simp only [Pi.zero_apply] at hfl hF' hg'
  simp [cwiRhs, hdx, hfl, hF', hg']

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Analysis.Convolution
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The paired kernel of width zero is the identity** (`PrepCorePart`). At width
`r = 0` both displacements vanish. Each periodic average is then `(∫ k_n) · id = id` for a
mass-one template (`integral_momentKernel`). So the identity-kernel paired weak solution `U` of
`IsWeakPaired` solves the plain coupled system.

For every order `n` the moment kernel has mass one, and for every time `t` and matrices `H_i(t)`
the displacement `0 • H` is zero. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] in
/-- A periodic average with zero displacement and a mass-one kernel is the identity. -/
theorem periodicComponentAverage_zero {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (r : ℝ) (hr : r = 0) (H : Vec 2 →L[ℝ] Vec 2) (hc : Continuous (displacement r H))
    (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    periodicComponentAverage (E := E) (displacement r H) hc κ hκ f = f := by
  subst hr
  have hρ : torusQuotient.comp (displacement 0 H) = 0 := by
    ext z
    simp [displacement_apply]
  unfold periodicComponentAverage
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have hav : averagingOperator (torusQuotient.comp (displacement 0 H))
      (continuous_torusQuotient.comp hc) κ hκ
      (cellToTorus.toContinuousLinearMap f) = cellToTorus.toContinuousLinearMap f := by
    rw [averagingOperator_apply]
    simp only [hρ, AddMonoidHom.zero_apply, translation_zero]
    rw [integral_smul_const, hmass, one_smul]
  rw [hav]
  exact torusToCell_cellToTorus f

/-- **The zero-width paired kernel is the identity** for a mass-one template. -/
theorem isoPairedKernel_zero_op {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1)
    (n : ℕ+) (t : ℝ) :
    (isoPairedKernel 0 n).op φ₀ hφ₀ (E := E) t = ContinuousLinearMap.id ℝ _ := by
  ext1 f
  have hk := integral_momentKernel hφ₀ hmass (isoPairedKernel 0 n).order
  simp only [KernelSpec.op, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [periodicComponentAverage_zero _ hk (isoPairedKernel 0 n).width rfl,
    periodicComponentAverage_zero _ hk (isoPairedKernel 0 n).width rfl]

end AVRegularity.EntryTerminal.Ingredients
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients

/-! **Jet facts for the plain coupled system** (E2, `PrepCorePart`).
- The canonical representative of a jet depends only on its `L²` component. So truncation commutes
  with `toFunction.jet` definitionally.
- The jets of `0` vanish almost everywhere.
- Torus elements with equal values have equal jets at every common order (`TorusHk.ext_value`).
- A sum over a subtype splits along a filter when the other terms vanish.

Special cases:
- `m = 0`: the value index.
- An empty filter: both sums are `0`. -/

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem toFunction_jet_truncate {K L : ℕ} (h : K ≤ L) (X : TorusHk L E) (a : JetIndex2 K) :
    (truncateTorusHk h X).toFunction.jet a = X.toFunction.jet (truncateJetIndex h a) := rfl

/-- The jets of `0` vanish almost everywhere. -/
theorem torusHk_zero_jet_ae {m : ℕ} (a : JetIndex2 m) :
    (0 : TorusHk m E).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube] 0 :=
  (periodicJetRepresentative_ae (0 : TorusHk m E).val a).trans (Lp.coeFn_zero _ _ _)

/-- **Equal values give equal jets** at every common order. -/
theorem torusHk_jet_eq_of_value [FiniteDimensional ℝ E] {L₁ L₂ m : ℕ} {Y : TorusHk L₁ E}
    {Z : TorusHk L₂ E} (hv : Y.val (valueIndex2 L₁) = Z.val (valueIndex2 L₂)) (h1 : m ≤ L₁)
    (h2 : m ≤ L₂) (p1 : m < L₁ + 1) (p2 : m < L₂ + 1) (word : DerivativeWord2 m) :
    Y.toFunction.jet ⟨⟨m, p1⟩, word⟩ = Z.toFunction.jet ⟨⟨m, p2⟩, word⟩ := by
  have he : truncateTorusHk h1 Y = truncateTorusHk h2 Z := TorusHk.ext_value (by exact hv)
  exact congrArg (fun T : TorusHk m E => T.toFunction.jet ⟨⟨m, Nat.lt_succ_self m⟩, word⟩) he

end Jets

/-- A sum over a subtype splits along a filter when the other terms vanish. -/
theorem sum_subtype_filter_eq {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] (f : ↥s → M) (hf : ∀ d : ↥s, ¬ p d.1 → f d = 0) :
    ∑ d : ↥s, f d = ∑ d : ↥(s.filter p), f ⟨d.1, (Finset.mem_filter.mp d.2).1⟩ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d : ↥s => p d.1),
    Finset.sum_eq_zero (s := Finset.univ.filter (fun d : ↥s => ¬ p d.1))
      (fun d hd => hf d (Finset.mem_filter.mp hd).2), add_zero]
  exact Finset.sum_bij' (fun d hd => ⟨d.1, Finset.mem_filter.mpr ⟨d.2, (Finset.mem_filter.mp hd).2⟩⟩)
    (fun d _ => ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) (fun _ _ => Finset.mem_univ _)
    (fun d _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp d.2).2⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end AVRegularity.EntryTerminal.Ingredients
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncFluxOperator
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Construction.Stream.NextAdmissible

section
section
/-! **Continuity in a parameter for formal adjoints between two spaces**.

`AdjCont` is stated for operators `(Vec 2 → E) → (Vec 2 → E)`. The commutator
adjoint passes through the space `PiLp 2 (Fin 2 → E)` of gradients, so the closure lemmas are
needed for operators between two spaces: `AdjCont2` is the same statement for
`T : S → (Vec 2 → F) → (Vec 2 → E)`; for `F = E` it is `AdjCont`.

Degenerate cases:
- A constant family is continuous (`AdjCont2.constAny`).
- For `F = E` the notion is `AdjCont` (the two definitions agree). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp

namespace AVRegularity.EntryTerminal.CovComm

section Cont

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  {S : Type*} [TopologicalSpace S]

/-- The adjoint maps of a family of structures vary continuously in operator norm. -/
def AdjCont2 {T : S → (Vec 2 → F) → (Vec 2 → E)} {m R Kc : ℕ} {C : S → ℝ}
    (A : ∀ s, TorusAdj (T s) m R Kc (C s)) : Prop :=
  ∀ K (hK : K + m ≤ Kc), Continuous fun s => (A s).adj K hK

theorem AdjCont2.constAny {T0 : (Vec 2 → F) → (Vec 2 → E)} {m R Kc : ℕ} {C0 : ℝ}
    (A : TorusAdj T0 m R Kc C0) : AdjCont2 (S := S) (fun _ => A) := fun _ _ => continuous_const

section Ops

variable {T T' : S → (Vec 2 → F) → (Vec 2 → E)} {m m' R R' Kc Kc' : ℕ} {C C' : S → ℝ} {C0 : ℝ}

theorem commAdj2_adj_ofOp {T0 T0' : (Vec 2 → F) → (Vec 2 → E)} (h : T0 = T0')
    (A : TorusAdj T0 m R Kc C0) (K : ℕ) (hK : K + m ≤ Kc) :
    (A.ofOp h).adj K hK = A.adj K hK := by
  subst h; rfl

theorem commAdj2_adj_ofOrder {T0 : (Vec 2 → F) → (Vec 2 → E)} (h : m = m')
    (A : TorusAdj T0 m R Kc C0) (K : ℕ) (hK : K + m' ≤ Kc) :
    (A.ofOrder h).adj K hK =
      (A.adj K (by omega)).comp (torusCast (by omega : K + m' = K + m)) := by
  subst h; rfl

theorem commAdj2_adj_sumMem {ι : Type*} (s0 : Finset ι) {T0 : ι → (Vec 2 → F) → (Vec 2 → E)}
    {C0 : ι → ℝ} (A : ∀ i ∈ s0, TorusAdj (T0 i) m R Kc (C0 i)) (K : ℕ) (hK : K + m ≤ Kc) :
    (TorusAdj.sumMem s0 A).adj K hK = ∑ i : s0, (A i.1 i.2).adj K hK := by
  unfold TorusAdj.sumMem
  rw [commAdj2_adj_ofOp]
  rfl

theorem AdjCont2.ofOp (h : ∀ s, T s = T' s) {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont2 A) : AdjCont2 (fun s => (A s).ofOp (h s)) := by
  intro K hK
  simp only [commAdj2_adj_ofOp]
  exact hA K hK

theorem AdjCont2.ofOrder (h : m = m') {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont2 A) : AdjCont2 (fun s => (A s).ofOrder h) := by
  intro K hK
  simp only [commAdj2_adj_ofOrder]
  exact (hA K (by omega)).clm_comp continuous_const

theorem AdjCont2.mono (hR : R' ≤ R) (hKc : Kc' ≤ Kc) (hC : ∀ s, C s ≤ C' s)
    {A : ∀ s, TorusAdj (T s) m R Kc (C s)} (hA : AdjCont2 A) :
    AdjCont2 (fun s => (A s).mono hR hKc (hC s)) := fun K hK => hA K (hK.trans hKc)

theorem AdjCont2.liftOrder (hm : m ≤ m') {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont2 A) : AdjCont2 (fun s => (A s).liftOrder hm) := fun K hK =>
  (hA K (by omega)).clm_comp continuous_const

theorem AdjCont2.smul (c : S → ℝ) (hc : Continuous c) {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont2 A) : AdjCont2 (fun s => (A s).smul (c s)) := fun K hK =>
  ((continuous_torusSmulCLM.comp hc)).clm_comp (hA K hK)

theorem AdjCont2.neg {A : ∀ s, TorusAdj (T s) m R Kc (C s)} (hA : AdjCont2 A) :
    AdjCont2 (fun s => (A s).neg) := fun K hK => covOp_continuous_clmNeg _ (hA K hK)

theorem AdjCont2.comp {m₁ m₂ R₁ R₂ : ℕ} {T₁ : S → (Vec 2 → G) → (Vec 2 → E)}
    {T₂ : S → (Vec 2 → F) → (Vec 2 → G)} {C₁ C₂ : S → ℝ}
    {A₁ : ∀ s, TorusAdj (T₁ s) m₁ R₁ Kc (C₁ s)} {A₂ : ∀ s, TorusAdj (T₂ s) m₂ R₂ Kc (C₂ s)}
    (hA₁ : AdjCont2 A₁) (hA₂ : AdjCont2 A₂) (hR₁ : R ≤ R₁) (hR₂ : R + m₁ ≤ R₂) :
    AdjCont2 (fun s => (A₁ s).comp (A₂ s) hR₁ hR₂) := fun K hK =>
  (hA₂ K (by omega)).clm_comp ((hA₁ (K + m₂) (by omega)).clm_comp continuous_const)

theorem AdjCont2.sum {ι : Type*} (s0 : Finset ι) {T : S → ι → (Vec 2 → F) → (Vec 2 → E)}
    {C : S → ι → ℝ} {A : ∀ s, ∀ i, TorusAdj (T s i) m R Kc (C s i)}
    (hA : ∀ i, AdjCont2 (fun s => A s i)) :
    AdjCont2 (fun s => TorusAdj.sum s0 (A s)) := fun K hK =>
  covOp_continuous_clmSum _ _ fun i => hA i K hK

theorem AdjCont2.sumMem {ι : Type*} (s0 : Finset ι) {T : S → ι → (Vec 2 → F) → (Vec 2 → E)}
    {C : S → ι → ℝ} {A : ∀ s, ∀ i ∈ s0, TorusAdj (T s i) m R Kc (C s i)}
    (hA : ∀ i hi, AdjCont2 (fun s => A s i hi)) :
    AdjCont2 (fun s => TorusAdj.sumMem s0 (A s)) := by
  intro K hK
  simp only [commAdj2_adj_sumMem]
  exact covOp_continuous_clmSum _ (fun (i : s0) x => (A x i.1 i.2).adj K hK) fun i =>
    hA i.1 i.2 K hK

end Ops

end Cont

end AVRegularity.EntryTerminal.CovComm
end
end

section
/-! # The fine matrix tail: the named steps and the assembly at a context

The route is split
at the classical field `û = termLiftedRep …` of the lifted field:

* **Lift step** (`FineLiftAt`, terminal specific; needs the represented terminal lift
  `terminal_lift_rep` and the strong energy of `P_pZ`): `û` has a torus Sobolev
  representative `Û` of the order `K_f + 1`, `K_f = k₀ + L_f + D_t`, on the window, with the coarse
  energy `(ν ∫_I |∇Û|²_{r_*,K_f;π})^{1/2} ≤ C‖f‖₂` (the terminal conversion).
* **Defect step** (`FineDefectAt`, generic in the weak stage): any such representative with energy
  `≤ E` gives a realization of the fine flux `fineFluxF` of order `k₀` with
  `(ν⁻¹ ∫_I ‖·‖²_{r_*,k₀;π})^{1/2} ≤ C · (C_χ x^{χ_w}) · (r_w / r_*)^{L_f} · E`. The coefficients enter
  through the Schur bound of the stage invariant (`kernelSchurMatrix`, `θ_K = C_χ x^{χ_w}`), the
  kernel through the moment bound of the defect (`momentKernel_paired_spatial_approximation_torus`).
  It is the defect version of `kernel_flux_bound_torus`.

`termFineTailAt_of_lift_defect` assembles them at a context with arithmetic only. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section Steps

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- The Sobolev order of the representative of `û`: `k₀ + L_f + D_t`. -/
def fineOrder : ℕ := A.k₀ + A.LfT + A.Dt

/-- `Û` is a torus Sobolev representative of the lifted field `û` of order `K_f + 1` on the
window: square integrable in time, and at every time of the window its value jet is the classical
lifted field almost everywhere on the cell. -/
def FineLiftRealization (Û : ∀ v : CompIn c.Gw.comps, ℝ →
    TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root)) : Prop :=
  (∀ v, MemLp (Û v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    (Û v t).toFunction.jet (valueIndex2 (fineOrder (A := A) + 1)) =ᵐ[volume.restrict unitCube]
      fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v) ∧
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((fineOrder (A := A) + 1 : ℕ) : ℕ∞)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v) ∧
      IsZ2Periodic
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v))

/-- The coarse energy of the representative: `t ↦ |∇Û|²_{r_*,K_f;π}` is integrable on the window
(a Bochner integral of a non-integrable function is `0`) and `(ν ∫_I |∇Û|²_{r_*,K_f;π})^{1/2} ≤ E`. -/
def FineLiftEnergyLe (Û : ∀ v : CompIn c.Gw.comps, ℝ →
    TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root)) (E : ℝ) : Prop :=
  Integrable (fun s => massGradNormSq (E := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      (K := fun _ => fineOrder (A := A)) (c.D.termRStar cK M) (c.Gw.mass c.lawW)
      (fun v => (Û v s).val)) (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) ∧
  Real.sqrt (c.D.termNu M * ∫ s in Set.Icc c.tp (c.a + A.T₀),
    massGradNormSq (E := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      (K := fun _ => fineOrder (A := A)) (c.D.termRStar cK M) (c.Gw.mass c.lawW)
      (fun v => (Û v s).val)) ≤ E

/-- **Lift step at a context** (terminal specific): the lifted field has a
representative with the coarse energy `≤ C‖f‖₂`, from the full ordered lift (`terminal_lift_rep`),
the terminal conversion and the energy step of the reconstruction. -/
def FineLiftAt (_x : TermResAux c) (C : ℝ) : Prop :=
  ∃ Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root),
    FineLiftRealization c Û ∧ FineLiftEnergyLe c Û (C * c.normF)

/-- **Defect step at a context** (generic in the weak stage): from a representative of
the lifted field with energy `≤ E`, the fine flux `∑ 𝖠 ∇^{d-1}(I - S_w)û` has a realization of
order `k₀` with `(ν⁻¹∫_I ‖·‖²_{r_*,k₀;π})^{1/2} ≤ C · (C_χ x^{χ_w}) · (r_w/r_*)^{L_f} · E`.
The prerequisites in the context: the stage invariant of `c.weak` at `θ_K = C_χ x^{χ_w}` (Schur
bound, kernels `S_w` with width `r_w = x^{1+σ_w}`), the moment order `L_f + 1 ≤ 2 n_W`
(`IsTerminalKernelOrders`), `c_K = kW.c₀` and the cap `Pe_M ≤ 1` (so that
`rhoStar D c_K M = r_*`; this holds above a threshold in `M`). -/
def FineDefectAt (_x : TermResAux c) (C : ℝ) : Prop :=
  ∀ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (E : ℝ), FineLiftRealization c Û → FineLiftEnergyLe c Û E →
    FineTailBound c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT
      A.dW A.k₀ c.CcT c.aRep (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (C * (|Cχ| * c.D.eps M ^ A.χw) * (c.D.termRW A.σw M / c.D.termRStar cK M) ^ A.LfT * E)

/-- The price of the two steps is the fine bill: arithmetic of the exponents,
`(C_χ x^{χ_w}) (x^{1+σ_w}/(c_K x))^{L_f} = C_χ c_K^{-L_f} x^{χ_w + σ_w L_f}`. -/
theorem fineStep_price_le (heps : 0 < c.D.eps M) (hcK : 0 < cK) {C₁ C₂ C : ℝ} (_hC₁ : 0 ≤ C₁)
    (_hC₂ : 0 ≤ C₂) (hC : C₂ * C₁ * |Cχ| / cK ^ A.LfT ≤ C) :
    C₂ * (|Cχ| * c.D.eps M ^ A.χw) * (c.D.termRW A.σw M / c.D.termRStar cK M) ^ A.LfT *
        (C₁ * c.normF) ≤ C * c.fineBill * c.normF := by
  set e := c.D.eps M with he
  have h1 : c.D.termRW A.σw M / c.D.termRStar cK M = e ^ A.σw / cK := by
    unfold OCData.termRW OCData.termRStar
    rw [← he, Real.rpow_add heps, Real.rpow_one]
    field_simp
  have h2 : (e ^ A.σw / cK) ^ A.LfT = e ^ (A.σw * (A.LfT : ℝ)) / cK ^ A.LfT := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul heps.le]
  have h3 : c.fineBill = e ^ A.χw * e ^ (A.σw * (A.LfT : ℝ)) := by
    unfold TermResCtx.fineBill
    rw [← he, Real.rpow_add heps]
  have hcp : 0 < cK ^ A.LfT := pow_pos hcK _
  have hP : 0 ≤ e ^ A.χw * e ^ (A.σw * (A.LfT : ℝ)) := by positivity
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hq : C₂ * C₁ * |Cχ| / cK ^ A.LfT ≤ C := hC
  rw [h1, h2, h3]
  calc C₂ * (|Cχ| * e ^ A.χw) * (e ^ (A.σw * (A.LfT : ℝ)) / cK ^ A.LfT) * (C₁ * c.normF)
      = (C₂ * C₁ * |Cχ| / cK ^ A.LfT) * (e ^ A.χw * e ^ (A.σw * (A.LfT : ℝ))) * c.normF := by
        field_simp
    _ ≤ C * (e ^ A.χw * e ^ (A.σw * (A.LfT : ℝ))) * c.normF := by gcongr

/-- **Assembly of the fine matrix tail at a context** from the lift step and the defect step. -/
theorem termFineTailAt_of_lift_defect (x : TermResAux c) (heps : 0 < c.D.eps M) (hcK : 0 < cK)
    {C₁ C₂ C : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : FineLiftAt c x C₁)
    (hD : FineDefectAt c x C₂) (hC : C₂ * C₁ * |Cχ| / cK ^ A.LfT ≤ C) :
    TermFineTailAt c x C := by
  obtain ⟨Û, hr, he⟩ := hL
  obtain ⟨Fk, hFk, hmem, hle⟩ := hD Û _ hr he
  exact ⟨Fk, hFk, hmem, hle.trans (fineStep_price_le c heps hcK hC₁ hC₂ hC)⟩

end Steps

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The fine matrix tail: the join of the two steps with the prefix of `entry_terminal_residual`

`termFineTail_of_lift_defect`: `TermFineLiftStatement` and `TermFineDefectStatement` (both with the
prefix of `entry_terminal_residual`) give `TermFineTailStatement`. The thresholds of the two
statements are joined by maxima, the carrier starts by `IsCarrierStart.mono`, and the constants by
`C ≥ C₂ C₁ |C_χ| / c_K^{L_f}`. -/

/-- **Lift step with the prefix of `entry_terminal_residual`.** -/
def TermFineLiftStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => FineLiftAt c x C

/-- **Defect step with the prefix of `entry_terminal_residual`.** -/
def TermFineDefectStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => FineDefectAt c x C

/-- **The fine matrix tail from the lift step and the defect step.** -/
theorem termFineTail_of_lift_defect (hL : TermFineLiftStatement) (hD : TermFineDefectStatement) :
    TermFineTailStatement := by
  intro X
  obtain ⟨Λ₁, h128, hL⟩ := hL X
  obtain ⟨Λ₂, -, hD⟩ := hD X
  refine ⟨max Λ₁ Λ₂, le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 (le_trans (le_max_left _ _) hΛ)
  obtain ⟨kc₁, hL⟩ := hL A (le_trans (le_max_left _ _) hΛ) hV
  obtain ⟨kc₂, hD⟩ := hD A (le_trans (le_max_right _ _) hΛ) hV
  refine ⟨max kc₁ kc₂, fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, hL⟩ := hL kc (le_trans (le_max_left _ _) hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, hD⟩ := hD kc (le_trans (le_max_right _ _) hkc)
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, max Kf₁ Kf₂, fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hL⟩ := hL sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
    Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, hD⟩ := hD sXT sZT (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hZ)
    Kout (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₁ ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₂ ≤ n := fun h => le_trans (le_max_right _ _) h
  obtain ⟨C₀₁, cg₁, Cg₁, hcg₁, CH₁, Υ₁, hCH₁, hΥ₁, hL⟩ :=
    hL Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0 (m1 hKs) (m1 hKan)
      (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₀₂, cg₂, Cg₂, hcg₂, CH₂, Υ₂, hCH₂, hΥ₂, hD⟩ :=
    hD Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcr hkS hc0 (m2 hKs) (m2 hKan)
      (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hall cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨max C₀₂ 0 * max C₀₁ 0 * |Cχ| / cK ^ A.LfT, 1, 1, one_pos, max CH₁ CH₂, max Υ₁ Υ₂,
    le_trans hCH₁ (le_max_left _ _), lt_of_lt_of_le hΥ₁ (le_max_left _ _), fun C hC j₀ hj₀ => ?_⟩
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀
  obtain ⟨M₁, hL⟩ := hL (max C₀₁ 0) (le_max_left _ _) j₀ hj₁
  obtain ⟨M₂, hD⟩ := hD (max C₀₂ 0) (le_max_left _ _) j₀ hj₂
  refine ⟨max M₁ M₂, fun M hM c x => ?_⟩
  have heps : 0 < c.D.eps M := by
    have h := Applications.eps_pos (m := M) X.hq.1 hΛ128
    have h1 := c.data.2.1
    have h2 := c.data.2.2.1
    show 0 < ocEpsilon c.D.q c.D.Λ M
    rw [h1, h2]
    exact h
  exact termFineTailAt_of_lift_defect c x heps hcK (le_max_right _ _) (le_max_right _ _)
    (hL M (le_trans (le_max_left _ _) hM) c x) (hD M (le_trans (le_max_right _ _) hM) c x) hC

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The energy of the lifted field at the order `K_f + 1`, statement

`TermLiftEnergyAt c x C` is the terminal analogue of `successor_full_lift_bound` and of the cascade
statement `FineLiftAt'` (the conclusion of `FullLiftClauses`): the lifted field
`menuLiftedRep (A.Mt …) c.Gw M A.NT A.dW c.CcT c.aRep`, built at the order
`K_f + 1 = k₀ + L_f + D_t + 1` as in the quiet entrance at `k₀`, has torus representatives
`Û` of order `K_f + 1` and `Ŵ` of order `K_f + 2` (the gradient representative) with

* the classical clause: `Û v t` has the lifted field as classical representative of order
  `K_f + 1` at every time of the window (value jet, `C^{K_f+1}`, periodicity);
* `Ŵ v t` truncates to `Û v t` for almost every time of the window;
* `Û v` is strongly measurable in time on the window;
* the strong energy `strongEnergy ρ_* ν π t_p (a + T₀) Û Ŵ ≤ C ‖f‖₂` with `ρ_* = c_K ε_M`
  (`termRStar`), `ν = κ_M`, `π` the masses of the weak stage.

The offset of the energy step (`ReconEnergyAt c x kc ℓ`) needed by the proof: its order `k₀ + ℓ` must cover
`K_f + 2 + N_T d_W`, i.e. `ℓ = L_f + D_t + 2 + N_T d_W`.

Degenerate cases: an empty family (`CompIn c.Gw.comps` empty: every clause is vacuous and the
energy is `0`); `L_f = 0` (`K_f = k₀ + D_t`, the same statement); `f = 0` (`C ‖f‖₂ = 0`, the energy bound
forces `Û = 0`, which is the lifted field of `Z = 0`; `C` is not required to be nonnegative here,
the prefix chooses `C₀ ≥ 0`). -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The energy of the lifted field at the order `K_f + 1`** (the terminal analogue of
`successor_full_lift_bound`). -/
def TermLiftEnergyAt (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP
    CP cHP Cw Ce cker j₀ M) (_x : TermResAux c) (C : ℝ) : Prop :=
  ∃ (Û : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1) (ScalarH v.1.root))
    (Ŵ : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (fineOrder (A := A) + 1 + 1) (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsClassicalRep (Û v t)
        (fun x => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t x v)
        (fineOrder (A := A) + 1)) ∧
    (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ (fineOrder (A := A) + 1)) (Ŵ v t) = Û v t) ∧
    (∀ v, AEStronglyMeasurable (Û v) (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) ∧
    strongEnergy (c.D.termRStar cK M) (c.D.κ M) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) Û Ŵ ≤
      ENNReal.ofReal (C * c.normF)

/-- **`TermLiftEnergyStatement`**, with the prefix of `entry_terminal_residual`. -/
def TermLiftEnergyStatement : Prop :=
  TermResPrefix fun c x _ _ C _ _ => TermLiftEnergyAt c x C

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncFluxOperator
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Construction.FreshAxes.RefFluxContinuous
public import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CycleComparison.Coarse.Defect.Final
import AVRegularity.CycleReference.TorusChartEquation
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp
namespace AVRegularity.EntryTerminal.CovGrad

/-! **A constant matrix acting on the gradient index, as a formal adjoint**.

For a real `2 × 2` matrix `M` the operator `ψ ↦ (x ↦ M · ψ x)` on gradient-valued fields (the
matrix acts on the index in `Fin 2`) is a `TorusAdj` of order zero, built as the sum of the four
fixed entry operators `w ↦ single j (w l)` scaled by `M j l`. The family in `M` is continuous in
operator norm (`covGrad_adjCont_matOp`), and the factorial-norm cost is `∑ |M j l|`
(`fbound_matOp`).

Degenerate cases:
- `M = 0`: the operator is `0`, cost `0`.
- `M = I`: the operator is the identity, cost `2`. -/

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℝ h] [MeasurableSpace h]
  [BorelSpace h] [CompleteSpace h] [FiniteDimensional ℝ h]

/-- The matrix `M` acting on the gradient index: `(M w)_j = ∑_l M_{jl} w_l`. -/
def matAct (M : Matrix (Fin 2) (Fin 2) ℝ) (w : PiLp 2 (fun _ : Fin 2 => h)) :
    PiLp 2 (fun _ : Fin 2 => h) :=
  WithLp.toLp 2 (fun j => ∑ l : Fin 2, M j l • w l)

/-- The embedding of the `j`-th component as a formal adjoint of order zero. -/
def singleOp (j : Fin 2) (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → h) (x : Vec 2) => (piSingleCLM h j) (ψ x))
      0 R Kc ((Kc.factorial : ℝ) * 1) :=
  TorusAdj.constOp (a := 1) (piSingleCLM h j) (PiLp.proj 2 (fun _ : Fin 2 => h) j)
    (fun v w => by
      rw [PiLp.proj_apply, ← real_inner_comm v (piSingleCLM h j w), inner_piSingleCLM,
        real_inner_comm])
    (by exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by
      simpa using PiLp.norm_apply_le w j)) R Kc

theorem fbound_singleOp (ρ : ℝ) (hρ : 0 ≤ ρ) (j : Fin 2) (R Kc : ℕ) :
    (singleOp (h := h) j R Kc).FBound ρ 1 := by
  unfold singleOp
  exact TorusAdj.FBound.constOp hρ

/-- The entry operator `ψ ↦ single j (ψ l)`. -/
def entryAdj (j l : Fin 2) (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h)) (x : Vec 2) =>
      piSingleCLM h j (ψ x l)) 0 R Kc (((Kc.factorial : ℝ) * 1) * ((Kc.factorial : ℝ) * 1)) :=
  ((singleOp (h := h) j R Kc).comp (TorusAdj.componentOp (E := h) l R Kc) le_rfl
    (by omega)).ofOrder (by simp) |>.ofOp (by funext ψ x; rfl)

theorem fbound_entryAdj (ρ : ℝ) (hρ : 0 ≤ ρ) (j l : Fin 2) (R Kc : ℕ) :
    (entryAdj (h := h) j l R Kc).FBound ρ 1 := by
  unfold entryAdj
  have h1 := TorusAdj.FBound.comp (fbound_singleOp (h := h) ρ hρ j R Kc)
    (TorusAdj.FBound.componentOp (E := h) hρ l R Kc) zero_le_one (R := R) le_rfl (by omega)
  exact TorusAdj.FBound.ofOp _ (TorusAdj.FBound.ofOrder _ (by simpa using h1))

/-- The matrix operator `ψ ↦ M ψ` as a formal adjoint of order zero. -/
def matOp (M : Matrix (Fin 2) (Fin 2) ℝ) (R Kc : ℕ) :
    TorusAdj (fun (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h)) (x : Vec 2) => matAct M (ψ x))
      0 R Kc (∑ jl : Fin 2 × Fin 2,
        |M jl.1 jl.2| * (((Kc.factorial : ℝ) * 1) * ((Kc.factorial : ℝ) * 1))) :=
  (TorusAdj.sum (Finset.univ : Finset (Fin 2 × Fin 2)) (fun jl =>
    (entryAdj (h := h) jl.1 jl.2 R Kc).smul (M jl.1 jl.2))).ofOp (by
      funext ψ x
      ext j
      simp only [matAct, Fintype.sum_prod_type, Pi.smul_apply,]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
        piSingleCLM_apply, PiLp.single_apply]
      simp)

theorem fbound_matOp (ρ : ℝ) (hρ : 0 ≤ ρ) (M : Matrix (Fin 2) (Fin 2) ℝ) (R Kc : ℕ) :
    (matOp (h := h) M R Kc).FBound ρ (∑ jl : Fin 2 × Fin 2, |M jl.1 jl.2| * 1) := by
  unfold matOp
  exact TorusAdj.FBound.ofOp _ (TorusAdj.FBound.sum _ fun jl =>
    TorusAdj.FBound.smul _ (fbound_entryAdj ρ hρ jl.1 jl.2 R Kc))

theorem fbound_matOp_le (ρ : ℝ) (hρ : 0 ≤ ρ) (M : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ)
    (ha : ∑ jl : Fin 2 × Fin 2, |M jl.1 jl.2| ≤ a) (R Kc : ℕ) :
    (matOp (h := h) M R Kc).FBound ρ a :=
  TorusAdj.FBound.mono_const (fbound_matOp ρ hρ M R Kc) (by simpa using ha)

/-- The matrix operators vary continuously in operator norm with the matrix. -/
theorem covGrad_adjCont_matOp {S : Type*} [TopologicalSpace S] {M : S → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : Continuous M) (R Kc : ℕ) :
    AdjCont (fun s => matOp (h := h) (M s) R Kc) := by
  unfold matOp
  refine AdjCont.ofOp _ (AdjCont.sum _ fun jl => AdjCont.smul (fun s => M s jl.1 jl.2) ?_
    (AdjCont.constAny _))
  exact (continuous_apply jl.2).comp ((continuous_apply jl.1).comp hM)

end AVRegularity.EntryTerminal.CovGrad
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The generic part** of the covariance truncation. Nothing here reads the terminal context.
It contains:
- the gradient term `covTruncGrad` and the identity `menuCovTruncFlux_eq_sub`;
- the generic steps `CovTruncSubStatement` and `CovTruncOpStatement`;
- the price arithmetic `covTrunc_price_le`.

Degenerate cases: `p = 0` (`covTruncGrad` reads `𝒞⁰ = id`); `H ≡ 0` (`ω = 0`). -/

section
section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The second term of `menuCovTruncFlux`: `(𝖩_m - BI)∇(𝒞^p/p!)Z`. -/
def covTruncGrad (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m p : ℕ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  fun j => ∑ l : Fin 2, (ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1) j l •
    gradE (fun y => ((p.factorial : ℝ)⁻¹) •
      (covOperator (menuCovPrimitive D Mn m t))^[p] (fun y' => aZ t y' v) y) x l

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The covariance truncation flux is `(G - P_pQ_pG) - T`. -/
theorem menuCovTruncFlux_eq_sub (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) :
    menuCovTruncFlux Mn G m N p depth CcT aZ v t x =
      (menuGFlux Mn G m N p depth CcT aZ v t x -
        covPolyP (menuCovPrimitive D Mn m t) p
          (covPolyQ (menuCovPrimitive D Mn m t) p
            (fun y => menuGFlux Mn G m N p depth CcT aZ v t y)) x) -
        covTruncGrad Mn G m p aZ v t x := rfl

end Generic

/-! ### The generic steps -/

/-- **Difference of two realized fluxes** (generic). Realizations subtract and the
masses add (Minkowski in `L²(I)` and `sqrt_massNormSq_add_le`). -/
def CovTruncSubStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (k : ℕ) (I : Set ℝ) (ν ρ : ℝ) (π : ι → ℝ), 0 < ν → (∀ v, 0 < π v) →
    ∀ (F₁ F₂ : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (Y₁ Y₂ : ℝ),
      HasFluxBound k I ν ρ π F₁ Y₁ → HasFluxBound k I ν ρ π F₂ Y₂ →
      HasFluxBound k I ν ρ π (fun v t x => F₁ v t x - F₂ v t x) (Y₁ + Y₂)

/-- **The truncation operator `I - P_pQ_p`** (generic over the family). For a flux
`G` of class `C^{k+4p}` with a realization of order `k + 4p` and a covariance primitive with
`‖H(t)‖ ≤ ω ρ²`, `ω ≤ 1`, the flux `G - P_pQ_pG` has a realization of order `k` with the mass
`C_op ω^{p+1}` times that of `G`, where `C_op` depends on `k` and `p` only.

Route: `sub_covPolyQ_covPolyP_eq`, `TorusAdj.qpRem` (order `4p`,
constant `cqp (fbCovConst ρ H k) p`), `cqp_le` (`≤ cqpBig · ω^{p+1}`); the time dependence of
`H(t)` is continuous, so the operator applied to the realization is measurable in time.
Degenerate cases: `ω = 0` gives `0`; `p = 0` gives `G - G = 0` (`cqp` is an empty sum). -/
def CovTruncOpStatement : Prop :=
  ∀ (k p : ℕ), ∃ Cop : ℝ, 0 ≤ Cop ∧
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (I : Set ℝ), MeasurableSet I → ∀ (ν ρ : ℝ) (π : ι → ℝ), 0 < ν → 0 < ρ → (∀ v, 0 < π v) →
    ∀ (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ), ContinuousOn Hc I → 0 ≤ ω → ω ≤ 1 →
    (∀ t ∈ I, AVRegularity.CycleComparison.Coarse.covBound (Hc t) ≤ ω * ρ ^ 2) →
    ∀ (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ),
      (∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 4 * p : ℕ) : ℕ∞) (Gf v t) ∧ IsZ2Periodic (Gf v t)) →
      HasFluxBound (k + 4 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y →
      HasFluxBound k I ν ρ π
        (fun v t x => toFluxL (Gf v t x - covPolyP (Hc t) p (covPolyQ (Hc t) p (Gf v t)) x))
        (Cop * ω ^ (p + 1) * Y)

/-! ### The price arithmetic -/

/-- The price of the two terms at `ω = C₁ E^δ`:
`C_op ω^{p+1} (C₁ n) + C₁ E^{δp} n ≤ (C_op C₁^{p+2} + C₁) E^{δp} n`. -/
theorem covTrunc_price_le {Cop C₁ E δ n : ℝ} (p : ℕ) (hCop : 0 ≤ Cop) (hC₁ : 0 ≤ C₁)
    (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ) (hn : 0 ≤ n) :
    Cop * (C₁ * E ^ δ) ^ (p + 1) * (C₁ * n) + C₁ * E ^ (δ * (p : ℝ)) * n ≤
      (Cop * C₁ ^ (p + 2) + C₁) * E ^ (δ * (p : ℝ)) * n := by
  have h1 : E ^ δ ≤ 1 := Real.rpow_le_one hE0.le hE1 hδ
  have h0 : 0 ≤ E ^ δ := (Real.rpow_pos_of_pos hE0 δ).le
  have h2 : (E ^ δ) ^ p = E ^ (δ * (p : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE0.le]
  have h3 : (E ^ δ) ^ (p + 1) ≤ E ^ (δ * (p : ℝ)) := by
    rw [pow_succ, h2]
    exact mul_le_of_le_one_right (Real.rpow_pos_of_pos hE0 _).le h1
  have h4 : 0 ≤ E ^ (δ * (p : ℝ)) := (Real.rpow_pos_of_pos hE0 _).le
  have h5 : Cop * (C₁ * E ^ δ) ^ (p + 1) * (C₁ * n) ≤ Cop * C₁ ^ (p + 2) * E ^ (δ * (p : ℝ)) * n := by
    rw [mul_pow]
    have : Cop * (C₁ ^ (p + 1) * (E ^ δ) ^ (p + 1)) * (C₁ * n) =
        Cop * C₁ ^ (p + 2) * (E ^ δ) ^ (p + 1) * n := by ring
    rw [this]
    have hc : 0 ≤ Cop * C₁ ^ (p + 2) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc) hn
  nlinarith [h5, mul_nonneg hC₁ (mul_nonneg h4 hn)]
end

/-! **The coarse filter tails, generic part**: the readout of the root flux defects
`filterReadoutDefect` (the argument of `P_p` in `menuFilterFlux`) and the generic step
`FilterPOpStatement`. It does not use the terminal bounds.

For `p = 0`, `P_0 = I`. -/

section
section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The readout of the root flux defects, as a function with values in `Fin 2 → _` (the argument
of `P_p` in `menuFilterFlux`). -/
def filterReadoutDefect (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (m : ℕ) (E η₀ : ℝ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (y : Vec 2) : Fin 2 → hr v.1.root :=
  WithLp.ofLp (readoutFlux m E η₀ (fun _ => True)
    (fun v' s y' => rootFluxDefect P seedK freshK φ₀ G G' aZ v' s y') v t y)

end Generic

/-- **The operator `P_p`** (generic over the family). For a flux `G` of class
`C^{k+2p}` with a realization of order `k + 2p` and a covariance primitive with
`‖H(t)‖ ≤ ω ρ²`, `ω ≤ 1`, the flux `P_pG` has a realization of order `k` with the mass of `G`
times `C_p(k, p)`.

Route: `TorusAdj.covPolyP`, `FBound.covPolyP` (cost `covPolyConst`),
the cost constant `fbCovConst ρ H k ≤ 4(k+2p)²ω ≤ 4(k+2p)²`; measurability in time as in
`CovTruncOpStatement`. For `p = 0`: `P_0 = I`, `C_p = 1`. -/
def FilterPOpStatement : Prop :=
  ∀ (k p : ℕ), ∃ Cp : ℝ, 0 ≤ Cp ∧
  ∀ {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (I : Set ℝ), MeasurableSet I → ∀ (ν ρ : ℝ) (π : ι → ℝ), 0 < ν → 0 < ρ → (∀ v, 0 < π v) →
    ∀ (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ω : ℝ), ContinuousOn Hc I → 0 ≤ ω → ω ≤ 1 →
    (∀ t ∈ I, AVRegularity.CycleComparison.Coarse.covBound (Hc t) ≤ ω * ρ ^ 2) →
    ∀ (Gf : ∀ v : ι, ℝ → Vec 2 → Fin 2 → h v) (Y : ℝ),
      (∀ v, ∀ t ∈ I, ContDiff ℝ ((k + 2 * p : ℕ) : ℕ∞) (Gf v t) ∧ IsZ2Periodic (Gf v t)) →
      HasFluxBound (k + 2 * p) I ν ρ π (fun v t x => toFluxL (Gf v t x)) Y →
      HasFluxBound k I ν ρ π (fun v t x => toFluxL (covPolyP (Hc t) p (Gf v t) x)) (Cp * Y)
end

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The covariance truncation at the terminal menu: the named steps and the assembly of
`TermCovTruncStatement`**.

With `G = menuGFlux` and `T = covTruncGrad` the flux of `TermCovTruncAt` is
`(G - P_pQ_pG) - T` (`menuCovTruncFlux_eq_sub`, by definition). Route:
* `CovTruncSizeStatement`: `‖H_M(t)‖ ≤ C E^δ ρ²` on the window, with `C E^δ ≤ 1`
  (`bandChain_covariance_estimates`, last clause: `|H|/R_h² ≤ C E^δ`, `R_h = ρ` at `c_r = 1`).
* `CovTruncGStatement`: `G` is `C^{k_c+4p}` and has a realization of order `k_c + 4p`
  with `B^{-1/2}‖G‖ ≤ C‖f‖₂` (energy of `Z`, mean letters).
* `CovTruncGradStatement`: `T` has a realization of order `k_c` with
  `B^{-1/2}‖T‖ ≤ C E^{δp}‖f‖₂` (`‖J - BI‖ ≤ CB`, `ω^p`, dissipation of `Z`).
* `CovTruncOpStatement` (generic): `(I - P_pQ_p)` costs `C ω^{p+1}` and `4p` orders
  (`TorusAdj.qpRem`, `cqp_le`).
* `CovTruncSubStatement` (generic): difference of two realized fluxes.

`termCovTrunc_of_steps` assembles the statement; the price arithmetic is
`covTrunc_price_le`.

Degenerate cases:
- `H_M ≡ 0`: `ω = 0`, the first term vanishes and `T = 0` (`covTrunc_price_le` at `ω = 0`).
- `p_T = 1`: `P_1Q_1 - I = -𝒞²` (the shift `4p` is `4`).
- `x.aZ = 0`: every flux is `0`. -/

/-! ### The steps at the terminal context -/

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- **The size step at a context**: the covariance primitive of the terminal menu is at most `C E^δ ρ²` on
the window, `C E^δ ≤ 1`, and the primitive is continuous in time on the window. -/
def CovTruncSizeAt (_x : TermResAux c) (_kc : ℕ) (C : ℝ) : Prop :=
  (∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    AVRegularity.CycleComparison.Coarse.covBound
        (menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) ≤
      (C * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) * c.D.termRho cr M ^ 2) ∧
    C * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q ≤ 1 ∧
  ContinuousOn (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    (Set.Icc c.tp (c.a + A.T₀))

/-- **The pre-truncation flux at a context**: `G = menuGFlux` is `C^{k_c+4p_T}`, `ℤ²`-periodic, and has a realization
of order `k_c + 4p_T` with `B^{-1/2}‖G‖_{L²(I;H_{ρ,k_c+4p_T;π})} ≤ C‖f‖₂`. -/
def CovTruncGAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 4 * A.pT : ℕ) : ℕ∞)
        (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y) ∧
      IsZ2Periodic
        (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)) ∧
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y))
    (C * c.normF)

/-- **The gradient term at a context**: `T = (𝖩_M - BI)∇(𝒞^{p_T}/p_T!)Z` has a realization of order `k_c` with
`B^{-1/2}‖T‖ ≤ C E^{δp_T}‖f‖₂`. -/
def CovTruncGradAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) kc
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL (covTruncGrad (A.Mt M sXT sZT c.tp cr) c.Gw M A.pT x.aZ v t y))
    (C * c.covPrice * c.normF)

end Terminal

/-- **The size of the covariance primitive at the terminal menu.**
`bandChain_covariance_estimates`, last clause, bounds each entry of `ocCovariance` between any two
times by `C E^δ R_h²` with `R_h² = B ocTauPP = ρ²` at `c_r = 1`; `E^δ → 0` gives `C E^δ ≤ 1` for large `M`. -/
def CovTruncSizeStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncSizeAt c x kc C

/-- **The pre-truncation flux `G`.** `G = 𝒟Z - 𝐄^flux P_pZ` is the
commutator flux plus the Eulerian mean flux of the lift of `P_pZ`; its mass is bounded by the
energy of `Z` (`coarse_solution`, `native_reg_solution_strongEnergy_of_initial_norm`, the
preparation bound `c.prepB`, the readout norm `terminalReadoutEnergy`) with the lift
coefficients `c.CcT` of `c.lift`. -/
def CovTruncGStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncGAt c x kc C

/-- **The gradient term.** Energy of `Z` (dissipation), `‖J_M - BI‖ ≤ CB` (the diffusivity
ledger), and `ω^{p_T}` from the size estimate. -/
def CovTruncGradStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncGradAt c x kc C

/-! ### The assembly -/

/-- **The covariance truncation from its steps.** -/
theorem termCovTrunc_of_steps (hOp : CovTruncOpStatement) (hSub : CovTruncSubStatement)
    (hS : CovTruncSizeStatement) (hG : CovTruncGStatement) (hT : CovTruncGradStatement) :
    TermCovTruncStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncSizeAt c x kc C)
    (P₂ := fun c x kc C => CovTruncGAt c x kc C ∧ CovTruncGradAt c x kc C) hS
    (termFluxPrefix_and (P₁ := fun c x kc C => CovTruncGAt c x kc C)
      (P₂ := fun c x kc C => CovTruncGradAt c x kc C) hG hT)
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncSizeAt c x kc C ∧ (CovTruncGAt c x kc C ∧ CovTruncGradAt c x kc C))
    (R := fun c x kc C => TermCovTruncAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ128 hC₁
  obtain ⟨Cop, hCop, hOp'⟩ := hOp kc A.pT
  refine ⟨Cop * C₁ ^ (A.pT + 2) + C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C'
    hC'
  obtain ⟨⟨hsz, hsm, hcont⟩, ⟨hGreg, hG'⟩, hT'⟩ := hP
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hε0 : 0 < c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1
  have hε1 : c.D.eps (M - 1) ≤ 1 := ocEpsilon_le_one (le_trans (by norm_num) hΛD) (M - 1)
  have hδ : 0 ≤ ocDelta c.D.α c.D.q := by
    rw [hDα, hDq]; exact (ocDelta_pos_of_admissible X.hα₀ X.hq).le
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hω : 0 ≤ C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q :=
    mul_nonneg hC₁ (Real.rpow_pos_of_pos hε0 _).le
  have hop := hOp' (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
    (Set.Icc c.tp (c.a + A.T₀)) measurableSet_Icc (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) hν hρ hπ
    (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    (C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) hcont hω hsm hsz
    (fun v t y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)
    (C₁ * c.normF) hGreg hG'
  have hsub := hSub (kc) (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M)
    (c.Gw.mass c.lawW) hν hπ _ _ _ _ hop hT'
  have hfun : (fun (v : CompIn c.Gw.comps) (t : ℝ) (y : Vec 2) => toFluxL
      (menuCovTruncFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)) =
      fun v t y => toFluxL
        (menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y -
          covPolyP (menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) A.pT
            (covPolyQ (menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) A.pT
              (fun z => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t z))
            y) -
        toFluxL (covTruncGrad (A.Mt M sXT sZT c.tp cr) c.Gw M A.pT x.aZ v t y) := by
    funext v t y
    rw [menuCovTruncFlux_eq_sub]
    exact WithLp.toLp_sub 2 _ _
  unfold TermCovTruncAt CovTruncBound
  rw [hfun]
  refine hasFluxBound_mono_Y hsub ?_
  have hprice := covTrunc_price_le (Cop := Cop) (C₁ := C₁) (E := c.D.eps (M - 1))
    (δ := ocDelta c.D.α c.D.q) (n := c.normF) A.pT hCop hC₁ hε0 hε1 hδ hn
  have hcov0 : 0 ≤ c.covPrice := (Real.rpow_pos_of_pos hε0 _).le
  calc _ ≤ (Cop * C₁ ^ (A.pT + 2) + C₁) * c.covPrice * c.normF := hprice
    _ ≤ C' * c.covPrice * c.normF :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hcov0) hn

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The coarse filter tails at the terminal menu: the named steps and the assembly of
`TermFilterStatement`**.

The flux of `TermFilterAt` is `P_p` (covariance anchored at `t_p`) of the readout of the root flux
defects (`menuFilterFlux`, by definition). Route:
* `FilterDefectStatement`: the readout `𝖱(∑𝖮_γ(I - S_γ)Z + ∑𝖥_{α,γ}(I - S_α)Z)` of the
  classical representative `x.aZ` is `C^{k_c+2p}`, `ℤ²`-periodic, and has a realization of order
  `k_c + 2p_T` with mass at most `C [E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}] ‖f‖₂`. Its
  steps: split by provenance (`kernelOf`, `RootSourceBookkeepingStatement`); the moment bound of
  one defect (`momentKernel_paired_spatial_approximation_torus`, generic in the stage); the coefficient
  prices (`c.weak`, `c.seed`); the energy of `Z` (as for `CovTruncGStatement`).
* `FilterPOpStatement` (generic): `P_p` costs `C_p` and `2p` orders for `ω ≤ 1`
  (`TorusAdj.covPolyP`, `FBound.covPolyP`).
* `CovTruncSizeStatement` (the size of the covariance primitive, shared with the covariance truncation).

`termFilter_of_steps` assembles the statement.

Degenerate cases:
- No fresh letter out of the roots: only the old term `x^{χ_w}(r_w/ρ)^{L_o}` is in the filter defect.
- Width `0` kernels: `S = I`, the defect is `0` and so is the flux.
- `L_c = 0`: no moment gain, the fresh price is `E^{b_T}`. -/

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- **At a context**: the readout of the root flux defects of the terminal successor, on the
classical representative `x.aZ`, is `C^{k_c+2p_T}`, periodic, and has a realization of order
`k_c + 2p_T` with `B^{-1/2}‖·‖ ≤ C [E^{b_T + t_TL_c} + x^{χ_w}(r_w/ρ)^{L_o}]‖f‖₂`. -/
def FilterDefectAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 2 * A.pT : ℕ) : ℕ∞)
        (fun y => filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y) ∧
      IsZ2Periodic
        (fun y => filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y)) ∧
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y))
    (C * c.filterPrice * c.normF)

end Terminal

/-- **The defect tails** (see the module docstring for the steps). -/
def FilterDefectStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => FilterDefectAt c x kc C

/-- **The coarse filter tails from their steps.** -/
theorem termFilter_of_steps (hP : FilterPOpStatement) (hS : CovTruncSizeStatement)
    (hF : FilterDefectStatement) : TermFilterStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncSizeAt c x kc C)
    (P₂ := fun c x kc C => FilterDefectAt c x kc C) hS hF
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncSizeAt c x kc C ∧ FilterDefectAt c x kc C)
    (R := fun c x kc C => TermFilterAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ128 hC₁
  obtain ⟨Cp, hCp, hP'⟩ := hP kc A.pT
  refine ⟨Cp * C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hPr C'
    hC'
  obtain ⟨⟨hsz, hsm, hcont⟩, hreg, hF'⟩ := hPr
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hε0 : 0 < c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1
  have hδ : 0 ≤ ocDelta c.D.α c.D.q := by
    rw [hDα, hDq]; exact (ocDelta_pos_of_admissible X.hα₀ X.hq).le
  have hω : 0 ≤ C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q :=
    mul_nonneg hC₁ (Real.rpow_pos_of_pos hε0 _).le
  have hop := hP' (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
    (Set.Icc c.tp (c.a + A.T₀)) measurableSet_Icc (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW) hν hρ hπ
    (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    (C₁ * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) hcont hω hsm hsz
    (fun v t y => filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
      c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y)
    (C₁ * c.filterPrice * c.normF) hreg hF'
  unfold TermFilterAt FilterBound
  refine hasFluxBound_mono_Y hop ?_
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hfp : 0 ≤ c.filterPrice := by
    unfold TermResCtx.filterPrice
    have h1 : 0 ≤ c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
      A.tT * (termExcess A.NT A.pT A.alph : ℝ) + A.tT * (A.LcT : ℝ)) :=
      (Real.rpow_pos_of_pos hε0 _).le
    have h2 : 0 ≤ c.D.eps M ^ A.χw * (c.D.termRW A.σw M / c.D.termRho cr M) ^ A.LoT := by
      have hεM : 0 < c.D.eps M := (Scales.epsilon_basic (m := M) hq1 hΛD).1
      exact mul_nonneg (Real.rpow_pos_of_pos hεM _).le
        (pow_nonneg (div_nonneg (Real.rpow_pos_of_pos hεM _).le hρ.le) _)
    exact add_nonneg h1 h2
  calc Cp * (C₁ * c.filterPrice * c.normF) = (Cp * C₁) * c.filterPrice * c.normF := by ring
    _ ≤ C' * c.filterPrice * c.normF :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hfp) hn

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter Topology
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The size of the covariance primitive at the terminal menu**
(`CovTruncSizeStatement`).

`bandChain_covariance_estimates` (last clause) bounds every entry of `ocCovariance` between any
two times by `C E^δ R_h²`, with `R_h² = B·ocTauPP`, which is `ρ²` at `c_r = 1`. The sum of the four
entries gives `covBound ≤ 4 C E^δ ρ²`. The smallness `C E^δ ≤ 1` holds for large `M` because
`ε_{M-1} → 0` (`epsilon_parent_tendsto_zero`), and the primitive is continuous in time because the
integrand is (`refFlux_entry_continuous`).

Degenerate cases:
- `H ≡ 0`: `covBound = 0`, the bound holds for every `C ≥ 0`.
- `t = t_p`: the primitive vanishes. -/

/-- **Statements without floors**: if the constants depend on nothing but the arguments `A` and
the large level `M`, the prefix is automatic. -/
theorem termFluxPrefix_of_simple {P : TermFluxPred}
    (h : ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ →
      ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ M₀ : ℕ,
        ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
          {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ}
          {j₀ M : ℕ}, M₀ ≤ M →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
          Ce cker j₀ M) (x : TermResAux c) (kc : ℕ), P c x kc C) :
    TermResPrefix fun c x kc _ C _ _ => P c x kc C := by
  intro X
  obtain ⟨Λ₀, h128, H⟩ := h X
  refine ⟨Λ₀, h128, fun A hΛ _ => ?_⟩
  obtain ⟨C₀, HC⟩ := H A hΛ
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨C₀, 1, 1, one_pos, 1, 1, le_rfl, one_pos, ?_⟩
  intro C hC j₀ hj₀
  obtain ⟨M₀, HM⟩ := HC C hC
  exact ⟨M₀, fun M hM c x => HM hM c x kc⟩

/-- The primitive of the covariance is continuous in time. -/
theorem covTrunc_primitive_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν) (s : ℝ) :
    Continuous (fun t => ocCovariance α q Λ ζ m ν B s t) := by
  refine continuous_matrix fun i j => ?_
  have hc : Continuous (fun r => ocRefFlux α q Λ ζ m ν r i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) :=
    (FreshAxes.refFlux_entry_continuous hΛ hζ hν i j).sub continuous_const
  exact intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) s

theorem covTrunc_epsilon_nonneg (X : TermConstruction) {Λ : ℕ} (hΛ : 128 ≤ Λ) (m : ℕ) :
    0 ≤ ocEpsilon X.q Λ m :=
  (Scales.epsilon_basic (m := m) X.hq.1 hΛ).1.le

/-- **The size of the covariance primitive.** -/
theorem covTruncSize : CovTruncSizeStatement := by
  refine termFluxPrefix_of_simple (P := fun c x kc C => CovTruncSizeAt c x kc C) ?_
  intro X
  obtain ⟨Ccov, hC1, Λ₁, hΛ₁, hest⟩ := CycleReference.bandChain_covariance_estimates X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨Λ₁, hΛ₁, fun A hΛ => ⟨4 * Ccov, fun C hC => ?_⟩⟩
  have hΛ128 : 128 ≤ A.Λ := hΛ₁.trans hΛ
  have hδ : 0 < ocDelta X.α X.q := ocDelta_pos_of_admissible X.hα₀ X.hq
  have hev : ∀ᶠ M : ℕ in atTop, C * ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q ≤ 1 := by
    have ht := (CycleReference.epsilon_parent_tendsto_zero X.hq.1 hΛ128).rpow_const
      (p := ocDelta X.α X.q) (Or.inr hδ.le)
    have ht2 := (tendsto_const_nhds (x := C)).mul ht
    rw [Real.zero_rpow hδ.ne', mul_zero] at ht2
    exact ht2.eventually (eventually_le_nhds one_pos)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 hev
  refine ⟨max M₁ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M hM c x kc
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, -⟩ := c.data
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hsmall := hM₁ M (le_trans (le_max_left _ _) hM)
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hνM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 X.hζ hband le_rfl
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (α := c.D.α) (q := c.D.q)
    (hDΛ ▸ hΛ1)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have e1 : ∀ t, menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t =
      ocCovariance X.α X.q A.Λ X.ζ M (c.D.κ M) (c.D.κ (M - 1)) c.tp t := by
    intro t
    simp only [menuCovPrimitive]
    rw [hDα, hDq, hDΛ, hDζ]
    rfl
  have e2 : c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q =
      ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q := by
    simp only [OCData.eps]
    rw [hDα, hDq, hDΛ]
  have e3 : c.D.termRho cr M ^ 2 = ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 := by
    have h1 := congrArg (fun r : ℝ => (r * Real.sqrt (c.D.κ (M - 1) *
      ocTauPP c.D.α c.D.q c.D.Λ M)) ^ 2) x.one
    unfold OCData.termRho OCData.termB OCData.termH ocRh
    refine h1.trans ?_
    rw [hDα, hDq, hDΛ, one_mul]
  have hpos : 0 < ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 := e3 ▸ pow_pos hρ 2
  have hentry : ∀ t i j, |menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t i j| ≤
      Ccov * ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q * c.D.termRho cr M ^ 2 := by
    intro t i j
    have h := (hest A.Λ hΛ M (by omega) c.D.κ hband M hM2 le_rfl c.tp t i j).2.2.2
    rw [e1, e3]
    exact (div_le_iff₀ hpos).1 h
  refine ⟨fun t _ => ?_, ?_, ?_⟩
  · have hER : 0 ≤ ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q * c.D.termRho cr M ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (covTrunc_epsilon_nonneg X hΛ128 (M - 1)) _) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_right hC hER
    simp only [AVRegularity.CycleComparison.Coarse.covBound, Fin.sum_univ_two]
    rw [e2]
    have := hentry t 0 0
    have := hentry t 0 1
    have := hentry t 1 0
    have := hentry t 1 1
    nlinarith
  · rw [e2]; exact hsmall
  · have hc : Continuous (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) := by
      have := covTrunc_primitive_continuous (α := c.D.α) (q := c.D.q) (m := M) (Λ := c.D.Λ)
        (ζ := c.D.ζ) (hDΛ ▸ hΛ1) (hDζ ▸ X.hζ) (ν := c.D.κ M) (B := c.D.κ (M - 1)) hνM
        (A.Mt M sXT sZT c.tp cr).anchor
      exact this
    exact hc.continuousOn

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Construction.Residual.Presentation

/-! **The difference of two realized fluxes** (`CovTruncSubStatement`).

The square root of the mass norm is the norm of the continuous linear readout
`massWeightedCarrierCLM`, so the time integral is the `L²(I; V)` norm of a `V`-valued trajectory,
and the bound is Minkowski's inequality in `L²` (`covTrunc_sqrt_inv_mul_integral_sub_le`).

Degenerate cases:
- `F₂ = F₁`: the difference is `0` and the bound `Y₁ + Y₂ ≥ 0` holds.
- `Y₂ = 0`: the second flux has mass `0`, the difference has the mass of the first. -/

theorem covTrunc_sqrt_integral_norm_sq_eq {α V : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup V] {g : α → V} (hg : MemLp g 2 μ) :
    Real.sqrt (∫ s, ‖g s‖ ^ 2 ∂μ) = (eLpNorm g 2 μ).toReal := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  simp

/-- Minkowski for the difference in the form of `FluxMassLe`. -/
theorem covTrunc_sqrt_inv_mul_integral_sub_le {α V : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup V] {g₁ g₂ : α → V} (h₁ : MemLp g₁ 2 μ) (h₂ : MemLp g₂ 2 μ) {ν : ℝ}
    (hν : 0 < ν) :
    Real.sqrt (ν⁻¹ * ∫ s, ‖g₁ s - g₂ s‖ ^ 2 ∂μ) ≤
      Real.sqrt (ν⁻¹ * ∫ s, ‖g₁ s‖ ^ 2 ∂μ) + Real.sqrt (ν⁻¹ * ∫ s, ‖g₂ s‖ ^ 2 ∂μ) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h₃ : MemLp (fun s => g₁ s - g₂ s) 2 μ := h₁.sub h₂
  rw [covTrunc_sqrt_integral_norm_sq_eq h₁, covTrunc_sqrt_integral_norm_sq_eq h₂,
    covTrunc_sqrt_integral_norm_sq_eq h₃]
  have := eLpNorm_sub_le (f := g₁) (g := g₂) (p := 2) (μ := μ) (by norm_num)
  have h4 : (eLpNorm (fun s => g₁ s - g₂ s) 2 μ).toReal ≤
      (eLpNorm g₁ 2 μ + eLpNorm g₂ 2 μ).toReal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h₁.eLpNorm_ne_top, h₂.eLpNorm_ne_top⟩) this
  rwa [ENNReal.toReal_add h₁.eLpNorm_ne_top h₂.eLpNorm_ne_top] at h4

/-- The mass readout of a flux family, as a trajectory in a normed space. -/
abbrev covTruncMassCLM {ι : Type} [Fintype ι] (h : ι → Type) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (k : ℕ) (ρ : ℝ) (π : ι → ℝ) :=
  massWeightedCarrierCLM (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (fun _ => k) ρ π

section Mass

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem covTrunc_mass_sub (k : ℕ) (ρ : ℝ) (π : ι → ℝ)
    (A B : ∀ v : ι, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) :
    covTruncMassCLM h k ρ π (fun v => A v - B v) =
      covTruncMassCLM h k ρ π A - covTruncMassCLM h k ρ π B := by
  rw [← ContinuousLinearMap.map_sub]
  rfl

theorem covTrunc_mass_memLp (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (I : Set ℝ) (Y : ℝ)
    (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    MemLp (fun s => covTruncMassCLM h k ρ π (fun v => G v s)) 2 (volume.restrict I) := by
  have hG1 : ∀ v, MemLp (G v) 2 (volume.restrict I) := fun v => hG.1 v
  have h1 : MemLp (fun s => fun v => G v s) 2 (volume.restrict I) := memLp_pi_iff.mpr hG1
  exact (covTruncMassCLM h k ρ π).comp_memLp' h1

theorem covTrunc_mass_integral (k : ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ)
    (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) :
    (∫ s in I, massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k)
        ρ π (fun v => (G v s).val)) =
      ∫ s in I, ‖covTruncMassCLM h k ρ π (fun v => G v s)‖ ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall fun s =>
    (massWeightedCarrierCLM_normSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (fun _ => k) ρ π hπ (fun v => G v s)).symm)

theorem covTrunc_mass_sub_pointwise (k : ℕ) (ρ : ℝ) (π : ι → ℝ)
    (G₁ G₂ : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (s : ℝ) :
    covTruncMassCLM h k ρ π (fun v => G₁ v s - G₂ v s) =
      covTruncMassCLM h k ρ π (fun v => G₁ v s) - covTruncMassCLM h k ρ π (fun v => G₂ v s) :=
  covTrunc_mass_sub k ρ π (fun v => G₁ v s) (fun v => G₂ v s)

/-- The mass part of the difference statement. -/
theorem covTrunc_fluxMassLe_sub (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    (I : Set ℝ) (Y₁ Y₂ : ℝ) (G₁ G₂ : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hm₁ : FluxMassLe (K := fun _ => k) ν ρ π I G₁ Y₁)
    (hm₂ : FluxMassLe (K := fun _ => k) ν ρ π I G₂ Y₂) :
    FluxMassLe (K := fun _ => k) ν ρ π I (fun v t => G₁ v t - G₂ v t) (Y₁ + Y₂) := by
  have hmem1 := covTrunc_mass_memLp k ν ρ π I Y₁ G₁ hm₁
  have hmem2 := covTrunc_mass_memLp k ν ρ π I Y₂ G₂ hm₂
  refine ⟨fun v => (hm₁.1 v).sub (hm₂.1 v), ?_⟩
  have hmin := covTrunc_sqrt_inv_mul_integral_sub_le hmem1 hmem2 hν
  have hb₁ := hm₁.2
  have hb₂ := hm₂.2
  rw [covTrunc_mass_integral k ρ π hπ I (fun v s => G₁ v s - G₂ v s)]
  simp only [covTrunc_mass_sub_pointwise]
  rw [covTrunc_mass_integral k ρ π hπ I G₁] at hb₁
  rw [covTrunc_mass_integral k ρ π hπ I G₂] at hb₂
  exact hmin.trans (add_le_add hb₁ hb₂)

end Mass

/-- **The difference of two realized fluxes.** -/
theorem covTruncSub : CovTruncSubStatement := by
  intro ι _ h _ _ _ _ _ _ k I ν ρ π hν hπ F₁ F₂ Y₁ Y₂ hF₁ hF₂
  refine Exists.elim hF₁ fun G₁ hG₁ => Exists.elim hF₂ fun G₂ hG₂ => ?_
  refine ⟨fun v t => G₁ v t - G₂ v t, ?_, ?_⟩
  · intro v t ht
    filter_upwards [AVRegularity.CycleComparison.Coarse.jet_sub_ae (G₁ v t) (G₂ v t),
      hG₁.1 v t ht, hG₂.1 v t ht] with x hx h1 h2
    rw [hx, h1, h2]
  · exact covTrunc_fluxMassLe_sub k ν ρ π hν hπ I Y₁ Y₂ G₁ G₂ hG₁.2 hG₂.2

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter Topology
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The size ledger of the gradient term of the covariance truncation**.

At a terminal context with `M ≥ 2`, with `N_t = 𝖩_M(t) - κ_{M-1} I` (the matrix of `covTruncGrad`):
* `covBound (H_M(t)) ≤ C_cov E^δ ρ²` for every `t` (`bandChain_covariance_estimates`),
* `∑_{ij} |N_t(i,j)| ≤ C_N κ_{M-1}` for every `t` (`refFlux_entry_norm_le` and the clause
  `ν + ε^{2(1+α)}/ν ≤ C B` of `bandChain_uniform_ledger`),
* `t ↦ H_M(t)` and `t ↦ N_t` are continuous.
The constants `C_cov`, `C_N` depend on the construction and `Λ` only (not on the level).

Degenerate cases:
- `ε_M → 0`: `J_M → ν I`, and `ν ≤ B`, so `N → (ν - B) I`, of size `≤ B`.
- `H ≡ 0` (no covariance): the first bound is trivial. -/

/-- The matrix `𝖩_m(t) - κ_{m-1} I` acting on the gradient index in `covTruncGrad`. -/
def covGradN (D : OCData) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t - D.κ (m - 1) • 1

theorem covGradN_continuous {D : OCData} {m : ℕ} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hν : 0 < D.κ m) : Continuous (covGradN D m) := by
  refine continuous_matrix fun i j => ?_
  unfold covGradN
  simp only [Matrix.sub_apply]
  exact (FreshAxes.refFlux_entry_continuous hΛ hζ hν i j).sub continuous_const

theorem covGradN_entry_le {D : OCData} {m : ℕ} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hν : 0 < D.κ m) {Cl : ℝ}
    (hled : D.κ m + ocEpsilon D.q D.Λ m ^ (2 * (1 + D.α)) / D.κ m ≤ Cl * D.κ (m - 1))
    (hB : 0 ≤ D.κ (m - 1)) (hε : 0 ≤ ocEpsilon D.q D.Λ m) (t : ℝ) (i j : Fin 2) :
    |covGradN D m t i j| ≤ (Cl + 1) * D.κ (m - 1) := by
  have h1 := CycleReference.refFlux_entry_norm_le (α := D.α) (q := D.q) (m := m) (ζ := D.ζ)
    hΛ hζ (t := t) hν i j
  rw [Real.norm_eq_abs] at h1
  have hX : 0 ≤ ocEpsilon D.q D.Λ m ^ (2 * (1 + D.α)) := Real.rpow_nonneg hε _
  have h2 : ocHStar D.α D.q D.Λ m (D.κ m) ≤
      ocEpsilon D.q D.Λ m ^ (2 * (1 + D.α)) / D.κ m := by
    unfold ocHStar
    rw [div_le_div_iff₀ (by positivity) hν]
    nlinarith
  have h3 : |ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t i j| ≤ Cl * D.κ (m - 1) := by linarith
  have h4 : |((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp
  unfold covGradN
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ ≤ |ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t i j| + |D.κ (m - 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| :=
        abs_sub _ _
    _ ≤ Cl * D.κ (m - 1) + D.κ (m - 1) := by
        refine add_le_add h3 ?_
        rw [abs_mul, abs_of_nonneg hB]
        exact mul_le_of_le_one_right hB h4
    _ = _ := by ring

/-- **The size ledger at a context.** -/
theorem covGrad_ledger (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → ∃ Ccov Cn : ℝ, 0 ≤ Ccov ∧ 0 ≤ Cn ∧
      ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
        {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ}
        {j₀ M : ℕ}, 2 ≤ M →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
          Ce cker j₀ M) (_x : TermResAux c),
        (∀ t, AVRegularity.CycleComparison.Coarse.covBound
            (menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) ≤
          (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) * c.D.termRho cr M ^ 2) ∧
        Continuous (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) ∧
        (∀ t, ∑ jl : Fin 2 × Fin 2, |covGradN c.D M t jl.1 jl.2| ≤ Cn * c.D.κ (M - 1)) ∧
        Continuous (covGradN c.D M) := by
  obtain ⟨Ccov, hC1, Λ₁, hΛ₁, hest⟩ := CycleReference.bandChain_covariance_estimates X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨Cl, hCl1, Λ₂, hΛ₂, hled⟩ := CycleReference.bandChain_uniform_ledger X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun A hΛ => ⟨4 * Ccov, 4 * (Cl + 1), by linarith,
    by linarith, ?_⟩⟩
  have hΛa : Λ₁ ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛb : Λ₂ ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := hΛ₁.trans hΛa
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M hM2 c x
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hνM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 X.hζ hband le_rfl
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (α := c.D.α) (q := c.D.q)
    (hDΛ ▸ hΛ1)
  have hρ : 0 < c.D.termRho cr M := mul_pos (x.one ▸ one_pos) (Real.sqrt_pos.2 (mul_pos hν hh))
  have hΛcov : Λ₁ ≤ A.Λ := hΛa
  have e1 : ∀ t, menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t =
      ocCovariance X.α X.q A.Λ X.ζ M (c.D.κ M) (c.D.κ (M - 1)) c.tp t := by
    intro t
    simp only [menuCovPrimitive]
    rw [hDα, hDq, hDΛ, hDζ]
    rfl
  have e2 : c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q =
      ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q := by
    simp only [OCData.eps]
    rw [hDα, hDq, hDΛ]
  have e3 : c.D.termRho cr M ^ 2 = ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 := by
    have h1 := congrArg (fun r : ℝ => (r * Real.sqrt (c.D.κ (M - 1) *
      ocTauPP c.D.α c.D.q c.D.Λ M)) ^ 2) x.one
    unfold OCData.termRho OCData.termB OCData.termH ocRh
    refine h1.trans ?_
    rw [hDα, hDq, hDΛ, one_mul]
  have hpos : 0 < ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 := e3 ▸ pow_pos hρ 2
  have hentry : ∀ t i j, |menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t i j| ≤
      Ccov * ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q * c.D.termRho cr M ^ 2 := by
    intro t i j
    have h := (hest A.Λ hΛcov M (by omega) c.D.κ hband M hM2 le_rfl c.tp t i j).2.2.2
    rw [e1, e3]
    exact (div_le_iff₀ hpos).1 h
  have hε1 : 0 ≤ ocEpsilon X.q A.Λ M :=
    (Scales.epsilon_basic (m := M) X.hq.1 hΛ128).1.le
  have hl4 := ((hled A.Λ hΛb M (by omega) c.D.κ hband).2 M hM2 le_rfl (c.D.κ M) (c.D.κ (M - 1))
    rfl rfl).2.2.2.1
  have hl4' : c.D.κ M + ocEpsilon c.D.q c.D.Λ M ^ (2 * (1 + c.D.α)) / c.D.κ M ≤
      Cl * c.D.κ (M - 1) := by
    rw [hDα, hDq, hDΛ]; exact hl4
  have hΛD : 1 ≤ c.D.Λ := hDΛ ▸ hΛ1
  have hζD : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  refine ⟨fun t => ?_, ?_, fun t => ?_, covGradN_continuous hΛD hζD hνM⟩
  · have hER : 0 ≤ ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q * c.D.termRho cr M ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (covTrunc_epsilon_nonneg X hΛ128 (M - 1)) _) (sq_nonneg _)
    simp only [AVRegularity.CycleComparison.Coarse.covBound, Fin.sum_univ_two]
    rw [e2]
    have := hentry t 0 0
    have := hentry t 0 1
    have := hentry t 1 0
    have := hentry t 1 1
    nlinarith
  · have := covTrunc_primitive_continuous (α := c.D.α) (q := c.D.q) (m := M) (Λ := c.D.Λ)
      (ζ := c.D.ζ) hΛD hζD (ν := c.D.κ M) (B := c.D.κ (M - 1)) hνM (A.Mt M sXT sZT c.tp cr).anchor
    exact this
  · have hε : 0 ≤ ocEpsilon c.D.q c.D.Λ M := by
      rw [hDq, hDΛ]; exact hε1
    have hent := fun i j => covGradN_entry_le hΛD hζD hνM hl4' hν.le hε t i j
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    have := hent 0 0
    have := hent 0 1
    have := hent 1 0
    have := hent 1 1
    nlinarith

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The decomposition of the pre-truncation flux `G`**.

`G = menuGFlux = (comm - diag) - mean` with
* `comm`: `∑_{l=1}^p (l!)⁻¹ ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} Z` (first order in `Z`, `commFluxE`);
* `diag`: `menuDiagFluxPhys` of `P_pZ` (glued mean flux of cell degree `≥ 2`, minus `ocRefFlux ∇P_pZ`);
* `mean`: `menuMeanFluxE` of `P_pZ` (glued mean flux, grades `1..depth`, degrees `2..N+Dm`).

The statement `CovTruncGStatement` follows from four statements of the same prefix form: the
regularity of `G` (`CovTruncGRegStatement`) and one realization-and-bound statement per term
(`CovTruncCommStatement`, `CovTruncDiagStatement`, `CovTruncMeanStatement`), each with NO window
factor (every term is a gradient term; the dissipation part of the coarse energy bounds it).

Degenerate cases:
- `Z = 0`: all four terms vanish.
- `H_M = 0`: `comm = 0`.
- Constants: the three masses add, so the constant of `G` is the sum of the three constants. -/

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The commutator part of `G`. -/
def gCommTerm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m p : ℕ)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
      (covOperator (menuCovPrimitive D Mn m t))^[a'] (commFluxE (streamVel (D.Φ (m - 1)) t)
        (menuCovPrimitive D Mn m t) ((covOperator (menuCovPrimitive D Mn m t))^[l - 1 - a']
          (fun y => aZ t y v))) x

/-- The diagonal mean-flux part of `G` (acting on `P_pZ`). -/
def gDiagTerm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  menuDiagFluxPhys Mn G m N CcT
    (fun s y w => covPolyP (menuCovPrimitive D Mn m s) p (fun y' => aZ s y' w) y) t x v

/-- The mean-flux part of `G` (acting on `P_pZ`). -/
def gMeanTerm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) : Fin 2 → hr v.1.root :=
  menuMeanFluxE Mn G m N depth CcT (menuCovPRep Mn D m p aZ) t x v

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- `G = (comm - diag) - mean`. -/
theorem menuGFlux_eq_terms (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (x : Vec 2) :
    menuGFlux Mn G m N p depth CcT aZ v t x =
      (gCommTerm Mn G m p aZ v t x - gDiagTerm Mn G m N p CcT aZ v t x) -
        gMeanTerm Mn G m N p depth CcT aZ v t x := rfl

end Generic

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- Regularity of `G`: `C^{k_c+4p_T}` and `ℤ²`-periodic in space. -/
def CovTruncGRegAt (x : TermResAux c) (kc : ℕ) (_C : ℝ) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 4 * A.pT : ℕ) : ℕ∞)
        (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y) ∧
      IsZ2Periodic
        (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)

/-- The commutator term: realization of order `k_c + 4p_T`, mass `≤ C‖f‖₂`. -/
def CovTruncCommAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL (gCommTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.pT x.aZ v t y))
    (C * c.normF)

/-- The diagonal mean-flux term. -/
def CovTruncDiagAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (gDiagTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT c.CcT x.aZ v t y))
    (C * c.normF)

/-- The mean-flux term. -/
def CovTruncMeanAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (gMeanTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y))
    (C * c.normF)

/-- The three term bounds give the bound of `G` (Minkowski twice). -/
theorem covTruncG_bound_of_terms (x : TermResAux c) (kc : ℕ) {C₁ : ℝ}
    (hν : 0 < c.D.κ (M - 1)) (hπ : ∀ v, 0 < c.Gw.mass c.lawW v)
    (h1 : CovTruncCommAt c x kc C₁) (h2 : CovTruncDiagAt c x kc C₁)
    (h3 : CovTruncMeanAt c x kc C₁) :
    HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT)
      (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
      (fun v t y => toFluxL
        (menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y))
      ((C₁ * c.normF + C₁ * c.normF) + C₁ * c.normF) := by
  have h12 := covTruncSub _ _ _ _ _ hν hπ _ _ _ _ h1 h2
  have h123 := covTruncSub _ _ _ _ _ hν hπ _ _ _ _ h12 h3
  have hfun : (fun (v : CompIn c.Gw.comps) (t : ℝ) (y : Vec 2) => toFluxL
      (menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)) =
      fun v t y =>
        (toFluxL (gCommTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.pT x.aZ v t y) -
          toFluxL (gDiagTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT c.CcT x.aZ v t y)) -
        toFluxL (gMeanTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y) := by
    funext v t y
    rw [menuGFlux_eq_terms]
    simp only [toFluxL, WithLp.toLp_sub]
  rw [hfun]
  exact h123

end Terminal

def CovTruncGRegStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncGRegAt c x kc C

def CovTruncCommStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncCommAt c x kc C

def CovTruncDiagStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncDiagAt c x kc C

def CovTruncMeanStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncMeanAt c x kc C

/-- **The pre-truncation flux bound from the regularity and the three term bounds.** -/
theorem covTruncG_of_terms (hR : CovTruncGRegStatement) (hC : CovTruncCommStatement)
    (hD : CovTruncDiagStatement) (hM : CovTruncMeanStatement) : CovTruncGStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncGRegAt c x kc C)
    (P₂ := fun c x kc C => CovTruncCommAt c x kc C ∧ CovTruncDiagAt c x kc C ∧
      CovTruncMeanAt c x kc C) hR
    (termFluxPrefix_and (P₁ := fun c x kc C => CovTruncCommAt c x kc C)
      (P₂ := fun c x kc C => CovTruncDiagAt c x kc C ∧ CovTruncMeanAt c x kc C) hC
      (termFluxPrefix_and (P₁ := fun c x kc C => CovTruncDiagAt c x kc C)
        (P₂ := fun c x kc C => CovTruncMeanAt c x kc C) hD hM))
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncGRegAt c x kc C ∧ (CovTruncCommAt c x kc C ∧
      (CovTruncDiagAt c x kc C ∧ CovTruncMeanAt c x kc C)))
    (R := fun c x kc C => CovTruncGAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ128 hC₁
  refine ⟨3 * C₁, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C'
    hC'
  obtain ⟨hreg, h1, h2, h3⟩ := hP
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  refine ⟨hreg, hasFluxBound_mono_Y (covTruncG_bound_of_terms c x kc hν hπ h1 h2 h3) ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hC' hn]

end AVRegularity.Construction.Residual.Presentation
end
end
end

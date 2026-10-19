-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ErrorEnergy.ResidualAssembly
import AVRegularity.EntryTerminal.Ingredients.Recon.CoarseWeak.Terminal
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.NativeKernelFluxTime
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Proofs.WeakGen.Residual.Equation.IncomingPassage
import AVRegularity.EntryTerminal.Ingredients.Deadline.Deadline
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncPhysical
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.Join
import AVRegularity.EntryTerminal.Ingredients.Frontier.LayerNative
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Edge.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Partition.Scale
import AVRegularity.EntryTerminal.Ingredients.Recon.Scale.Scale
import AVRegularity.EntryTerminal.Ingredients.Recon.FluxSum.FluxSum
import AVRegularity.EntryTerminal.Ingredients.Recon.Conv.Conv
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.ConvAssembly
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerStatements

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Route

/-! **The residual clauses, the pieces at a context**:
- the lifted field is `C^{D_t−1}` and periodic on the window (terminal frame);
- the reconstruction is `(û, ŵ)` on the window;
- the paired solution at the order `k₀` on `[t_p, a+T₀]`;
- the restart and the subtraction of regularized solutions (generic);
- the drift of the stream is continuous and bounded. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Two scalar Sobolev fields with almost everywhere equal values are equal. -/
theorem e8c_torusHk_eq_of_value {k : ℕ} {f g : TorusHk k ℝ}
    (h : f.toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      g.toFunction.jet (valueIndex2 k)) : f = g := by
  apply TorusHk.ext_value
  apply Lp.ext
  exact (periodicJetRepresentative_ae f.val (valueIndex2 k)).symm.trans
    (h.trans (periodicJetRepresentative_ae g.val (valueIndex2 k)))

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀' : ℕ}

/-- A regularized solution restarts at a later time of its window. -/
theorem e8c_regSolution_restart {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {G : GenStage D hr Dm b j₀'} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {k : ℕ} {t₀ t₁ : ℝ} {f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)}
    {F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {g U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (h : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f F g U W Y) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k s t₁ (fun v => U v s) F g U W Y :=
  Providers.WeakGen.Residual.kernelWeakSolutionTorus_restart ν t₀ t₁ bv k Dm _ _ _ f F g U W Y h s hs

/-- The difference of two regularized solutions, read on the window. -/
theorem e8c_regSolution_sub {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {G : GenStage D hr Dm b j₀'} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {k : ℕ} {t₀ t₁ : ℝ}
    {f₁ f₂ f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)}
    {F₁ F₂ F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {g₁ g₂ g U₁ U₂ U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {W₁ W₂ W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Y₁ Y₂ Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (h₁ : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f₁ F₁ g₁ U₁ W₁ Y₁)
    (h₂ : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f₂ F₂ g₂ U₂ W₂ Y₂)
    (hwin : t₀ ≤ t₁)
    (hv : ∀ s ∈ Set.Icc t₀ t₁, Continuous (bv s) ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖bv s x‖ ≤ V)
    (hf : ∀ v, f v = f₁ v - f₂ v) (hF : ∀ v t, F v t = F₁ v t - F₂ v t)
    (hg : ∀ v t, g v t = g₁ v t - g₂ v t)
    (hu : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, U v t = U₁ v t - U₂ v t)
    (hw : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc t₀ t₁)), W v t = W₁ v t - W₂ v t)
    (hy : ∀ v u γ t, Y v u γ t = Y₁ v u γ t - Y₂ v u γ t) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f F g U W Y :=
  Providers.WeakGen.Residual.kernelWeakSolutionTorus_sub ν t₀ t₁ bv k Dm _ _ _ hwin hv
    f₁ f₂ f F₁ F₂ F g₁ g₂ g U₁ U₂ U W₁ W₂ W Y₁ Y₂ Y h₁ h₂ hf hF hg hu hw hy

end Generic

/-- **The lifted field is `C^{D_t−1}` and periodic on the window** (terminal frame). -/
theorem e8c_lift_regular
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (htp : c.tp ≤ c.a + A.T₀) (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hK : 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout)
    (hKd : A.Dt + A.NT + 2 * A.pT + 1 ≤ Kout)
    (hsX : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((A.Dt - 1 : ℕ) : ℕ∞)
        (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v) ∧
      IsZ2Periodic
        (fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v) := by
  have hi := Ingredients.Recon.termNativeInput c x hΛ hA hM htp hstart hK hsX hsZ
  intro v t ht
  refine ⟨native_input_lifted_spatial_contDiff hi (A.Dt - 1) ?_ t ht v,
    fun n y => congrFun (native_input_lifted_periodic hi t ht n y) v⟩
  show A.Dt - 1 + A.NT ≤ A.Khat Kout - 2 - 2 * A.pT
  have := le_max_left Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))
  unfold TermArgs.Khat
  omega

/-- **(3a) The reconstruction is the lifted field on the window.** -/
theorem e8c_identify
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) {K : CompIn c.Gw.comps → ℕ} (hK : ∀ v, A.k₀ ≤ K v)
    {uK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root)}
    (hval : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ v,
      (uK v t).toFunction.jet (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep t y v) :
    ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), truncateTorusHk (hK v) (uK v t) = c.û v t := by
  have hrep : menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep =
      termLiftedRep c.Gw M A.NT A.dW cr c.CcT c.aRep :=
    menuLiftedRep_terminal _ cr rfl _ _ _ _ _
  intro v t ht
  apply e8c_torusHk_eq_of_value
  have h1 := hval t ht v
  rw [hrep] at h1
  exact h1.trans (c.lift.2.2 v t ht).symm

/-- **(3b) The lift of the reconstruction is `ŵ` almost everywhere on the window.** -/
theorem e8c_identify_lift
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) {K : CompIn c.Gw.comps → ℕ} (hK : ∀ v, A.k₀ ≤ K v)
    {uK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v) (ScalarH v.1.root)}
    {wK : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (K v + 1) (ScalarH v.1.root)}
    (hwu : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ (K v)) (wK v t) = uK v t)
    (hid : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), truncateTorusHk (hK v) (uK v t) = c.û v t) :
    ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.succ_le_succ (hK v)) (wK v t) = c.ŵ v t := by
  intro v
  filter_upwards [hwu v, c.trunc v, ae_restrict_mem measurableSet_Icc] with t h1 h2 ht
  apply TorusHk.ext_value
  have e1 := congrArg (fun T => T.val (valueIndex2 (K v))) h1
  have e2 := congrArg (fun T => T.val (valueIndex2 A.k₀)) (hid v t ht)
  have e3 := congrArg (fun T => T.val (valueIndex2 A.k₀)) h2
  exact e1.trans (e2.trans e3.symm)

/-- **The paired solution at the order `k₀` on `[t_p, a + T₀]`.** -/
theorem e8c_paired
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (htp : c.tp ≤ c.a + A.T₀) (haM : c.aM ≤ c.tp) :
    c.Gw.IsRegSolution c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (c.D.κ M)
      (streamVel (c.D.Φ M)) A.k₀ c.tp (c.a + A.T₀)
      (fun v => truncateTorusHk hk₀w (c.V v c.tp)) (fun _ _ => 0) (fun _ _ => 0)
      (fun v t => truncateTorusHk hk₀w (c.V v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (c.Vw v t))
      (fun v u γ t => truncateTorusHk (by omega : A.k₀ + A.Dt - 1 ≤ Kw + A.Dt - 1)
        (c.Vk v u γ t)) :=
  e8c_regSolution_restart (Construction.Preservation.FullLift.native_reg_solution_truncate c.PW
    (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ c.Gw (c.D.κ M) c.aM (c.a + A.T₀)
    (streamVel (c.D.Φ M)) A.k₀ Kw hk₀w c.U₀ c.V c.Vw c.Vk c.paired.2.2.1) ⟨haM, htp⟩

/-- The drift of the stream is continuous and bounded on the window. -/
theorem e8c_drift (D : OCData) (m : ℕ) (t₀ t₁ : ℝ) :
    ∀ s ∈ Set.Icc t₀ t₁, Continuous (streamVel (D.Φ m) s) ∧
      ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖streamVel (D.Φ m) s x‖ ≤ V := by
  obtain ⟨hs, -, -, ⟨Vb, hVb⟩, -⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data
    (D.hΦ m) t₀ t₁
  exact fun s hs' => ⟨(hs s hs').continuous, max Vb 0, le_max_right _ _,
    fun y => (hVb s hs' y).trans (le_max_left _ _)⟩

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The bundled data of the residual clauses.** The data of the three regularized systems:
- `E8cRecon`: the reconstruction `(K, uK, wK, RK, qK)` and the fine flux realization `F_f`;
- `E8cPaired`: the paired solution `(V, Vw, Vk)` at the order `K_w ≥ k`;
- the data of the error system, as named families over both.

The bundles are generic over the fibres `hr`, as `GenStage.IsRegSolution` is: at a stage
`G : GenStage D ScalarH …` the instance `NormedSpace ℝ (ScalarH r)` is found through
`Real.normedCommRing`, while the generic statements derive it from `NormedAddCommGroup` and
`InnerProductSpace`, so each mention of `G.comps` or `G.fam.Γ` in a statement at `ScalarH` unfolds
the two instances; over `hr` the two paths agree syntactically. The families are named so that
statements stay short. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀' : ℕ}

/-- The reconstruction of the lifted field at descending slots `K ≥ k`, with the fine flux
realization `F_f` at the order `k`. -/
structure E8cRecon (G : GenStage D hr Dm b j₀') (k : ℕ) where
  K : CompIn G.comps → ℕ
  hK : ∀ v, k ≤ K v
  uK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)
  wK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v + 1) (hr v.1.root)
  RK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root))
  qK : ∀ v : CompIn G.comps, ℝ → TorusHk (K v) (hr v.1.root)
  Ff : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))

/-- The paired solution at the order `K_w ≥ k`. -/
structure E8cPaired (G : GenStage D hr Dm b j₀') (k : ℕ) where
  Kw : ℕ
  hk : k ≤ Kw
  V : ∀ v : CompIn G.comps, ℝ → TorusHk Kw (hr v.1.root)
  Vw : ∀ v : CompIn G.comps, ℝ → TorusHk (Kw + 1) (hr v.1.root)
  Vk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (hr u.1.root)

namespace E8cRecon

variable {G : GenStage D hr Dm b j₀'} {k : ℕ} (R : E8cRecon G k)

/-- The initial value of the truncated reconstruction. -/
def init (tp : ℝ) : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root) :=
  fun v => truncateTorusHk (R.hK v) (R.uK v tp)

/-- The truncated reconstruction. -/
def u : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root) :=
  fun v t => truncateTorusHk (R.hK v) (R.uK v t)

/-- The truncated lift of the reconstruction. -/
def w : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root) :=
  fun v t => truncateTorusHk (Nat.succ_le_succ (R.hK v)) (R.wK v t)

/-- The flux forcing of its kernel system `trunc RK + F_f`. -/
def F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
  fun v t => truncateTorusHk (R.hK v) (R.RK v t) + R.Ff v t

/-- The scalar forcing `trunc qK`. -/
def g : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root) :=
  fun v t => truncateTorusHk (R.hK v) (R.qK v t)

/-- The flux forcing of the error `−trunc RK − F_f`. -/
def errF : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
  fun v t => -(truncateTorusHk (R.hK v) (R.RK v t)) - R.Ff v t

/-- The scalar forcing of the error `−trunc qK`. -/
def errG : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root) :=
  fun v t => -(truncateTorusHk (R.hK v) (R.qK v t))

end E8cRecon

namespace E8cPaired

variable {G : GenStage D hr Dm b j₀'} {k : ℕ} (W : E8cPaired G k)

/-- The truncated initial value. -/
def init (tp : ℝ) : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root) :=
  fun v => truncateTorusHk W.hk (W.V v tp)

/-- The truncated solution. -/
def u : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root) :=
  fun v t => truncateTorusHk W.hk (W.V v t)

/-- The truncated lift. -/
def w : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root) :=
  fun v t => truncateTorusHk (Nat.succ_le_succ W.hk) (W.Vw v t)

/-- The truncated kernel lift. -/
def y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
  fun v u γ t => truncateTorusHk (Nat.sub_le_sub_right (Nat.add_le_add_right W.hk Dm) 1)
    (W.Vk v u γ t)

/-- The initial value of the error `trunc V(t_p) − û(t_p)`. -/
def errInit (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)) (tp : ℝ) :
    ∀ v : CompIn G.comps, TorusHk k (hr v.1.root) :=
  fun v => truncateTorusHk W.hk (W.V v tp) - û v tp

/-- The error `trunc V − û`. -/
def errU (û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)) :
    ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root) :=
  fun v t => truncateTorusHk W.hk (W.V v t) - û v t

/-- The lift of the error `trunc Vw − ŵ`. -/
def errW (ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)) :
    ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root) :=
  fun v t => truncateTorusHk (Nat.succ_le_succ W.hk) (W.Vw v t) - ŵ v t

/-- The kernel lift of the error `trunc Vk − ŷ`. -/
def errY (ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)) :
    ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root) :=
  fun v u γ t => W.y v u γ t - ŷ v u γ t

end E8cPaired

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Route

/-! **The clauses of the residual at a context, from its bounds**. At a context, from
`TermResidualBoundAt c C c_gap C_g`:

1. **Plain to kernel** (`plainToKernelStatementR` at the weak stage). The truncations of
   the reconstruction `uK` solve the regularized system with the forcing `(trunc RK + F_f, trunc qK)`.
   - The lifted field `menuLiftedRep` is `C^{D_t−1}` and periodic on the window, at terminal
     frame (`native_input_lifted_spatial_contDiff`, `native_input_lifted_periodic`; a `K_out` floor).
   - `F_f` is square-integrable (`TermResidualBoundAt`, from the fine tail bound).
2. **The paired solution.** `V` solves the same system with zero forcing on `[a_M, a+T₀]` at the
   order `K_w` (`c.paired`); truncate to `k₀` and restart at `t_p`.
3. **Subtraction and identification** (`kernelWeakSolutionTorus_sub`). The error `V − û`, with
   `Vw − ŵ` and the forcing `(−trunc RK − F_f, −trunc qK)`:
   - `trunc uK = û` on the window, from the two value clauses (`IsStageRecon.value`,
     `c.lift`; `menuLiftedRep_terminal`);
   - `trunc wK = ŵ` almost everywhere, from the values of the lifts.
4. **The residual clauses** are `ErrorResidualClause` for this pair, verbatim.

The floors of the prefix are hypotheses of `termResClausesAt_of`:
- the window `a_M ≤ t_p ≤ a + T₀`;
- the order `K_out` for the frame and for `C^{D_t−1}`;
- the slow and fast floors of the frame;
- the carrier pair `(1, 1)`;
- `k₀ ≤ K_s^W`.

The core steps are stated over the fibres `hr` (as the bundled data above), and the
context-level steps are separate declarations.

For `f = 0` all fields vanish and the clauses hold with zero forcing; for `t_p = a + T₀` the
window is a single time. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section Core

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀' : ℕ}

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- **Plain to kernel at a stage** (the weak stage, `seedK = freshK`). -/
theorem e8c_core_kernel (h2 : 2 ≤ Dm) (law : BirthLaw) (P : ProvParams)
    (sK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ) (G : GenStage D hr Dm b j₀') (m k : ℕ)
    (hinv : IsStageInvariant law P sK sK φ₀ hφ₀ Mnat kI tA tB S θK G) (hlev : G.level = m)
    (hkap : D.kap G.level = D.κ m) (hk : k ≤ kI.Ks) (π : CompIn G.comps → ℝ) (tp tf rs Xr : ℝ)
    (htA : tA ≤ tp) (htB : tf ≤ tB) (uh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (R : E8cRecon G k)
    (huh : ∀ v, ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((Dm - 1 : ℕ) : ℕ∞) (fun x => uh t x v) ∧
      IsZ2Periodic (fun x => uh t x v))
    (hrecon : IsStageRecon G m k π tp tf rs uh Xr R.K R.hK R.uK R.wK R.RK R.qK)
    (hFf : IsFluxRealization (ι := CompIn G.comps) (h := fun v => hr v.1.root) k
      (Set.Icc tp tf) (fineFluxF P sK sK φ₀ G uh) R.Ff)
    (hFm : ∃ Yf : ℝ, FluxMassLe (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (K := fun _ => k) (D.κ m) rs π (Set.Icc tp tf) R.Ff Yf) :
    ∃ ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root),
      G.IsRegSolution P sK sK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) k tp tf (R.init tp) R.F R.g R.u
        R.w ŷ := by
  obtain ⟨_, hY⟩ := hFm
  have hm := hY.1
  beta_reduce at hm
  exact Cascade.plainToKernelStatementR h2 law P sK sK φ₀ hφ₀ hsm hsupp Mnat kI tA tB S θK G m k
    hinv hlev hkap hk π tp tf rs Xr htA htB uh R.K R.hK R.uK R.wK R.RK R.qK huh hrecon R.Ff hFf hm

/-- **The regularized system of the error at a stage**: the difference of the paired solution
and the kernel system of the reconstruction, read through the identification. -/
theorem e8c_core_error {P : ProvParams} {sK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {G : GenStage D hr Dm b j₀'} {ν : ℝ} {bv : ℝ → Vec 2 → Vec 2}
    {k : ℕ} {tp tf : ℝ} (W : E8cPaired G k) (R : E8cRecon G k)
    {û : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {ŷ : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (hpaired : G.IsRegSolution P sK sK φ₀ hφ₀ ν bv k tp tf (W.init tp) (fun _ _ => 0)
      (fun _ _ => 0) W.u W.w W.y)
    (hU : G.IsRegSolution P sK sK φ₀ hφ₀ ν bv k tp tf (R.init tp) R.F R.g R.u R.w ŷ)
    (htp : tp ≤ tf)
    (hv : ∀ s ∈ Set.Icc tp tf, Continuous (bv s) ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖bv s x‖ ≤ V)
    (hid : ∀ v, ∀ t ∈ Set.Icc tp tf, R.u v t = û v t)
    (hidw : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp tf)), R.w v t = ŵ v t) :
    G.IsRegSolution P sK sK φ₀ hφ₀ ν bv k tp tf (W.errInit û tp) R.errF R.errG (W.errU û)
      (W.errW ŵ) (W.errY ŷ) :=
  e8c_regSolution_sub hpaired hU htp hv
    (fun v => by
      show W.errInit û tp v = W.init tp v - R.u v tp
      rw [hid v tp ⟨le_rfl, htp⟩]
      rfl)
    (fun v t => by
      show R.errF v t = 0 - R.F v t
      simp only [E8cRecon.errF, E8cRecon.F, zero_sub, neg_add'])
    (fun v t => by
      show R.errG v t = 0 - R.g v t
      simp only [E8cRecon.errG, E8cRecon.g]
      rw [zero_sub])
    (fun v t ht => by
      rw [hid v t ht]
      rfl)
    (fun v => by
      filter_upwards [hidw v] with t ht
      rw [ht]
      rfl)
    (fun v u γ t => rfl)

end Generic

/-- **The clauses of the residual at a stage**, from the system of the error and the
residual clause of the reconstruction. -/
theorem e8c_core_clauses {PW : ProvParams} {sK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {lawW : BirthLaw} {M k₀ : ℕ} {cK C bill tp tf : ℝ}
    {f : Vec 2 → ℝ} {G : GenStage D ScalarH Dm b j₀'} (W : E8cPaired G k₀) (R : E8cRecon G k₀)
    {û : ∀ v : CompIn G.comps, ℝ → TorusHk k₀ (ScalarH v.1.root)}
    {ŵ : ∀ v : CompIn G.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)}
    {ek : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k₀ + Dm - 1) (ScalarH u.1.root)}
    (hsys : G.IsRegSolution PW sK sK φ₀ hφ₀ (D.κ M) (streamVel (D.Φ M)) k₀ tp tf
      (W.errInit û tp) R.errF R.errG (W.errU û) (W.errW ŵ) ek)
    (hres : ErrorResidualClause G M k₀ (G.mass lawW) tp tf (D.termRStar cK M)
      (C * bill * Real.sqrt (l2NormSq f)) R.K R.hK R.RK R.qK R.Ff) :
    TerminalResidualClauses PW sK φ₀ hφ₀ lawW M W.Kw k₀ W.hk cK C bill tp tf f G W.V W.Vw û ŵ :=
  ⟨R.errF, R.errG, ek, hsys, hres.2.2, hres.1, hres.2.1⟩

end Core

/-! ### At a context

Each step is its own declaration: the data of the context are at the instance path of
`ScalarH`, the bundles at the generic one, and every passage between the two is checked once. -/

/-- The paired solution of the context as a bundle at the order `k₀`. -/
def e8cPairedOf (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) : E8cPaired c.Gw A.k₀ :=
  ⟨Kw, hk₀w, c.V, c.Vw, c.Vk⟩

/-- **The paired solution**, as a bundle. -/
theorem e8c_paired_bundle
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (htp : c.tp ≤ c.a + A.T₀) (haM : c.aM ≤ c.tp) :
    c.Gw.IsRegSolution c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (c.D.κ M)
      (streamVel (c.D.Φ M)) A.k₀ c.tp (c.a + A.T₀) ((e8cPairedOf c).init c.tp) (fun _ _ => 0)
      (fun _ _ => 0) (e8cPairedOf c).u (e8cPairedOf c).w (e8cPairedOf c).y :=
  e8c_paired c htp haM

/-- **(3a, 3b) The identification**, for a reconstruction bundle. -/
theorem e8c_identify_bundle
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (R : E8cRecon c.Gw A.k₀) {Xr : ℝ}
    (hrecon : IsStageRecon c.Gw M A.k₀ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep) Xr R.K R.hK R.uK R.wK
      R.RK R.qK) :
    (∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), R.u v t = c.û v t) ∧
      ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))), R.w v t = c.ŵ v t := by
  have hid := e8c_identify c R.hK hrecon.value
  exact ⟨hid, e8c_identify_lift c R.hK (uK := R.uK) (wK := R.wK) hrecon.plain.2.2.1 hid⟩

/-- **The system of the error**, for a reconstruction bundle. -/
theorem e8c_error_bundle
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (htp : c.tp ≤ c.a + A.T₀) (haM : c.aM ≤ c.tp) (R : E8cRecon c.Gw A.k₀)
    {ŷ : ∀ v u (_ : c.Gw.fam.Γ v u), ℝ → TorusHk (A.k₀ + A.Dt - 1) (ScalarH u.1.root)}
    (hU : c.Gw.IsRegSolution c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (c.D.κ M)
      (streamVel (c.D.Φ M)) A.k₀ c.tp (c.a + A.T₀) (R.init c.tp) R.F R.g R.u R.w ŷ)
    (hid : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), R.u v t = c.û v t)
    (hidw : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))), R.w v t = c.ŵ v t) :
    c.Gw.IsRegSolution c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ (c.D.κ M)
      (streamVel (c.D.Φ M)) A.k₀ c.tp (c.a + A.T₀) ((e8cPairedOf c).errInit c.û c.tp) R.errF
      R.errG ((e8cPairedOf c).errU c.û) ((e8cPairedOf c).errW c.ŵ) ((e8cPairedOf c).errY ŷ) :=
  e8c_core_error _ R (e8c_paired_bundle c htp haM) hU htp (e8c_drift c.D M _ _) hid hidw

/-- **The residual clauses at a context, for a reconstruction bundle.** -/
theorem e8c_clauses_bundle
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (htp : c.tp ≤ c.a + A.T₀) (haM : c.aM ≤ c.tp)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hK : 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout)
    (hKd : A.Dt + A.NT + 2 * A.pT + 1 ≤ Kout)
    (hsX : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT) (hk0 : A.k₀ ≤ kW.Ks)
    {C cgap Cg : ℝ} (R : E8cRecon c.Gw A.k₀) {Xr : ℝ}
    (hrecon : IsStageRecon c.Gw M A.k₀ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀) (c.D.termRStar cK M)
      (menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep) Xr R.K R.hK R.uK R.wK
      R.RK R.qK)
    (hFf : IsFluxRealization (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) A.k₀
      (Set.Icc c.tp (c.a + A.T₀))
      (fineFluxF c.PW (A.Kw_ c.D M nW) (A.Kw_ c.D M nW) A.φ₀ c.Gw
        (menuLiftedRep (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.dW c.CcT c.aRep)) R.Ff)
    (hFm : ∃ Yf : ℝ, FluxMassLe (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => A.k₀) (c.D.κ M) (c.D.termRStar cK M) (c.Gw.mass c.lawW)
      (Set.Icc c.tp (c.a + A.T₀)) R.Ff Yf)
    (hres : ErrorResidualClause c.Gw M A.k₀ (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
      (c.D.termRStar cK M) (C * c.bill cgap Cg * c.normF) R.K R.hK R.RK R.qK R.Ff) :
    TerminalResidualClauses c.PW (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ c.lawW M Kw A.k₀ hk₀w cK C
      (c.bill cgap Cg) c.tp (c.a + A.T₀) c.f c.Gw c.V c.Vw c.û c.ŵ := by
  have hterm : c.D.term = M := c.data.2.2.2.2.2.2
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hkap : c.D.kap c.Gw.level = c.D.κ M := by
    rw [hlev]
    unfold OCData.kap
    rw [hterm, min_self]
  obtain ⟨ŷ, hU⟩ := e8c_core_kernel (le_max_left _ _ : 2 ≤ A.Dt) c.lawW c.PW (A.Kw_ c.D M nW)
    A.φ₀ A.hφ₀ hA.2.1.1 hA.2.1.2.2.2 (M + A.Jw) kW c.aM (c.a + A.T₀) _ _ c.Gw M A.k₀
    c.weak.2.2.2.2.2.2.2.2.2 hlev hkap hk0 (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
    (c.D.termRStar cK M) Xr haM le_rfl _ R
    (e8c_lift_regular c x hΛ hA hM htp hstart hK hKd hsX hsZ) hrecon hFf hFm
  obtain ⟨hid, hidw⟩ := e8c_identify_bundle c R hrecon
  exact e8c_core_clauses (e8cPairedOf c) R (e8c_error_bundle c htp haM R hU hid hidw) hres

/-- **The residual clauses at a context**, given the floors of the prefix. -/
theorem termResClausesAt_of
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (hΛ : 128 ≤ A.Λ) (hA : A.Valid) (hM : j₀ + 2 ≤ M)
    (htp : c.tp ≤ c.a + A.T₀) (haM : c.aM ≤ c.tp)
    (hstart : IsCarrierStart X.α X.q A.Λ A.bw 1 1 j₀)
    (hK : 4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2 ≤ Kout)
    (hKd : A.Dt + A.NT + 2 * A.pT + 1 ≤ Kout)
    (hsX : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + 2) (2 * A.pT) + A.Dt + 2 ≤ sZT) (hk0 : A.k₀ ≤ kW.Ks)
    (C cgap Cg : ℝ) : TermResClausesAt c x C cgap Cg := by
  intro hB
  obtain ⟨K, hK', uK, wK, RK, qK, Ff, Xr, hrecon, hFf, hFm, hres⟩ := hB
  exact e8c_clauses_bundle c x hΛ hA hM htp haM hstart hK hKd hsX hsZ hk0
    ⟨K, hK', uK, wK, RK, qK, Ff⟩ hrecon hFf hFm hres

end AVRegularity.EntryTerminal.Route
end

section
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Route

/-! **The residual clauses are proved: `TermResClausesStatement`.** The prefix of
`termResClausesAt_of`:
- `Λ₀` is the threshold of the composition deadline (`deadline`); the window
  `a_M ≤ t_p ≤ a + T₀` holds past its level `M₂` (`e8c_window`);
- the coarse order is free (`kc₀ = 0`);
- the slow and fast floors `max (N_T + 2) (2p_T) + D_t + 2` and the order floor
  `max (4(N_T + D_t) + 16 + D_t + 6p_T + 2) (D_t + N_T + 2p_T + 1)` are those of the frame;
- `K_need = k₀`, so `k₀ ≤ K_s ≤ K_s^W` (the weak allocation);
- the carrier pair is `(1, 1)` and `M₀ = max (j₀ + 2) M₂`;
- the constants `C₀, c_gap, C_g` are free (the clauses hold for every bound). The window needs only `0 < c_P`, and `t_p = a + T₀` is allowed. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The window of the residual clauses**: `a_M ≤ t_p` from the preparation, and `t_p ≤ a + T₀` past the
composition deadline. -/
theorem e8c_window
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (hΛ : 128 ≤ A.Λ) (hcP : 0 < cP) (hdl : DeadlineAtM A CP M) :
    c.tp ≤ c.a + A.T₀ ∧ c.aM ≤ c.tp := by
  obtain ⟨-, -, h3, -⟩ := c.data
  have hP := c.prep
  have hd := hdl c.D c.data c.a c.aM c.tp c.weak.2.1
    (by simpa [OCData.termH] using hP.2.2.1)
  have hpos : 0 < c.D.termH M := by
    simp only [OCData.termH]
    exact Construction.Stream.ocTauPP_pos (by omega)
  have hτ : 0 ≤ ocTau X.α X.q A.Λ (M - 1) := (Construction.Stream.ocTau_pos (by omega)).le
  have hτ2 : 0 ≤ ocTauPP X.α X.q A.Λ (M - 1) := (Construction.Stream.ocTauPP_pos (by omega)).le
  have hch : 0 ≤ cP * c.D.termH M := mul_nonneg hcP.le hpos.le
  exact ⟨by linarith, by linarith [hP.2.1]⟩

/-- **The clauses of the residual from its bounds.** -/
theorem termResClauses : TermResClausesStatement := by
  intro X
  obtain ⟨Λd, hΛd, hd⟩ := deadline X
  refine ⟨Λd, hΛd, fun A hΛ hV => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := le_trans hΛd hΛ
  refine ⟨0, fun kc _ => ?_⟩
  refine ⟨max (A.NT + 2) (2 * A.pT) + A.Dt + 2, max (A.NT + 2) (2 * A.pT) + A.Dt + 2,
    max (4 * (A.NT + A.Dt) + 16 + A.Dt + 6 * A.pT + 2) (A.Dt + A.NT + 2 * A.pT + 1),
    fun sXT sZT hX hZ Kout hKout => ⟨A.k₀, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ hKs _ _ _ cK CK CL Cχ Cread Cid kW _ _ hWA
    cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨M₂, hM₂⟩ := hd A hΛ hV CP
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ hcar =>
    ⟨max (j₀ + 2) M₂, fun M hM c x => ?_⟩⟩
  obtain ⟨htp, haM⟩ := e8c_window c hΛ128 hcP (hM₂ M (le_trans (le_max_right _ _) hM))
  exact fun C' cgap' Cg' => termResClausesAt_of c x hΛ128 hV (le_trans (le_max_left _ _) hM)
    htp haM hcar (le_trans (le_max_left _ _) hKout) (le_trans (le_max_right _ _) hKout) hX hZ
    (le_trans hKs hWA.1) C' cgap' Cg'

end AVRegularity.EntryTerminal.Route
end
end
end

section
@[expose] public noncomputable section

section
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Route

/-! **The terminal residual and the error energy from the open bound statements.** With the join of the
five bounds (`termResidualBound_of_steps`) and the residual assembly (`residualBundled_of_steps`),
the residual over the bundled data follows from:
- the five bound statements (covariance truncation, inner flux, coarse filter tails,
  reconstruction, fine tail);
- the conversion of the bounds to the clauses of the statement.

The error energy adds only the proved quiet entrance (`errorEnergyBundled_of_residual`). -/

/-- **The bundled residual from the five bound statements and the conversion.** -/
theorem residualBundled_of_bounds (h2a : TermCovTruncStatement) (h2b : TermFrontierStatement)
    (h3 : TermFilterStatement) (hrec : TermReconStatement) (hfine : TermFineTailStatement)
    (hC : TermResClausesStatement) : ResidualBundled :=
  residualBundled_of_steps (termResidualBound_of_steps h2a h2b h3 hrec hfine) hC

/-- **The bundled error energy from the five bound statements and the conversion.** -/
theorem errorEnergyBundled_of_bounds (h2a : TermCovTruncStatement) (h2b : TermFrontierStatement)
    (h3 : TermFilterStatement) (hrec : TermReconStatement) (hfine : TermFineTailStatement)
    (hC : TermResClausesStatement) : ErrorEnergyBundled :=
  errorEnergyBundled_of_residual (residualBundled_of_bounds h2a h2b h3 hrec hfine hC)
    QuietEntrance.terminalQuietEntrance

/-! **The error energy from the Layer and the reconstruction statement.** Of the inputs of `errorEnergyBundled_of_bounds`:
- the covariance truncation `termCovTrunc`, the fine tail `termFineTail` and the conversion `termResClauses` are proved;
- the coarse filter tails are proved from their three steps (`filterPOp`, `covTruncSize`, `filterDefect`);
- the inner flux is proved from its six parts except the Layer (`termInnerLayer`):
  the rows (`termInnerRows`), the marker, the initial part, the identification and the
  smoothness.

So the error energy depends exactly on the Layer and on the reconstruction statement (`TermReconStatement`). -/

/-- **The coarse filter tails**, from their three proved steps. -/
theorem e9_termFilter : TermFilterStatement :=
  termFilter_of_steps filterPOp covTruncSize Ingredients.ResidualFlux.filterDefect

/-- **The response boundary**, from the Layer. -/
theorem e9_termFrontier_of_layer (hL : TermInnerLayerStatement) : TermFrontierStatement :=
  termFrontier_of_inner (frontierInner_of_parts Ingredients.Frontier.termInnerRows termInnerMarker
    hL termInnerInitial termInnerIdent_prefix termInnerSmooth)

/-- **The bundled error energy from the Layer and the reconstruction statement.** -/
theorem errorEnergyBundled_of_layer_recon (hL : TermInnerLayerStatement)
    (hrec : TermReconStatement) : ErrorEnergyBundled :=
  errorEnergyBundled_of_bounds termCovTrunc (e9_termFrontier_of_layer hL) e9_termFilter hrec
    Ingredients.ResidualFlux.termFineTail termResClauses

end AVRegularity.EntryTerminal.Route
end

section
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.EntryTerminal.Route

/-! **The error energy from the native temporal representatives.** With the Layer
(`termInnerLayer`) and the coarse weak statement (`termCoarseWeak_of_native`), every step of the reconstruction is
proved except `NativeTemporalRepresentativesStatement`:
- The coarse reconstruction step is `termReconCoarse_of_parts` at the coarse weak statement, the letters and the defect conversion;
- the ten other steps of `termRecon_of_steps` are proved.

So `ErrorEnergyBundled` depends only on `NativeTemporalRepresentativesStatement`. -/

/-- **The reconstruction from the native temporal representatives.** -/
theorem termRecon_of_native (hN : NativeTemporalRepresentativesStatement) : TermReconStatement :=
  termRecon_of_steps termReconSeq termReconSetting termReconFamily
    (termReconCoarse_of_parts (termCoarseWeak_of_native hN) termReconLetters
      termReconDefectConv)
    termReconEnergy termReconCoeff termReconPartition liftSettingMono termReconScale
    termReconFluxSum termReconConv termReconTimes

/-- **The bundled error energy from the native temporal representatives.** -/
theorem errorEnergyBundled_of_native (hN : NativeTemporalRepresentativesStatement) :
    ErrorEnergyBundled :=
  errorEnergyBundled_of_layer_recon Ingredients.Frontier.termInnerLayer (termRecon_of_native hN)

end AVRegularity.EntryTerminal.Route
end

section
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Route

/-! **The terminal residual from the native temporal representatives.** The bundled residual is
`residualBundled_of_bounds` at the five proved bound statements (covariance truncation, inner flux
with the Layer, coarse filter tails, reconstruction from the native representatives, fine tail)
and the conversion; its form is the unbundling `residualStatement_of_bundled`. -/

/-- **The bundled residual from the native temporal representatives.** -/
theorem residualBundled_of_native (hN : NativeTemporalRepresentativesStatement) :
    ResidualBundled :=
  residualBundled_of_bounds termCovTrunc
    (e9_termFrontier_of_layer Ingredients.Frontier.termInnerLayer) e9_termFilter
    (termRecon_of_native hN) Ingredients.ResidualFlux.termFineTail termResClauses

/-- **The residual in its stated form from the native temporal representatives.** -/
theorem residualStatement_of_native (hN : NativeTemporalRepresentativesStatement) :
    ResidualStatement :=
  residualStatement_of_bundled (residualBundled_of_native hN)

end AVRegularity.EntryTerminal.Route
end
end
end

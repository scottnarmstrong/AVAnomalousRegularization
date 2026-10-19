-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.FrontierInnerBound
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.CycleComparison.Reconstruction.PartitionBound
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct

section
section
/-! **The frontier inner flux at every context: facts of a context** (cascade side of the
bill residual).

* `BillCtx.rows'`: the rows of the extended stage have grade at most `H + 1`, and a row of
  grade at most `H` has a word of length at most `J + 1` (`hrows` of `frontierInner_bound`).
* `BillCtx.retained_mass_pos`: the masses of the retained family are positive.
* `BillCtx.trace_norm`: `‖Y₀‖ ≤ C_pr A_in` at the radius `ρ_enh` (clause 6 of the common
  preparation, through `common_preparation_retained_trace_norm`).
* `contextFrontierFrame`, `BillCtx.frontierAt`: the frame-level statements of the frontier production at
  the frontier frame of a context (the frame that `FrontierFrame` builds), with the retained
  data of the context at the order `k ≤ K_res`.

The cases of no omitted row, `A_in = 0`, `J = 0` and `t_p = t_f` are allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Frontier

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- A component whose births are all at scales `≥ m` has the empty word at the passage `m`. -/
theorem compWord_nil_of_old' (m : ℕ) (hm : 1 ≤ m) (v : Comp)
    (hv : ∀ e ∈ v.births, m ≤ e.scale) : compWord m v = [] := by
  rcases v with ⟨r, bs⟩
  cases bs with
  | nil => simp [compWord]
  | cons e rest =>
    have : e.scale ≠ m - 1 := by
      have := hv e (by simp)
      omega
    simp [compWord, this]

namespace BillCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- The rows of the extended stage of a context have grade at most `H + 1`, and a row of grade at
most `H` has a word of length at most `J + 1`. -/
theorem rows' : ∀ x ∈ c.G'.comps, compGrade x ≤ H + 1 ∧
    (compGrade x ≤ H → (compWord c.m x).length ≤ J + 1) := by
  intro x hx
  refine ⟨Providers.CascadeInvariants.grade_le_of_succ
    (Providers.CascadeInvariants.grade_le_of_cascade c.hseed.2.1 c.hcascade) c.hactual ⟨x, hx⟩, fun _ => ?_⟩
  have hm1 : 1 ≤ c.m := c.hlevel ▸ c.hactual.1
  have hx' : x ∈ succExtComps c.m (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ
      (succEta0 α q s)).A (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)).J
      c.G.comps := by
    rw [← c.hlevel, ← c.hactual.2.2.1]
    exact hx
  obtain ⟨v, hv, t, ht, rfl⟩ := Providers.CascadeInvariants.exists_of_mem_succExtComps hx'
  by_cases ht0 : t = []
  · subst ht0
    have hold : ∀ e ∈ v.births, c.m ≤ e.scale := fun e he =>
      c.hlevel ▸ (InitialValue.cascade_invariant c.hseed.2.1 c.hcascade v hv).1 e he
    have hv0 : compWord c.m v = [] := compWord_nil_of_old' c.m hm1 v hold
    simp only [succComp, dite_true, hv0, List.length_nil]
    exact Nat.zero_le _
  · rw [EntryTerminal.Ingredients.compWord_succComp_ne c.m v ht0]
    exact ht

/-- The masses of the retained family of a context are positive. -/
theorem retained_mass_pos (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (v : CompIn (c.G'.retained c.m H J).comps) :
    0 < (c.G'.retained c.m H J).mass c.law v := by
  unfold GenStage.mass
  exact Construction.Preservation.Buffer.birth_compMass_pos (c.q_gt hq) (c.lambda_ge hΛ) c.law v.1

/-- **`‖Y₀‖ ≤ C_pr A_in`** at the radius `ρ_enh` and in the weights of the retained family. -/
theorem trace_norm :
    weightedNorm (rhoEnh c.D kI.cr c.m) ((c.G'.retained c.m H J).mass c.law)
      ((c.G'.retained c.m H J).marker c.law) c.Y0 ≤ Cpr * c.Ain := by
  have hST : c.G.comps ⊆ (c.G'.retained c.m H J).comps := by
    have := incoming_mem_retained_of_cascade c.hseed.2.1 c.hcascade c.hactual c.hlevel
    exact this
  have h := common_preparation_retained_trace_norm c.law
    (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ c.G
    (c.G'.retained c.m H J) c.hlevel hST c.Preg c.hprep
    (fun x => compMarker c.D.q c.D.Λ c.law x) (Or.inr rfl) c.f c.Ain c.hf c.Y0 c.htrace
  rw [c.hlevel] at h
  exact h

variable {Kres : ℕ} [∀ r, Nontrivial (hr r)]

/-- **The frontier frame of a context** at the order `k` with the retained data `Y₀, Y_w` and the
edge inputs `yom` (the frame of the frontier statements; the frame that
`FrontierFrame` builds from the frame of a lifted field). -/
def contextFrontierFrame (k : ℕ) (Y0 : ∀ v : CompIn (c.G'.retained c.m H J).comps, TorusHk k (hr v.1.root))
    (Yw : ∀ v : CompIn (c.G'.retained c.m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (yom : ∀ v u (_ : c.G'.fam.Γ v u), ℝ →
      TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)) :
    Preservation.Frontier.Frame c.D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
  { G := c.G, G' := c.G', law := c.law, m := c.m, H := H, J := J, k := k,
    cr := kI.cr, η := succEta0 α q s,
    θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
    θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
    tp := c.tp, tf := c.tf, Y0 := Y0, Yw := Yw, yom := yom }

/-- **The three frame-level frontier statements at the frontier frame of a context**, from the
frontier production at one value of `grade` (its default join), at the retained data of order
`k ≤ K_res`. -/
theorem frontierAt {C : ℝ} {mStar : ℕ} {grade : Bool}
    (hT : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
      Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar grade)
    (hm : mStar ≤ c.m) (k : ℕ) (hk : k ≤ Kres)
    (Y0 : ∀ v : CompIn (c.G'.retained c.m H J).comps, TorusHk k (hr v.1.root))
    (Y : ∀ v : CompIn (c.G'.retained c.m H J).comps, ℝ → TorusHk k (hr v.1.root))
    (Yw : ∀ v : CompIn (c.G'.retained c.m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : (c.G'.retained c.m H J).fam.Γ v u), ℝ →
      TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (htrace : IsRetainedTrace c.G (c.G'.retained c.m H J) c.m p c.tp (c.Preg c.f) Y0)
    (hsol : (c.G'.retained c.m H J).IsRegSolution
      (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀
      (c.D.κ (c.m - 1)) (streamVel (c.D.Φ (c.m - 1))) k c.tp c.tf Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk)
    (yom : ∀ v u (_ : c.G'.fam.Γ v u), ℝ →
      TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root))
    (hyom : ∀ v u (γ : c.G'.fam.Γ v u) (hu : IsRetained c.m H J u.1),
      ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp c.tf)),
        (yom v u γ t).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
          c.G'.sysS (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
            hφ₀ v u γ t ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val (valueIndex2 (k + 1)))) :
    FrontierAt (contextFrontierFrame c k Y0 Yw yom) grade C :=
  hT c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
    c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
    c.Ain c.hf k hk Y0 Y Yw Yk htrace hsol yom (fun v u γ hu => by
      filter_upwards [hyom v u γ hu] with t ht
      rw [ht, sysS_succProvParams_eta Cw kI.cr σ₀ (succEta0 α q s) (succEta0 α q t) N p])

end BillCtx

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The reconstruction at a cascade frame: the orders of the window, the order floor, and the
plain-to-kernel statement**.

`FrameReconAt` has the form of the terminal `TermReconAt`: one instance of
`ReconWindowAt.physical_lift` at the actual family of the incoming stage. This module fixes what
does not depend on the window assembly:

* the orders of the window at a stage with maximal order `D_m`, depth `r`, lift order `N`, cleanup
  order `A_cl` and offset `ℓ` (`wKmax`, `wKlift`, `wLlift`, `wDens`, `wKres`, `wNchi`, `wR0`,
  `wPord`: the terminal `rKmax`, …, `rpord` with `k₀ = 0`), and `frameReconOrders`: they satisfy
  `ReconOrders` and the partition order as soon as the coarse order is at least `wKcFloor`;
* the order floor `succWindowFloor` of the auxiliary order `N_aux` that the window needs at a
  cascade frame (coarse field `W = P_pZ` and initial datum at `p_c = 1`, `J_c = 0`), and
  `windowOrders_of_floor`.

The floor of `IsSuccessorSchedule` does not give the coarse order of the window: that floor does
not depend on the seed depth `r₀`, while a chain of `r₀` identities of order `D₀ ≥ 3` forces
`K_max ≥ (D₀ - 2)·r₀`. The passage from the plain coupled system of the reconstruction to the
kernel system of the stage, generic over the stage (needed by both the terminal case and the
cascade), is `PlainToKernelStatementR`.

For depth `r = 0` (no edges) one has `K_max = ℓ`, and `wKcFloor` is
`max(2A_cl + 8 + 2ℓ + 4N + D_m, 3(N + D_m) + 2A_cl + 16 + ℓ)`. In `PlainToKernelStatementR`,
`(R + F_f, q)` is the forcing of `û`; with kernels of width `0` (`S = I`) the fine flux is `0` and
the kernel system is the plain one.

`succWindowFloor` need not be the least floor: the terminal choices of the orders are kept, and
`(D_m - 2)·r` could replace `D_m·r` in `K_max`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! ### The orders of the window -/

/-- `K_max = ℓ + D_m r`: the top of the descending slots `K_v = ℓ + D_m(r - rank v)`. -/
def wKmax (Dm depth ℓ : ℕ) : ℕ := ℓ + Dm * depth

/-- `K_lift`. -/
def wKlift (Dm depth N Acl ℓ : ℕ) : ℕ :=
  2 * Acl + 2 + wKmax Dm depth ℓ + Dm * (depth + 1) * N + 2

/-- `L_lift`. -/
def wLlift (Dm depth N ℓ : ℕ) : ℕ := wKmax Dm depth ℓ + Dm * (depth + 1) * N + 2

/-- The density order `m'`. -/
def wDens (Dm depth N Acl ℓ : ℕ) : ℕ := Acl + 1 + wKmax Dm depth ℓ + 2 * N + Dm

/-- The residual reserve `k_res`. -/
def wKres (Dm depth N Acl ℓ : ℕ) : ℕ := Acl + 3 + wKmax Dm depth ℓ + N

/-- The chart order `N_χ`. -/
def wNchi (Dm depth N Acl ℓ : ℕ) : ℕ := Acl + 2 + wKmax Dm depth ℓ + 2 * N + Dm

/-- The classical order of the coarse field `r₀ = k_c + N + D_m - 1`. -/
def wR0 (Dm N kc : ℕ) : ℕ := kc + (N + Dm) - 1

/-- The partition order `4(N + D_m) + 2A_cl + 16 + K_max`. -/
def wPord (Dm depth N Acl ℓ : ℕ) : ℕ := 4 * (N + Dm) + 2 * Acl + 16 + wKmax Dm depth ℓ

/-- A sufficient floor of the coarse order `k_c`: the orders of the window (the terminal choice
`m' + k_res + N + 4`) and the partition order. -/
def wKcFloor (Dm depth N Acl ℓ : ℕ) : ℕ :=
  max (wDens Dm depth N Acl ℓ + wKres Dm depth N Acl ℓ + N + 4)
    (3 * (N + Dm) + 2 * Acl + 16 + wKmax Dm depth ℓ)

/-- **The orders of the window at a stage**: above the floor of the coarse order, the orders
satisfy `ReconOrders`, and the partition order is at most `k_c + N + D_m`. -/
theorem frameReconOrders {Dm depth N Acl ℓ kc : ℕ} (Jc pc : ℕ) (hD2 : 2 ≤ Dm) (hN1 : 1 ≤ N)
    (hA1 : 1 ≤ Acl) (hkc : wKcFloor Dm depth N Acl ℓ ≤ kc) :
    ReconOrders Dm N depth (wKlift Dm depth N Acl ℓ) (wLlift Dm depth N ℓ) kc Jc pc
        (wR0 Dm N kc) (wKmax Dm depth ℓ) Acl (wDens Dm depth N Acl ℓ) (wKres Dm depth N Acl ℓ)
        (wNchi Dm depth N Acl ℓ) ∧
      wPord Dm depth N Acl ℓ ≤ kc + (N + Dm) := by
  have h1 : wDens Dm depth N Acl ℓ + wKres Dm depth N Acl ℓ + N + 4 ≤ kc :=
    le_trans (le_max_left _ _) hkc
  have h2 : 3 * (N + Dm) + 2 * Acl + 16 + wKmax Dm depth ℓ ≤ kc :=
    le_trans (le_max_right _ _) hkc
  have hDH : Dm ≤ Dm * (depth + 1) * N := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) hN1)
  simp only [wDens, wKres, wNchi, wKlift, wLlift, wR0, wPord] at h1 ⊢
  refine ⟨?_, by omega⟩
  exact
    { hD2 := hD2, hAcl := hA1, hK := by omega, hrL := by omega, hJL := by omega,
      hDL := by omega, hK2 := by omega, hord := by omega, hk := by omega, hNχ := by omega,
      hNχ' := by omega, hkres := by omega, hmr := by omega, hrW := by omega,
      hNco := by omega, hordd := by omega, hrK := by omega }

/-- **The floor of the auxiliary order of the window at a cascade frame** (offset `ℓ = 0`,
`p_c = 1`, `J_c = 0`): `P_pZ ∈ H^{N_aux - 2p}` is truncated to the coarse field at the order
`k_c + 1 + (N + D_m)` and to the initial datum at the order `k_c + (r + 3)(N + D_m + 12)`. -/
def succWindowFloor (Dm depth N p Acl : ℕ) : ℕ :=
  2 * p + wKcFloor Dm depth N Acl 0 + (depth + 3) * (N + Dm + 12)

/-- Above `succWindowFloor` the coarse field and the initial datum of the window are truncations
of `P_pZ`. -/
theorem windowOrders_of_floor {Dm depth N p Acl Naux : ℕ}
    (h : succWindowFloor Dm depth N p Acl ≤ Naux) :
    wKcFloor Dm depth N Acl 0 + 1 + (N + Dm) ≤ Naux - 2 * p ∧
      wKcFloor Dm depth N Acl 0 + (depth + 3) * (N + Dm + 12) ≤ Naux - 2 * p := by
  have h1 : N + Dm + 12 ≤ (depth + 3) * (N + Dm + 12) :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp only [succWindowFloor] at h
  constructor <;> omega

/-! ### Plain to kernel -/

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The reconstruction order floor suffices for the reconstruction at a cascade frame.**

The passage statements assume `succReconFloor r₀ D₀ H J N p A_cl L_c ≤ N_aux`. This module checks
that the premise gives every order the assembly of the bill residual uses, at the maximal order
`D = D_{H+1}` and the depth `r = r_H` of the incoming family:
* `succWindowFloor_le_succReconFloor`: the floor of the window (`succWindowFloor`) is below it, so
  `frameReconOrders` and `windowOrders_of_floor` apply (`windowOrders_of_succReconFloor`);
* `fluxOrders_of_succReconFloor`: at the coarse order `k_c = wKcFloor D r N A_cl 0` the three
  flux pieces fit: `k_c + 4p + 2 ≤ N_aux` (covariance truncation), `k_c + 2p ≤ N_aux` (response
  boundary; with `N_aux ≤ K_res` it is the order of the frontier statements), and
  `k_c + 2p + (D - 2) + L_c + 1 + N + 2p ≤ N_aux` (coarse filter tails).

The cases `r = 0` (no edge) and `p = 0` are covered, since no positivity is used; the statements
are arithmetic in the two schedules `succSchedD`, `succSchedR`, which enter as opaque numbers. -/

@[expose] public section

namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-- The coarse order of the window is below the first group of the reconstruction order floor. -/
theorem wKcFloor_le (D r N Acl : ℕ) :
    wKcFloor D r N Acl 0 ≤ 4 * (N + D) + 2 * Acl + 16 + 2 * D * r := by
  have h : 2 * D * r = 2 * (D * r) := Nat.mul_assoc 2 D r
  simp only [wKcFloor, wDens, wKres, wKmax]
  exact max_le (by omega) (by omega)

/-- **The reconstruction order floor implies the floor of the window.** -/
theorem succWindowFloor_le_succReconFloor (r₀ D₀ H J N p Acl Lc : ℕ) :
    succWindowFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N p Acl ≤
      succReconFloor r₀ D₀ H J N p Acl Lc := by
  have h1 := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have h2 := le_max_right (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  simp only [succWindowFloor, succReconFloor]
  omega

/-- Above the reconstruction order floor the coarse field and the initial datum of the window are
truncations of `P_pZ ∈ H^{N_aux - 2p}`. -/
theorem windowOrders_of_succReconFloor {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 + 1 +
          (N + succSchedD D₀ N p (H + 1)) ≤ Naux - 2 * p ∧
      wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 +
          (succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) ≤ Naux - 2 * p :=
  windowOrders_of_floor ((succWindowFloor_le_succReconFloor r₀ D₀ H J N p Acl Lc).trans h)

/-- **Above the reconstruction order floor the three flux pieces fit at the coarse order of the
window.** -/
theorem fluxOrders_of_succReconFloor {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 + 4 * p + 2 ≤ Naux ∧
      wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 + 2 * p ≤ Naux ∧
      wKcFloor (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl 0 + 2 * p +
          (succSchedD D₀ N p (H + 1) - 2) + Lc + 1 + N + 2 * p ≤ Naux := by
  have h1 := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have h2 := le_max_left (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  simp only [succReconFloor] at h
  refine ⟨by omega, by omega, by omega⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The reconstruction window at a cascade frame: the bodies of the steps** (cascade side of
the bill residual).

The window theorem `ReconWindowAt.physical_lift` is applied at the actual family of the incoming
stage `F.G` of a cascade frame, on `[t_p, t_f]`, at the slow length `√(κ_{m-1} τ''_m)`. Its
hypotheses are the fields of `ReconWindow`. This module states, at a frame, the groups of fields
that the cascade pieces prove; they are the terminal bodies (`ReconSeqAt`, `ReconSettingBody`,
`ReconFamilyBody`) under the substitution (`c.Gw → F.G`, `M → F.m`, `A.dW → F.depth`, `A.NT → F.N`,
`A.Dt → D_m`, `A.k₀ → 0`, `c.lawW → law`, the window `[t_p, t_f]`), with the orders `wKlift`,
`wLlift`, `wKmax` above.

* `FrameReconSeqAt`: the lift sequences of the observed pulses on the clipped
  windows, at the orders `(K_lift + D_m + 2, max (L_lift + 1) (L_lift + 2))`.
* `FrameReconSettingBody`: the lift settings of the observed pulses at
  `(K_lift, L_lift, L_lift)` with stored orders `(q_s, q_f)`, and the grading of the coefficients.
* `FrameReconFamilyBody`: the family side: descending slots, torus compatibility,
  the atlas, the pieces of the observed pulses, the partition, fast independence.

For a stage without identities `descSlots = D_m·depth` on every component, and the sequences and
settings are those of the trivial lift data. The window theorem itself asks `0 < T_obs`, which the
assembly treats apart. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The slots of the window: `K_v = ℓ + D_m (depth - rank v)`. -/
abbrev fK (ℓ : ℕ) : CompIn F.G.comps → ℕ :=
  fun v => ℓ + descSlots F.G.actualFamily F.depth Dm v

/-- The length of the window `T_obs = t_f - t_p`. -/
abbrev fTobs : ℝ := F.tf - F.tp

/-- The slow length of the window `√(κ_{m-1} τ''_m)`. -/
abbrev fRho : ℝ := Real.sqrt (D.κ (F.m - 1) * ocTauPP D.α D.q D.Λ F.m)

/-- The lift data of the observed pulse `k` in the form of the window. -/
abbrev fLiftData (k : ℤ) : LiftOperatorData (CompIn F.G.comps) (fun v => hr v.1.root) Dm :=
  pulseLiftData D.α D.q D.Λ F.m D.ζ (D.Φ (F.m - 1)) (D.hΦ (F.m - 1)) (D.κ F.m)
    (D.κ (F.m - 1)) (fRho F) (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) k
    (F.G.actualFamily.fiber (oddSlotOf k) ())

/-- The clipped lift window of the pulse `k`, in cell time: its left end. -/
abbrev fSeqStart (k : ℤ) : ℝ :=
  max (((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ F.m) F.tp / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2

/-- The clipped lift window of the pulse `k`, in cell time: its right end. -/
abbrev fSeqEnd (k : ℤ) : ℝ :=
  min (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) (F.tp + fTobs F) /
    ocEll D.q D.Λ F.m (D.κ F.m) ^ 2

/-- **The lift sequences of the observed pulses on the clipped
windows**, at the orders of the window. -/
def FrameReconSeqAt (Acl ℓ : ℕ) : Prop :=
  ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSequence (fLiftData F k) (wKlift Dm F.depth F.N Acl ℓ + Dm + 2)
      (max (wLlift Dm F.depth F.N ℓ + 1) (wLlift Dm F.depth F.N ℓ + 2))
      (fSeqStart F k) (fSeqEnd F k) F.N F.depth (F.CcT k)

/-- **The lift settings and the grading of the observed pulses**, at
given setting data. The stored orders `(q_s, q_f)` are free: with `s_X ≤ q_s`, `s_Z ≤ q_f` the
given sequences are promoted to the orders of the window
(`positive_layer_lift_sequence_promote`). -/
def FrameReconSettingBody (Acl ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ) (qs qf : ℕ)
    (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ) :
    Prop :=
  (∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (par k) (V k) F.depth F.N
      (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) (wLlift Dm F.depth F.N ℓ) qs qf
      CGl Cw (fun _ _ => Ca) bM Sb) ∧
  ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F), ∀ hh, hh ≤ F.depth →
    ∀ n, 1 ≤ n → n ≤ F.N → ∀ m'', 1 ≤ m'' → m'' ≤ n → ∀ j, j ≤ Acl + 2 + wKmax Dm F.depth ℓ →
      schurEnergyJet (F.G.mass law) (Set.Icc (fSeqStart F k) (fSeqEnd F k))
          (wLlift Dm F.depth F.N ℓ) j (F.CcT k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh * (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) ^ (n - m'' + j))

/-- **The family side of the window** at the actual family of the
incoming stage, an atlas and a partition constant. -/
def FrameReconFamilyBody (ℓ : ℕ) (T : F.G.actualFamily.Atlas) (Cpart : ℝ) : Prop :=
    F.G.actualFamily.IsDescending (fK F ℓ) ∧
    IsTorusCompatible F.G.actualFamily (fun _ => ()) (ocEpsilon D.q D.Λ (F.m - 1)) ∧
    T.IsConsecutiveClosed (Set.Icc F.tp (F.tp + fTobs F)) ∧
    T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ F.m) (Set.Icc F.tp (F.tp + fTobs F)) ∧
    T.IsQuiet (D.κ F.m) (ocEpsilon D.q D.Λ F.m) (ocEpsilon D.q D.Λ (F.m - 1)) ∧
    (∀ p q' (hpq : T.adjacent p q'),
      ((F.G.actualFamily.piece p).output ∩ (F.G.actualFamily.piece q').output ∩
        Set.Icc F.tp (F.tp + fTobs F)).Nonempty → T.sameCtx p q' hpq () ()) ∧
    (∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
      (F.G.actualFamily.piece (oddSlotOf k)).label = ocPulseChartIndex D.α D.q D.Λ F.m k ∧
      (∀ t, ⇑((F.G.actualFamily.piece (oddSlotOf k)).material t) =
        ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k) t) ∧
      ocPulseWindow D.α D.q D.Λ F.m k ∩ Set.Icc F.tp (F.tp + fTobs F) ⊆
        (F.G.actualFamily.piece (oddSlotOf k)).output) ∧
    Set.InjOn oddSlotOf ↑(ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F)) ∧
    IsLiftPartition (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
      (fun k => F.G.actualFamily.weight (oddSlotOf k)) (ocPulseWindow D.α D.q D.Λ F.m)
      (ocQuietTimes D.α D.q D.Λ D.ζ F.m) (Set.Icc F.tp (F.tp + fTobs F))
      (ocTau D.α D.q D.Λ F.m) Cpart ∧
    F.G.actualFamily.IsFastIndependentOn
      (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ F.m ∩ Set.Icc F.tp (F.tp + fTobs F))

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The reconstruction window at a cascade frame: the coarse side** (cascade side of the bill
residual).

The coarse data of the window `ReconWindow` at a cascade frame, the cascade form of the terminal
`ReconFluxRealizations`, `ReconCoarseBody`: the coarse field is `W = P_pZ` truncated to the order
`k_c + 1 + N + D_m`, the coarse flux is `F_c = F_cov - F_filter - F_front` for realizations of order
`k_c` of the three fluxes of the menu (the conclusions of `FrameCovTruncAt`, `FrameFrontierAt`,
`FrameFilterAt`).

* `FrameReconFluxRealizations`: the three realizations on `[t_p, t_f]`.
* `FrameReconCoarseBody`: the coarse setting, the coarse defect equation of `W`
  with the flux `F_c` (from `F.macroWeak` and the mean flux split), and the letters presenting
  the glued means.

For `p = 0` one has `P_p = I` and the covariance flux is the untruncated one; for zero fluxes
(`F_c = 0`) the coarse defect equation is the homogeneous one. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The coarse field of the window: `P_pZ` truncated to the order `k_c + 1 + N + D_m`. -/
abbrev frameReconW (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) :
    ∀ v : CompIn F.G.comps, ℝ → TorusHk (kc + 1 + (F.N + Dm)) (hr v.1.root) :=
  fun v t => truncateTorusHk hW (F.PZ v t)

/-- The coarse flux of the window `F_c = F_cov - F_filter - F_front` (a definition, so that the
subtraction on `TorusHk` is elaborated once). -/
def frameReconFc {kc : ℕ}
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)) :=
  fun v t => F1 v t - F3 v t - F2 v t

/-- The three flux realizations of order `k_c` on the window (from `FrameCovTruncAt`,
`FrameFrontierAt`, `FrameFilterAt`). -/
def FrameReconFluxRealizations (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    Prop :=
  IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc
      (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuCovTruncFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y))
      F1 ∧
    IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc
      (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuFrontierFlux F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m
        F.p F.H F.J (D.eps (F.m - 1)) F.η₀ F.aY v t y)) F2 ∧
    IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc
      (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuFilterFlux F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.m F.p
        (D.eps (F.m - 1)) F.η₀ F.aZ v t y)) F3

/-- **The coarse side of the window** at given coarse data. -/
def FrameReconCoarseBody (kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn F.G.comps,
      TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root)) : Prop :=
  IsCoarseSetting F.tp (F.tp + fTobs F) (fRho F) (D.κ (F.m - 1)) aC B₀C lamC
    (streamVel (D.Φ (F.m - 1))) (F.N + Dm) F.depth pc Jc kc ((F.N + Dm) + 8 * pc + 4)
    (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4))
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) AD CE (F.G.mass law) Aedge Cstar Θc ∧
  IsCoarseDefect F.tp (F.tp + fTobs F) (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)))
    (F.N + Dm) F.depth kc (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) AD CE
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) f0 (frameReconW F kc hW)
    (frameReconFc F F1 F2 F3) ∧
  ∀ r ∈ Finset.range (F.depth + 1),
    IsMeanPresentation (Set.Icc F.tp (F.tp + fTobs F)) (F.N + Dm) r AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (gluedMean (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
        (fun k => F.G.actualFamily.weight (oddSlotOf k))
        (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N r
        (fun k => fLiftData F k) F.CcT
        (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k))
        (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k)))

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **The reconstruction window at a cascade frame from the bodies of the steps** (cascade side
of the bill residual).

`mkFrameReconWindow`: the family side, the lift settings, the lift sequences,
the coarse side and the scales give the hypothesis `ReconWindow` of the window
theorem `ReconWindowAt.physical_lift` at the actual family of the incoming stage of the frame, on
`[t_p, t_f]`, with the coarse field `P_pZ` truncated to the order `k_c + 1 + N + D_m` and its
classical representative `F.aRep` at the order `k_c + N + D_m - 1`. It is the terminal
`mkReconWindow` at a frame, and it checks that the bodies above (the family side and the coarse
side) are literally the fields of the window.

For `ℓ = 0` this is the reconstruction at the order `0`, and for a stage without identities the
bodies are those of the trivial lift data. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The window at a frame from the bodies of the steps.** -/
theorem mkFrameReconWindow (F : Frame D hr Dm b j₀) (law : BirthLaw) {s : ℝ}
    (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (T : F.G.actualFamily.Atlas) (Cpart : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn F.G.comps,
      TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root))
    (ρs : ℝ)
    (hfam : FrameReconFamilyBody F ℓ T Cpart)
    (hset : FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hseq : FrameReconSeqAt F Acl ℓ)
    (hco : FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hα₀ : 0 < D.α) (hα₁ : D.α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - D.α) / 2)
    (hq : IsAdmissibleQ D.α s D.q) (hζ : IsFastProfile D.ζ) (hΛ : 128 ≤ D.Λ)
    (hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ) (hm : 2 ≤ F.m) (hν : 0 < D.κ F.m)
    (hB : 0 < D.κ (F.m - 1)) (hρs : 0 < ρs) (hρs_e : ρs ≤ ocEpsilon D.q D.Λ F.m)
    (hρs_R : ρs ≤ fRho F) (hRE : fRho F ≤ ocEpsilon D.q D.Λ (F.m - 1))
    (hTobs : 0 < fTobs F) (hkc : 1 ≤ kc)
    (Fc : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (hFc : ∀ v, Fc v =ᵐ[volume.restrict (Set.Icc F.tp (F.tp + fTobs F))]
      frameReconFc F F1 F2 F3 v) :
    ReconWindow D.α s D.q D.Λ D.ζ D.Φ F.m (D.hΦ (F.m - 1)) (D.κ F.m) (D.κ (F.m - 1)) F.tp
      (fTobs F) ρs F.G.actualFamily (fun _ => ()) (fK F ℓ) T oddSlotOf (F.G.mass law) Cpart
      F.depth F.N (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) qs qf F.CcT par V CGl
      Cwl Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 (frameReconW F kc hW) Fc F.aRep
      (wR0 Dm F.N kc) := by
  have hcd := isCoarseDefect_congr_ae hco.2.1 hFc
  obtain ⟨hdesc, htorus, hTcons, hTcov, hTq, hTact, hpp, hppinj, hpart, hquiet⟩ := hfam
  have htf : F.tp + fTobs F = F.tf := by simp only [fTobs]; ring
  have hrep : ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ v,
      IsClassicalRep (frameReconW F kc hW v t) (fun y => F.aRep t y v) (wR0 Dm F.N kc) := by
    intro t ht v
    rw [htf] at ht
    have h1 : wR0 Dm F.N kc ≤ F.Naux - 2 * F.p := by
      show kc + (F.N + Dm) - 1 ≤ _
      omega
    have h2 : wR0 Dm F.N kc ≤ kc + 1 + (F.N + Dm) := by
      show kc + (F.N + Dm) - 1 ≤ _
      omega
    exact classicalRep_truncate hW h2 _ _ (isClassicalRep_of_le (F.lift.2.1 v t ht).2 h1)
  have hr₀ : wR0 Dm F.N kc ≤ kc + 1 + (F.N + Dm) := by
    show kc + (F.N + Dm) - 1 ≤ _
    omega
  have hDr : F.N + Dm ≤ wR0 Dm F.N kc := by
    show _ ≤ kc + (F.N + Dm) - 1
    omega
  exact
    { hα₀ := hα₀, hα₁ := hα₁, hs₀ := hs₀, hs₁ := hs₁, hq := hq, hζ := hζ, hΛ := hΛ, hΦ := hΦ,
      hm := hm, hν := hν, hB := hB, hTobs := hTobs, hρs := hρs, hρs_e := hρs_e, hρs_R := hρs_R,
      hRE := hRE, hdesc := hdesc, htorus := htorus, hTcons := hTcons, hTcov := hTcov, hTq := hTq,
      hTact := hTact, hpp := hpp, hppinj := hppinj, hpart := hpart, hquiet := hquiet,
      hsetting := hset.1, hseq := hseq, hcs := hco.1, hcd := hcd, hrep := hrep, hr₀ := hr₀,
      hDr := hDr, hmean := hco.2.2 }

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **At a cascade frame: the positive lifts of the slot vanish at `t_p`**
(cascade side of the bill residual).

The cascade form of the terminal `seq_zero_at_tp`. For a
pulse `k` whose window contains `t_p` (`slotStart ≤ t_p ≤ (k + 61/48) τ`) the stretch
`[slotStart, t_p]` lies in the quiet margin `[t_p - τ', t_p + τ']` (`τ' = L τ`, `L ≥ 5`) and in
`[t_A, t_B]` (the entrance `t_A + τ' ≤ t_p ≤ t_B`). There the pulse drift vanishes and the edges
are fast independent (the stage invariant), so `r2c_quietZero_core` gives zero positive lifts at
`t_p`. The data are `familyLiftData` of the menu of the frame at `lenFactor`.

For `t_p = slotStart` the stretch is a point, and if no pulse window passes through `t_p` the
hypothesis `slotStart ≤ t_p ≤ (k + 61/48) τ` is empty and the lemma is not used. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison AVRegularity.EntryTerminal.Ingredients.Recon.Seq
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀)

/-- The lift data of the odd slot `k` of the incoming stage of the frame (the data of the first
clause of `F.lift`). -/
abbrev fSeqQ (k : ℤ) (hk : Odd k) :
    LiftOperatorData (CompIn F.G.comps) (fun v => hr v.1.root) Dm :=
  familyLiftData D F.m k (nativeChain F.m k) (F.Mn.lenFactor * liftLength D F.m)
    (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))

/-- The output window of a piece of the incoming stage is the pulse window. -/
theorem output_eq {Mnat : ℕ} (hnat : F.G.IsNatural Mnat) (hlev : F.G.level = F.m)
    (p : OddSlot) : (F.G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ F.m p.1 :=
  (hnat.1 p).2.1.trans (congrArg (ocPulseWindow D.α D.q D.Λ · p.1) hlev)

/-- The quiet margin geometry: between `t_p - 61τ/24` and `t_p` the `τ/24`-neighbourhood lies in the
quiet margin of half-width `Lτ`, and the time is at least `t_A` (cascade form of `seq_geometry`). -/
theorem geometry' {τ L tp kr aM : ℝ} (hτ : 0 < τ) (hL : 5 ≤ L)
    (hwin : tp ≤ (kr + 61 / 48) * τ) (haM : aM + 3 * τ ≤ tp) :
    ∀ u ∈ Set.Icc ((kr - 61 / 48) * τ) tp,
      Set.Icc (u - τ / 24) (u + τ / 24) ⊆ Set.Icc (tp - L * τ) (tp + L * τ) ∧ aM ≤ u := by
  have hLτ : 5 * τ ≤ L * τ := by nlinarith
  intro u hu
  refine ⟨fun y hy => ⟨by linarith [hu.1, hy.1], by linarith [hu.2, hy.2]⟩, by linarith [hu.1]⟩

/-- The cell-scale facts of a level `m ≤ D.term` of a band chain. -/
theorem cellScale_facts (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hch : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hmt : F.m ≤ D.term) :
    0 < D.cellScaleSq F.m ∧ ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 = D.cellScaleSq F.m := by
  have hκM : 0 < D.κ F.m := CycleReference.bandChain_pos hΛ hζ hch hmt
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hmt]
  refine ⟨?_, ?_⟩
  · unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hκM
  · rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]

/-- **The positive lifts of the slot `k` vanish at the cell time of `t_p`.** -/
theorem seq_zero_at_tp' {law : BirthLaw} {hφ₀ : Integrable F.φ₀} {Mnat : ℕ} {kI : InvConsts}
    {tA tB S θK : ℝ}
    (hinv : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G)
    (hlev : F.G.level = F.m) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hch : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hmt : F.m ≤ D.term)
    (hentry : tA + 3 * ocTau D.α D.q D.Λ F.m ≤ F.tp) (htp : F.tp ≤ tB)
    (hquietMargin : Set.Icc (F.tp - ocTauP D.α D.q D.Λ F.m) (F.tp + ocTauP D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m)
    {sX sZ : ℕ} {k : ℤ} (hk : Odd k)
    (hwin : F.tp ≤ ((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m)
    (hstart : D.slotStart F.m k ≤ F.tp)
    (hell : ∀ t ∈ Set.Icc (D.slotStart F.m k / D.cellScaleSq F.m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m),
      ∀ X' ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (fSeqQ F k hk).G t X' i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (fSeqQ F k hk).G t X' i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hseq : IsLiftSequence (fSeqQ F k hk) sX sZ (D.slotStart F.m k / D.cellScaleSq F.m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) F.N F.depth
      (F.CcT k)) :
    ∀ hh ≤ F.depth, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X' z v u,
      F.CcT k hh n m α (F.tp / D.cellScaleSq F.m) X' z v u = 0 := by
  classical
  obtain ⟨hnat, -, -, -, -, -, -, -, -, -, -, -, hfast, -⟩ := hinv
  have hfastM : F.G.fam.IsFastIndependentOn
      (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ F.m ∩ Set.Icc tA tB) := by
    simpa only [hlev] using hfast
  obtain ⟨hcs, hsq⟩ := cellScale_facts F hΛ hζ hch hmt
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hΛ
  have hLge := ChildInert.ocL_ge_five D.α D.q hΛ F.m
  have hTP : ocTauP D.α D.q D.Λ F.m = (ocL D.α D.q D.Λ F.m : ℝ) * ocTau D.α D.q D.Λ F.m := by
    have h5 : (0 : ℝ) < ocL D.α D.q D.Λ F.m := by linarith
    unfold ocTauP ocTau
    field_simp
  have hcol : Set.Icc (F.tp - (ocL D.α D.q D.Λ F.m : ℝ) * ocTau D.α D.q D.Λ F.m)
      (F.tp + (ocL D.α D.q D.Λ F.m : ℝ) * ocTau D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m := by rw [← hTP]; exact hquietMargin
  have hss : D.slotStart F.m k = ((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ F.m := rfl
  have hgeo := geometry' hτ hLge hwin hentry
  have hpt : ∀ t ∈ Set.Icc (D.slotStart F.m k / D.cellScaleSq F.m) (F.tp / D.cellScaleSq F.m),
      D.cellScaleSq F.m * t ∈ ocTrimmedQuietTimes D.α D.q D.Λ D.ζ F.m ∩ Set.Icc tA tB ∧
        D.cellScaleSq F.m * t ∈ ocPulseWindow D.α D.q D.Λ F.m k := by
    intro t ht
    have h1 : D.slotStart F.m k ≤ D.cellScaleSq F.m * t := by
      have := (div_le_iff₀ hcs).1 ht.1
      linarith
    have h2 : D.cellScaleSq F.m * t ≤ F.tp := by
      have := (le_div_iff₀ hcs).1 ht.2
      linarith
    obtain ⟨hg1, hg2⟩ := hgeo _ ⟨by rw [← hss]; exact h1, h2⟩
    refine ⟨⟨fun y hy => hcol (hg1 hy), hg2, h2.trans htp⟩, ⟨?_, h2.trans hwin⟩⟩
    rw [hss] at h1; exact h1
  have hsC : D.slotStart F.m k / D.cellScaleSq F.m ≤ F.tp / D.cellScaleSq F.m :=
    div_le_div_of_nonneg_right hstart hcs.le
  have hend : F.tp / D.cellScaleSq F.m ≤
      (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m :=
    div_le_div_of_nonneg_right hwin hcs.le
  intro hh hhH n hn m α X' z v u
  refine EntryTerminal.Ingredients.Recon.r2c_quietZero_core (fSeqQ F k hk) sX sZ F.N F.depth _ _ _ (F.CcT k) hseq hsC hend
    (fun t X'' i j => EntryWeakProofs.familyLiftData_metric_symmetric D F.m k _ _ _ t X'' i j)
    ⟨3 / 4, 5 / 4, by norm_num, fun t ht X'' ξ => hell t ⟨ht.1, ht.2.trans hend⟩ X'' ξ⟩
    (fun t ht z => ?_) (fun t ht v' u' d γ hγ w X'' z z' => ?_) hh hhH n hn m α _ ⟨hsC, le_rfl⟩
    X' z v u
  · have h0 : ocPulse D.α D.q D.Λ D.ζ F.m k (D.cellScaleSq F.m * t) = 0 :=
      Assembly.ocPulse_eq_zero_of_quiet hΛ hζ hk
        (ocTrimmedQuietTimes_subset_quiet hΛ D.ζ F.m (hpt t ht).1.1)
    show ocPulseCellDrift D.α D.q D.Λ D.ζ F.m (D.kap F.m) k t z = 0
    have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hmt]
    unfold ocPulseCellDrift
    rw [hkap, hsq, h0]
    simp only [zero_smul, smul_zero]
  · have hγ' : γ ∈ liftEdges (D.cellScaleSq F.m)
        (F.Mn.lenFactor * liftLength D F.m / D.eps (F.m - 1))
        (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩)) v' u' d := hγ
    obtain ⟨γ₀, -, -, hc⟩ := LiftSetting.mem_liftEdges_fiber hγ'
    have hmem := hpt t ht
    have hout : D.cellScaleSq F.m * t ∈ (F.G.fam.piece ⟨k, hk⟩).output := by
      rw [output_eq F hnat hlev]; exact hmem.2
    rw [hc]
    exact hfastM ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩) v' u' γ₀ d.1 w (D.cellScaleSq F.m * t)
      ⟨hmem.1, hout⟩ _ z z'

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The lift sequences of the observed pulses on the clipped windows at a cascade frame**
(cascade side of the bill residual).

The cascade form of the terminal `reconSeqStep_of_ctx`
(module `EntryTerminal.Ingredients.Recon.Seq.Main`). The first clause of `F.lift` is the lift
sequence of `familyLiftData` (the data `fSeqQ`) on the whole slot window. On the clipped window
of an observed pulse it is the restriction (the pulse window starts after `t_p`) or the restart at
`t_p` (the pulse window contains `t_p`: the positive lifts vanish at `t_p` by the quiet margin,
`seq_zero_at_tp'`). The data `fSeqQ` and `fLiftData` (`pulseLiftData`) agree on the pulse window,
so the sequence is one of `fLiftData`, and the lift setting of the observed pulse
promotes it to the orders of the window (`liftSequence_promote_of_setting`, no condition on the
stored orders `F.sX`, `F.sZ`).

If no pulse window contains `t_p` only the restriction remains, and for an empty family of
observed pulses the conclusion is empty. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison AVRegularity.EntryTerminal.Ingredients.Recon.Seq
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀)

/-- **The stage's data and the window's data agree** on the pulse window. -/
theorem seq_agree' {Mnat : ℕ} (hnat : F.G.IsNatural Mnat) (hlev : F.G.level = F.m)
    (hone : F.Mn.lenFactor = 1) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hch : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hmt : F.m ≤ D.term) (hm : 1 ≤ F.m)
    {k : ℤ} (hk : Odd k) :
    (fSeqQ F k hk).η = (fLiftData F k).η ∧
      ∀ t, D.cellScaleSq F.m * t ∈ ocPulseWindow D.α D.q D.Λ F.m k →
        SeqAgreeAt (fSeqQ F k hk) (fLiftData F k) t := by
  have hτ'' : 0 < ocTauPP D.α D.q D.Λ F.m := Construction.Stream.ocTauPP_pos hΛ
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hmt]
  have hkap1 : D.kap (F.m - 1) = D.κ (F.m - 1) := by
    unfold OCData.kap; rw [min_eq_left ((Nat.sub_le _ _).trans hmt)]
  have hρ : F.Mn.lenFactor * liftLength D F.m = fRho F := by
    rw [hone, one_mul]; rfl
  obtain ⟨-, hc⟩ := cellScale_facts F hΛ hζ hch hmt
  have hη : (fSeqQ F k hk).η = (fLiftData F k).η := by
    show D.kap F.m / D.kap (F.m - 1) = D.κ F.m / D.κ (F.m - 1)
    rw [hkap, hkap1]
  refine ⟨hη, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · funext X' i j
    show (familyLiftData D F.m k (nativeChain F.m k) (F.Mn.lenFactor * liftLength D F.m) _).G
      t X' i j = _
    rw [EntryWeakProofs.native_familyLiftData_metric D F.m hm k _ _ t X', hρ]
    show _ = ocMaterialMetric D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k) (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 * t)
      (fRho F • X') i j
    unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
    rw [hc, ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ'']
  · funext z
    show ocPulseCellDrift D.α D.q D.Λ D.ζ F.m (D.kap F.m) k t z = _
    rw [hkap]
    rfl
  · intro ε Φ i
    have hout : D.cellScaleSq F.m * t ∈ (F.G.fam.piece ⟨k, hk⟩).output := by
      rw [output_eq F hnat hlev]; exact ht
    have key := seq_sourceFlux_actual_eq F.G ⟨k, hk⟩ (D.cellScaleSq F.m)
      (F.Mn.lenFactor * liftLength D F.m / D.eps (F.m - 1)) (fSeqQ F k hk).η ε t hout Φ i
    have e2 : (fLiftData F k).edge = liftEdges (D.cellScaleSq F.m)
        (F.Mn.lenFactor * liftLength D F.m / D.eps (F.m - 1))
        (F.G.actualFamily.fiber ⟨k, hk⟩ ()) := by
      show liftEdges (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F / ocEpsilon D.q D.Λ (F.m - 1))
        (F.G.actualFamily.fiber (oddSlotOf k) ()) = _
      rw [oddSlotOf_of_odd hk, hc, hρ]
      rfl
    rw [e2]
    exact key

/-- The ellipticity of the lift metric of the stage on the slot windows (from the uniform native
ellipticity above a level threshold). -/
def FrameSeqEll : Prop :=
  ∀ (k : ℤ) (hk : Odd k), ∀ t ∈ Set.Icc (D.slotStart F.m k / D.cellScaleSq F.m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m),
      ∀ X' ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (fSeqQ F k hk).G t X' i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (fSeqQ F k hk).G t X' i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2

/-- The lift settings of the observed pulses (the first clause of `FrameReconSettingBody`, at
given setting data). -/
def FrameLiftSettingsAt (law : BirthLaw) (Acl ℓ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ) (qs qf : ℕ)
    (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ) :
    Prop :=
  ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
    IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (par k) (V k) F.depth F.N
      (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) (wLlift Dm F.depth F.N ℓ) qs qf
      CGl Cw (fun _ _ => Ca) bM Sb

/-- **The lift sequences at a frame, from the lift settings.** -/
theorem frameReconSeqAt_of_settings (law : BirthLaw) {hφ₀ : Integrable F.φ₀} {Mnat : ℕ}
    {kI : InvConsts} {tA tB S θK : ℝ}
    (hinv : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G)
    (hlev : F.G.level = F.m) (hone : F.Mn.lenFactor = 1) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hch : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hmt : F.m ≤ D.term) (hm : 1 ≤ F.m)
    (hentry : tA + 3 * ocTau D.α D.q D.Λ F.m ≤ F.tp) (htp : F.tp ≤ tB)
    (hquietMargin : Set.Icc (F.tp - ocTauP D.α D.q D.Λ F.m) (F.tp + ocTauP D.α D.q D.Λ F.m) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ F.m)
    (hell : FrameSeqEll F) {Acl ℓ : ℕ} {CGl Cw : ℕ → ℝ} {Ca Sb : ℝ} {qs qf : ℕ}
    {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ} {bM : CompIn F.G.comps → CompIn F.G.comps → ℝ}
    (hset : FrameLiftSettingsAt F law Acl ℓ CGl Cw Ca Sb qs qf par V bM) :
    FrameReconSeqAt F Acl ℓ := by
  classical
  intro k hkobs
  have hk : Odd k := LiftSetting.obsPulse_odd hkobs
  obtain ⟨y, hy1, hy2⟩ := LiftSetting.obsPulse_nonempty hkobs
  have hwin : F.tp ≤ ((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m := hy2.1.trans hy1.2
  have hnat := hinv.1
  obtain ⟨hcs, hc⟩ := cellScale_facts F hΛ hζ hch hmt
  have hseq0 : IsLiftSequence (fSeqQ F k hk) F.sX F.sZ (D.slotStart F.m k / D.cellScaleSq F.m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m) F.N F.depth
      (F.CcT k) := F.lift.1 k hk
  have hlo : fSeqStart F k = max (((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ F.m) F.tp /
      D.cellScaleSq F.m := by unfold fSeqStart; rw [hc]
  have hhi : fSeqEnd F k = min (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) (F.tp + fTobs F) /
      D.cellScaleSq F.m := by unfold fSeqEnd; rw [hc]
  have hmem : ∀ t ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k),
      D.cellScaleSq F.m * t ∈ ocPulseWindow D.α D.q D.Λ F.m k := by
    intro t ht
    rw [hlo] at ht; rw [hhi] at ht
    have h1 := (div_le_iff₀ hcs).1 ht.1
    have h2 := (le_div_iff₀ hcs).1 ht.2
    have e : t * D.cellScaleSq F.m = D.cellScaleSq F.m * t := mul_comm _ _
    exact ⟨(((le_max_left _ _).trans h1).trans_eq e), (e.symm.le.trans h2).trans (min_le_left _ _)⟩
  have hhi_le : fSeqEnd F k ≤ (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) /
      D.cellScaleSq F.m := by
    rw [hhi]; exact div_le_div_of_nonneg_right (min_le_left _ _) hcs.le
  have hseq1 : IsLiftSequence (fSeqQ F k hk) F.sX F.sZ (fSeqStart F k) (fSeqEnd F k) F.N
      F.depth (F.CcT k) := by
    by_cases hcase : F.tp ≤ ((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ F.m
    · have hl : fSeqStart F k = D.slotStart F.m k / D.cellScaleSq F.m := by
        rw [hlo, max_eq_left hcase]; rfl
      rw [hl]
      exact EntryTerminal.Ingredients.Recon.R2Core.r2c_liftSequence_restrict_right hseq0 hhi_le
    · have hcase' : D.slotStart F.m k ≤ F.tp := (not_le.1 hcase).le
      have hl : fSeqStart F k = F.tp / D.cellScaleSq F.m := by
        rw [hlo, max_eq_right (not_le.1 hcase).le]
      have hzero := seq_zero_at_tp' F hinv hlev hΛ hζ hch hmt hentry htp hquietMargin hk hwin
        hcase' (hell k hk) hseq0
      rw [hl]
      exact EntryTerminal.Ingredients.Recon.R2Core.r2c_liftSequence_restart hseq0
        (div_le_div_of_nonneg_right hcase' hcs.le) hhi_le hzero
  obtain ⟨hη, hag⟩ := seq_agree' F hnat hlev hone hΛ hζ hch hmt hm hk
  exact liftSequence_promote_of_setting (hset k hkobs)
    (seq_isLiftSequence_congr _ _ hη (fun t ht => hag t (hmem t ht)) hseq1)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

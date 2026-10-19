-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
public import AVRegularity.CycleJoint.PathReduction.Premises
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Unrolling a triangular row recursion along stage paths**.

If nonnegative row quantities satisfy `X_v ≤ A_v + L ∑_{e = (v, u, γ)} β_e X_u` and the stage has
no path with `N + 1` edges, then
`X_v ≤ A_v + ∑_{n < N} L^{n+1} ∑_{paths π with n+1 edges ending at v} β(π) A_{start π}`
(`row_recursion_unroll`). A path is extended at its start by an edge into its first source
(`stagePathCons`), and this extension is injective. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}

/-- Prepend an edge whose target is the first source of the path. -/
def stagePathCons {n : ℕ} (e : LedgerEdge G) (π : StagePath G (n + 1))
    (he : e.1 = (π.step 0).2.1) : StagePath G (n + 2) where
  step := Fin.cons e π.step
  joined j hj := by
    cases j with
    | zero => exact he.symm
    | succ k => exact π.joined k (by omega)

theorem stagePathCons_start {n : ℕ} (e : LedgerEdge G) (π : StagePath G (n + 1))
    (he : e.1 = (π.step 0).2.1) : ((stagePathCons e π he).step 0) = e :=
  rfl

theorem stagePathCons_end {n : ℕ} (e : LedgerEdge G) (π : StagePath G (n + 1))
    (he : e.1 = (π.step 0).2.1) :
    ((stagePathCons e π he).step (Fin.last (n + 1))) = π.step (Fin.last n) := by
  change (Fin.cons e π.step : Fin (n + 2) → LedgerEdge G) (Fin.last (n + 1)) = _
  rw [← Fin.succ_last, Fin.cons_succ]

theorem stagePathCons_weight {n : ℕ} (β : LedgerEdge G → ℝ) (e : LedgerEdge G)
    (π : StagePath G (n + 1)) (he : e.1 = (π.step 0).2.1) :
    pathWeight β (stagePathCons e π he) = β e * pathWeight β π := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  rfl

/-- The one-edge path. -/
def stagePathOne (e : LedgerEdge G) : StagePath G 1 where
  step := fun _ => e
  joined j hj := absurd hj (by omega)

/-- Path sums of `f` at the starts of the paths with `n + 1` edges ending at `v`. -/
def rowPathSum (β : LedgerEdge G → ℝ) (f : CompIn G.comps → ℝ) (n : ℕ) (v : CompIn G.comps) :
    ℝ :=
  ∑ π : StagePath G (n + 1),
    if (π.step (Fin.last n)).1 = v then pathWeight β π * f (π.step 0).2.1 else 0

/-- Extending at the start: the edge sums of the path sums are at most the longer path sums. -/
theorem rowPathSum_cons_le (β : LedgerEdge G → ℝ) (hβ : ∀ e, 0 ≤ β e)
    (X : CompIn G.comps → ℝ) (hX : ∀ u, 0 ≤ X u) (n : ℕ) (v : CompIn G.comps) :
    (∑ π : StagePath G (n + 1), if (π.step (Fin.last n)).1 = v then
      pathWeight β π * ∑ e : LedgerEdge G, (if e.1 = (π.step 0).2.1 then β e * X e.2.1 else 0)
      else 0) ≤ rowPathSum β X (n + 1) v := by
  classical
  let P : LedgerEdge G × StagePath G (n + 1) → Prop := fun p => p.1.1 = (p.2.step 0).2.1
  let g : LedgerEdge G × StagePath G (n + 1) → ℝ := fun p =>
    if (p.2.step (Fin.last n)).1 = v ∧ P p then pathWeight β p.2 * (β p.1 * X p.1.2.1) else 0
  let f : StagePath G (n + 2) → ℝ := fun π =>
    if (π.step (Fin.last (n + 1))).1 = v then pathWeight β π * X (π.step 0).2.1 else 0
  have hf : ∀ π, 0 ≤ f π := fun π => by
    dsimp only [f]
    split
    · exact mul_nonneg (pathWeight_nonneg β hβ π) (hX _)
    · exact le_rfl
  have hl : (∑ π : StagePath G (n + 1), if (π.step (Fin.last n)).1 = v then
      pathWeight β π * ∑ e : LedgerEdge G, (if e.1 = (π.step 0).2.1 then β e * X e.2.1 else 0)
      else 0) = ∑ p : LedgerEdge G × StagePath G (n + 1), g p := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun π _ => ?_
    split
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e.1 = (π.step 0).2.1
      · simp only [g, P, and_self, ↓reduceIte, *]
      · simp only [g, P, he, and_false, ↓reduceIte, mul_zero]
    · symm
      exact Finset.sum_eq_zero fun e _ => by simp only [g, *, false_and, ↓reduceIte]
  have hsplit := Fintype.sum_subtype_add_sum_subtype P g
  have hzero : ∑ x : {p // ¬ P p}, g x.1 = 0 :=
    Finset.sum_eq_zero fun x _ => by simp only [g, x.2, and_false, ↓reduceIte]
  have hj : Function.Injective (fun x : {p // P p} => stagePathCons x.1.1 x.1.2 x.2) := by
    rintro ⟨⟨e, π⟩, he⟩ ⟨⟨e', π'⟩, he'⟩ h
    have hs := congrArg StagePath.step h
    have h0 : e = e' := congrFun hs 0
    have hπ : π = π' := by
      apply stagePath_step_injective G (n + 1)
      funext i
      exact congrFun hs i.succ
    subst h0
    subst hπ
    rfl
  have hfj : ∀ x : {p // P p}, g x.1 = f (stagePathCons x.1.1 x.1.2 x.2) := by
    rintro ⟨⟨e, π⟩, he⟩
    have he' : e.1 = (π.step 0).2.1 := he
    simp only [g, f, P, stagePathCons_end, stagePathCons_start, stagePathCons_weight]
    by_cases hv : (π.step (Fin.last n)).1 = v
    · simp only [hv, he', and_self, ↓reduceIte]
      ring
    · simp only [hv, false_and, ↓reduceIte]
  calc _ = ∑ p, g p := hl
    _ = ∑ x : {p // P p}, g x.1 := by rw [← hsplit, hzero, add_zero]
    _ = ∑ x : {p // P p}, f (stagePathCons x.1.1 x.1.2 x.2) := Finset.sum_congr rfl fun x _ => hfj x
    _ ≤ ∑ π, f π := sum_comp_le _ hj f hf
    _ = rowPathSum β X (n + 1) v := rfl

/-- The edge sum at `v` is at most the one-edge path sum. -/
theorem edgeSum_le_rowPathSum_zero (β : LedgerEdge G → ℝ) (hβ : ∀ e, 0 ≤ β e)
    (X : CompIn G.comps → ℝ) (hX : ∀ u, 0 ≤ X u) (v : CompIn G.comps) :
    (∑ e : LedgerEdge G, if e.1 = v then β e * X e.2.1 else 0) ≤ rowPathSum β X 0 v := by
  classical
  let f : StagePath G 1 → ℝ := fun π =>
    if (π.step (Fin.last 0)).1 = v then pathWeight β π * X (π.step 0).2.1 else 0
  have hf : ∀ π, 0 ≤ f π := fun π => by
    dsimp only [f]
    split
    · exact mul_nonneg (pathWeight_nonneg β hβ π) (hX _)
    · exact le_rfl
  have hj : Function.Injective (stagePathOne (G := G)) := fun e e' h =>
    congrFun (congrArg StagePath.step h) 0
  have hw : ∀ e, pathWeight β (stagePathOne e) = β e := fun e => Fin.prod_univ_one _
  calc _ = ∑ e : LedgerEdge G, f (stagePathOne e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [f, hw]
        rfl
    _ ≤ ∑ π, f π := sum_comp_le _ hj f hf
    _ = rowPathSum β X 0 v := rfl

/-- **Unrolling the row recursion along stage paths.** -/
theorem row_recursion_unroll (β : LedgerEdge G → ℝ) (hβ : ∀ e, 0 ≤ β e)
    (A X : CompIn G.comps → ℝ) (hX0 : ∀ u, 0 ≤ X u) (L : ℝ) (hL : 0 ≤ L)
    (hX : ∀ u, X u ≤ A u + L * ∑ e : LedgerEdge G, if e.1 = u then β e * X e.2.1 else 0)
    (N : ℕ) (hN : IsEmpty (StagePath G (N + 1))) (v : CompIn G.comps) :
    X v ≤ A v + ∑ n ∈ Finset.range N, L ^ (n + 1) * rowPathSum β A n v := by
  have hstep : ∀ n v, rowPathSum β X n v ≤ rowPathSum β A n v + L * rowPathSum β X (n + 1) v := by
    intro n v
    have hle : rowPathSum β X n v ≤ ∑ π : StagePath G (n + 1),
        if (π.step (Fin.last n)).1 = v then pathWeight β π * ((A (π.step 0).2.1) +
          L * ∑ e : LedgerEdge G, (if e.1 = (π.step 0).2.1 then β e * X e.2.1 else 0)) else 0 := by
      refine Finset.sum_le_sum fun π _ => ?_
      split
      · exact mul_le_mul_of_nonneg_left (hX _) (pathWeight_nonneg β hβ π)
      · exact le_rfl
    refine hle.trans (le_of_eq_of_le ?_ (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (rowPathSum_cons_le β hβ X hX0 n v) hL)))
    rw [rowPathSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    split
    · ring
    · ring
  have hclaim : ∀ k, X v ≤ A v + ∑ n ∈ Finset.range k, L ^ (n + 1) * rowPathSum β A n v +
      L ^ (k + 1) * rowPathSum β X k v := by
    intro k
    induction k with
    | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, pow_one] using
        (hX v).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (edgeSum_le_rowPathSum_zero β hβ X hX0 v) hL))
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ]
      have h := mul_le_mul_of_nonneg_left (hstep k v) (pow_nonneg hL (k + 1))
      have he : L ^ (k + 1) * (rowPathSum β A k v + L * rowPathSum β X (k + 1) v) =
          L ^ (k + 1) * rowPathSum β A k v + L ^ (k + 1 + 1) * rowPathSum β X (k + 1) v := by
        ring
      linarith
  have hzero : rowPathSum β X N v = 0 := by
    unfold rowPathSum
    exact Finset.sum_of_isEmpty _
  simpa only [hzero, mul_zero, add_zero] using hclaim N

end AVRegularity.Providers.WeakGen.Comparison
end

section
open MeasureTheory Homogenization AVRegularity.Analysis.Convolution
namespace AVRegularity.Providers.WeakGen

/-! **A kernel of width zero is the identity** (a prerequisite of the comparison energy). The
averaging over a zero displacement is the multiplication by the kernel's mass, and the moment kernel
has unit mass (`integral_momentKernel`). So `KernelSpec.op` at width `0` is the identity
(`KernelSpec.op_width_zero`), and the regularizer `sysS` of a stage whose kernels are the isotropic
paired kernels of width `0` is the identity (`sysS_isoPairedKernel_zero`): the weak passage systems
are the unregularized local-coefficient systems. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] in
/-- **Averaging over a zero displacement** with a kernel of unit mass is the identity. -/
theorem periodicComponentAverage_zero_displacement (H : Vec 2 →L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hκ : Integrable κ) (hmass : ∫ z, κ z = 1) :
    periodicComponentAverage (E := E) (displacement 0 H) (continuous_displacement 0 H) κ hκ =
      ContinuousLinearMap.id ℝ _ := by
  ext1 f
  have hav : averagingOperator (torusQuotient.comp (displacement 0 H))
      (continuous_torusQuotient.comp (continuous_displacement 0 H)) κ hκ (cellToTorus f) =
      cellToTorus f := by
    change (∫ z : Vec 2, κ z • translation ((torusQuotient.comp (displacement 0 H)) z)
      (cellToTorus f)) = _
    simp only [AddMonoidHom.comp_apply, displacement_apply, zero_smul, map_zero,
      translation_zero]
    rw [integral_smul_const, hmass, one_smul]
  simp only [periodicComponentAverage, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, ContinuousLinearMap.id_apply]
  rw [hav]
  exact torusToCell_cellToTorus f

/-- **A kernel of width zero is the identity.** -/
theorem KernelSpec.op_width_zero {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (hmass : ∫ z, φ₀ z = 1) (S : KernelSpec) (hS : S.width = 0) (t : ℝ) :
    S.op φ₀ hφ₀ (E := E) t = ContinuousLinearMap.id ℝ _ := by
  have hm := integral_momentKernel hφ₀ hmass S.order
  unfold KernelSpec.op
  simp only [hS]
  rw [periodicComponentAverage_zero_displacement _ _ _ hm,
    periodicComponentAverage_zero_displacement _ _ _ hm, ContinuousLinearMap.id_comp]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The regularizer of a stage with width-zero isotropic kernels is the identity.** -/
theorem sysS_isoPairedKernel_zero (P : ProvParams) (n : ℕ+) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hmass : ∫ z, φ₀ z = 1) (G : GenStage D hr Dm b j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (t : ℝ) :
    G.sysS P (fun _ => isoPairedKernel 0 n) (fun _ => isoPairedKernel 0 n) φ₀ hφ₀ v u γ t =
      ContinuousLinearMap.id ℝ _ := by
  unfold GenStage.sysS GenStage.kernelOf
  split <;> exact KernelSpec.op_width_zero hφ₀ hmass _ rfl t

end AVRegularity.Providers.WeakGen
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Scalar rows of a coupled solution** (the comparison energy: bootstrap and rows). A forced row
is a one-component solution without coupling and with forcing `(Q, g)` (`IsTorusForcedRow`). Every
row of a coupled solution is a forced row whose flux forcing is its own forcing plus the incoming
coupling flux (`torusWeakSolution_forcedRow`). -/

section
open CycleJointProofs CycleJointProofs.PathReduction CoupledEnergy.Variational

section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- **A forced scalar row**: one component, no coupling, flux forcing `Q` and source `g`. -/
def IsTorusForcedRow (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (D k : ℕ) (f : TorusHk k E)
    (Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))) (g : ℝ → TorusHk k E)
    (u : ℝ → TorusHk k E) (w : ℝ → TorusHk (k + 1) E) : Prop :=
  IsCoupledWeakSolutionTorus (ι := Fin 1) (h := fun _ => E) ν a b v D (fun _ => k)
    (fun _ _ _ _ _ => 0) (fun _ => f) (fun _ => Q) (fun _ => g) (fun _ => u) (fun _ => w)

omit [FiniteDimensional ℝ E] in
/-- Truncation composes. -/
theorem truncateTorusHk_trans {k k' k'' : ℕ} (h₁ : k'' ≤ k') (h₂ : k' ≤ k) (x : TorusHk k E) :
    truncateTorusHk h₁ (truncateTorusHk h₂ x) = truncateTorusHk (h₁.trans h₂) x :=
  rfl

omit [FiniteDimensional ℝ E] in
theorem truncate_continuousOn {k k' : ℕ} (hk : k' ≤ k) {a b : ℝ} {u : ℝ → TorusHk k E}
    (hu : ContinuousOn u (Set.Icc a b)) :
    ContinuousOn (fun s => truncateTorusHk hk (u s)) (Set.Icc a b) :=
  Continuous.comp_continuousOn (g := truncateTorusHk hk) (truncateTorusHk hk).continuous hu

omit [FiniteDimensional ℝ E] in
theorem truncate_memLp {k k' : ℕ} (hk : k' ≤ k) {a b : ℝ} {w : ℝ → TorusHk k E}
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun s => truncateTorusHk hk (w s)) 2 (volume.restrict (Set.Icc a b)) :=
  hw.continuousLinearMap_comp (truncateTorusHk hk)

omit [FiniteDimensional ℝ E] in
theorem truncate_lift_ae {k k' : ℕ} (hk : k' ≤ k) {a b : ℝ} {u : ℝ → TorusHk k E}
    {w : ℝ → TorusHk (k + 1) E}
    (hw : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ k) (w s) = u s) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      truncateTorusHk (Nat.le_succ k') (truncateTorusHk (Nat.succ_le_succ hk) (w s)) =
        truncateTorusHk hk (u s) := by
  filter_upwards [hw] with s hs'
  rw [truncateTorusHk_trans, ← hs', truncateTorusHk_trans]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The right side of the weak identity at a point reads only the gradient, the total flux and the
source there. -/
theorem weakIdentityRhs_congr_at (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du du' : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g g' : ℝ → Vec 2 → E)
    (s : ℝ) (x : Vec 2) (hdu : ∀ q, du s q x = du' s q x)
    (hfl : flux s x + F s x = flux' s x + F' s x) (hg : g s x = g' s x) :
    Weighted.weakIdentityRhs ν v φ dφ du flux F g s x =
      Weighted.weakIdentityRhs ν v φ dφ du' flux' F' g' s x := by
  have hfl' : ∀ q, flux s x q + F s x q = flux' s x q + F' s x q := fun q => by
    have := congrArg (fun y : PiLp 2 (fun _ : Fin 2 => E) => y q) hfl
    simpa only [PiLp.add_apply] using this
  simp only [Weighted.weakIdentityRhs, hdu, hfl', hg]

/-- **A forced row truncates to every lower order.** -/
theorem torusForcedRow_truncate {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D k k' : ℕ} (hk : k' ≤ k)
    {f : TorusHk k E} {Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))} {g : ℝ → TorusHk k E}
    {u : ℝ → TorusHk k E} {w : ℝ → TorusHk (k + 1) E}
    (hs : IsTorusForcedRow ν a b v D k f Q g u w) :
    IsTorusForcedRow ν a b v D k' (truncateTorusHk hk f) (fun s => truncateTorusHk hk (Q s))
      (fun s => truncateTorusHk hk (g s)) (fun s => truncateTorusHk hk (u s))
      (fun s => truncateTorusHk (Nat.succ_le_succ hk) (w s)) := by
  have hc : ContinuousOn (fun s => truncateTorusHk hk (u s)) (Set.Icc a b) :=
    truncate_continuousOn hk (hs.1 0)
  have hm : MemLp (fun s => truncateTorusHk (Nat.succ_le_succ hk) (w s)) 2
      (volume.restrict (Set.Icc a b)) := truncate_memLp (Nat.succ_le_succ hk) (hs.2.1 0)
  have hl := truncate_lift_ae hk (hs.2.2.1 0)
  have hi : truncateTorusHk hk (u a) = truncateTorusHk hk f := congrArg _ (hs.2.2.2.1 0)
  refine ⟨fun _ => hc, fun _ => hm, fun _ => hl, fun _ => hi, ?_⟩
  intro _ t ht φ
  have hold := hs.2.2.2.2 0 t ht φ
  refine coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ hold
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae hk (u t) (valueIndex2 k')] with x hx
    exact congrArg (fun y => inner ℝ y _) hx.symm
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae hk f (valueIndex2 k')] with x hx
    exact congrArg (fun y => inner ℝ y _) hx.symm
  · intro s _
    filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.succ_le_succ hk) (w s)
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k')⟩, fun _ => 0⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.succ_le_succ hk) (w s)
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k')⟩, fun _ => 1⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae hk (Q s) (valueIndex2 k'),
      KernelEnergy.truncateTorusHk_toFunction_jet_ae hk (g s) (valueIndex2 k')] with x h0 h1 hQ hg
    refine weakIdentityRhs_congr_at _ _ _ _ _ _ _ _ _ _ _ _ s x (fun q => ?_) ?_ hg.symm
    · fin_cases q
      · exact h0.symm
      · exact h1.symm
    · simp only [zero_apply, Finset.sum_const_zero, zero_add]
      exact hQ.symm

/-! ### The drift hypotheses of `coupled_energy_torus`, and scalar uniqueness -/

/-- **The drift hypotheses of `coupled_energy_torus`** on `[t₀, t₁]` at the radius `ρ`. -/
structure TorusDriftData (ν ρ t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (Kmax : ℕ) : Prop where
  bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ C
  meas : Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => v p.1 p.2
  smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (v t)
  div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0
  per : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t)
  jets : ∃ a B₀ lam : ℝ, 0 ≤ a ∧ 1 ≤ B₀ ∧ 0 < lam ∧
    (∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) ∧
    B₀ * ρ / lam ≤ 1 / 2 ∧ a * B₀ * ρ ^ 2 ≤ ν / 8

/-- **Uniqueness of a forced row** (`coupled_energy_torus` on one component without coupling). -/
theorem torusForcedRow_unique {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax) (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν)
    {D k : ℕ} (hD : 2 ≤ D) (hk : k ≤ Kmax) {f : TorusHk k E}
    {Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))} {g : ℝ → TorusHk k E}
    (hQ : MemLp Q 2 (volume.restrict (Set.Icc a b)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    {u u' : ℝ → TorusHk k E} {w w' : ℝ → TorusHk (k + 1) E}
    (h₁ : IsTorusForcedRow ν a b v D k f Q g u w) (h₂ : IsTorusForcedRow ν a b v D k f Q g u' w') :
    ∀ t ∈ Set.Icc a b, u t = u' t := by
  obtain ⟨a', B₀, lam, ha, hB₀, hlam, hjets, hB, hab'⟩ := hd.jets
  have hgate := coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div hd.per
    a' B₀ lam ha hB₀ hlam Kmax hjets hB hab' D hD (ι := Fin 1) (h := fun _ => E)
    (fun _ => 1) (fun _ => one_pos) (fun _ => k) (fun _ => hk) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ => fun _ _ => rfl)
    (fun _ _ _ => by rw [CycleComparison.Coarse.coefficientSeminorm_const_zero]; exact ENNReal.zero_ne_top)
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ _ _ D a b)
    (fun _ => f) (fun _ => Q) (fun _ => hQ) (fun _ => g) (fun _ => hg)
  intro t ht
  exact hgate.2.1 (fun _ => u) (fun _ => u') (fun _ => w) (fun _ => w') h₁ h₂ 0 t ht

end Row

section Extract

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {r : ℝ}

/-- **Every row of a coupled solution is a forced row**, with flux forcing its own forcing plus
the incoming coupling flux. -/
theorem torusWeakSolution_forcedRow (R : TorusCoefficientData (h := h) r K D a b A)
    (f : ∀ i, TorusHk (K i) (h i)) (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w) (i : ι) :
    IsTorusForcedRow ν a b v D (K i) (f i) (fun s => F i s + ∑ j, R.edgeFlux i j s (w j s))
      (g i) (u i) (w i) := by
  refine ⟨fun _ => hs.1 i, fun _ => hs.2.1 i, fun _ => hs.2.2.1 i, fun _ => hs.2.2.2.1 i, ?_⟩
  intro _ t ht φ
  have hold := hs.2.2.2.2 i t ht φ
  simp only [zero_apply, Finset.sum_const_zero]
  apply coupledWeakIdentity_flux_reallocation (volume.restrict AVenhance.unitCube) ν a t v
    _ _ _ _ _ _ _ _ _ _ ?_ hold
  intro s hs'
  have hsab : s ∈ Set.Icc a b := ⟨hs'.1.le, hs'.2.trans ht.2⟩
  filter_upwards [(periodicJetRepresentative_add_global (F i s).val
      (∑ j, R.edgeFlux i j s (w j s)).val (valueIndex2 (K i))).restrict,
    R.totalFlux_value_ae i s hsab (fun j => w j s)] with x hx hT
  change torusRawCouplingFlux K D s A (fun j => w j s) i x + (F i s).toFunction.jet
      (valueIndex2 (K i)) x = 0 + (F i s + ∑ j, R.edgeFlux i j s (w j s)).toFunction.jet
      (valueIndex2 (K i)) x
  rw [zero_add]
  change _ = (periodicJetRepresentative (F i s + ∑ j, R.edgeFlux i j s (w j s)).val
    (valueIndex2 (K i))) x
  rw [show (F i s + ∑ j, R.edgeFlux i j s (w j s)).val =
    (F i s).val + (∑ j, R.edgeFlux i j s (w j s)).val from rfl, hx]
  change _ = (F i s).toFunction.jet (valueIndex2 (K i)) x +
    (∑ j, R.edgeFlux i j s (w j s)).toFunction.jet (valueIndex2 (K i)) x
  rw [hT, add_comm]

end Extract
end

/-! **Identification of an order-zero solution** (the comparison energy: bootstrap). An order-zero
solution of a triangular system with identity kernels and scalar maps is the order-zero truncation
of every coupled solution at reserves `K` with the same data, whose local coefficients are the
summed kernel coefficients at the admissible orders (`kernel_solution_identified`).

The proof goes row by row in rank order. The difference of the given row and the truncated
regular row solves a forced row with zero data: the kernel flux reads the inputs of lower rank,
which are already identified, and the jets of two carriers with the same value agree
(`torusHk_jet_ae_of_value_eq`). Scalar uniqueness (`torusForcedRow_unique`) ends the step. No
time integrability of the coupling flux is needed. -/

section
open CycleJointProofs CycleJointProofs.PathReduction

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The jets of a difference of carriers. -/
theorem torusHk_jet_sub_ae {K : ℕ} (U V : TorusHk K E) (a : JetIndex2 K) :
    (U - V).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => U.toFunction.jet a x - V.toFunction.jet a x := by
  filter_upwards [periodicJetRepresentative_ae (U - V).val a,
    periodicJetRepresentative_ae U.val a, periodicJetRepresentative_ae V.val a,
    Lp.coeFn_sub (U.val a) (V.val a)] with x h1 h2 h3 h4
  change periodicJetRepresentative (U - V).val a x =
    periodicJetRepresentative U.val a x - periodicJetRepresentative V.val a x
  rw [h1, h2, h3]
  exact h4

/-- **Two carriers with the same value have the same jets** up to the smaller order. -/
theorem torusHk_jet_ae_of_value_eq [FiniteDimensional ℝ E] {L₁ L₂ : ℕ} (Y : TorusHk L₁ E)
    (W : TorusHk L₂ E) (hv : Y.val (valueIndex2 L₁) = W.val (valueIndex2 L₂)) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (n : ℕ) (h₁ : n < L₁ + 1) (h₂ : n < L₂ + 1)
      (word : DerivativeWord2 n),
      Y.toFunction.jet ⟨⟨n, h₁⟩, word⟩ x = W.toFunction.jet ⟨⟨n, h₂⟩, word⟩ x := by
  have hT : truncateTorusHk (min_le_left L₁ L₂) Y = truncateTorusHk (min_le_right L₁ L₂) W :=
    TorusHk.ext_value hv
  have hY : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (truncateTorusHk (min_le_left L₁ L₂) Y).toFunction.jet a x =
        Y.toFunction.jet (truncateJetIndex (min_le_left L₁ L₂) a) x :=
    ae_all_iff.2 fun a => KernelEnergy.truncateTorusHk_toFunction_jet_ae _ Y a
  have hW : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (truncateTorusHk (min_le_right L₁ L₂) W).toFunction.jet a x =
        W.toFunction.jet (truncateJetIndex (min_le_right L₁ L₂) a) x :=
    ae_all_iff.2 fun a => KernelEnergy.truncateTorusHk_toFunction_jet_ae _ W a
  filter_upwards [hY, hW] with x hx hw n h₁ h₂ word
  have hn : n < min L₁ L₂ + 1 := by omega
  have e1 := hx ⟨⟨n, hn⟩, word⟩
  rw [hT] at e1
  exact e1.symm.trans (hw ⟨⟨n, hn⟩, word⟩)

/-- The zero trajectory of carriers is square integrable (through a linear map, which keeps the
normed instance path of the carriers). -/
theorem torusHk_memLp_zero (k : ℕ) (μ : Measure ℝ) :
    MemLp (fun _ : ℝ => (0 : TorusHk k E)) 2 μ :=
  ((0 : ℝ →L[ℝ] TorusHk k E).comp_memLp' (MemLp.zero' (ε := ℝ))).ae_eq
    (Filter.Eventually.of_forall fun _ => zero_apply _)

/-- The zero trajectory of carriers is integrable. -/
theorem torusHk_integrable_zero (k : ℕ) (μ : Measure ℝ) :
    Integrable (fun _ : ℝ => (0 : TorusHk k E)) μ :=
  ((0 : ℝ →L[ℝ] TorusHk k E).integrable_comp (integrable_zero ℝ ℝ μ)).congr
    (Filter.Eventually.of_forall fun _ => zero_apply _)

end Jets

/-- The identity map on `L²` fields. -/
theorem id_compLp_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    (ContinuousLinearMap.id ℝ E).compLp z = z :=
  Lp.ext ((ContinuousLinearMap.coeFn_compLp' _ z).trans (Filter.Eventually.of_forall fun _ => rfl))

/-! ### Two weak identities with the same total flux -/

/-- The difference of two weak identities whose total fluxes agree almost everywhere solves the
identity without flux. -/
theorem coupledWeakIdentity_sub_of_flux_ae {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u₁ u₂ f₁ f₂ φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H) (du₁ du₂ : ℝ → Fin 2 → Vec 2 → H)
    (flux₁ flux₂ F₁ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g₁ g₂ : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity μ ν a t v u₁ f₁ φ dφ du₁ flux₁ F₁ g₁)
    (h₂ : CoupledWeakIdentity μ ν a t v u₂ f₂ φ dφ du₂ flux₂ F₂ g₂)
    (hflux : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂μ,
      flux₁ r x + F₁ r x = flux₂ r x + F₂ r x)
    (hpoint : ∀ r ∈ Set.Ioc a t,
      Integrable (Weighted.weakIdentityRhs ν v φ dφ (du₁ - du₂) 0 0 (g₁ - g₂) r) μ) :
    CoupledWeakIdentity μ ν a t v (u₁ - u₂) (f₁ - f₂) φ dφ (du₁ - du₂) 0 0 (g₁ - g₂) := by
  refine KernelEnergy.weakIdentity_flux_congr_time μ ν a t v _ _ _ _ _ (flux₁ - flux₂)
    (F₁ - F₂) 0 0 _ ?_ hpoint (CycleWords.coupledWeakIdentity_sub μ ν a t v u₁ u₂ f₁ f₂ φ dφ
      du₁ du₂ flux₁ flux₂ F₁ F₂ g₁ g₂ h₁ h₂)
  filter_upwards [hflux] with r hr
  filter_upwards [hr] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply, add_zero]
  rw [sub_add_sub_comm, hx, sub_self]

section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The zero forced row. -/
theorem torusForcedRow_zero (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (D k : ℕ) :
    IsTorusForcedRow (E := E) ν a b v D k 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) := by
  refine ⟨fun _ => continuousOn_const, fun _ => torusHk_memLp_zero _ _,
    fun _ => Filter.Eventually.of_forall fun _ => map_zero _, fun _ => rfl, ?_⟩
  intro _ t _ φ
  refine coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
    0 _ 0 _ (φ.toFunction.jet (valueIndex2 1)) _
    (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) _ 0 _ 0 _ 0 _ 0 _ ?_ ?_ ?_
    (CycleWords.coupledWeakIdentity_zero _ ν a t v _ _)
  · filter_upwards [torusZero_rawJet_ae (E := E) k (valueIndex2 k)] with x hx
    simp only [hx, Pi.zero_apply]
  · filter_upwards [torusZero_rawJet_ae (E := E) k (valueIndex2 k)] with x hx
    simp only [hx, Pi.zero_apply]
  · intro s _
    filter_upwards [torusZero_rawJet_ae (E := E) (k + 1)
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => 0⟩,
      torusZero_rawJet_ae (E := E) (k + 1) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => 1⟩,
      torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => E)) k (valueIndex2 k),
      torusZero_rawJet_ae (E := E) k (valueIndex2 k)] with x h0 h1 hQ hg
    refine weakIdentityRhs_congr_at _ _ _ _ _ _ _ _ _ _ _ _ s x (fun q => ?_) ?_ ?_
    · fin_cases q
      · exact h0.symm
      · exact h1.symm
    · simp only [hQ, Pi.zero_apply, zero_apply, Finset.sum_const_zero, add_zero]
    · exact hg.symm

/-- **A forced row from its fields**, with the flux written as zero. -/
theorem isTorusForcedRow_of {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D k : ℕ} {f : TorusHk k E}
    {Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))} {g u : ℝ → TorusHk k E}
    {w : ℝ → TorusHk (k + 1) E} (hc : ContinuousOn u (Set.Icc a b))
    (hm : MemLp w 2 (volume.restrict (Set.Icc a b)))
    (hl : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ k) (w s) = u s)
    (hi : u a = f)
    (hid : ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 E,
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
        ((u t).toFunction.jet (valueIndex2 k)) (f.toFunction.jet (valueIndex2 k))
        (φ.toFunction.jet (valueIndex2 1))
        (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
        (fun s q => (w s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
        (fun _ _ => 0) (fun s => (Q s).toFunction.jet (valueIndex2 k))
        (fun s => (g s).toFunction.jet (valueIndex2 k))) :
    IsTorusForcedRow ν a b v D k f Q g u w := by
  refine ⟨fun _ => hc, fun _ => hm, fun _ => hl, fun _ => hi, fun _ t ht φ => ?_⟩
  simp only [zero_apply, Finset.sum_const_zero]
  exact hid t ht φ

end Row

/-! ### The kernel flux of one edge read through the local coefficients -/

/-- **The kernel orders and the admissible orders.** If the order-`n` coefficients vanish at
the non-admissible orders and the two jet families agree up to the admissible orders, the sum
over `[2, D]` equals the sum over the admissible orders. -/
theorem kernel_orders_sum_eq {ι : Type*} {G H : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : ι → ℕ) {D D' : ℕ} (hD : D' ≤ D) (i j : ι) {L₁ L₂ : ℕ} (hL₁ : D - 1 ≤ L₁)
    (P : ∀ n : ℕ, PiLp 2 (fun _ : DerivativeWord2 (n - 1) => G) →L[ℝ] H)
    (hP : ∀ n ∈ Finset.Icc 2 D, n ∉ admissibleOrders K D' i j → P n = 0)
    (Y : JetIndex2 L₁ → G) (W : JetIndex2 L₂ → G)
    (hYW : ∀ (n : ℕ) (h₁ : n < L₁ + 1) (h₂ : n < L₂ + 1) (word : DerivativeWord2 n),
      Y ⟨⟨n, h₁⟩, word⟩ = W ⟨⟨n, h₂⟩, word⟩)
    (pf₁ : ∀ d : ↥(Finset.Icc 2 D), d.1 - 1 < L₁ + 1)
    (pf₂ : ∀ d : ↥(admissibleOrders K D' i j), d.1 - 1 < L₂ + 1) :
    ∑ d : ↥(Finset.Icc 2 D), P d.1 (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Y ⟨⟨d.1 - 1, pf₁ d⟩, word⟩) =
      ∑ d : ↥(admissibleOrders K D' i j), P d.1
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) => W ⟨⟨d.1 - 1, pf₂ d⟩, word⟩) := by
  classical
  let T : ℕ → H := fun n => if h : n - 1 < L₁ + 1 then
    P n (WithLp.toLp 2 fun word : DerivativeWord2 (n - 1) => Y ⟨⟨n - 1, h⟩, word⟩) else 0
  have hsub : admissibleOrders K D' i j ⊆ Finset.Icc 2 D := fun n hn => by
    have h2 := Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1
    exact Finset.mem_Icc.2 ⟨h2.1, h2.2.trans hD⟩
  have h1 : ∑ d : ↥(Finset.Icc 2 D), P d.1 (WithLp.toLp 2
      fun word : DerivativeWord2 (d.1 - 1) => Y ⟨⟨d.1 - 1, pf₁ d⟩, word⟩) =
      ∑ n ∈ Finset.Icc 2 D, T n := by
    rw [← Finset.sum_coe_sort (Finset.Icc 2 D)]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [T, dite_eq_left (pf₁ d)]
  have h2 : ∑ n ∈ admissibleOrders K D' i j, T n = ∑ n ∈ Finset.Icc 2 D, T n := by
    refine Finset.sum_subset hsub fun n hn hna => ?_
    simp only [T, hP n hn hna, zero_apply, dite_eq_ite, ite_self]
  have h3 : ∑ d : ↥(admissibleOrders K D' i j), P d.1 (WithLp.toLp 2
      fun word : DerivativeWord2 (d.1 - 1) => W ⟨⟨d.1 - 1, pf₂ d⟩, word⟩) =
      ∑ n ∈ admissibleOrders K D' i j, T n := by
    rw [← Finset.sum_coe_sort (admissibleOrders K D' i j)]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd₁ : d.1 - 1 < L₁ + 1 := by
      have := Finset.mem_Icc.1 (hsub d.2)
      omega
    simp only [T, dite_eq_left hd₁]
    congr 2
    funext word
    exact (hYW _ hd₁ (pf₂ d) word).symm
  rw [h1, ← h2, h3]

/-! ### Identification, row by row -/

section Identify

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D D' : ℕ} {K : ι → ℕ}
  {P : ∀ i j (_ : Γ i j) (n : ℕ), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (n - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {A : ∀ i j, (d : admissibleOrders K D' i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {S : ∀ i j (_ : Γ i j), ℝ → Lp (h j) 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
    Lp (h j) 2 (volume.restrict AVenhance.unitCube)}
  {f₀ : ∀ i, TorusHk 0 (h i)} {F₀ : ∀ i, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))}
  {g₀ u : ∀ i, ℝ → TorusHk 0 (h i)} {w : ∀ i, ℝ → TorusHk (0 + 1) (h i)}
  {y : ∀ i j (_ : Γ i j), ℝ → TorusHk (0 + D - 1) (h j)}
  {f' : ∀ i, TorusHk (K i) (h i)} {F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
  {g' u' : ∀ i, ℝ → TorusHk (K i) (h i)} {w' : ∀ i, ℝ → TorusHk (K i + 1) (h i)}

/-- The value of an identified input: the kernel input of an edge into a row of lower rank has
the value of the regular solution. -/
theorem kernel_input_value_ae
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (i j : ι) (α : Γ i j)
    (hprev : ∀ t ∈ Set.Icc a b, truncateTorusHk (Nat.zero_le _) (u' j t) = u j t) :
    ∀ᵐ r ∂(volume.restrict (Set.Icc a b)),
      (y i j α r).val (valueIndex2 (0 + D - 1)) = (w' j r).val (valueIndex2 (K j + 1)) := by
  filter_upwards [hk.2.2.2.2.2.1 i j α, hk.2.2.1 j, hc.2.2.1 j,
    ae_restrict_mem measurableSet_Icc] with r hy hw hw' hr
  rw [hy]
  simp only [hS, ContinuousLinearMap.id_apply, id_compLp_eq]
  have e1 : (w j r).val (valueIndex2 (0 + 1)) = (u j r).val (valueIndex2 0) := by
    rw [← hw]
    rfl
  have e2 : (u' j r).val (valueIndex2 (K j)) = (w' j r).val (valueIndex2 (K j + 1)) := by
    rw [← hw']
    rfl
  rw [e1, ← hprev r hr, ← e2]
  rfl

/-- **The kernel flux of a row equals its local flux** almost everywhere, once its inputs of
lower rank are identified. -/
theorem kernel_row_flux_ae (hD : D' ≤ D)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w') (i : ι)
    (hprev : ∀ j, Nonempty (Γ i j) → ∀ t ∈ Set.Icc a b,
      truncateTorusHk (Nat.zero_le _) (u' j t) = u j t) :
    ∀ᵐ r ∂(volume.restrict (Set.Icc a b)), ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        P i j α d.1 r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α r).toFunction.jet ⟨⟨d.1 - 1, by
            have := Finset.mem_Icc.1 d.2
            omega⟩, word⟩ x)) =
      ∑ j : ι, ∑ d : admissibleOrders K D' i j,
        A i j d r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (w' j r).toFunction.jet ⟨⟨d.1 - 1, by
            have h := Finset.mem_filter.1 d.2
            have := Finset.mem_Icc.1 h.1
            omega⟩, word⟩ x) := by
  have hval : ∀ᵐ r ∂(volume.restrict (Set.Icc a b)), ∀ j (α : Γ i j),
      (y i j α r).val (valueIndex2 (0 + D - 1)) = (w' j r).val (valueIndex2 (K j + 1)) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun α =>
      kernel_input_value_ae hS hk hc i j α (hprev j ⟨α⟩)
  filter_upwards [hval] with r hr
  have hjet : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j (α : Γ i j) (n : ℕ)
      (h₁ : n < 0 + D - 1 + 1) (h₂ : n < K j + 1 + 1) (word : DerivativeWord2 n),
      (y i j α r).toFunction.jet ⟨⟨n, h₁⟩, word⟩ x =
        (w' j r).toFunction.jet ⟨⟨n, h₂⟩, word⟩ x :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun α => torusHk_jet_ae_of_value_eq _ _ (hr j α)
  filter_upwards [hjet] with x hx
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hA, _root_.sum_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact kernel_orders_sum_eq K hD i j (L₁ := 0 + D - 1) (L₂ := K j + 1) (by omega)
    (fun n => P i j α n r x) (fun n hn hna => hP i j α n hn hna r x)
    (fun a => (y i j α r).toFunction.jet a x) (fun a => (w' j r).toFunction.jet a x) (hx j α)
    (fun d => by have := Finset.mem_Icc.1 d.2; omega)
    (fun d => by
      have h := Finset.mem_filter.1 d.2
      have := Finset.mem_Icc.1 h.1
      omega)

/-- The total fluxes of the given row and of the regular row agree almost everywhere. -/
theorem kernel_row_total_flux_ae (hD : D' ≤ D)
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (hF : ∀ i s, truncateTorusHk (Nat.zero_le _) (F' i s) = F₀ i s) (i : ι)
    (hprev : ∀ j, Nonempty (Γ i j) → ∀ t ∈ Set.Icc a b,
      truncateTorusHk (Nat.zero_le _) (u' j t) = u j t) :
    ∀ᵐ r ∂(volume.restrict (Set.Icc a b)), ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        P i j α d.1 r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α r).toFunction.jet ⟨⟨d.1 - 1, by
            have := Finset.mem_Icc.1 d.2
            omega⟩, word⟩ x)) + (F₀ i r).toFunction.jet (valueIndex2 0) x =
      (∑ j : ι, ∑ d : admissibleOrders K D' i j,
        A i j d r x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (w' j r).toFunction.jet ⟨⟨d.1 - 1, by
            have h := Finset.mem_filter.1 d.2
            have := Finset.mem_Icc.1 h.1
            omega⟩, word⟩ x)) + (F' i r).toFunction.jet (valueIndex2 (K i)) x := by
  filter_upwards [kernel_row_flux_ae hD hA hP hS hk hc i hprev] with r hr
  filter_upwards [hr, KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le (K i))
    (F' i r) (valueIndex2 0)] with x hx hFx
  rw [hF i r] at hFx
  exact congrArg₂ (· + ·) hx hFx

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The right side of the difference identity is integrable at every time. -/
theorem kernel_row_rhs_integrable {ρ : ℝ} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
    ∀ r ∈ Set.Ioc a t, Integrable (Weighted.weakIdentityRhs ν v (φ.toFunction.jet (valueIndex2 1))
      (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
      ((fun s q => (w i s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => q⟩) -
        fun s q => (w' i s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => q⟩)
      0 0 ((fun s => (g₀ i s).toFunction.jet (valueIndex2 0)) -
        fun s => (g' i s).toFunction.jet (valueIndex2 (K i))) r)
      (volume.restrict AVenhance.unitCube) := by
  obtain ⟨C, hC⟩ := hd.bdd
  intro r hr
  have hrI : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.trans ht.2⟩
  exact cell_weakIdentityRhs_integrable ν r v _ _ _ 0 0 _ (hd.smooth r hrI).continuous
    (max C 0) (le_max_right _ _) (fun x => (hC r hrI x).trans (le_max_left _ _))
    (φ.toFunction.hasPeriodicWeakJet.2.1 _) (fun _ => φ.toFunction.hasPeriodicWeakJet.2.1 _)
    (fun _ => ((w i r).toFunction.hasPeriodicWeakJet.2.1 _).sub
      ((w' i r).toFunction.hasPeriodicWeakJet.2.1 _))
    (fun _ => MemLp.zero') (fun _ => MemLp.zero')
    (((g₀ i r).toFunction.hasPeriodicWeakJet.2.1 _).sub
      ((g' i r).toFunction.hasPeriodicWeakJet.2.1 _))

/-- **The difference identity**: the given row minus the truncated regular row solves the weak
identity with zero data. -/
theorem kernel_row_difference_identity {ρ : ℝ} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hD : D' ≤ D) (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (hf : ∀ i, truncateTorusHk (Nat.zero_le _) (f' i) = f₀ i)
    (hF : ∀ i s, truncateTorusHk (Nat.zero_le _) (F' i s) = F₀ i s)
    (hg : ∀ i s, truncateTorusHk (Nat.zero_le _) (g' i s) = g₀ i s) (i : ι)
    (hprev : ∀ j, Nonempty (Γ i j) → ∀ t ∈ Set.Icc a b,
      truncateTorusHk (Nat.zero_le _) (u' j t) = u j t)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v
      ((u i t - truncateTorusHk (Nat.zero_le _) (u' i t)).toFunction.jet (valueIndex2 0))
      ((0 : TorusHk 0 (h i)).toFunction.jet (valueIndex2 0))
      (φ.toFunction.jet (valueIndex2 1)) (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
      (fun s q => (w i s - truncateTorusHk (Nat.add_le_add_right (Nat.zero_le (K i)) 1)
        (w' i s)).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => q⟩)
      (fun _ _ => 0)
      (fun _ => ((0 : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))).toFunction.jet (valueIndex2 0))
      (fun _ => (0 : TorusHk 0 (h i)).toFunction.jet (valueIndex2 0)) := by
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hdiff := coupledWeakIdentity_sub_of_flux_ae _ ν a t v _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hk.2.2.2.2.2.2 i t ht φ) (hc.2.2.2.2 i t ht φ)
    (ae_restrict_of_ae_restrict_of_subset hsub
      (kernel_row_total_flux_ae hD hA hP hS hk hc hF i hprev))
    (kernel_row_rhs_integrable hd i t ht φ)
  refine coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ hdiff
  · filter_upwards [torusHk_jet_sub_ae (u i t) (truncateTorusHk (Nat.zero_le _) (u' i t))
      (valueIndex2 0), KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le (K i))
      (u' i t) (valueIndex2 0)] with x h1 h2
    exact congrArg (fun z => inner ℝ z _)
      (h1.trans (congrArg (fun z => (u i t).toFunction.jet (valueIndex2 0) x - z) h2)).symm
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le (K i)) (f' i)
      (valueIndex2 0), torusZero_rawJet_ae (E := h i) 0 (valueIndex2 0)] with x h1 h2
    rw [hf i] at h1
    have h3 : (f₀ i).toFunction.jet (valueIndex2 0) x -
        (f' i).toFunction.jet (valueIndex2 (K i)) x = 0 := sub_eq_zero.2 h1
    simp only [Pi.sub_apply, h3, h2, Pi.zero_apply, inner_zero_left]
  · intro s _
    filter_upwards [torusHk_jet_sub_ae (w i s)
        (truncateTorusHk (Nat.add_le_add_right (Nat.zero_le (K i)) 1) (w' i s))
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => 0⟩,
      torusHk_jet_sub_ae (w i s)
        (truncateTorusHk (Nat.add_le_add_right (Nat.zero_le (K i)) 1) (w' i s))
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => 1⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.add_le_add_right (Nat.zero_le (K i)) 1)
        (w' i s) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => 0⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.add_le_add_right (Nat.zero_le (K i)) 1)
        (w' i s) ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩, fun _ => 1⟩,
      torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (valueIndex2 0),
      torusZero_rawJet_ae (E := h i) 0 (valueIndex2 0),
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le (K i)) (g' i s)
        (valueIndex2 0)] with x hd0 hd1 ht0 ht1 hQ hz hgx
    refine weakIdentityRhs_congr_at _ _ _ _ _ _ _ _ _ _ _ _ s x (fun q => ?_) ?_ ?_
    · fin_cases q
      · exact (hd0.trans (congrArg (fun z => _ - z) ht0)).symm
      · exact (hd1.trans (congrArg (fun z => _ - z) ht1)).symm
    · simp only [hQ, Pi.zero_apply, add_zero]
    · rw [hg i s] at hgx
      have h3 : (g₀ i s).toFunction.jet (valueIndex2 0) x -
          (g' i s).toFunction.jet (valueIndex2 (K i)) x = 0 := sub_eq_zero.2 hgx
      simp only [Pi.sub_apply, h3, hz, Pi.zero_apply]

/-- The difference of the given row and the truncated regular row is a forced row with zero
data. -/
theorem kernel_row_difference_row {ρ : ℝ} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hD : D' ≤ D) (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (hf : ∀ i, truncateTorusHk (Nat.zero_le _) (f' i) = f₀ i)
    (hF : ∀ i s, truncateTorusHk (Nat.zero_le _) (F' i s) = F₀ i s)
    (hg : ∀ i s, truncateTorusHk (Nat.zero_le _) (g' i s) = g₀ i s) (i : ι)
    (hprev : ∀ j, Nonempty (Γ i j) → ∀ t ∈ Set.Icc a b,
      truncateTorusHk (Nat.zero_le _) (u' j t) = u j t) :
    IsTorusForcedRow ν a b v D' 0 (0 : TorusHk 0 (h i)) (fun _ => 0) (fun _ => 0)
      (fun s => u i s - truncateTorusHk (Nat.zero_le _) (u' i s))
      (fun s => w i s - truncateTorusHk (Nat.add_le_add_right (Nat.zero_le (K i)) 1) (w' i s)) := by
  refine isTorusForcedRow_of ((hk.1 i).sub (truncate_continuousOn _ (hc.1 i)))
    ((hk.2.1 i).sub ((hc.2.1 i).continuousLinearMap_comp _)) ?_ ?_
    (kernel_row_difference_identity hd hD hA hP hS hk hc hf hF hg i hprev)
  · filter_upwards [hk.2.2.1 i, hc.2.2.1 i] with s h1 h2
    rw [ContinuousLinearMap.map_sub, h1, truncateTorusHk_trans, ← h2, truncateTorusHk_trans]
  · rw [hk.2.2.2.1 i, hc.2.2.2.1 i, hf i, sub_self]

/-- **One row is identified** once the rows it reads are. -/
theorem kernel_row_identified {ρ : ℝ} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hD : D' ≤ D) (hD' : 2 ≤ D')
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (hf : ∀ i, truncateTorusHk (Nat.zero_le _) (f' i) = f₀ i)
    (hF : ∀ i s, truncateTorusHk (Nat.zero_le _) (F' i s) = F₀ i s)
    (hg : ∀ i s, truncateTorusHk (Nat.zero_le _) (g' i s) = g₀ i s) (i : ι)
    (hprev : ∀ j, Nonempty (Γ i j) → ∀ t ∈ Set.Icc a b,
      truncateTorusHk (Nat.zero_le _) (u' j t) = u j t) :
    ∀ t ∈ Set.Icc a b, truncateTorusHk (Nat.zero_le _) (u' i t) = u i t := by
  intro t ht
  have hδ := torusForcedRow_unique hd hab hρ hν hD' (Nat.zero_le Kmax) (torusHk_memLp_zero _ _)
    (torusHk_integrable_zero _ _)
    (kernel_row_difference_row hd hD hA hP hS hk hc hf hF hg i hprev)
    (torusForcedRow_zero ν a b v D' 0) t ht
  exact (sub_eq_zero.1 hδ).symm

/-- **Identification of an order-zero kernel solution.** For a triangular family with identity
kernels and scalar maps, the order-zero solution is the truncation of the coupled solution at
reserves `K` with the same data, at every time. -/
theorem kernel_solution_identified {ρ : ℝ} {Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hD : D' ≤ D) (hD' : 2 ≤ D')
    (hA : ∀ i j d s x, A i j d s x = ∑ α : Γ i j, P i j α d.1 s x)
    (hP : ∀ i j α n, n ∈ Finset.Icc 2 D → n ∉ admissibleOrders K D' i j →
      ∀ s x, P i j α n s x = 0)
    (r : ι → ℕ) (htri : ∀ i j, Nonempty (Γ i j) → r j < r i)
    (hS : ∀ i j α s, S i j α s = ContinuousLinearMap.id ℝ _)
    (hk : IsKernelWeakSolutionTorus (Γ := Γ) (G := fun _ j _ => h j) ν a b v 0 D
      (fun i j α d => P i j α d.1) (fun _ j _ => ContinuousLinearMap.id ℝ (h j)) S f₀ F₀ g₀ u w y)
    (hc : IsCoupledWeakSolutionTorus ν a b v D' K A f' F' g' u' w')
    (hf : ∀ i, truncateTorusHk (Nat.zero_le _) (f' i) = f₀ i)
    (hF : ∀ i s, truncateTorusHk (Nat.zero_le _) (F' i s) = F₀ i s)
    (hg : ∀ i s, truncateTorusHk (Nat.zero_le _) (g' i s) = g₀ i s) :
    ∀ i, ∀ t ∈ Set.Icc a b, truncateTorusHk (Nat.zero_le _) (u' i t) = u i t := by
  intro i
  induction hn : r i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    exact kernel_row_identified hd hab hρ hν hD hD' hA hP hS hk hc hf hF hg i
      fun j hj => ih (r j) (hn ▸ htri i j hj) j rfl

end Identify

/-- **The gradients are identified** almost everywhere once the values are. -/
theorem lift_identified {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {a b : ℝ}
    {k : ℕ} {e : ℝ → TorusHk k E} {ew : ℝ → TorusHk (k + 1) E} {e₀ : ℝ → TorusHk 0 E}
    {ew₀ : ℝ → TorusHk 1 E}
    (hv : ∀ t ∈ Set.Icc a b, truncateTorusHk (Nat.zero_le _) (e t) = e₀ t)
    (h₁ : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ k) (ew t) = e t)
    (h₂ : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), truncateTorusHk (Nat.le_succ 0) (ew₀ t) = e₀ t) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      truncateTorusHk (Nat.succ_le_succ (Nat.zero_le k)) (ew t) = ew₀ t := by
  filter_upwards [h₁, h₂, ae_restrict_mem measurableSet_Icc] with t ht₁ ht₂ ht
  apply TorusHk.ext_value
  rw [show (ew₀ t).val (valueIndex2 1) =
    (truncateTorusHk (Nat.le_succ 0) (ew₀ t)).val (valueIndex2 0) from rfl, ht₂, ← hv t ht, ← ht₁]
  rfl
end

/-! **Existence for triangular coupled systems** (the bootstrap of the comparison energy). A
coupled system whose coefficients strictly lower a rank (`htri`) has a solution at every reserve
vector, by `coupled_energy_torus` at the rank-scaled masses `π_v L^{2 r_v}`
(`schurCondition_rankScaledMass`),
with `L` eight times the total Schur sum at unit masses (`triangular_coupled_exists`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **A triangular coupled system has a solution** at every reserve vector, from zero data. -/
theorem triangular_coupled_exists {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
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
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v D K A (fun _ => 0) F g u w := by
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
    K hK A hA_meas hA_smooth hA_per hA_fin hschur (fun _ => 0) F hF g hg
  exact hgate.1
end

end AVRegularity.Providers.WeakGen.Comparison
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **Drift and forcing inputs of `coupled_energy_torus`**.

* The actual stream velocity satisfies its drift hypotheses at every small radius
  (`stream_torusDriftData`): the qualitative facts are `stream_kernel_drift_data`, the jets are
  `actual_stream_drift_arrays` at `a = C ocA`, `B₀ = 1024`, `λ = ε_m`.
* A carrier trajectory that is measurable in time and has a finite factorial cost is square
  integrable (`torusHk_memLp_of_factorial`), or integrable when the cost is the time integral of
  the norm (`torusHk_integrable_of_factorial`). -/

/-- **Drift data of the actual stream velocity** at a radius `ρ ≤ ε_m/2048` with
`ρ² (C ocA_m + 1) ≤ ν/8192`. -/
theorem stream_torusDriftData_at (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m) {ν : ℝ} (t₀ t₁ : ℝ) (Kmax : ℕ)
    (ρ : ℝ) (h1 : ρ ≤ ocEpsilon q Λ m / 2048)
    (h2 : ρ ^ 2 * (Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m + 1) ≤
      ν / 8192) :
    TorusDriftData ν ρ t₀ t₁ (streamVel (Φ m)) Kmax := by
  obtain ⟨hsm, hper, hdiv, hbdd, hmeas⟩ :=
    Construction.Preservation.Buffer.stream_kernel_drift_data
      (Velocity.streamSeq_admissible hζ hΛ hΦ m) t₀ t₁
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 ≤ Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m :=
    mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos he _).le
  refine ⟨hbdd, hmeas, hsm, hdiv, hper, _, 1024, ocEpsilon q Λ m, ha, by norm_num, he,
    fun l hl _ t _ x => ?_, ?_, ?_⟩
  · exact Construction.Preservation.Buffer.actual_stream_drift_arrays α s hα₀ hα₁ hs₀ hs₁ q hq
      ζ hζ Λ hΛ Φ hΦ m hm t l hl x
  · rw [div_le_iff₀ he]
    linarith
  · nlinarith [sq_nonneg ρ]

/-- **Drift data of the actual stream velocity** at every radius below an explicit `ρ₀`. -/
theorem stream_torusDriftData (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m) {ν : ℝ} (hν : 0 < ν) (t₀ t₁ : ℝ)
    (Kmax : ℕ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      TorusDriftData ν ρ t₀ t₁ (streamVel (Φ m)) Kmax := by
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 ≤ Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m :=
    mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos he _).le
  set a := Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m with ha_def
  refine ⟨min (ocEpsilon q Λ m / 2048) (Real.sqrt (ν / (8192 * (a + 1)))),
    lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)), fun ρ hρ hρ₀ => ?_⟩
  refine stream_torusDriftData_at α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm t₀ t₁ Kmax ρ
    (hρ₀.trans (min_le_left _ _)) ?_
  have h2 : ρ ≤ Real.sqrt (ν / (8192 * (a + 1))) := hρ₀.trans (min_le_right _ _)
  have hsq : ρ ^ 2 ≤ ν / (8192 * (a + 1)) :=
    (pow_le_pow_left₀ hρ.le h2 2).trans_eq (Real.sq_sqrt (by positivity))
  rw [le_div_iff₀ (by positivity)] at hsq
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

section Forcing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- **A measurable carrier trajectory of finite factorial cost is square integrable.** -/
theorem torusHk_memLp_of_factorial {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {μ : Measure ℝ}
    {F : ℝ → TorusHk k E} (hF : AEStronglyMeasurable F μ)
    (hfin : ∫⁻ t, ENNReal.ofReal (factorialNormSq ρ (F t).val) ∂μ ≠ ⊤) : MemLp F 2 μ := by
  have hmin := factorialWeightMin_pos (K := k) ρ hρ
  refine (memLp_two_iff_integrable_sq_norm hF).2 ⟨hF.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ t, ENNReal.ofReal ‖‖F t‖ ^ 2‖ ∂μ
      ≤ ∫⁻ t, ENNReal.ofReal ((factorialWeightMin ρ k)⁻¹) *
          ENNReal.ofReal (factorialNormSq ρ (F t).val) ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hmin.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), le_inv_mul_iff₀ hmin]
        exact factorialNormSq_lower ρ (F t).val
    _ = ENNReal.ofReal ((factorialWeightMin ρ k)⁻¹) *
          ∫⁻ t, ENNReal.ofReal (factorialNormSq ρ (F t).val) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)

/-- **A measurable carrier trajectory whose norm has finite factorial time integral is
integrable.** -/
theorem torusHk_integrable_of_factorial {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {μ : Measure ℝ}
    {g : ℝ → TorusHk k E} (hg : AEStronglyMeasurable g μ)
    (hfin : ∫⁻ t, ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g t).val)) ∂μ ≠ ⊤) :
    Integrable g μ := by
  have hmin := factorialWeightMin_pos (K := k) ρ hρ
  have hs : 0 < Real.sqrt (factorialWeightMin ρ k) := Real.sqrt_pos.2 hmin
  refine ⟨hg, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ t, ENNReal.ofReal ‖g t‖ ∂μ
      ≤ ∫⁻ t, ENNReal.ofReal ((Real.sqrt (factorialWeightMin ρ k))⁻¹) *
          ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g t).val)) ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hs, ← Real.sqrt_sq (norm_nonneg (g t)), ← Real.sqrt_mul hmin.le]
        exact Real.sqrt_le_sqrt (factorialNormSq_lower ρ (g t).val)
    _ = ENNReal.ofReal ((Real.sqrt (factorialWeightMin ρ k))⁻¹) *
          ∫⁻ t, ENNReal.ofReal (Real.sqrt (factorialNormSq ρ (g t).val)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)

end Forcing

end AVRegularity.Providers.WeakGen.Comparison
end

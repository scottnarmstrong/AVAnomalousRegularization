-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ApproxDefect
public import AVRegularity.CycleComparison.Reconstruction.PrimWeak
import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.CycleComparison.Reconstruction.PiolaTested
public import AVRegularity.CycleComparison.Coarse.JointOps.Final
public import AVRegularity.CycleComparison.Coarse.Defect.FcIdent
public import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The coupled weak solution of a limit of approximants**. Let `U` be a family of `C^{K_v+2}`
periodic fields with jets of order `≤ K_v + 2` bounded uniformly on `[t_A, t_Z]`, and let
approximants `U_n` with residuals `(R_n, q_n)` satisfy the integrated weak identity of the coupled
system (edge flux `edgeFluxOf K A`) against smooth periodic tests. If the values converge in `L²` of
the cell at every time, the gradients, edge fluxes and residuals converge to those of `U` and to
`(R, q)` with errors bounded by `c n` with `∫ c n → 0`, and the limit data are bounded by an
integrable function, then the carrier trajectories `û_v = periodicHk (K_v) U_v` and
`ŵ_v = periodicHk (K_v + 1) U_v` form a coupled weak solution with residual `(R, q)`
(`isCoupledWeakSolutionTorus_of_approximants`). Continuity in time comes from the weak identity
(`tendsto_cellL2_sub_of_weakIdentity`, `continuousOn_periodicHk_of_L2`). -/

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The jets of the carrier of a finitely smooth periodic field are a.e. its ordered
derivatives. -/
theorem periodicHk_toFunction_ae (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 K) :
    (periodicHk K f hf hp).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative a.2 f :=
  (periodicJetRepresentative_ae (periodicHk K f hf hp).val a).trans (periodicHk_jet_ae K f hf hp a)

end Carrier

/-- An admissible order is at most one above the slot of the target component. -/
theorem admissibleOrders_sub_one_le {ι : Type*} {K : ι → ℕ} {D : ℕ} {i i' : ι}
    (d : admissibleOrders K D i i') : d.1 - 1 ≤ K i' + 1 := by
  have h := Finset.mem_filter.1 d.2
  omega

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The edge flux of a field `U` with the edge coefficients `A`:
`∑_{i'} ∑_d A_{v i' d}(s, x) (∂^{d-1} U_{i'})(x)`. -/
def edgeFluxOf {D : ℕ} (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (s : ℝ) (U : Vec 2 → ∀ i, h i) (v : ι) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ i' : ι, ∑ d : admissibleOrders K D v i', A v i' d s x
    (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => U y i') x)

/-- **The coupled weak solution of a limit of approximants.** -/
theorem isCoupledWeakSolutionTorus_of_approximants {ν tA tZ : ℝ} (htAZ : tA ≤ tZ)
    (b : ℝ → Vec 2 → Vec 2) (Vb : ℝ)
    (hbm : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      AEStronglyMeasurable (fun x => b s x k) (volume.restrict AVenhance.unitCube))
    (hb : ∀ s ∈ Set.Ioc tA tZ, ∀ x k, |b s x k| ≤ Vb)
    {D : ℕ} (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (U : ℝ → Vec 2 → ∀ i, h i)
    (hU : ∀ t v, ContDiff ℝ ((K v + 2 : ℕ) : ℕ∞) (fun x => U t x v))
    (hUp : ∀ t v, AVenhance.IsZ2Periodic (fun x => U t x v)) {CU : ℝ} (hCU : 0 ≤ CU)
    (hUb : ∀ t ∈ Set.Icc tA tZ, ∀ v, ∀ i, i ≤ K v + 2 → ∀ (w : DerivativeWord2 i) (x : Vec 2),
      ‖orderedDerivative w (fun y => U t y v) x‖ ≤ CU)
    (R : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk (K v) (h v))
    (C : ℝ → ℝ) (hC : IntegrableOn C (Set.Ioc tA tZ))
    (hCU' : ∀ s ∈ Set.Ioc tA tZ, CU ≤ C s)
    (hEC : ∀ s ∈ Set.Ioc tA tZ, ∀ v k,
      MemLp (fun x => edgeFluxOf K A s (U s) v x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => edgeFluxOf K A s (U s) v x k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hRC : ∀ s ∈ Set.Ioc tA tZ, ∀ v k,
      MemLp (fun x => (R v s).toFunction.jet (valueIndex2 (K v)) x k) 2
          (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => (R v s).toFunction.jet (valueIndex2 (K v)) x k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hqC : ∀ s ∈ Set.Ioc tA tZ, ∀ v,
      MemLp ((q v s).toFunction.jet (valueIndex2 (K v))) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm ((q v s).toFunction.jet (valueIndex2 (K v))) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (Un : ℕ → ℝ → Vec 2 → ∀ i, h i)
    (Rn : ℕ → ∀ v, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (qn : ℕ → ∀ v, ℝ → Vec 2 → h v)
    (hUn : ∀ n, ∀ t ∈ Set.Icc tA tZ, ∀ v,
      MemLp (fun x => Un n t x v - U t x v) 2 (volume.restrict AVenhance.unitCube))
    (hUlim : ∀ t ∈ Set.Icc tA tZ, ∀ v, Tendsto (fun n =>
      (eLpNorm (fun x => Un n t x v - U t x v) 2 (volume.restrict AVenhance.unitCube)).toReal)
      atTop (𝓝 0))
    (c : ℕ → ℝ → ℝ) (hc : ∀ n, IntegrableOn (c n) (Set.Ioc tA tZ))
    (hc0 : Tendsto (fun n => ∫ s in Set.Ioc tA tZ, c n s) atTop (𝓝 0))
    (hdUn : ∀ n, ∀ s ∈ Set.Ioc tA tZ, ∀ v k,
      MemLp (fun x => fderiv ℝ (fun y => Un n s y v) x (basisVec k) -
          fderiv ℝ (fun y => U s y v) x (basisVec k)) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => fderiv ℝ (fun y => Un n s y v) x (basisVec k) -
          fderiv ℝ (fun y => U s y v) x (basisVec k)) 2
            (volume.restrict AVenhance.unitCube)).toReal ≤ c n s)
    (hEn : ∀ n, ∀ s ∈ Set.Ioc tA tZ, ∀ v k,
      MemLp (fun x => (edgeFluxOf K A s (Un n s) v x - edgeFluxOf K A s (U s) v x) k) 2
          (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => (edgeFluxOf K A s (Un n s) v x - edgeFluxOf K A s (U s) v x) k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c n s)
    (hRn : ∀ n, ∀ s ∈ Set.Ioc tA tZ, ∀ v k,
      MemLp (fun x => (Rn n v s x - (R v s).toFunction.jet (valueIndex2 (K v)) x) k) 2
          (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => (Rn n v s x - (R v s).toFunction.jet (valueIndex2 (K v)) x) k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c n s)
    (hqn : ∀ n, ∀ s ∈ Set.Ioc tA tZ, ∀ v,
      MemLp (fun x => qn n v s x - (q v s).toFunction.jet (valueIndex2 (K v)) x) 2
          (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => qn n v s x - (q v s).toFunction.jet (valueIndex2 (K v)) x) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c n s)
    (hid : ∀ n, ∀ t ∈ Set.Icc tA tZ, ∀ v, ∀ φ : Vec 2 → h v, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t b (fun x => Un n t x v)
        (fun x => Un n tA x v) φ (fun k x => fderiv ℝ φ x (basisVec k))
        (fun s k x => fderiv ℝ (fun y => Un n s y v) x (basisVec k))
        (fun s x => edgeFluxOf K A s (Un n s) v x) (Rn n v) (qn n v)) :
    IsCoupledWeakSolutionTorus ν tA tZ b D K A
      (fun v => periodicHk (K v) (fun x => U tA x v)
        ((hU tA v).of_le (by exact_mod_cast Nat.le_add_right (K v) 2)) (hUp tA v)) R q
      (fun v t => periodicHk (K v) (fun x => U t x v)
        ((hU t v).of_le (by exact_mod_cast Nat.le_add_right (K v) 2)) (hUp t v))
      (fun v t => periodicHk (K v + 1) (fun x => U t x v)
        ((hU t v).of_le (by exact_mod_cast Nat.le_succ (K v + 1))) (hUp t v)) := by
  classical
  -- the continuity, smoothness and bounds of the components
  have hUc : ∀ t v, Continuous (fun x => U t x v) := fun t v => (hU t v).continuous
  have hU1 : ∀ t v, ContDiff ℝ 1 (fun x => U t x v) := fun t v =>
    (hU t v).of_le (by exact_mod_cast (by omega : 1 ≤ K v + 2))
  have hmem : ∀ t v, MemLp (fun x => U t x v) 2 (volume.restrict AVenhance.unitCube) :=
    fun t v => Coarse.memLp_two_cell_of_continuous (hUc t v)
  have hdcont : ∀ s v (k : Fin 2),
      Continuous (fun x => fderiv ℝ (fun y => U s y v) x (basisVec k)) :=
    fun s v k => ((hU1 s v).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdbound : ∀ s ∈ Set.Icc tA tZ, ∀ v (k : Fin 2) x,
      ‖fderiv ℝ (fun y => U s y v) x (basisVec k)‖ ≤ CU := by
    intro s hs v k x
    have := hUb s hs v 1 (by omega) (fun _ => k) x
    rwa [orderedDerivative_one_eq_fderiv] at this
  -- the limit identity against first-order tests
  have hlim : ∀ v, ∀ t ∈ Set.Icc tA tZ, ∀ φ : TorusHk 1 (h v),
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t b (fun x => U t x v)
        (fun x => U tA x v) (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
        (fun s k x => fderiv ℝ (fun y => U s y v) x (basisVec k))
        (fun s x => edgeFluxOf K A s (U s) v x)
        (fun s => (R v s).toFunction.jet (valueIndex2 (K v)))
        (fun s => (q v s).toFunction.jet (valueIndex2 (K v))) := by
    intro v
    refine coupledWeakIdentity_limit (H := h v) b Vb hbm hb (fun t x => U t x v)
      (fun s k x => fderiv ℝ (fun y => U s y v) x (basisVec k))
      (fun s x => edgeFluxOf K A s (U s) v x)
      (fun s => (R v s).toFunction.jet (valueIndex2 (K v)))
      (fun s => (q v s).toFunction.jet (valueIndex2 (K v))) (fun t _ => hmem t v) C hC
      (fun s hs k => ⟨Coarse.memLp_two_cell_of_continuous (hdcont s v k),
        (cellL2_le_of_bound (hdcont s v k).aestronglyMeasurable hCU
          (hdbound s (Set.Ioc_subset_Icc_self hs) v k)).trans (hCU' s hs)⟩)
      (fun s hs k => hEC s hs v k) (fun s hs k => hRC s hs v k) (fun s hs => hqC s hs v)
      (fun n t x => Un n t x v) (fun n s k x => fderiv ℝ (fun y => Un n s y v) x (basisVec k))
      (fun n s x => edgeFluxOf K A s (Un n s) v x) (fun n => Rn n v) (fun n => qn n v)
      (fun n t ht => hUn n t ht v) (fun t ht => hUlim t ht v) c hc hc0
      (fun n s hs k => hdUn n s hs v k) (fun n s hs k => hEn n s hs v k)
      (fun n s hs k => hRn n s hs v k) (fun n s hs => hqn n s hs v)
      (fun n t ht φ hφ hφp => hid n t ht v φ hφ hφp)
  -- `L²` continuity in time of every component
  have hL2 : ∀ v, ∀ t ∈ Set.Icc tA tZ, Tendsto (fun s => cellL2 (fun x => U s x v - U t x v))
      (𝓝[Set.Icc tA tZ] t) (𝓝 0) := by
    intro v
    set U' : ℝ → TorusHk 1 (h v) := fun t => periodicHk 1 (fun x => U t x v)
      (contDiff_one_natCast (hU1 t v)) (hUp t v) with hU'
    have hU'ae : ∀ t, (U' t).toFunction.jet (valueIndex2 1) =ᵐ[volume.restrict
        AVenhance.unitCube] fun x => U t x v := fun t =>
      (periodicHk_toFunction_ae 1 _ _ _ (valueIndex2 1)).trans
        (Filter.EventuallyEq.of_eq (orderedDerivative_valueIndex2_one _))
    have hU'b : ∀ t ∈ Set.Icc tA tZ, ‖U' t‖ ≤ Fintype.card (JetIndex2 1) * CU := by
      intro t ht
      have h0 : ∀ a : JetIndex2 1, (0 : TorusHk 1 (h v)).val a =ᵐ[volume.restrict
          AVenhance.unitCube] (fun _ : Vec 2 => (0 : h v)) := fun a => Lp.coeFn_zero _ _ _
      have := torusHk_sub_norm_le_of_jet_ae (U' t) 0
        (fun a => orderedDerivative a.2 (fun x => U t x v)) (fun _ _ => 0)
        (fun a => periodicHk_jet_ae 1 _ _ _ a) h0 hCU (fun a x _ => by
          rw [sub_zero]
          exact hUb t ht v a.1.val (by have := a.1.isLt; omega) a.2 x)
      rwa [sub_zero] at this
    have hid' : ∀ t ∈ Set.Icc tA tZ, ∀ φ : TorusHk 1 (h v),
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t b
          ((U' t).toFunction.jet (valueIndex2 1)) ((U' tA).toFunction.jet (valueIndex2 1))
          (φ.toFunction.jet (valueIndex2 1))
          (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
          (fun s k x => fderiv ℝ (fun y => U s y v) x (basisVec k))
          (fun s x => edgeFluxOf K A s (U s) v x)
          (fun s => (R v s).toFunction.jet (valueIndex2 (K v)))
          (fun s => (q v s).toFunction.jet (valueIndex2 (K v))) := by
      intro t ht φ
      refine AVRegularity.CycleJointProofs.coupledWeakIdentity_integrands_congr _ ν tA t b b
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ (fun s _ => Filter.EventuallyEq.rfl)
        (hlim v t ht φ)
      · filter_upwards [hU'ae t] with x hx
        rw [hx]
      · filter_upwards [hU'ae tA] with x hx
        rw [hx]
    have hC₁ := tendsto_cellL2_sub_of_weakIdentity htAZ b Vb hbm hb U' hU'b
      (fun s k x => fderiv ℝ (fun y => U s y v) x (basisVec k))
      (fun s x => edgeFluxOf K A s (U s) v x)
      (fun s => (R v s).toFunction.jet (valueIndex2 (K v)))
      (fun s => (q v s).toFunction.jet (valueIndex2 (K v))) C hC
      (fun s hs k => ⟨Coarse.memLp_two_cell_of_continuous (hdcont s v k),
        (cellL2_le_of_bound (hdcont s v k).aestronglyMeasurable hCU
          (hdbound s (Set.Ioc_subset_Icc_self hs) v k)).trans (hCU' s hs)⟩)
      (fun s hs k => hEC s hs v k) (fun s hs k => hRC s hs v k) (fun s hs => hqC s hs v) hid'
    intro t ht
    refine (hC₁ t ht).congr fun s => ?_
    unfold cellL2
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hU'ae s, hU'ae t] with x hs ht'
    rw [hs, ht']
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => rfl, fun v t ht φ => ?_⟩
  · -- continuity of the value trajectory
    exact continuousOn_periodicHk_of_L2 (K v) (fun t x => U t x v)
      (fun t => (hU t v).of_le (by exact_mod_cast (by omega : K v + 1 ≤ K v + 2)))
      (fun t => hUp t v) hCU (fun t ht i hi w x => hUb t ht v i (by omega) w x) (hL2 v)
  · -- the gradient trajectory is square integrable
    exact memLp_two_of_continuousOn_Icc (continuousOn_periodicHk_of_L2 (K v + 1)
      (fun t x => U t x v) (fun t => hU t v) (fun t => hUp t v) hCU
      (fun t ht i hi w x => hUb t ht v i (by omega) w x) (hL2 v))
  · -- the truncation of the gradient trajectory is the value trajectory
    exact Filter.Eventually.of_forall fun s => truncate_periodicHk_succ (K v) _ _ _
  · -- the weak identity, by a.e. congruence of the integrands
    have hval : ∀ s, (periodicHk (K v) (fun x => U s x v)
        ((hU s v).of_le (by exact_mod_cast Nat.le_add_right (K v) 2)) (hUp s v)).toFunction.jet
          (valueIndex2 (K v)) =ᵐ[volume.restrict AVenhance.unitCube] fun x => U s x v :=
      fun s => (periodicHk_toFunction_ae (K v) _ _ _ (valueIndex2 (K v))).trans
        (Filter.EventuallyEq.of_eq (AVRegularity.orderedDerivative_zero _ _))
    have hgrad : ∀ s (k : Fin 2), (periodicHk (K v + 1) (fun x => U s x v)
        ((hU s v).of_le (by exact_mod_cast Nat.le_succ (K v + 1))) (hUp s v)).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => k⟩
          =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => fderiv ℝ (fun y => U s y v) x (basisVec k) :=
      fun s k => (periodicHk_toFunction_ae (K v + 1) _ _ _ _).trans
        (Filter.EventuallyEq.of_eq (orderedDerivative_one_eq_fderiv _ _))
    have hedge : ∀ s, (fun x => ∑ i' : ι, ∑ d : admissibleOrders K D v i',
        A v i' d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (periodicHk (K i' + 1) (fun x => U s x i')
            ((hU s i').of_le (by exact_mod_cast Nat.le_succ (K i' + 1))) (hUp s i')).toFunction.jet
            ⟨⟨d.1 - 1, by have := admissibleOrders_sub_one_le d; omega⟩, word⟩ x))
          =ᵐ[volume.restrict AVenhance.unitCube] fun x => edgeFluxOf K A s (U s) v x := by
      intro s
      have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ i' : ι,
          ∀ d : admissibleOrders K D v i', ∀ word : DerivativeWord2 (d.1 - 1),
            (periodicHk (K i' + 1) (fun x => U s x i')
              ((hU s i').of_le (by exact_mod_cast Nat.le_succ (K i' + 1)))
                (hUp s i')).toFunction.jet
              ⟨⟨d.1 - 1, by have := admissibleOrders_sub_one_le d; omega⟩, word⟩ x =
            orderedDerivative word (fun y => U s y i') x := by
        refine ae_all_iff.2 fun i' => ae_all_iff.2 fun d => ae_all_iff.2 fun word => ?_
        exact periodicHk_toFunction_ae (K i' + 1) _ _ _
          ⟨⟨d.1 - 1, by have := admissibleOrders_sub_one_le d; omega⟩, word⟩
      filter_upwards [hall] with x hx
      simp only [edgeFluxOf, hx]
    have hall : ∀ s, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ k : Fin 2,
        (periodicHk (K v + 1) (fun x => U s x v)
          ((hU s v).of_le (by exact_mod_cast Nat.le_succ (K v + 1))) (hUp s v)).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => k⟩ x =
        fderiv ℝ (fun y => U s y v) x (basisVec k) :=
      fun s => ae_all_iff.2 fun k => hgrad s k
    refine AVRegularity.CycleJointProofs.coupledWeakIdentity_integrands_congr _ ν tA t b b
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ (fun s _ => ?_) (hlim v t ht φ)
    · filter_upwards [hval t] with x hx
      rw [hx]
    · filter_upwards [hval tA] with x hx
      rw [hx]
    · filter_upwards [hall s, hedge s] with x hx he
      simp only [AVRegularity.Weighted.weakIdentityRhs, hx, he]

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Coarse.JointOps
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time measurability of the retained coarse flux** `F_coarse` of a coarse witness,
for the physical reconstruction.

The flux `Fc` is only characterized by the second clause of `IsCoarseWitness`: on the window, its
pairing with a family of smooth periodic tests `ψ` is a finite sum of pairings
`∫_{cell} ⟨∑_{(i,h) ∈ S} U_{i,h}(s), A(s)⟩` of partial response sums, which are continuous in time
(`IsCoarseResponses`), with test fields `A(s)` built from `ψ` by the adjoint operators
`coarseFluxAdjoint`, `edgeFluxAdjoint`, `covPolyP/Q` and the Taylor operator, which are jointly
measurable in time and space with continuous slices (the `JMF` calculus of `Coarse.JointOps`, from
the measurability premises of `IsCoarseSetting`). The pairing of a continuous `L²`-valued curve with
such a field is measurable in time, everywhere on the window (Pettis, through a countable separating
family of the separable space `L²(cell)`). Hence:

* (F1) the clamped pairings `s ↦ ∑_v ∫ ⟨Fc_v(π s), ψ_v⟩` and `s ↦ ∫ ⟨Fc_{v₀}(π s), ψ₀⟩` are
  measurable, `π = Set.projIcc t₀ t₁` (`coarseFc_pairing_measurable`,
  `coarseFc_pairing_single_measurable`);
* (F2) the Galerkin coefficients of `Fc(π s)` are measurable (`coarseFc_modeCoeff_measurable`, the
  hypothesis `hFm` of `approxFlux_tested_measurable`);
* (F3) each `Fc v` is a.e. strongly measurable on the window (`coarseFc_aestronglyMeasurable`).

No measurability of `Fc` itself is assumed. -/

/-! ### Measurability tools -/

/-- Measurability transfers along a pointwise equality. -/
theorem measurable_of_pointwise_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f g : α → β} (hg : Measurable g) (h : ∀ a, f a = g a) : Measurable f := by
  rw [show f = g from funext h]
  exact hg

/-- A map into a Polish normed space is strongly measurable if the coordinates of a countable
separating family of continuous functionals are measurable (everywhere version of
`aestronglyMeasurable_of_separating_coords`). -/
theorem stronglyMeasurable_of_separating_coords {α X : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [SecondCountableTopology X] [CompleteSpace X]
    (Φ : ℕ → X → ℝ) (hΦ : ∀ n, Continuous (Φ n))
    (hsep : ∀ x y : X, (∀ n, Φ n x = Φ n y) → x = y) {G : α → X}
    (hG : ∀ n, Measurable fun a => Φ n (G a)) : StronglyMeasurable G := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have : PolishSpace X := inferInstance
  let Ψ : X → ℕ → ℝ := fun x n => Φ n x
  have hΨc : Continuous Ψ := continuous_pi hΦ
  have hΨi : Function.Injective Ψ := fun x y h => hsep x y (fun n => congrFun h n)
  have hemb : MeasurableEmbedding Ψ := hΨc.measurableEmbedding hΨi
  have hcomp : Measurable (Ψ ∘ G) := measurable_pi_iff.mpr hG
  exact (hemb.measurable_comp_iff.mp hcomp).stronglyMeasurable

/-- **The pairing of a continuous Sobolev curve with a jointly measurable field of continuous
slices is measurable in time**, everywhere on the window. -/
theorem measurable_cellInner_tval_of_jointlyMeas {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t₀ t₁ : ℝ} {K : ℕ} {X : ℝ → TorusHk K E} (hX : ContinuousOn X (Set.Icc t₀ t₁))
    {A : ℝ → Vec 2 → E} (hA : JointlyMeas t₀ t₁ A)
    (hc : ∀ s ∈ Set.Icc t₀ t₁, Continuous (A s)) :
    Measurable fun s : Set.Icc t₀ t₁ => cellInner (tval (X s)) (A s) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have hL : ∀ s : Set.Icc t₀ t₁, MemLp (A s) 2 (volume.restrict AVenhance.unitCube) :=
    fun s => memLp_two_cell_of_continuous (hc s s.2)
  -- the value classes are continuous in time
  have hu : StronglyMeasurable fun s : Set.Icc t₀ t₁ => tvalL2 (X s) :=
    (continuous_tvalL2.comp hX.domRestrict).stronglyMeasurable
  -- the classes of the test fields are strongly measurable in time
  have ha : StronglyMeasurable fun s : Set.Icc t₀ t₁ => (hL s).toLp (A s) := by
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq
      (Lp E 2 (volume.restrict AVenhance.unitCube))
    refine stronglyMeasurable_of_separating_coords (fun n w => inner ℝ w (d n))
      (fun n => continuous_id.inner continuous_const) (fun x y hxy => ?_) fun n => ?_
    · have hc' : Continuous (fun w : Lp E 2 (volume.restrict AVenhance.unitCube) =>
          inner ℝ (x - y) w) := continuous_const.inner continuous_id
      have hz : (fun w : Lp E 2 (volume.restrict AVenhance.unitCube) =>
          inner ℝ (x - y) w) = fun _ => 0 := by
        refine hc'.ext_on hd continuous_const ?_
        rintro _ ⟨n, rfl⟩
        simp [inner_sub_left, hxy n]
      have := congrFun hz (x - y)
      simpa [inner_self_eq_zero, sub_eq_zero] using this
    · have hprod : StronglyMeasurable fun q : Set.Icc t₀ t₁ × Vec 2 =>
          inner ℝ (A q.1 q.2) (d n q.2) :=
        StronglyMeasurable.inner (𝕜 := ℝ) (Measurable.stronglyMeasurable hA)
          ((Lp.stronglyMeasurable (d n)).comp_measurable measurable_snd)
      have hint := hprod.integral_prod_right' (ν := volume.restrict AVenhance.unitCube)
      refine measurable_of_pointwise_eq hint.measurable fun s => ?_
      show inner ℝ ((hL s).toLp (A s)) (d n) =
        ∫ x in AVenhance.unitCube, inner ℝ (A s x) (d n x)
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(hL s).coeFn_toLp] with x hx
      rw [hx]
  refine measurable_of_pointwise_eq (StronglyMeasurable.inner (𝕜 := ℝ) hu ha).measurable
    fun s => ?_
  exact (inner_tvalL2 (X s) ((hL s).toLp (A s)) (A s) (hL s).coeFn_toLp).symm

/-! ### Pairings of partial response sums -/

/-- A truncated partial sum of the responses is continuous in time on the window. -/
theorem respSum_continuousOn {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ : ℝ} {k J H L : ℕ}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    (hU : ∀ i, i ≤ J → ∀ j, j ≤ H → ∀ v, ContinuousOn (U i j v) (Set.Icc t₀ t₁))
    {S : Finset (ℕ × ℕ)} (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) (v : ι) :
    ContinuousOn (fun t => respSum k J H L U S v t) (Set.Icc t₀ t₁) := by
  show ContinuousOn (fun t => ∑ ij ∈ S, respTrunc k J H L U ij v t) (Set.Icc t₀ t₁)
  refine continuousOn_finsetSum _ fun ij hij => ?_
  have hb := hS ij hij
  by_cases hle : k + 2 * L ≤ coarseSlot k J H L ij.1 ij.2
  · refine ((truncateTorusHk (E := h v) hle).continuous.comp_continuousOn
      (hU ij.1 hb.1 ij.2 hb.2 v)).congr fun _ _ => ?_
    unfold respTrunc
    simp only [hle, ↓reduceDIte, Function.comp_apply]
  · refine (continuousOn_const (c := (0 : TorusHk (k + 2 * L) (h v)))).congr fun _ _ => ?_
    unfold respTrunc
    simp only [hle, ↓reduceDIte]

/-- **The pairing of a partial response sum with a jointly measurable test field of continuous
slices is measurable in time** on the window. -/
theorem measurable_cellInner_familyValueSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ : ℝ} {k J H L : ℕ}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    (hU : ∀ i, i ≤ J → ∀ j, j ≤ H → ∀ v, ContinuousOn (U i j v) (Set.Icc t₀ t₁))
    {S : Finset (ℕ × ℕ)} (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) (v : ι)
    (A : ℝ → Vec 2 → h v) (hA : JMF t₀ t₁ 0 A) :
    Measurable fun s : Set.Icc t₀ t₁ => cellInner (familyValueSum k J H L U S v s) (A s) := by
  refine measurable_of_pointwise_eq (measurable_cellInner_tval_of_jointlyMeas
    (X := fun t => respSum k J H L U S v t) (respSum_continuousOn hU hS v) hA.1
    fun s hs => hA.continuous hs) fun s => ?_
  exact (cellInner_respSum U S hS v s (hA.continuous s.2)).symm

/-! ### Joint measurability of the test fields of the retained flux -/

/-- `ψ - 𝖰_p 𝖯_p ψ` is jointly measurable with smooth slices, for a smooth time-independent `ψ`. -/
theorem jmf_sub_covPolyQP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {t₀ t₁ : ℝ}
    {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) (p : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    JMF t₀ t₁ n fun s =>
      ψ - AVRegularity.covPolyQ (Hc s) p (AVRegularity.covPolyP (Hc s) p ψ) := by
  have h1 := (JMF.of_contDiff (t₀ := t₀) (t₁ := t₁) (r := n) hψ).sub
    (JMF.cov_polyQ hH p (JMF.cov_polyP hH p (JMF.of_contDiff (r := n + 2 * p + 2 * p) hψ)))
  exact h1

/-- The coarse flux adjoint `F_p(s)^*` of a jointly measurable family of fields of every order is
jointly measurable with continuous slices. -/
theorem jmf_coarseFluxAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t₀ t₁ : ℝ} {b : ℝ → Vec 2 → Vec 2} {D p N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => b q.1 q.2)
    (hbs : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hAD : ∀ d, Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => AD d q.1 q.2)
    (hADs : ∀ d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (AD d t))
    (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j) (hN : 2 * p + D ≤ N)
    {Φ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hΦ : ∀ n, JMF t₀ t₁ n Φ) :
    JMF t₀ t₁ 0 fun s => AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s (Φ s) := by
  have hbj : ∀ n, JMF t₀ t₁ n b := JMF.of_smooth hb hbs
  have hQa : ∀ a n, JMF t₀ t₁ n fun s => (AVRegularity.covOperator (Hc s))^[a] (Φ s) :=
    fun a n => JMF.cov_iter hH a n _ (hΦ (n + 2 * a))
  -- the commutator terms
  have hA : JMF t₀ t₁ 0 fun s x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator (Hc s))^[l - 1 - a]
        (AVRegularity.commutatorAdjoint b (Hc s) s
          ((AVRegularity.covOperator (Hc s))^[a] (Φ s))) x := by
    refine JMF.sum _ fun l _ => ?_
    have h1 : JMF t₀ t₁ 0 fun s x => ∑ a ∈ Finset.range l,
        (AVRegularity.covOperator (Hc s))^[l - 1 - a]
          (AVRegularity.commutatorAdjoint b (Hc s) s
            ((AVRegularity.covOperator (Hc s))^[a] (Φ s))) x := by
      refine JMF.sum _ fun a _ => ?_
      have h2 := JMF.comm_adjoint (r := 2 * (l - 1 - a)) hbj hH (hQa a _)
      exact JMF.cov_iter hH (l - 1 - a) 0 _ (h2.mono (by omega))
    exact ⟨h1.1.smul measurable_const, fun s hs => (h1.2 s hs).const_smul _⟩
  -- the diagonal term
  have hdiag : JMF t₀ t₁ (2 * p) fun s => AVRegularity.diagonalFluxAdjoint D AD s (Φ s) :=
    JMF.diagonal_flux D (fun d => ⟨hAD d, fun s hs =>
      (hADs d s hs).of_le (by exact_mod_cast hN)⟩) (hΦ _)
  have hP := JMF.cov_polyP hH p (r := 0) (hdiag.mono (by omega))
  have e : (fun s => AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s (Φ s)) =
      fun s x => (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
        ∑ a ∈ Finset.range l, (AVRegularity.covOperator (Hc s))^[l - 1 - a]
          (AVRegularity.commutatorAdjoint b (Hc s) s
            ((AVRegularity.covOperator (Hc s))^[a] (Φ s))) x) -
        AVRegularity.covPolyP (Hc s) p (AVRegularity.diagonalFluxAdjoint D AD s (Φ s)) x := by
    funext s x
    simp only [AVRegularity.coarseFluxAdjoint, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  exact (congrArg (JMF t₀ t₁ 0) e).mpr (hA.sub hP)

/-- The `u`-component of the edge flux adjoint `F_E(s)^*` of a jointly measurable family is jointly
measurable, losing `D` orders. -/
theorem jmf_edgeFluxAdjoint {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ : ℝ} {D H N r : ℕ}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))} (u : ι)
    (hCE : ∀ ρ ∈ Finset.Icc 1 H, ∀ v d,
      Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => CE ρ v u d q.1 q.2)
    (hCEs : ∀ ρ ∈ Finset.Icc 1 H, ∀ v d, ∀ t ∈ Set.Icc t₀ t₁,
      ContDiff ℝ (N : ℕ) (CE ρ v u d t))
    (hN : r + D ≤ N) {Φ : ∀ v, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (hΦ : ∀ v, JMF t₀ t₁ (r + D) (Φ v)) :
    JMF t₀ t₁ r fun s => AVRegularity.edgeFluxAdjoint D H CE s (fun v => Φ v s) u := by
  have hE : JMF t₀ t₁ r fun s x => ∑ ρ ∈ Finset.Icc 1 H, ∑ v : ι, ∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint
        (CE ρ v u d s y) (Φ v s y)) x := by
    refine JMF.sum _ fun ρ hρ => JMF.sum _ fun v _ => JMF.sum _ fun d _ => ?_
    have hd : d.1 - 1 ≤ D := by have := (Finset.mem_Icc.mp d.2).2; omega
    exact JMF.word_adjoint_adjoint ⟨hCE ρ hρ v d, fun s hs =>
      (hCEs ρ hρ v d s hs).of_le (by exact_mod_cast (by omega : r + (d.1 - 1) ≤ N))⟩
      ((hΦ v).mono (by omega))
  unfold AVRegularity.edgeFluxAdjoint
  exact hE

/-- The Taylor test field `(p!)⁻¹ 𝒞^p ∑_{k,l} (𝖩(s) - B I)_{kl} ∂_l ψ_k` of a smooth
time-independent `ψ` is jointly measurable with continuous slices. -/
theorem jmf_taylorField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {t₀ t₁ : ℝ}
    {Hc Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j)
    (hJ : ∀ i j, Measurable fun t => Jm t i j) (B : ℝ) (p : ℕ)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    JMF t₀ t₁ 0 fun s => ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (Hc s))^[p]
      (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
        (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
          fderiv ℝ (fun y => ψ y k') x (basisVec l)) := by
  have hc : ∀ k' l : Fin 2, Measurable fun s : Set.Icc t₀ t₁ =>
      Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l := fun k' l =>
    ((hJ k' l).comp measurable_subtype_coe).sub measurable_const
  have hd : ∀ n (k' l : Fin 2), JMF t₀ t₁ n fun _ x =>
      fderiv ℝ (fun y => ψ y k') x (basisVec l) :=
    fun n k' l => ((JMF.of_contDiff (t₀ := t₀) (t₁ := t₁) (r := n + 1) hψ).proj k').dbasis l
  have hin : ∀ n, JMF t₀ t₁ n fun s x => ∑ k' : Fin 2, ∑ l : Fin 2,
      (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
        fderiv ℝ (fun y => ψ y k') x (basisVec l) := fun n =>
    JMF.sum _ fun k' _ => JMF.sum _ fun l _ => (hd n k' l).smul_time
      (c := fun s => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) (hc k' l)
  have h1 := JMF.cov_iter hH p 0 _ (hin (0 + 2 * p))
  exact h1.smul_time (c := fun _ => ((p.factorial : ℝ)⁻¹)) measurable_const

/-! ### The retained flux -/

/-- **(F1) The pairings of the retained flux with a family of smooth periodic tests are measurable
in the clamped time.** -/
theorem coarseFc_pairing_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (ψ : ∀ v, Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (hψ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (ψ v))
    (hp : ∀ v, AVenhance.IsZ2Periodic (ψ v)) :
    Measurable fun s => ∑ v, cellInner (fun x =>
      (Fc v (Set.projIcc t₀ t₁ P.window s)).toFunction.jet (valueIndex2 k) x) (ψ v) := by
  set Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ := covarianceMatrix Jm B t₀
  obtain ⟨Mj, hMj⟩ := jm_bound P
  have hH : ∀ i j, Measurable fun s : Set.Icc t₀ t₁ => Hc s i j :=
    jo_covarianceMatrix_entries_measurable P.window B P.J_meas hMj
  have hU : ∀ i, i ≤ J → ∀ j, j ≤ H → ∀ u, ContinuousOn (U i j u) (Set.Icc t₀ t₁) := by
    intro i hi j hj u
    obtain ⟨_, _, hsol, _⟩ := hR i hi j hj
    exact hsol.1 u
  have hLN : L ≤ N := by
    rw [P.N_eq]
    exact (Nat.le_mul_of_pos_left L (by omega : 0 < J + H + 3)).trans (Nat.le_add_left _ _)
  have hN : 2 * p + D ≤ N := by have := P.L_eq; omega
  -- the cell boxes of the five pieces
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS4 : ∀ ij ∈ Finset.range (J + 1) ×ˢ ({H} : Finset ℕ), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  -- the five test fields are jointly measurable with continuous slices
  have hA1 : ∀ v, JMF t₀ t₁ 0 fun s => AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s
      (ψ v - AVRegularity.covPolyQ (Hc s) p (AVRegularity.covPolyP (Hc s) p (ψ v))) :=
    fun v => jmf_coarseFluxAdjoint P.drift_meas P.drift_smooth P.AD_meas
      (fun d t ht => P.AD_smooth d t ht) hH hN (jmf_sub_covPolyQP hH p (hψ v))
  have hA2 : ∀ u, JMF t₀ t₁ 0 fun s => AVRegularity.covPolyP (Hc s) p
      (AVRegularity.edgeFluxAdjoint D H CE s (fun v => ψ v - AVRegularity.covPolyQ (Hc s) p
        (AVRegularity.covPolyP (Hc s) p (ψ v))) u) := fun u =>
    JMF.cov_polyP hH p (r := 0) (jmf_edgeFluxAdjoint u (fun r hr v d => P.CE_meas r hr v u d)
      (fun r hr v d t ht => P.CE_smooth r hr v u d t ht) (by omega)
      (Φ := fun v s => ψ v - AVRegularity.covPolyQ (Hc s) p (AVRegularity.covPolyP (Hc s) p (ψ v)))
      fun v => jmf_sub_covPolyQP hH p (hψ v) _)
  have hA3 : ∀ v, JMF t₀ t₁ 0 fun s => AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s (ψ v) :=
    fun v => jmf_coarseFluxAdjoint P.drift_meas P.drift_smooth P.AD_meas
      (fun d t ht => P.AD_smooth d t ht) hH hN (Φ := fun _ => ψ v)
      fun _ => JMF.of_contDiff (hψ v)
  have hA4 : ∀ u, JMF t₀ t₁ 0 fun s => AVRegularity.covPolyP (Hc s) p
      (AVRegularity.edgeFluxAdjoint D H CE s ψ u) := fun u =>
    JMF.cov_polyP hH p (r := 0) (jmf_edgeFluxAdjoint u (fun r hr v d => P.CE_meas r hr v u d)
      (fun r hr v d t ht => P.CE_smooth r hr v u d t ht) (by omega) (Φ := fun v _ => ψ v)
      fun v => JMF.of_contDiff (hψ v))
  have hA5 : ∀ v, JMF t₀ t₁ 0 fun s => ((p.factorial : ℝ)⁻¹) •
      (AVRegularity.covOperator (Hc s))^[p] (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
        (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
          fderiv ℝ (fun y => ψ v y k') x (basisVec l)) :=
    fun v => jmf_taylorField hH P.J_meas B p (hψ v)
  -- the five pairings are measurable on the window
  have T1 : ∀ v, Measurable fun s : Set.Icc t₀ t₁ => cellInner
      (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
      (AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s
        (ψ v - AVRegularity.covPolyQ (Hc s) p (AVRegularity.covPolyP (Hc s) p (ψ v)))) :=
    fun v => (measurable_cellInner_familyValueSum hU hS1 v _ (hA1 v) :)
  have T2 : ∀ u, Measurable fun s : Set.Icc t₀ t₁ => cellInner
      (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
      (AVRegularity.covPolyP (Hc s) p (AVRegularity.edgeFluxAdjoint D H CE s
        (fun v => ψ v - AVRegularity.covPolyQ (Hc s) p (AVRegularity.covPolyP (Hc s) p (ψ v)))
        u)) :=
    fun u => (measurable_cellInner_familyValueSum hU hS2 u _ (hA2 u) :)
  have T3 : ∀ v, Measurable fun s : Set.Icc t₀ t₁ => cellInner
      (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
      (AVRegularity.coarseFluxAdjoint D b AD (Hc s) p s (ψ v)) :=
    fun v => (measurable_cellInner_familyValueSum hU hS3 v _ (hA3 v) :)
  have T4 : ∀ u, Measurable fun s : Set.Icc t₀ t₁ => cellInner
      (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
      (AVRegularity.covPolyP (Hc s) p (AVRegularity.edgeFluxAdjoint D H CE s ψ u)) :=
    fun u => (measurable_cellInner_familyValueSum hU hS4 u _ (hA4 u) :)
  have T5 : ∀ v, Measurable fun s : Set.Icc t₀ t₁ => cellInner
      (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
      (((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (Hc s))^[p]
        (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
          (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
            fderiv ℝ (fun y => ψ v y k') x (basisVec l))) :=
    fun v => (measurable_cellInner_familyValueSum hU hS5 v _ (hA5 v) :)
  -- the witness identity on the window
  have hsub : Measurable fun s : Set.Icc t₀ t₁ => ∑ v, cellInner
      (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) (ψ v) := by
    refine measurable_of_pointwise_eq ?_ fun s => hWit.2 s s.2 ψ hψ hp
    exact (((Finset.measurable_sum Finset.univ fun v _ => T1 v).sub
      (Finset.measurable_sum Finset.univ fun u _ => T2 u)).add
      ((Finset.measurable_sum Finset.univ fun v _ => T3 v).sub
        (Finset.measurable_sum Finset.univ fun u _ => T4 u))).add
      (Finset.measurable_sum Finset.univ fun v _ => T5 v)
  exact hsub.comp (continuous_projIcc (h := P.window)).measurable

/-- **(F1, one component) The pairing of one component of the retained flux with a smooth periodic
test is measurable in the clamped time.** -/
theorem coarseFc_pairing_single_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (v₀ : ι) (ψ₀ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v₀)) (hψ₀ : ContDiff ℝ (⊤ : ℕ∞) ψ₀)
    (hp₀ : AVenhance.IsZ2Periodic ψ₀) :
    Measurable fun s => cellInner (fun x =>
      (Fc v₀ (Set.projIcc t₀ t₁ P.window s)).toFunction.jet (valueIndex2 k) x) ψ₀ := by
  let Ψ : ∀ w, Vec 2 → PiLp 2 (fun _ : Fin 2 => h w) := Function.update (fun _ => 0) v₀ ψ₀
  have hΨs : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ψ w) := fun w => by
    by_cases hw : w = v₀
    · subst hw; simpa [Ψ] using hψ₀
    · simp only [Ψ, Function.update_of_ne hw]; exact contDiff_zero_fun
  have hΨp : ∀ w, AVenhance.IsZ2Periodic (Ψ w) := fun w => by
    by_cases hw : w = v₀
    · subst hw; simpa [Ψ] using hp₀
    · intro n x; simp [Ψ, Function.update_of_ne hw]
  have hz : ∀ w, w ≠ v₀ → Ψ w = 0 := fun w hw => by simp only [Ψ, Function.update_of_ne hw]
  have hΨv : Ψ v₀ = ψ₀ := by simp [Ψ]
  have e : ∀ s : ℝ, cellInner (fun x =>
      (Fc v₀ (Set.projIcc t₀ t₁ P.window s)).toFunction.jet (valueIndex2 k) x) ψ₀ =
      ∑ w, cellInner (fun x =>
        (Fc w (Set.projIcc t₀ t₁ P.window s)).toFunction.jet (valueIndex2 k) x) (Ψ w) := by
    intro s
    rw [Finset.sum_eq_single v₀ (fun w _ hw => by rw [hz w hw]; simp [cellInner])
      (fun hv => absurd (Finset.mem_univ v₀) hv), hΨv]
  exact measurable_of_pointwise_eq (coarseFc_pairing_measurable P hR hWit Ψ hΨs hΨp) e

/-- The Galerkin coefficient is the cell pairing with the mode. -/
theorem coarseModeCoeff_eq_cellInner {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i))
    (r : CoupledFourierModeIndex (h := h) n) :
    coarseModeCoeff n U r = cellInner (fun x => (U r.1).toFunction.jet (valueIndex2 K) x)
      (coupledModeJet n r r.1 0 Fin.elim0) :=
  rfl

/-- **(F2) The Galerkin coefficients of the retained flux are measurable in the clamped time**
(the hypothesis `hFm` of `approxFlux_tested_measurable`). -/
theorem coarseFc_modeCoeff_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (n : ℕ) (r : CoupledFourierModeIndex (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n) :
    Measurable fun s => coarseModeCoeff n (fun v => Fc v (Set.projIcc t₀ t₁ P.window s)) r :=
  measurable_of_pointwise_eq (coarseFc_pairing_single_measurable P hR hWit r.1
    (coupledModeJet n r r.1 0 Fin.elim0) (coupledModeJet_contDiff n r r.1 0 Fin.elim0)
    (coupledModeJet_periodic n r r.1 0 Fin.elim0)) fun _ => coarseModeCoeff_eq_cellInner n _ r

/-- **(F3) Each component of the retained flux is a.e. strongly measurable on the window.** -/
theorem coarseFc_aestronglyMeasurable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (v : ι) : AEStronglyMeasurable (Fc v) (volume.restrict (Set.Icc t₀ t₁)) := by
  refine aestronglyMeasurable_of_weak fun ψ₀ hψ₀ hp₀ => ?_
  refine (coarseFc_pairing_single_measurable P hR hWit v ψ₀ hψ₀ hp₀).aestronglyMeasurable.congr
    (ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_)
  exact congrArg (fun t : ℝ => cellInner (tval (Fc v t)) ψ₀)
    (congrArg Subtype.val (Set.projIcc_of_mem P.window hs))

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Torus norms of carriers from slice norms**. The
mass-weighted factorial norm `massNormSq` at radius `r_s` of the carriers of a smooth periodic flux
(resp. scalar) family is at most the sum over the derivative words of order `≤ K_max` of the
weighted slice norms `fluxInt π (r_s^j ∂^w F)` (resp. `scalInt`): the factorial weights are at most
`r_s^{2j}` (`massNormSq_periodicHk_flux_le`, `massNormSq_periodicHk_scal_le`). -/

section Cell

variable {E : Type*} [NormedAddCommGroup E]

/-- The square of the cell `L²` norm of a field in `L²` of the cell is the lower integral of the
squared norm. -/
theorem ofReal_cellL2_sq {g : Vec 2 → E} (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) :
    ENNReal.ofReal (cellL2 g ^ 2) = ∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ 2 := by
  have hne := hg.eLpNorm_ne_top
  have he : eLpNorm g 2 (volume.restrict AVenhance.unitCube) =
      (∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by simp)
      hg.aestronglyMeasurable]
    norm_num
  unfold cellL2
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne, he,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Cell

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The jets of the carrier of a smooth periodic field have the cell `L²` norms of its ordered
derivatives. -/
theorem norm_periodicHk_val (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 K) :
    ‖(periodicHk K f hf hp).val a‖ = cellL2 (orderedDerivative a.2 f) := by
  rw [Lp.norm_def]
  unfold cellL2
  rw [eLpNorm_congr_ae (periodicHk_jet_ae K f hf hp a)]

end Carrier

section Mass

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- One weighted jet of the carrier of a component family is at most the slice integrand. -/
theorem ofReal_weight_jet_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {K j : ℕ} (hj : j ≤ K) {rs : ℝ}
    (hrs : 0 ≤ rs) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (w : DerivativeWord2 j) :
    ENNReal.ofReal (factorialWeight rs j *
        ‖(periodicHk K f hf hp).val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩‖ ^ 2) ≤
      ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative w f x‖ₑ ^ 2 := by
  rw [norm_periodicHk_val]
  have hc : Continuous (orderedDerivative w f) :=
    continuous_orderedDerivative w (hf.of_le (by exact_mod_cast hj))
  have hmem : MemLp (orderedDerivative w f) 2 (volume.restrict AVenhance.unitCube) :=
    Coarse.memLp_two_cell_of_continuous hc
  have hw : factorialWeight rs j ≤ rs ^ (2 * j) := by
    unfold factorialWeight
    have h1 : (1 : ℝ) ≤ (j.factorial : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast j.factorial_pos)
    exact div_le_self (by positivity) h1
  calc ENNReal.ofReal (factorialWeight rs j * cellL2 (orderedDerivative w f) ^ 2)
      ≤ ENNReal.ofReal (rs ^ (2 * j) * cellL2 (orderedDerivative w f) ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw (sq_nonneg _))
    _ = ENNReal.ofReal (rs ^ (2 * j)) * ∫⁻ x in AVenhance.unitCube,
          ‖orderedDerivative w f x‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ofReal_cellL2_sq hmem]
    _ = ∫⁻ x in AVenhance.unitCube, ‖rs ^ j • orderedDerivative w f x‖ₑ ^ 2 := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal (by positivity),
          ← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm j 2]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The mass-weighted factorial norm of the carriers of a scalar family** is at most the sum of
the weighted scalar slice norms of the derivative words of order `≤ K_max`. -/
theorem massNormSq_periodicHk_scal_le (K : ι → ℕ) {Kmax : ℕ} (hK : ∀ v, K v ≤ Kmax) {rs : ℝ}
    (hrs : 0 ≤ rs) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (q : Vec 2 → ∀ i, h i)
    (hq : ContDiff ℝ (Kmax : ℕ∞) q)
    (hqv : ∀ v, ContDiff ℝ (K v : ℕ∞) (fun x => q x v))
    (hqvp : ∀ v, AVenhance.IsZ2Periodic (fun x => q x v)) :
    ENNReal.ofReal (massNormSq (E := h) (K := K) rs π
        (fun v => (periodicHk (K v) (fun x => q x v) (hqv v) (hqvp v)).val)) ≤
      ∑ j ∈ Finset.range (Kmax + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun x => rs ^ j • orderedDerivative w q x) := by
  -- the component of a word derivative is the word derivative of the component
  have hcomp : ∀ (j : ℕ) (hj : j ≤ Kmax) (w : DerivativeWord2 j) (v : ι) (x : Vec 2),
      (rs ^ j • orderedDerivative w q x) v = rs ^ j • orderedDerivative w (fun x' => q x' v) x := by
    intro j hj w v x
    have := orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) w
      (hq.of_le (by exact_mod_cast hj))
    rw [Pi.smul_apply]
    exact congrArg (rs ^ j • ·) (congrFun this x).symm
  have hterm : ∀ v, ENNReal.ofReal ((π v)⁻¹ * factorialNormSq rs
      (periodicHk (K v) (fun x => q x v) (hqv v) (hqvp v)).val) ≤
      ENNReal.ofReal (π v)⁻¹ * ∑ j ∈ Finset.range (Kmax + 1), ∑ w : DerivativeWord2 j,
        ∫⁻ x in AVenhance.unitCube, ‖(rs ^ j • orderedDerivative w q x) v‖ₑ ^ 2 := by
    intro v
    have hfac : 0 ≤ factorialNormSq rs (periodicHk (K v) (fun x => q x v) (hqv v) (hqvp v)).val :=
      Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
        (derivativeNormSq_nonneg _ _)
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
    gcongr
    unfold factorialNormSq derivativeNormSq
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc ∑ j : Fin (K v + 1), ENNReal.ofReal (factorialWeight rs j.val *
          ∑ w : DerivativeWord2 j.val,
            ‖(periodicHk (K v) (fun x => q x v) (hqv v) (hqvp v)).val ⟨j, w⟩‖ ^ 2)
        ≤ ∑ j : Fin (K v + 1), ∑ w : DerivativeWord2 j.val,
            ∫⁻ x in AVenhance.unitCube, ‖(rs ^ j.val • orderedDerivative w q x) v‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun w _ =>
            mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _)]
          refine Finset.sum_le_sum fun w _ => ?_
          have hj : j.val ≤ K v := Nat.lt_succ_iff.1 j.isLt
          refine (ofReal_weight_jet_le hj hrs (fun x => q x v) (hqv v) (hqvp v) w).trans
            (le_of_eq ?_)
          refine lintegral_congr fun x => ?_
          rw [hcomp j.val (hj.trans (hK v)) w v x]
      _ = ∑ j ∈ Finset.range (K v + 1), ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ‖(rs ^ j • orderedDerivative w q x) v‖ₑ ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun j => ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ‖(rs ^ j • orderedDerivative w q x) v‖ₑ ^ 2) (K v + 1)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ (hK v)))
  unfold massNormSq
  refine (ENNReal.ofReal_sum_of_nonneg ?_).trans_le ?_
  · exact fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
        (derivativeNormSq_nonneg _ _))
  refine (Finset.sum_le_sum fun v _ => hterm v).trans (le_of_eq ?_)
  simp only [scalInt, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- The squared norm of a pair in `PiLp 2` is the sum of the squared norms of its entries. -/
theorem enorm_toLp_sq {E : Type*} [NormedAddCommGroup E] (y : Fin 2 → E) :
    ‖(WithLp.toLp 2 y : PiLp 2 (fun _ : Fin 2 => E))‖ₑ ^ 2 = ∑ a₀ : Fin 2, ‖y a₀‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, PiLp.norm_sq_eq_of_L2,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun a₀ _ => (enorm_sq_eq_ofReal _).symm

/-- **The mass-weighted factorial norm of the carriers of a flux family** is at most the sum of the
weighted flux slice norms of the derivative words of order `≤ K_max`. -/
theorem massNormSq_periodicHk_flux_le (K : ι → ℕ) {Kmax : ℕ} (hK : ∀ v, K v ≤ Kmax) {rs : ℝ}
    (hrs : 0 ≤ rs) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (F : Vec 2 → Fin 2 → ∀ i, h i)
    (hF : ContDiff ℝ (Kmax : ℕ∞) F)
    (hfv : ∀ v, ContDiff ℝ (K v : ℕ∞)
      (fun x => (WithLp.toLp 2 (fun a₀ => F x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))))
    (hfvp : ∀ v, AVenhance.IsZ2Periodic
      (fun x => (WithLp.toLp 2 (fun a₀ => F x a₀ v) : PiLp 2 (fun _ : Fin 2 => h v)))) :
    ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) rs π
        (fun v => (periodicHk (K v) _ (hfv v) (hfvp v)).val)) ≤
      ∑ j ∈ Finset.range (Kmax + 1), ∑ w : DerivativeWord2 j,
        fluxInt π (fun x a₀ => rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) := by
  -- the word derivative of the carrier field is the pair of the word derivatives
  have hcomp : ∀ (j : ℕ) (hj : j ≤ Kmax) (w : DerivativeWord2 j) (v : ι) (x : Vec 2),
      ‖rs ^ j • orderedDerivative w
          (fun x' => (WithLp.toLp 2 (fun a₀ => F x' a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))) x‖ₑ ^ 2
        = ∑ a₀ : Fin 2, ‖(rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) v‖ₑ ^ 2 := by
    intro j hj w v x
    set L : (Fin 2 → ∀ i, h i) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h v)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun a₀ => (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) a₀)) with hL
    have hFj : ContDiff ℝ (j : ℕ∞) F := hF.of_le (by exact_mod_cast hj)
    have h1 : orderedDerivative w
        (fun x' => (WithLp.toLp 2 (fun a₀ => F x' a₀ v) : PiLp 2 (fun _ : Fin 2 => h v))) =
        fun x' => L (orderedDerivative w F x') := orderedDerivative_clm_comp L w hFj
    have h2 : ∀ a₀ : Fin 2, orderedDerivative w (fun x' => F x' a₀) x =
        orderedDerivative w F x a₀ := fun a₀ =>
      congrFun (orderedDerivative_clm_comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ∀ i, h i) a₀) w hFj) x
    rw [h1, ← map_smul]
    have h3 : L (rs ^ j • orderedDerivative w F x) =
        WithLp.toLp 2 (fun a₀ => (rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) v) := by
      rw [hL]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, h2]
      rfl
    rw [h3, enorm_toLp_sq]
  have hterm : ∀ v, ENNReal.ofReal ((π v)⁻¹ * factorialNormSq rs
      (periodicHk (K v) _ (hfv v) (hfvp v)).val) ≤
      ENNReal.ofReal (π v)⁻¹ * ∑ j ∈ Finset.range (Kmax + 1), ∑ w : DerivativeWord2 j,
        ∫⁻ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
          ‖(rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) v‖ₑ ^ 2 := by
    intro v
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
    gcongr
    unfold factorialNormSq derivativeNormSq
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc ∑ j : Fin (K v + 1), ENNReal.ofReal (factorialWeight rs j.val *
          ∑ w : DerivativeWord2 j.val, ‖(periodicHk (K v) _ (hfv v) (hfvp v)).val ⟨j, w⟩‖ ^ 2)
        ≤ ∑ j : Fin (K v + 1), ∑ w : DerivativeWord2 j.val,
            ∫⁻ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
              ‖(rs ^ j.val • orderedDerivative w (fun x' => F x' a₀) x) v‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun w _ =>
            mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _)]
          refine Finset.sum_le_sum fun w _ => ?_
          have hj : j.val ≤ K v := Nat.lt_succ_iff.1 j.isLt
          refine (ofReal_weight_jet_le hj hrs _ (hfv v) (hfvp v) w).trans (le_of_eq ?_)
          exact lintegral_congr fun x => hcomp j.val (hj.trans (hK v)) w v x
      _ = ∑ j ∈ Finset.range (K v + 1), ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
              ‖(rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) v‖ₑ ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun j => ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
              ‖(rs ^ j • orderedDerivative w (fun x' => F x' a₀) x) v‖ₑ ^ 2) (K v + 1)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ (hK v)))
  unfold massNormSq
  refine (ENNReal.ofReal_sum_of_nonneg ?_).trans_le ?_
  · exact fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg _ _)
        (derivativeNormSq_nonneg _ _))
  refine (Finset.sum_le_sum fun v _ => hterm v).trans (le_of_eq ?_)
  simp only [fluxInt, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end Mass

end AVRegularity.CycleComparison.Reconstruction
end

-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Defect.CovCommute
public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseDefectFlux
public import AVRegularity.Statements.Intermediate.CycleComparison.WordAdjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The pairing of the defect flux `(𝖩 - B I)∇W + F_A W + F_E W` with a smooth periodic flux test
field `ψ`, in adjoint form: `-(W, ∑_{kl} (𝖩 - B I)_{kl} ∂_l ψ_k) + (W, F_A^* ψ) + ∑_u (W_u, (F_E^* ψ)_u)`.
Each jet of `W` is moved onto the test field by periodic integration by parts. -/

section
section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem contDiff_piLp_component {n : WithTop ℕ∞} {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hψ : ContDiff ℝ n ψ) (k : Fin 2) : ContDiff ℝ n (fun x => ψ x k) :=
  (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => E) k).contDiff.comp hψ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] in
theorem periodic_piLp_component {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hp : AVenhance.IsZ2Periodic ψ) (k : Fin 2) : AVenhance.IsZ2Periodic (fun x => ψ x k) :=
  fun n x => by simp only [hp n x]

theorem torusJetOrder_of_le {K : ℕ} (W : TorusHk K E) {m : ℕ} (hm : m ≤ K)
    (α : DerivativeWord2 m) :
    torusJetOrder W m α = W.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le hm⟩, α⟩ := by
  funext x
  simp [torusJetOrder, hm]

theorem memLp_torusJetOrder {K : ℕ} (W : TorusHk K E) {m : ℕ} (hm : m ≤ K)
    (α : DerivativeWord2 m) :
    MemLp (torusJetOrder W m α) 2 (volume.restrict AVenhance.unitCube) := by
  rw [torusJetOrder_of_le W hm α]
  exact W.toFunction.hasPeriodicWeakJet.2.1 _

/-- Integration by parts for `torusJetOrder`. -/
theorem cellInner_torusJetOrder_eq [FiniteDimensional ℝ E] {K : ℕ} (W : TorusHk K E) {m : ℕ}
    (hm : m ≤ K) (α : DerivativeWord2 m) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ (m : WithTop ℕ∞) χ) (hp : AVenhance.IsZ2Periodic χ) :
    cellInner (torusJetOrder W m α) χ =
      (-1 : ℝ) ^ m * cellInner (tval W) (AVRegularity.orderedDerivativeRev α χ) := by
  rw [torusJetOrder_of_le W hm α]
  exact cellInner_jet_eq W hm α hχ hp

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem orderedDerivativeRev_one (l : Fin 2) (χ : Vec 2 → E) :
    AVRegularity.orderedDerivativeRev (fun _ : Fin 1 => l) χ =
      fun x => fderiv ℝ χ x (basisVec l) := by
  rw [orderedDerivativeRev_succ]
  rfl

/-- The constant-coefficient gradient part. -/
theorem cellInner_constGrad [FiniteDimensional ℝ E] {K : ℕ} (W : TorusHk K E) (hK : 1 ≤ K)
    (c : Matrix (Fin 2) (Fin 2) ℝ) {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hψ : ContDiff ℝ 1 ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (fun x => inner ℝ (WithLp.toLp 2 fun k =>
        ∑ l : Fin 2, c k l • torusJetOrder W 1 (fun _ => l) x : PiLp 2 (fun _ : Fin 2 => E))
        (ψ x)) (volume.restrict AVenhance.unitCube) ∧
    cellInner (fun x => (WithLp.toLp 2 fun k =>
        ∑ l : Fin 2, c k l • torusJetOrder W 1 (fun _ => l) x : PiLp 2 (fun _ : Fin 2 => E))) ψ =
      -cellInner (tval W) (fun x => ∑ k : Fin 2, ∑ l : Fin 2,
        c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)) := by
  have hψk : ∀ k, ContDiff ℝ 1 (fun x => ψ x k) := fun k => contDiff_piLp_component hψ k
  have hpk : ∀ k, AVenhance.IsZ2Periodic (fun x => ψ x k) := fun k => periodic_piLp_component hp k
  have hint : ∀ k l, Integrable (fun x => inner ℝ (torusJetOrder W 1 (fun _ => l) x)
      (c k l • ψ x k)) (volume.restrict AVenhance.unitCube) := fun k l =>
    integrable_inner_continuous (memLp_torusJetOrder W hK _)
      (continuous_const.smul (hψk k).continuous)
  have hpt : ∀ x, inner ℝ (WithLp.toLp 2 fun k =>
      ∑ l : Fin 2, c k l • torusJetOrder W 1 (fun _ => l) x : PiLp 2 (fun _ : Fin 2 => E))
      (ψ x) = ∑ k : Fin 2, ∑ l : Fin 2,
        inner ℝ (torusJetOrder W 1 (fun _ => l) x) (c k l • ψ x k) := by
    intro x
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [sum_inner, real_inner_smul_left, real_inner_smul_right]
  have hI : Integrable (fun x => ∑ k : Fin 2, ∑ l : Fin 2,
      inner ℝ (torusJetOrder W 1 (fun _ => l) x) (c k l • ψ x k))
      (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l
  refine ⟨hI.congr (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  have hd : ∀ k l, Continuous (fun x => fderiv ℝ (fun y => ψ y k) x (basisVec l)) := fun k l =>
    ((hψk k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  calc cellInner (fun x => (WithLp.toLp 2 fun k =>
        ∑ l : Fin 2, c k l • torusJetOrder W 1 (fun _ => l) x :
          PiLp 2 (fun _ : Fin 2 => E))) ψ
      = ∑ k : Fin 2, ∑ l : Fin 2, cellInner (torusJetOrder W 1 (fun _ => l))
          (fun x => c k l • ψ x k) := by
        unfold cellInner
        rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun k _ =>
          integrable_finsetSum _ fun l _ => hint k l]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hint k l
    _ = ∑ k : Fin 2, ∑ l : Fin 2, -(c k l * cellInner (tval W)
          (fun x => fderiv ℝ (fun y => ψ y k) x (basisVec l))) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [cellInner_smul_right, cellInner_torusJetOrder_eq W hK _ (by exact_mod_cast hψk k)
          (hpk k), orderedDerivativeRev_one]
        ring
    _ = -cellInner (tval W) (fun x => ∑ k : Fin 2, ∑ l : Fin 2,
          c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)) := by
        have hi : ∀ k l, Integrable (fun x => inner ℝ (tval W x)
            (c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)))
            (volume.restrict AVenhance.unitCube) := fun k l =>
          integrable_tval_inner W ((hd k l).const_smul _)
        unfold cellInner
        simp_rw [inner_sum]
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l,
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun l _ => hi k l, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp_rw [real_inner_smul_right]
        rw [integral_const_mul]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem continuous_orderedDerivativeRev {m : ℕ} (α : DerivativeWord2 m) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ (m : WithTop ℕ∞) χ) :
    Continuous (AVRegularity.orderedDerivativeRev α χ) :=
  (contDiff_orderedDerivativeRev_of (n := 0) α (by simpa using hχ)).continuous

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem contDiff_wordComponent {m : ℕ} {n : WithTop ℕ∞}
    {G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)} (hG : ContDiff ℝ n G)
    (α : DerivativeWord2 m) : ContDiff ℝ n (fun y => G y α) :=
  (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : DerivativeWord2 m => E) α).contDiff.comp hG

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem continuous_wordAdjoint {m : ℕ} {G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)}
    (hG : ContDiff ℝ (m : WithTop ℕ∞) G) : Continuous (AVRegularity.wordAdjoint m G) := by
  unfold AVRegularity.wordAdjoint
  exact continuous_const.smul (continuous_finsetSum _ fun α _ =>
    continuous_orderedDerivativeRev α (contDiff_wordComponent hG α))

/-- **The jets of order `m` tested against a word field.** -/
theorem integral_jets_word [FiniteDimensional ℝ E] {K m : ℕ} (W : TorusHk K E) (hm : m ≤ K)
    {G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)} (hG : ContDiff ℝ (m : WithTop ℕ∞) G)
    (hGp : AVenhance.IsZ2Periodic G) :
    Integrable (fun x => ∑ α : DerivativeWord2 m, inner ℝ (torusJetOrder W m α x) (G x α))
        (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube, ∑ α : DerivativeWord2 m, inner ℝ (torusJetOrder W m α x) (G x α)
        = cellInner (tval W) (AVRegularity.wordAdjoint m G) := by
  have hGα : ∀ α, ContDiff ℝ (m : WithTop ℕ∞) (fun y => G y α) := fun α =>
    contDiff_wordComponent hG α
  have hGαp : ∀ α, AVenhance.IsZ2Periodic (fun y => G y α) := fun α n x => by
    simp only [hGp n x]
  have hint : ∀ α, Integrable (fun x => inner ℝ (torusJetOrder W m α x) (G x α))
      (volume.restrict AVenhance.unitCube) := fun α =>
    integrable_inner_continuous (memLp_torusJetOrder W hm α) (hGα α).continuous
  refine ⟨integrable_finsetSum _ fun α _ => hint α, ?_⟩
  rw [integral_finsetSum _ fun α _ => hint α]
  unfold AVRegularity.wordAdjoint
  rw [cellInner_smul_right, gcellInner_finsetSum_right _ _ _ fun α _ =>
    integrable_tval_inner W (continuous_orderedDerivativeRev α (hGα α)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact cellInner_torusJetOrder_eq W hm α (hGα α) (hGαp α)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem contDiff_tensorField {m : ℕ} {n : WithTop ℕ∞}
    {A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    (hA : ContDiff ℝ n A) {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hψ : ContDiff ℝ n ψ) :
    ContDiff ℝ n (fun y => AVRegularity.tensorFluxAdjoint (A y) (ψ y)) := by
  have hc : ∀ (k : Fin 2) (α : DerivativeWord2 m),
      ContDiff ℝ n (fun y => A y (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) := fun k α =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) k).contDiff.comp
      (hA.clm_apply contDiff_const)
  have e : (fun y => AVRegularity.tensorFluxAdjoint (A y) (ψ y)) = fun y =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 m => E)).symm (fun α =>
        ∑ k : Fin 2, (A y (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) • ψ y k) := rfl
  rw [e]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 m => E)).symm.contDiff.comp
    (contDiff_pi.2 fun α => ContDiff.sum fun k _ => (hc k α).smul (contDiff_piLp_component hψ k))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem periodic_tensorField {m : ℕ}
    {A : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    (hA : AVenhance.IsZ2Periodic A) {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hψ : AVenhance.IsZ2Periodic ψ) :
    AVenhance.IsZ2Periodic (fun y => AVRegularity.tensorFluxAdjoint (A y) (ψ y)) := fun n x => by
  simp only [hA n x, hψ n x]

/-- **The diagonal part.** -/
theorem cellInner_diagPart [FiniteDimensional ℝ E] {K D : ℕ} (W : TorusHk K E)
    (hDK : D ≤ K + 1)
    (A : ∀ d : Finset.Icc 2 D, Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : ∀ d, ContDiff ℝ (D : WithTop ℕ∞) (A d)) (hAp : ∀ d, AVenhance.IsZ2Periodic (A d))
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hψ : ContDiff ℝ (D : WithTop ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (fun x => inner ℝ (WithLp.toLp 2 fun k => ∑ d : Finset.Icc 2 D,
        ∑ α : DerivativeWord2 (d.1 - 1), (A d x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
          torusJetOrder W (d.1 - 1) α x : PiLp 2 (fun _ : Fin 2 => E)) (ψ x))
        (volume.restrict AVenhance.unitCube) ∧
    cellInner (fun x => (WithLp.toLp 2 fun k => ∑ d : Finset.Icc 2 D,
        ∑ α : DerivativeWord2 (d.1 - 1), (A d x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
          torusJetOrder W (d.1 - 1) α x : PiLp 2 (fun _ : Fin 2 => E))) ψ =
      cellInner (tval W) (fun x => ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => AVRegularity.tensorFluxAdjoint (A d y) (ψ y)) x) := by
  have hdm : ∀ d : Finset.Icc 2 D, d.1 - 1 ≤ K := fun d => by
    have := (Finset.mem_Icc.mp d.2).2; omega
  have hG : ∀ d : Finset.Icc 2 D, ContDiff ℝ ((d.1 - 1 : ℕ) : WithTop ℕ∞)
      (fun y => AVRegularity.tensorFluxAdjoint (A d y) (ψ y)) := fun d =>
    (contDiff_tensorField (hA d) hψ).of_le (by
      have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega : d.1 - 1 ≤ D))
  have hGp : ∀ d : Finset.Icc 2 D, AVenhance.IsZ2Periodic
      (fun y => AVRegularity.tensorFluxAdjoint (A d y) (ψ y)) := fun d =>
    periodic_tensorField (hAp d) hp
  have hpt : ∀ x, inner ℝ (WithLp.toLp 2 fun k => ∑ d : Finset.Icc 2 D,
      ∑ α : DerivativeWord2 (d.1 - 1), (A d x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
        torusJetOrder W (d.1 - 1) α x : PiLp 2 (fun _ : Fin 2 => E)) (ψ x) =
      ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        inner ℝ (torusJetOrder W (d.1 - 1) α x)
          (AVRegularity.tensorFluxAdjoint (A d x) (ψ x) α) := by
    intro x
    simp only [PiLp.inner_apply, sum_inner, real_inner_smul_left, tensorFluxAdjoint_apply,
      tcoef, inner_sum, real_inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact Finset.sum_comm
  have hparts := fun d : Finset.Icc 2 D => integral_jets_word W (hdm d) (hG d) (hGp d)
  refine ⟨(integrable_finsetSum _ fun d _ => (hparts d).1).congr
    (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  unfold cellInner
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun d _ => (hparts d).1]
  have hR : ∫ x in AVenhance.unitCube, inner ℝ (tval W x) (∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => AVRegularity.tensorFluxAdjoint (A d y) (ψ y)) x) =
      ∑ d : Finset.Icc 2 D, cellInner (tval W) (AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => AVRegularity.tensorFluxAdjoint (A d y) (ψ y))) :=
    gcellInner_finsetSum_right _ _ _ fun d _ =>
      integrable_tval_inner W (continuous_wordAdjoint (hG d))
  rw [hR]
  exact Finset.sum_congr rfl fun d _ => (hparts d).2

end Single

section Multi

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The edge part.** -/
theorem cellInner_edgePart {K D H : ℕ} (W : ∀ u, TorusHk K (h u)) (hDK : D ≤ K + 1) (v : ι)
    (C : ℕ → ∀ (u : ι) (d : Finset.Icc 2 D), Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (hC : ∀ r ∈ Finset.Icc 1 H, ∀ u d, ContDiff ℝ (D : WithTop ℕ∞) (C r u d))
    (hCp : ∀ r ∈ Finset.Icc 1 H, ∀ u d, AVenhance.IsZ2Periodic (C r u d))
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (D : WithTop ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (fun x => inner ℝ (WithLp.toLp 2 fun k => ∑ r ∈ Finset.Icc 1 H, ∑ u : ι,
        ∑ d : Finset.Icc 2 D, (C r u d x (WithLp.toLp 2 fun α =>
          torusJetOrder (W u) (d.1 - 1) α x)) k : PiLp 2 (fun _ : Fin 2 => h v)) (ψ x))
        (volume.restrict AVenhance.unitCube) ∧
    cellInner (fun x => (WithLp.toLp 2 fun k => ∑ r ∈ Finset.Icc 1 H, ∑ u : ι,
        ∑ d : Finset.Icc 2 D, (C r u d x (WithLp.toLp 2 fun α =>
          torusJetOrder (W u) (d.1 - 1) α x)) k : PiLp 2 (fun _ : Fin 2 => h v))) ψ =
      ∑ u : ι, cellInner (tval (W u)) (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y)) x) := by
  have hdm : ∀ d : Finset.Icc 2 D, d.1 - 1 ≤ K := fun d => by
    have := (Finset.mem_Icc.mp d.2).2; omega
  have hG : ∀ r ∈ Finset.Icc 1 H, ∀ u (d : Finset.Icc 2 D),
      ContDiff ℝ ((d.1 - 1 : ℕ) : WithTop ℕ∞)
        (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y)) := fun r hr u d =>
    ((((adjointCLM _ _).contDiff.comp (hC r hr u d)).clm_apply hψ)).of_le (by
      have := (Finset.mem_Icc.mp d.2).2; exact_mod_cast (by omega : d.1 - 1 ≤ D))
  have hGp : ∀ r ∈ Finset.Icc 1 H, ∀ u (d : Finset.Icc 2 D), AVenhance.IsZ2Periodic
      (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y)) := fun r hr u d n x => by
    simp only [hCp r hr u d n x, hp n x]
  have hpt : ∀ x, inner ℝ (WithLp.toLp 2 fun k => ∑ r ∈ Finset.Icc 1 H, ∑ u : ι,
      ∑ d : Finset.Icc 2 D, (C r u d x (WithLp.toLp 2 fun α =>
        torusJetOrder (W u) (d.1 - 1) α x)) k : PiLp 2 (fun _ : Fin 2 => h v)) (ψ x) =
      ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        inner ℝ (torusJetOrder (W u) (d.1 - 1) α x)
          (ContinuousLinearMap.adjoint (C r u d x) (ψ x) α) := by
    intro x
    rw [PiLp.inner_apply]
    simp only [sum_inner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← PiLp.inner_apply, ← ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  have hparts : ∀ r ∈ Finset.Icc 1 H, ∀ u (d : Finset.Icc 2 D), _ := fun r hr u d =>
    integral_jets_word (W u) (hdm d) (hG r hr u d) (hGp r hr u d)
  have hint : Integrable (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
      ∑ α : DerivativeWord2 (d.1 - 1), inner ℝ (torusJetOrder (W u) (d.1 - 1) α x)
        (ContinuousLinearMap.adjoint (C r u d x) (ψ x) α)) (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun r hr => integrable_finsetSum _ fun u _ =>
      integrable_finsetSum _ fun d _ => (hparts r hr u d).1
  refine ⟨hint.congr (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  unfold cellInner
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun r hr =>
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun d _ => (hparts r hr u d).1]
  have hval : ∀ r ∈ Finset.Icc 1 H, ∀ u : ι,
      ∫ x in AVenhance.unitCube, ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        inner ℝ (torusJetOrder (W u) (d.1 - 1) α x)
          (ContinuousLinearMap.adjoint (C r u d x) (ψ x) α) =
      ∑ d : Finset.Icc 2 D, cellInner (tval (W u)) (AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y))) := fun r hr u => by
    rw [integral_finsetSum _ fun d _ => (hparts r hr u d).1]
    exact Finset.sum_congr rfl fun d _ => (hparts r hr u d).2
  have hcont : ∀ r ∈ Finset.Icc 1 H, ∀ u (d : Finset.Icc 2 D), Continuous
      (AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y))) := fun r hr u d =>
    continuous_wordAdjoint (hG r hr u d)
  calc ∑ r ∈ Finset.Icc 1 H, ∫ x in AVenhance.unitCube, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        ∑ α : DerivativeWord2 (d.1 - 1), inner ℝ (torusJetOrder (W u) (d.1 - 1) α x)
          (ContinuousLinearMap.adjoint (C r u d x) (ψ x) α)
      = ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
          cellInner (tval (W u)) (AVRegularity.wordAdjoint (d.1 - 1)
            (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y))) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun d _ =>
          (hparts r hr u d).1]
        exact Finset.sum_congr rfl fun u _ => hval r hr u
    _ = ∑ u : ι, ∫ x in AVenhance.unitCube, inner ℝ (tval (W u) x)
          (∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
            (fun y => ContinuousLinearMap.adjoint (C r u d y) (ψ y)) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp_rw [inner_sum]
        rw [integral_finsetSum _ fun r hr => integrable_finsetSum _ fun d _ =>
          integrable_tval_inner (W u) (hcont r hr u d)]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [integral_finsetSum _ fun d _ => integrable_tval_inner (W u) (hcont r hr u d)]
        rfl

/-- Splitting of a pairing whose left field is a sum of three components. -/
theorem cellInner_toLp_add3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : Vec 2 → Fin 2 → E) (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (ha : Integrable (fun x => inner ℝ (WithLp.toLp 2 (a x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x))
      (volume.restrict AVenhance.unitCube))
    (hb : Integrable (fun x => inner ℝ (WithLp.toLp 2 (b x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x))
      (volume.restrict AVenhance.unitCube))
    (hc : Integrable (fun x => inner ℝ (WithLp.toLp 2 (c x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x))
      (volume.restrict AVenhance.unitCube)) :
    Integrable (fun x => inner ℝ (WithLp.toLp 2 (fun k => a x k + b x k + c x k) :
        PiLp 2 (fun _ : Fin 2 => E)) (ψ x)) (volume.restrict AVenhance.unitCube) ∧
    cellInner (fun x => (WithLp.toLp 2 (fun k => a x k + b x k + c x k) :
        PiLp 2 (fun _ : Fin 2 => E))) ψ =
      cellInner (fun x => (WithLp.toLp 2 (a x) : PiLp 2 (fun _ : Fin 2 => E))) ψ +
        cellInner (fun x => (WithLp.toLp 2 (b x) : PiLp 2 (fun _ : Fin 2 => E))) ψ +
        cellInner (fun x => (WithLp.toLp 2 (c x) : PiLp 2 (fun _ : Fin 2 => E))) ψ := by
  have hpt : ∀ x, inner ℝ (WithLp.toLp 2 (fun k => a x k + b x k + c x k) :
      PiLp 2 (fun _ : Fin 2 => E)) (ψ x) =
      inner ℝ (WithLp.toLp 2 (a x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x) +
        inner ℝ (WithLp.toLp 2 (b x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x) +
        inner ℝ (WithLp.toLp 2 (c x) : PiLp 2 (fun _ : Fin 2 => E)) (ψ x) := by
    intro x
    simp only [PiLp.inner_apply, inner_add_left, Finset.sum_add_distrib]
  refine ⟨((ha.add hb).add hc).congr (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  unfold cellInner
  rw [integral_congr_ae (ae_of_all _ hpt)]
  have h1 := integral_add (ha.add hb) hc
  have h2 := integral_add ha hb
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2]

/-- **The pairing of the defect flux with a smooth periodic flux test field.** -/
theorem cellInner_coarseDefectFlux {K D H : ℕ} (B : ℝ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (W : ∀ v, ℝ → TorusHk K (h v)) (hDK : D ≤ K + 1)
    (hK : 1 ≤ K) (hD1 : 1 ≤ D) (v : ι) (s : ℝ)
    (hA : ∀ d, ContDiff ℝ (D : WithTop ℕ∞) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hC : ∀ r ∈ Finset.Icc 1 H, ∀ u d, ContDiff ℝ (D : WithTop ℕ∞) (CE r v u d s))
    (hCp : ∀ r ∈ Finset.Icc 1 H, ∀ u d, AVenhance.IsZ2Periodic (CE r v u d s))
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (D : WithTop ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (fun x => inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) (ψ x))
        (volume.restrict AVenhance.unitCube) ∧
    cellInner (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) ψ =
      -cellInner (tval (W v s)) (fun x => ∑ k : Fin 2, ∑ l : Fin 2,
          (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) •
            fderiv ℝ (fun y => ψ y k) x (basisVec l))
        + cellInner (tval (W v s)) (fun x => ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint
            (d.1 - 1) (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (ψ y)) x)
        + ∑ u : ι, cellInner (tval (W u s)) (fun x => ∑ r ∈ Finset.Icc 1 H,
            ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
              (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (ψ y)) x) := by
  obtain ⟨i1, e1⟩ := cellInner_constGrad (W v s) hK
    (fun k l => Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l)
    (hψ.of_le (by exact_mod_cast hD1)) hp
  obtain ⟨i2, e2⟩ := cellInner_diagPart (W v s) hDK (fun d => AD d s) hA hAp hψ hp
  obtain ⟨i3, e3⟩ := cellInner_edgePart (fun u => W u s) hDK v (fun r u d => CE r v u d s) hC
    hCp hψ hp
  obtain ⟨i, e⟩ := cellInner_toLp_add3 _ _ _ ψ i1 i2 i3
  exact ⟨i, e.trans (by rw [e1, e2, e3])⟩

end Multi
end

/-! Periodic integration by parts for the drift and diffusion terms of a weak identity: for a
divergence-free periodic drift `b`, `∫ ∑_k b_k ⟨∂_k U, χ⟩ = -(U, b·∇χ)`, and
`∫ ∑_k ⟨∂_k U, ∂_k χ⟩ = -(U, Δχ)`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem periodic_partial {χ : Vec 2 → E} (hp : AVenhance.IsZ2Periodic χ)
    (i : Fin 2) : AVenhance.IsZ2Periodic (fun x => fderiv ℝ χ x (basisVec i)) := by
  intro n x
  have hd : (fun y => χ (y + AVenhance.latticeShift n)) = χ := funext fun y => hp n y
  have := (fderiv_comp_add_right (𝕜 := ℝ) (f := χ) (AVenhance.latticeShift n) :
    fderiv ℝ (fun y => χ (y + AVenhance.latticeShift n)) x =
      fderiv ℝ χ (x + AVenhance.latticeShift n))
  rw [hd] at this
  change fderiv ℝ χ (x + AVenhance.latticeShift n) _ = fderiv ℝ χ x _
  rw [← this]

/-- **Integration by parts for the drift term.** -/
theorem integral_drift_jet {K : ℕ} (U : TorusHk K E) (hK : 1 ≤ K) {bt : Vec 2 → Vec 2}
    (hb : ContDiff ℝ 1 bt) (hbp : AVenhance.IsZ2Periodic bt)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ bt x (basisVec k) k = 0) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ 1 χ) (hp : AVenhance.IsZ2Periodic χ) :
    Integrable (fun x => ∑ k : Fin 2, bt x k * inner ℝ (torusJetOrder U 1 (fun _ => k) x) (χ x))
        (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube,
          ∑ k : Fin 2, bt x k * inner ℝ (torusJetOrder U 1 (fun _ => k) x) (χ x) =
        -cellInner (tval U) (fun x => ∑ k : Fin 2, bt x k • fderiv ℝ χ x (basisVec k)) := by
  have hbk : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => bt y k) := fun k =>
    (contDiff_apply ℝ ℝ k).comp hb
  have hg : ∀ k : Fin 2, ContDiff ℝ 1 (fun y => bt y k • χ y) := fun k => (hbk k).smul hχ
  have hgp : ∀ k : Fin 2, AVenhance.IsZ2Periodic (fun y => bt y k • χ y) := fun k n x => by
    simp only [hbp n x, hp n x]
  have hint : ∀ k : Fin 2, Integrable (fun x => inner ℝ (torusJetOrder U 1 (fun _ => k) x)
      (bt x k • χ x)) (volume.restrict AVenhance.unitCube) := fun k =>
    integrable_inner_continuous (memLp_torusJetOrder U hK _) (hg k).continuous
  have hpt : ∀ x, ∑ k : Fin 2, bt x k * inner ℝ (torusJetOrder U 1 (fun _ => k) x) (χ x) =
      ∑ k : Fin 2, inner ℝ (torusJetOrder U 1 (fun _ => k) x) (bt x k • χ x) := fun x =>
    Finset.sum_congr rfl fun k _ => by rw [real_inner_smul_right]
  have hI := integrable_finsetSum (Finset.univ : Finset (Fin 2)) fun k _ => hint k
  refine ⟨hI.congr (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun k _ => hint k]
  have hstep : ∀ k : Fin 2, ∫ x in AVenhance.unitCube,
      inner ℝ (torusJetOrder U 1 (fun _ => k) x) (bt x k • χ x) =
      -cellInner (tval U) (fun x => fderiv ℝ (fun y => bt y k • χ y) x (basisVec k)) := by
    intro k
    have := cellInner_torusJetOrder_eq U hK (fun _ => k) (by exact_mod_cast hg k) (hgp k)
    rw [orderedDerivativeRev_one] at this
    unfold cellInner at this ⊢
    rw [this]
    ring
  simp_rw [hstep]
  have hderiv : ∀ k x, fderiv ℝ (fun y => bt y k • χ y) x (basisVec k) =
      fderiv ℝ bt x (basisVec k) k • χ x + bt x k • fderiv ℝ χ x (basisVec k) := by
    intro k x
    have h1 : DifferentiableAt ℝ (fun y => bt y k) x :=
      (hbk k).differentiable one_ne_zero x
    have h2 : DifferentiableAt ℝ χ x := hχ.differentiable one_ne_zero x
    rw [fderiv_fun_smul h1 h2]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    have h3 : fderiv ℝ (fun y => bt y k) x (basisVec k) = fderiv ℝ bt x (basisVec k) k := by
      have hc := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).hasFDerivAt.comp
        x (hb.differentiable one_ne_zero x).hasFDerivAt).fderiv
      change fderiv ℝ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k) ∘ bt) x
        (basisVec k) = _
      rw [hc]
      rfl
    rw [h3, add_comm]
  have hcont : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ (fun y => bt y k • χ y) x (basisVec k)) :=
    fun k => ((hg k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [Finset.sum_neg_distrib, ← gcellInner_finsetSum_right _ _ _ fun k _ =>
    integrable_tval_inner U (hcont k)]
  congr 2
  funext x
  simp only [hderiv, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hdiv x, zero_smul, zero_add]

/-- **Integration by parts for the diffusion term.** -/
theorem integral_diffusion_jet {K : ℕ} (U : TorusHk K E) (hK : 1 ≤ K) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ 2 χ) (hp : AVenhance.IsZ2Periodic χ) :
    Integrable (fun x => ∑ k : Fin 2, inner ℝ (torusJetOrder U 1 (fun _ => k) x)
        (fderiv ℝ χ x (basisVec k))) (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube, ∑ k : Fin 2, inner ℝ (torusJetOrder U 1 (fun _ => k) x)
          (fderiv ℝ χ x (basisVec k)) =
        -cellInner (tval U) (fun x => ∑ k : Fin 2,
          fderiv ℝ (fun y => fderiv ℝ χ y (basisVec k)) x (basisVec k)) := by
  have hd : ∀ k : Fin 2, ContDiff ℝ 1 (fun x => fderiv ℝ χ x (basisVec k)) := fun k =>
    (hχ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdp : ∀ k : Fin 2, AVenhance.IsZ2Periodic (fun x => fderiv ℝ χ x (basisVec k)) := fun k =>
    periodic_partial hp k
  have hint : ∀ k : Fin 2, Integrable (fun x => inner ℝ (torusJetOrder U 1 (fun _ => k) x)
      (fderiv ℝ χ x (basisVec k))) (volume.restrict AVenhance.unitCube) := fun k =>
    integrable_inner_continuous (memLp_torusJetOrder U hK _) (hd k).continuous
  refine ⟨integrable_finsetSum _ fun k _ => hint k, ?_⟩
  rw [integral_finsetSum _ fun k _ => hint k]
  have hcont : ∀ k : Fin 2, Continuous
      (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (basisVec k)) x (basisVec k)) := fun k =>
    ((hd k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [gcellInner_finsetSum_right _ _ _ fun k _ => integrable_tval_inner U (hcont k),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := cellInner_torusJetOrder_eq U hK (fun _ => k) (by exact_mod_cast hd k) (hdp k)
  rw [orderedDerivativeRev_one] at this
  unfold cellInner at this ⊢
  rw [this]
  ring
end

/-! Uniform `L²` bounds for pairings: Cauchy–Schwarz for `L²` fields, the `L²` norm of the jets of
a periodic Sobolev field in terms of its norm, and the pairing bound with a bounded weight. -/

section
section Pairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure (Vec 2)} {X Y : Vec 2 → E}

theorem integrable_inner_memLp (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun x => inner ℝ (X x) (Y x)) μ :=
  (L2.integrable_inner (hX.toLp X) (hY.toLp Y)).congr (by
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with x hx hy
    rw [hx, hy])

theorem abs_integral_inner_le (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ x, inner ℝ (X x) (Y x) ∂μ| ≤ (eLpNorm X 2 μ).toReal * (eLpNorm Y 2 μ).toReal := by
  have h := abs_real_inner_le_norm (hX.toLp X) (hY.toLp Y)
  rw [MeasureTheory.L2.inner_def] at h
  have h1 : ∫ a, inner ℝ ((hX.toLp X : Lp E 2 μ) a) ((hY.toLp Y : Lp E 2 μ) a) ∂μ
      = ∫ x, inner ℝ (X x) (Y x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [h1] at h
  simpa [Lp.norm_toLp] using h

theorem abs_integral_mul_inner_le {c : Vec 2 → ℝ} {C : ℝ} (hc : AEStronglyMeasurable c μ)
    (hC : ∀ x, |c x| ≤ C) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ x, c x * inner ℝ (X x) (Y x) ∂μ| ≤
      C * ((eLpNorm X 2 μ).toReal * (eLpNorm Y 2 μ).toReal) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hbd : ∀ᵐ x ∂μ, ‖(c x • X x)‖ ≤ C * ‖X x‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have hcX : MemLp (fun x => c x • X x) 2 μ :=
    hX.of_le_mul (hc.smul hX.aestronglyMeasurable) hbd
  have hn : (eLpNorm (fun x => c x • X x) 2 μ).toReal ≤ C * (eLpNorm X 2 μ).toReal := by
    have := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := X) (c := C) (hc.smul hX.aestronglyMeasurable) hbd 2
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX.eLpNorm_lt_top.ne) this
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0] at h2
  have h := abs_integral_inner_le hcX hY
  have e : (fun x => c x * inner ℝ (X x) (Y x)) = fun x => inner ℝ (c x • X x) (Y x) := by
    funext x; rw [real_inner_smul_left]
  rw [e]
  calc _ ≤ _ := h
    _ ≤ (C * (eLpNorm X 2 μ).toReal) * (eLpNorm Y 2 μ).toReal :=
        mul_le_mul_of_nonneg_right hn ENNReal.toReal_nonneg
    _ = _ := by ring

end Pairing

theorem piLp_norm_le_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] (x : PiLp 2 fun _ : ι => E) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  refine (abs_le_of_sq_le_sq' ?_ (Finset.sum_nonneg fun i _ => norm_nonneg _)).2
  calc ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ x
    _ ≤ (∑ i, ‖x i‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem memLp_jet (U : TorusHk K E) (a : JetIndex2 K) :
    MemLp (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube) :=
  U.toFunction.hasPeriodicWeakJet.2.1 a

theorem eLpNorm_jet_le (U : TorusHk K E) (a : JetIndex2 K) :
    (eLpNorm (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ ‖U‖ := by
  have h1 : eLpNorm (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube) =
      eLpNorm (U.val a) 2 (volume.restrict AVenhance.unitCube) :=
    eLpNorm_congr_ae (periodicJetRepresentative_ae U.val a)
  rw [h1, ← Lp.norm_def]
  exact (PiLp.norm_apply_le U.val a).trans (le_of_eq rfl)

theorem eLpNorm_torusJetOrder_le (U : TorusHk K E) {m : ℕ} (hm : m ≤ K)
    (w : DerivativeWord2 m) :
    (eLpNorm (AVRegularity.torusJetOrder U m w) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ ‖U‖ := by
  rw [torusJetOrder_of_le U hm w]
  exact eLpNorm_jet_le U _

end Jets
end

/-! An `L²` bound on the coarse defect flux on the unit cell, linear in the sup of the `H^K`
norms of the fields `W v s`: each jet is `L²` with norm `≤ ‖W‖`, and the flux is
pointwise dominated by a finite sum of coefficient bounds times norms of jets. -/

section
/-- A nonnegative function in `L²` of the unit cell with `L²` norm at most `a`. -/
def CellL2Bd (G : Vec 2 → ℝ) (a : ℝ) : Prop :=
  MemLp G 2 (volume.restrict AVenhance.unitCube) ∧
    (eLpNorm G 2 (volume.restrict AVenhance.unitCube)).toReal ≤ a

theorem CellL2Bd.zero : CellL2Bd (fun _ => 0) 0 := by
  refine ⟨MemLp.zero, ?_⟩
  simp

theorem CellL2Bd.add {G₁ G₂ : Vec 2 → ℝ} {a₁ a₂ : ℝ} (h₁ : CellL2Bd G₁ a₁)
    (h₂ : CellL2Bd G₂ a₂) : CellL2Bd (fun x => G₁ x + G₂ x) (a₁ + a₂) := by
  refine ⟨h₁.1.add h₂.1, ?_⟩
  have h := eLpNorm_add_le (p := 2) (f := G₁) (g := G₂)
    (μ := volume.restrict AVenhance.unitCube) (by norm_num)
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨h₁.1.eLpNorm_lt_top.ne, h₂.1.eLpNorm_lt_top.ne⟩) h
  rw [ENNReal.toReal_add h₁.1.eLpNorm_lt_top.ne h₂.1.eLpNorm_lt_top.ne] at h3
  exact h3.trans (add_le_add h₁.2 h₂.2)

theorem CellL2Bd.sum {γ : Type*} (S : Finset γ) {G : γ → Vec 2 → ℝ} {a : γ → ℝ}
    (h : ∀ i ∈ S, CellL2Bd (G i) (a i)) :
    CellL2Bd (fun x => ∑ i ∈ S, G i x) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CellL2Bd.zero
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CellL2Bd.const_mul {G : Vec 2 → ℝ} {a c : ℝ} (hc : 0 ≤ c) (h : CellL2Bd G a) :
    CellL2Bd (fun x => c * G x) (c * a) := by
  have hbd : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ‖c * G x‖ ≤ c * ‖G x‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg hc]
  have hm : AEStronglyMeasurable (fun x => c * G x) (volume.restrict AVenhance.unitCube) :=
    h.1.aestronglyMeasurable.const_mul c
  refine ⟨h.1.of_le_mul hm hbd, ?_⟩
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hbd 2
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    h.1.eLpNorm_lt_top.ne) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h.2 hc)

theorem CellL2Bd.mono {G : Vec 2 → ℝ} {a b : ℝ} (h : CellL2Bd G a) (hab : a ≤ b) :
    CellL2Bd G b := ⟨h.1, h.2.trans hab⟩

theorem CellL2Bd.dom {E : Type*} [NormedAddCommGroup E] {F : Vec 2 → E} {G : Vec 2 → ℝ}
    {a : ℝ} (hF : AEStronglyMeasurable F (volume.restrict AVenhance.unitCube))
    (hFG : ∀ x, ‖F x‖ ≤ G x) (hG : CellL2Bd G a) :
    MemLp F 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm F 2 (volume.restrict AVenhance.unitCube)).toReal ≤ a := by
  have hle : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ‖F x‖ ≤ ‖G x‖ :=
    Filter.Eventually.of_forall fun x => (hFG x).trans (le_abs_self _ |>.trans_eq
      (Real.norm_eq_abs _).symm)
  refine ⟨hG.1.of_le hF hle, ?_⟩
  exact (ENNReal.toReal_mono hG.1.eLpNorm_lt_top.ne (eLpNorm_mono_ae hF hle)).trans hG.2

theorem cellL2Bd_norm_torusJetOrder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (U : TorusHk K E) {m : ℕ}
    (hm : m ≤ K) (w : DerivativeWord2 m) {M : ℝ} (hU : ‖U‖ ≤ M) :
    CellL2Bd (fun x => ‖AVRegularity.torusJetOrder U m w x‖) M := by
  refine ⟨(memLp_torusJetOrder U hm w).norm, ?_⟩
  rw [eLpNorm_norm _ (memLp_torusJetOrder U hm w).aestronglyMeasurable]
  exact (eLpNorm_torusJetOrder_le U hm w).trans hU

/-- The explicit constant in the `L²` bound of the coarse defect flux. -/
def dfConst (D H N : ℕ) (CA CC CJ : ℝ) : ℝ :=
  4 * CJ + 2 * (∑ d ∈ Finset.Icc 2 D, (2 : ℝ) ^ (d - 1)) * CA +
    2 * (H : ℝ) * N * (∑ d ∈ Finset.Icc 2 D, (2 : ℝ) ^ (d - 1)) * CC

theorem aestronglyMeasurable_toLp_pi {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure (Vec 2)} {f : Vec 2 → ι → E}
    (h : ∀ k, AEStronglyMeasurable (fun x => f x k) μ) :
    AEStronglyMeasurable (fun x => (WithLp.toLp 2 (f x) : PiLp 2 fun _ : ι => E)) μ := by
  classical
  have h1 : AEStronglyMeasurable (fun x => ∑ k, (Pi.single k (f x k) : ι → E)) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ =>
      (continuous_single k).comp_aestronglyMeasurable (h k)
  have h2 : (fun x => ∑ k, (Pi.single k (f x k) : ι → E)) = f := by
    funext x; exact Finset.univ_sum_single (f x)
  rw [h2] at h1
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.continuous.comp_aestronglyMeasurable h1

section Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem norm_sum_smul_le {β : Type*} [Fintype β] {C : ℝ} (a : β → ℝ) (ha : ∀ l, |a l| ≤ C)
    (j : β → E) : ‖∑ l, a l • j l‖ ≤ ∑ l, C * ‖j l‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (ha l) (norm_nonneg _))

theorem norm_clm_apply_le {β : Type*} [Fintype β]
    (T : PiLp 2 (fun _ : β => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => F)) {C : ℝ} (hT : ‖T‖ ≤ C)
    (j : β → E) (k : Fin 2) : ‖T (WithLp.toLp 2 j) k‖ ≤ C * ∑ α, ‖j α‖ := by
  calc ‖T (WithLp.toLp 2 j) k‖ ≤ ‖T (WithLp.toLp 2 j)‖ := PiLp.norm_apply_le _ k
    _ ≤ ‖T‖ * ‖(WithLp.toLp 2 j : PiLp 2 (fun _ : β => E))‖ := T.le_opNorm _
    _ ≤ C * ∑ α, ‖j α‖ := by
        refine mul_le_mul hT ?_ (norm_nonneg _) ((norm_nonneg T).trans hT)
        exact piLp_norm_le_sum (WithLp.toLp 2 j)

end Pointwise

theorem card_word2 (m : ℕ) : Fintype.card (DerivativeWord2 m) = 2 ^ m := by
  simp [DerivativeWord2]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

theorem coarseDefectFlux_memLp_bound {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) {D H : ℕ}
    (hD : D ≤ K + 1) (hK : 1 ≤ K) (B : ℝ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ι) (s : ℝ) {CA CC CJ MW : ℝ}
    (hAD : ∀ d x, ‖AD d s x‖ ≤ CA)
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ u d x, ‖CE r v u d s x‖ ≤ CC)
    (hJ : ∀ k l, |Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l| ≤ CJ)
    (hW : ∀ w, ‖W w s‖ ≤ MW)
    (hAc : ∀ d, Continuous (AD d s))
    (hCc : ∀ r ∈ Finset.Icc 1 H, ∀ u d, Continuous (CE r v u d s)) :
    MemLp (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) 2
        (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) 2
        (volume.restrict AVenhance.unitCube)).toReal ≤
        dfConst D H (Fintype.card ι) CA CC CJ * MW := by
  have hKD : ∀ d : Finset.Icc 2 D, d.1 - 1 ≤ K := fun d => by
    have := (Finset.mem_Icc.1 d.2).2
    omega
  have hCJ : 0 ≤ CJ := (abs_nonneg _).trans (hJ 0 0)
  have hn : ∀ (u : ι) (m : ℕ) (hm : m ≤ K) (w : DerivativeWord2 m),
      CellL2Bd (fun x => ‖AVRegularity.torusJetOrder (W u s) m w x‖) MW :=
    fun u m hm w => cellL2Bd_norm_torusJetOrder (W u s) hm w (hW u)
  -- the majorant
  have hG1 : CellL2Bd (fun x => ∑ _k : Fin 2, ∑ l : Fin 2,
      CJ * ‖AVRegularity.torusJetOrder (W v s) 1 (fun _ => l) x‖)
      (∑ _k : Fin 2, ∑ _l : Fin 2, CJ * MW) :=
    CellL2Bd.sum _ fun _ _ => CellL2Bd.sum _ fun l _ => (hn v 1 hK _).const_mul hCJ
  have hG2 : CellL2Bd (fun x => ∑ _k : Fin 2, ∑ d : Finset.Icc 2 D,
      ∑ α : DerivativeWord2 (d.1 - 1),
        CA * ‖AVRegularity.torusJetOrder (W v s) (d.1 - 1) α x‖)
      (∑ _k : Fin 2, ∑ d : Finset.Icc 2 D, ∑ _α : DerivativeWord2 (d.1 - 1), CA * MW) :=
    CellL2Bd.sum _ fun _ _ => CellL2Bd.sum _ fun d _ => CellL2Bd.sum _ fun α _ =>
      (hn v _ (hKD d) α).const_mul ((norm_nonneg (AD d s 0)).trans (hAD d 0))
  have hG3 : CellL2Bd (fun x => ∑ _k : Fin 2, ∑ r ∈ Finset.Icc 1 H, ∑ u : ι,
      ∑ d : Finset.Icc 2 D, CC * ∑ α : DerivativeWord2 (d.1 - 1),
        ‖AVRegularity.torusJetOrder (W u s) (d.1 - 1) α x‖)
      (∑ _k : Fin 2, ∑ r ∈ Finset.Icc 1 H, ∑ _u : ι, ∑ d : Finset.Icc 2 D,
        CC * ∑ _α : DerivativeWord2 (d.1 - 1), MW) :=
    CellL2Bd.sum _ fun _ _ => CellL2Bd.sum _ fun r hr => CellL2Bd.sum _ fun u _ =>
      CellL2Bd.sum _ fun d _ => (CellL2Bd.sum _ fun α _ => hn u _ (hKD d) α).const_mul
        ((norm_nonneg (CE r v u d s 0)).trans (hCE r hr u d 0))
  have hmeas : AEStronglyMeasurable
      (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x)
      (volume.restrict AVenhance.unitCube) := by
    refine aestronglyMeasurable_toLp_pi fun k => ?_
    refine ((Finset.aestronglyMeasurable_fun_sum _ fun l _ => ?_).add
      (Finset.aestronglyMeasurable_fun_sum _ fun d _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_)).add
      (Finset.aestronglyMeasurable_fun_sum _ fun r hr =>
        Finset.aestronglyMeasurable_fun_sum _ fun u _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun d _ => ?_)
    · exact aestronglyMeasurable_const.smul (memLp_torusJetOrder _ hK _).aestronglyMeasurable
    · exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) k).continuous.comp
        ((hAc d).clm_apply continuous_const)).aestronglyMeasurable).smul
        (memLp_torusJetOrder _ (hKD d) _).aestronglyMeasurable
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h v) k).continuous.comp_aestronglyMeasurable
        ((ContinuousLinearMap.apply ℝ (PiLp 2 (fun _ : Fin 2 => h v))
          (E := PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))).aestronglyMeasurable_comp₂
          (aestronglyMeasurable_toLp_pi fun α =>
            (memLp_torusJetOrder _ (hKD d) α).aestronglyMeasurable)
          (hCc r hr u d).aestronglyMeasurable)
  have hpt : ∀ x, ‖AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x‖ ≤
      ((fun x => ∑ _k : Fin 2, ∑ l : Fin 2,
        CJ * ‖AVRegularity.torusJetOrder (W v s) 1 (fun _ => l) x‖) x +
      (fun x => ∑ _k : Fin 2, ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        CA * ‖AVRegularity.torusJetOrder (W v s) (d.1 - 1) α x‖) x) +
      (fun x => ∑ _k : Fin 2, ∑ r ∈ Finset.Icc 1 H, ∑ u : ι,
      ∑ d : Finset.Icc 2 D, CC * ∑ α : DerivativeWord2 (d.1 - 1),
        ‖AVRegularity.torusJetOrder (W u s) (d.1 - 1) α x‖) x := by
    intro x
    refine (piLp_norm_le_sum _).trans ?_
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · exact norm_sum_smul_le (fun l => Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l)
        (fun l => hJ k l) _
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
      exact norm_sum_smul_le (fun α => tcoef (AD d s x) k α)
        (fun α => (abs_tcoef_le (AD d s x) k α).trans (hAD d x)) _
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
      exact norm_clm_apply_le (CE r v u d s x) (hCE r hr u d x)
        (fun α => AVRegularity.torusJetOrder (W u s) (d.1 - 1) α x) k
  have hdom := CellL2Bd.dom hmeas hpt ((hG1.add hG2).add hG3)
  refine ⟨hdom.1, hdom.2.trans (le_of_eq ?_)⟩
  have hS : ∑ d : Finset.Icc 2 D, (2 : ℝ) ^ (d.1 - 1) =
      ∑ d ∈ Finset.Icc 2 D, (2 : ℝ) ^ (d - 1) :=
    Finset.sum_coe_sort _ (fun d => (2 : ℝ) ^ (d - 1))
  have h2 : ∑ d : Finset.Icc 2 D, ∑ _α : DerivativeWord2 (d.1 - 1), CA * MW =
      (∑ d ∈ Finset.Icc 2 D, (2 : ℝ) ^ (d - 1)) * (CA * MW) := by
    simp only [Finset.sum_const, Finset.card_univ, card_word2, nsmul_eq_mul]
    rw [← hS, Finset.sum_mul]
    simp
  have h3 : ∑ d : Finset.Icc 2 D, CC * ∑ _α : DerivativeWord2 (d.1 - 1), MW =
      (∑ d ∈ Finset.Icc 2 D, (2 : ℝ) ^ (d - 1)) * (CC * MW) := by
    simp only [Finset.sum_const, Finset.card_univ, card_word2, nsmul_eq_mul]
    rw [← hS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  rw [h2, h3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.card_Icc]
  unfold dfConst
  push_cast
  ring
end

end AVRegularity.CycleComparison.Coarse
end

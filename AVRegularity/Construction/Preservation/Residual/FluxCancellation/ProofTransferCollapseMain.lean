-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.ComplexContext.ExtFam
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseSum
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.CycleComparison.Reconstruction.Tested

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **Source mean, Left: a pushed-forward label operator of finite order, on a smooth field**.

`sml_push_expansion`: if the label operator `L` is at the label `Ψ⁻¹ x` the differential operator of
its coefficients of the orders `1 ≤ d ≤ K` on smooth fields, then `Ψ_* L` applied to a smooth field
`φ` at `x` is the contraction of the jets of `φ` at `x` with the transported arrays of
`transportedCoeff` (the finite-order Piola identity
`transportedCoeff_flux_orders_of_contDiff` on `V = φ ∘ Ψ`). -/

section
open Providers.QuietAtlas Providers.GenSem CycleComparison.Reconstruction

/-- **The finite-order form of a pushed-forward label operator** on a smooth field. -/
theorem sml_push_expansion {Ψ Ψi : Vec 2 → Vec 2} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨi : ContDiff ℝ (⊤ : ℕ∞) Ψi) (h1 : ∀ y, Ψi (Ψ y) = y) (h2 : ∀ x, Ψ (Ψi x) = x)
    (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (K : ℕ) (x : Vec 2)
    (hfo : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L g (Ψi x) = ∑ d ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d - 1),
        orderedDerivative J g (Ψi x) • fluxCoeff L d J (Ψi x))
    {φ : Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a₀ : Fin 2) :
    pushFlux Ψ Ψi L φ x a₀ =
      ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian Ψi) K (fun d' J => fluxCoeff L d' J (Ψi x))
          (d - 1) A x a₀ * orderedDerivative A φ x := by
  have hVs : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ Ψ) := hφ.comp hΨ
  have hVψ : (φ ∘ Ψ) ∘ Ψi = φ := by
    funext x'
    simp only [Function.comp_apply, h2]
  have hp2 := transportedCoeff_flux_orders_of_contDiff hΨ hΨi h1 h2 (n := K)
    (V := φ ∘ Ψ) (hVs.of_le (by exact_mod_cast le_top)) K (Nat.le_succ K)
    (fun d' J => fluxCoeff L d' J (Ψi x)) x a₀
  rw [hVψ] at hp2
  have hR2 : (∑ d' ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d' - 1), ∑ i₀ : Fin 2,
      (chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀) •
        orderedDerivative J (φ ∘ Ψ) (Ψi x)) =
      ∑ i₀ : Fin 2, chartInvJacobian Ψi x a₀ i₀ * L (φ ∘ Ψ) (Ψi x) i₀ := by
    rw [hfo _ hVs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : ∀ d' : ℕ, (∑ J : DerivativeWord2 (d' - 1), ∑ i₀ : Fin 2,
        chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀ *
          orderedDerivative J (φ ∘ Ψ) (Ψi x)) =
        ∑ i₀ : Fin 2, ∑ J : DerivativeWord2 (d' - 1),
          chartInvJacobian Ψi x a₀ i₀ * fluxCoeff L d' J (Ψi x) i₀ *
            orderedDerivative J (φ ∘ Ψ) (Ψi x) := fun d' => Finset.sum_comm
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun d' _ =>
      Finset.sum_congr rfl fun J _ => ?_
    ring
  have hjac : chartInvJacobian Ψi x = jacMatrix Ψ (Ψi x) := by
    rw [chartInvJacobian_eq_of_inverse (hΨ.differentiable (by simp))
      (hΨi.differentiable (by simp)) h1 h2 x]
    rfl
  have hp3 := hp2.trans hR2
  simp only [smul_eq_mul] at hp3
  rw [hp3]
  unfold pushFlux
  rw [← hjac]
  simp [Matrix.mulVec, dotProduct]
end

/-! **The source-mean step, Left: the glue of label operators of finite order, on a smooth field**.

`sml_glued_expansion`: for label operators `L k` of the active finer slots which at the finer
labels of the point are, on smooth fields, the differential operators of their coefficients of the
orders `2 ≤ d ≤ K`, the glue `gluedFluxOp D (m+1) L t` applied to a smooth field at `x` is the
differential operator of its own symmetric coefficients (`fluxCoeff`) of the orders `2 ≤ d ≤ Dm`,
`K ≤ Dm`. The proof pushes every slot forward by `sml_push_expansion`, sums over the slots with
the cutoffs (`tc_sum_obsPulses_eq_activeSlots`), and reads the transported arrays through the
symmetric coefficients of the glue (`tc_fluxCoeff_glued`, `tc_word_sum`); the zeroth-order terms
vanish because the label operators annihilate constants. -/

section
open Providers.QuietAtlas Providers.GenSem CycleComparison.Reconstruction

/-- The zeroth-order coefficient of an operator of finite order from `2` on vanishes. -/
theorem sml_coeff_one (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (y : Vec 2) (K : ℕ)
    (hfo : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L g y = ∑ d ∈ Finset.Icc 2 K, ∑ J : DerivativeWord2 (d - 1),
        orderedDerivative J g y • fluxCoeff L d J y) :
    L (fun _ => 1) y = 0 := by
  rw [hfo _ contDiff_const]
  refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun J _ => ?_
  have hd2 := (Finset.mem_Icc.mp hd).1
  rw [AVRegularity.CycleComparison.Lift.orderedDerivative_const J (1 : ℝ) (by omega)]
  simp

/-- The Icc-one form of the expansion from the Icc-two form. -/
theorem sml_expansion_one (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (y : Vec 2) (K : ℕ)
    (hfo : ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L g y = ∑ d ∈ Finset.Icc 2 K, ∑ J : DerivativeWord2 (d - 1),
        orderedDerivative J g y • fluxCoeff L d J y) :
    ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L g y = ∑ d ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d - 1),
        orderedDerivative J g y • fluxCoeff L d J y := by
  intro g hg
  rw [hfo g hg]
  refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun d hd hnd => ?_
  have h1 : d = 1 := by
    have := Finset.mem_Icc.mp hd
    by_contra hne
    exact hnd (Finset.mem_Icc.mpr ⟨by omega, this.2⟩)
  subst h1
  refine Finset.sum_eq_zero fun J _ => ?_
  have hz := sml_coeff_one L y K hfo
  have : fluxCoeff L 1 J y = 0 := by
    unfold fluxCoeff
    have hp : (fun Y : Vec 2 => ∏ j, (Y - y) (J j)) = fun _ => 1 := by
      funext Y
      have : IsEmpty (Fin (1 - 1)) := ⟨fun j => by have := j.2; omega⟩
      simp
    rw [hp, hz, smul_zero]
  rw [this, smul_zero]

/-- **The glue of label operators of finite order, on a smooth field, with the transported
arrays.** -/
theorem sml_glued_expansion_one (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (t : ℝ) (x : Vec 2) (K : ℕ)
    (L : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hfo : ∀ k ∈ activeSlots D hΛ m t, ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L k.1 g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) =
        ∑ d ∈ Finset.Icc 1 K, ∑ J : DerivativeWord2 (d - 1),
          orderedDerivative J g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) •
            fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (a₀ : Fin 2) :
    gluedFluxOp D (m + 1) L t ψ x a₀ =
      ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1),
        (∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
          transportedCoeff
            (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) K
            (fun d' J => fluxCoeff (L k.1) d' J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
            (d - 1) A x) a₀ * orderedDerivative A ψ x := by
  unfold gluedFluxOp
  simp only [Nat.add_sub_cancel]
  rw [tc_sum_obsPulses_eq_activeSlots D hΛ m t (fun k =>
    pushFlux (fun y => D.flowOf m t y (D.slotAnchor (m + 1) k))
      (fun x' => D.flowOf m (D.slotAnchor (m + 1) k) x' t) (L k) ψ x)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hk : ∀ k ∈ activeSlots D hΛ m t,
      pushFlux (fun y => D.flowOf m t y (D.slotAnchor (m + 1) k.1))
        (fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) (L k.1) ψ x a₀ =
      ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff
          (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) K
          (fun d' J => fluxCoeff (L k.1) d' J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
          (d - 1) A x a₀ * orderedDerivative A ψ x := fun k hk =>
    sml_push_expansion (flowOf_contDiff D m _ _) (flowOf_contDiff D m _ _)
      (fun y => flowOf_inv D m _ _ y) (fun x' => flowOf_inv D m _ _ x') (L k.1) K x
      (hfo k hk) hψ a₀
  rw [Finset.sum_congr rfl fun k hk' => by rw [hk k hk']]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The glue of label operators of finite order from `2` on, on a smooth field, is the
differential operator of its symmetric coefficients.** -/
theorem sml_glued_expansion (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) (t : ℝ) (x : Vec 2)
    (K Dm : ℕ) (hK : K ≤ Dm) (L : ℤ → (Vec 2 → ℝ) → Vec 2 → Vec 2)
    (hfo : ∀ k ∈ activeSlots D hΛ m t, ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      L k.1 g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) =
        ∑ d ∈ Finset.Icc 2 K, ∑ J : DerivativeWord2 (d - 1),
          orderedDerivative J g (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) •
            fluxCoeff (L k.1) d J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (a₀ : Fin 2) :
    gluedFluxOp D (m + 1) L t ψ x a₀ =
      ∑ d ∈ Finset.Icc 2 Dm, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (gluedFluxOp D (m + 1) L t) d I x a₀ * orderedDerivative I ψ x := by
  have hfo1 := fun k hk => sml_expansion_one (L k.1) _ K (hfo k hk)
  set Tg : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ := fun d A =>
    (∑ k ∈ activeSlots D hΛ m t, ocCutoff D.α D.q D.Λ (m + 1) k.1 t •
      transportedCoeff
        (chartInvJacobian fun x' => D.flowOf m (D.slotAnchor (m + 1) k.1) x' t) K
        (fun d' J => fluxCoeff (L k.1) d' J (D.flowOf m (D.slotAnchor (m + 1) k.1) x t))
        (d - 1) A x) a₀ with hTg
  have E1 := sml_glued_expansion_one D hΛ m t x K L hfo1 hψ a₀
  -- the glue annihilates constants
  have hz : gluedFluxOp D (m + 1) L t (fun _ => 1) x a₀ = 0 := by
    unfold gluedFluxOp
    simp only [Nat.add_sub_cancel]
    rw [tc_sum_obsPulses_eq_activeSlots D hΛ m t (fun k =>
      pushFlux (fun y => D.flowOf m t y (D.slotAnchor (m + 1) k))
        (fun x' => D.flowOf m (D.slotAnchor (m + 1) k) x' t) (L k) (fun _ => 1) x)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun k hk => ?_
    have h0 : L k.1 ((fun _ : Vec 2 => (1 : ℝ)) ∘ fun y => D.flowOf m t y (D.slotAnchor (m + 1) k.1))
        (D.flowOf m (D.slotAnchor (m + 1) k.1) x t) = 0 :=
      sml_coeff_one (L k.1) _ K (hfo k hk)
    simp only [pushFlux, h0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
  -- the zeroth-order coefficient of the glue
  have hconst : ∀ (d : ℕ), 2 ≤ d → ∀ A : DerivativeWord2 (d - 1),
      orderedDerivative A (fun _ : Vec 2 => (1 : ℝ)) x = 0 := by
    intro d hd A
    exact congrFun (AVRegularity.CycleComparison.Lift.orderedDerivative_const A (1 : ℝ)
      (by omega)) x
  have hder0 : ∀ (A : DerivativeWord2 (1 - 1)) (f : Vec 2 → ℝ), orderedDerivative A f x = f x :=
    fun A f => congrFun (orderedDerivative_zero f A) x
  have hone : (1 ≤ K) → ∑ A : DerivativeWord2 (1 - 1), Tg 1 A = 0 := by
    intro h1K
    have E2 : gluedFluxOp D (m + 1) L t (fun _ => 1) x a₀ =
        ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1),
          Tg d A * orderedDerivative A (fun _ : Vec 2 => (1 : ℝ)) x :=
      sml_glued_expansion_one D hΛ m t x K L hfo1 (contDiff_const (c := (1 : ℝ))) a₀
    have hsplit : ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1),
        Tg d A * orderedDerivative A (fun _ : Vec 2 => (1 : ℝ)) x =
        ∑ A : DerivativeWord2 (1 - 1), Tg 1 A := by
      rw [Finset.sum_eq_single 1]
      · exact Finset.sum_congr rfl fun A _ => by rw [hder0]; ring
      · intro d hd hne
        have := Finset.mem_Icc.mp hd
        exact Finset.sum_eq_zero fun A _ => by rw [hconst d (by omega) A, mul_zero]
      · intro h
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, h1K⟩) h
    rw [hz] at E2
    exact (E2.trans hsplit).symm
  have hF1 : (1 ≤ K) → ∑ A : DerivativeWord2 (1 - 1), Tg 1 A * orderedDerivative A ψ x = 0 := by
    intro h1K
    rw [Finset.sum_congr rfl fun A _ => by rw [hder0], ← Finset.sum_mul, hone h1K, zero_mul]
  have hsub : ∑ d ∈ Finset.Icc 1 K, ∑ A : DerivativeWord2 (d - 1), Tg d A * orderedDerivative A ψ x =
      ∑ d ∈ Finset.Icc 2 K, ∑ A : DerivativeWord2 (d - 1), Tg d A * orderedDerivative A ψ x := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun d hd hnd => ?_).symm
    have h1 : d = 1 := by
      have := Finset.mem_Icc.mp hd
      by_contra hne
      exact hnd (Finset.mem_Icc.mpr ⟨by omega, this.2⟩)
    subst h1
    exact hF1 (Finset.mem_Icc.mp hd).2
  rw [E1, hsub]
  have hmid : ∀ d ∈ Finset.Icc 2 K, ∑ A : DerivativeWord2 (d - 1), Tg d A * orderedDerivative A ψ x =
      ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (gluedFluxOp D (m + 1) L t) d I x a₀ * orderedDerivative I ψ x := by
    intro d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    have hfd : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) ψ := hψ.of_le (by exact_mod_cast le_top)
    have := tc_word_sum (ContinuousLinearMap.id ℝ ℝ) (fun A => Tg d A)
      (gluedFluxOp D (m + 1) L t) x a₀
      (fun I => tc_fluxCoeff_glued D hΛ m t x K L hfo1 hd2 I a₀) hfd
    simpa using this
  rw [Finset.sum_congr rfl hmid]
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hK) fun d hd hnd => ?_
  have hd' := Finset.mem_Icc.mp hd
  have hKd : K < d := by
    by_contra hle
    exact hnd (Finset.mem_Icc.mpr ⟨hd'.1, by omega⟩)
  refine Finset.sum_eq_zero fun I _ => ?_
  have h := tc_fluxCoeff_glued D hΛ m t x K L hfo1 hd'.1 I a₀
  rw [Finset.sum_eq_zero (fun σ _ => by
    simp [transportedCoeff_eq_zero_of_le _ (show K ≤ d - 1 by omega)])] at h
  have hf : ((d - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [(mul_eq_zero.mp h).resolve_left hf, zero_mul]
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! **Source mean, Right: the pushed path mean is the Eulerian pulse flux of the path family.**

`right_liftFluxX_time_congr`: `liftFluxX` reads its field only through the slice at its time
argument. `right_pathJ_eq_euler`: `pathJ` is `pulseMeanFluxEuler` of the path family, read at the
last grade, for the field `Pi.single 0 φ` (frozen in time). -/

open CovarianceTransport Providers.GenSem

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- `liftFluxX` depends on its field only through the slice at its time argument. -/
theorem right_liftFluxX_time_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h) (a a' : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (hta : a t = a' t) :
    liftFluxX Q Cc a hh n t = liftFluxX Q Cc a' hh n t := by
  have e : ∀ (n' : ℕ) (c : LiftCoeff ι h), liftApply n' c a t = liftApply n' c a' t :=
    fun n' c => by funext X z v; simp only [liftApply, hta]
  funext X z k
  simp only [liftFluxX, e]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- **The pushed path mean is the Eulerian pulse flux of the path family**, read at the last grade,
for the field `Pi.single 0 φ`. -/
theorem right_pathJ_eq_euler (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {k : ℤ}
    (hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k)
    (htop : G.level ≤ D.term) (hm : 1 ≤ G.level) (hc : D.cellScaleSq G.level ≠ 0) {h : ℕ}
    (π : StagePath G h) (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (n : ℕ) (t : ℝ) (φ : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2) :
    pathJ Mn G π Cc n k t φ y j =
      pulseMeanFluxEuler (D.cellScaleSq G.level) (Mn.lenFactor * liftLength D G.level)
        (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
          (Mn.lenFactor * liftLength D G.level)) n h
        (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
          (pathEdges G π ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩))
        (Cc k (nativeChain G.level k))
        (fun s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level k))
        (fun s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level k) y s')
        (fun _ z => (Pi.single (0 : Fin (h + 1)) (φ z) : Fin (h + 1) → ℝ)) t y (Fin.last h) j := by
  have hk1 : D.kap G.level = D.κ G.level := kap_eq_of_le_term D htop
  have hk2 : D.kap (G.level - 1) = D.κ (G.level - 1) := kap_eq_of_le_term D (by omega)
  have hclk : D.cellScaleSq G.level * ((D.cellScaleSq G.level)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  unfold pathJ pushFlux pulseMeanFluxEuler
  rw [nativePathMean_pos Mn G π Cc n t hA]
  unfold pathMeanFlux
  simp only [hk1, hk2, Matrix.mulVec, dotProduct, Function.comp_apply]
  refine Finset.sum_congr rfl fun k' _ => ?_
  have hcongr := right_liftFluxX_time_congr
    (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
      (pathEdges G π ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩))
    (Cc k (nativeChain G.level k))
    (fun _ X => (Pi.single (0 : Fin (h + 1)) (φ (D.flowOf (G.level - 1) t
      ((Mn.lenFactor * liftLength D G.level) • X) (D.slotAnchor G.level k))) : Fin (h + 1) → ℝ))
    (fun s' X' => (fun _ z => (Pi.single (0 : Fin (h + 1)) (φ z) : Fin (h + 1) → ℝ)) (D.cellScaleSq G.level * s')
      (D.flowOf (G.level - 1) (D.cellScaleSq G.level * s') ((Mn.lenFactor * liftLength D G.level) • X')
        (D.slotAnchor G.level k))) h n ((D.cellScaleSq G.level)⁻¹ * t)
    (by funext X'; simp only [hclk])
  rw [hcongr]
  simp only [smul_eq_mul]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The first-source-flux step: the diagonal mean flux of a constant field vanishes (degrees `n ≥ 2`),
from the grade-zero lifts `IsDiagLifts` and the order-zero vanishing of lift sequences. -/

open Uniqueness Providers Providers.GenSem

/-- The order-zero entries of a scalar grade-zero lift sequence of a family vanish. -/
theorem fsc_diag_hZ {Dm : ℕ} (D : OCData) (hζ : IsFastProfile D.ζ) (m : ℕ) {k : ℤ} (hk : Odd k)
    (A : RealChain) (ρ : ℝ) {t₀ t₁ : ℝ} (hab : t₀ ≤ t₁) {sX sZ N : ℕ}
    {C : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hC : IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) sX sZ t₀ t₁ N 0 C) :
    ∀ n', n' ≠ 0 → PccZero (Set.univ : Set (Vec 2)) t₀ t₁ C 0 n' := by
  classical
  set Q := familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => [])
  have hW : ∀ X ∈ (Set.univ : Set (Vec 2)), ∃ lo A' Mv : ℝ,
      WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A' Mv := by
    intro X' _
    obtain ⟨lo, hi, hlo, he⟩ := familyLiftData_pos_window (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D hζ m k A ρ
      (fun _ _ _ => []) t₀ t₁ X'
    obtain ⟨Mv, hMv⟩ := familyLiftData_v_bounded D hζ m hk A ρ (hv := fun _ : Fin 1 => ℝ)
      (fun _ _ _ => [])
    exact ⟨lo, hi, Mv, windowData_of_elliptic (fun t => Matrix.of (Q.G t X')) Q.v _ _ lo hi Mv
      (fun t => familyLiftData_symm (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []) t X' 0 1) hlo he
      (fun t _ z => hMv t z)⟩
  intro n' hn'
  exact pcc_order_zero_vanish Q t₀ t₁ hab isOpen_univ hW sX sZ N 0 C (IsLiftSequence.toOn hC _) 0 le_rfl n'
    (Or.inr hn')

open scoped Classical in
/-- The diagonal mean flux of order `n ≥ 2` of a constant vanishes. -/
theorem fsc_diagMeanFluxCtx_const_zero {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) (Mn : SuccMenu)
    (m : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hc : 0 < D.cellScaleSq m)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (t : ℝ) (ch : RealChain) (ζ : Vec 2) {n : ℕ}
    (hn : 2 ≤ n) (c : ℝ) (x : Vec 2) :
    diagMeanFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Cc0 t ch ζ n (fun _ => c) x = 0 := by
  unfold diagMeanFluxCtx
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  rw [finsum_eq_if]
  split_ifs with hk hadm
  swap
  · rfl
  swap
  · rfl
  by_cases hct : ocCutoff D.α D.q D.Λ m k t = 0
  · rw [hct, zero_smul]
  have hwin := ccov_inv_mul_mem_window hc (ComplexContext.mem_window_of_cutoff hΛ hct)
  have hC := hdiag k _ hk.1 hadm
  have hZ := fsc_diag_hZ D hζ m hk.1 _ _ (hwin.1.trans hwin.2) hC
  have hP := fsc_pathMeanFlux_const_zero_grade0 D m (Mn.lenFactor * liftLength D m)
    (isOpen_univ) (IsLiftSequence.toOn hC Set.univ) hZ hn t hwin c
  unfold pushFlux diagLabelFlux
  have : ((fun _ : Vec 2 => c) ∘ ((ch.appendChild D k t ζ).famMap D t)) = fun _ => c := rfl
  rw [this, hP _ (mem_univ _)]
  simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! Transfer collapse, step A and the piece itself: **the transfer to the
coarser chart collapses to the finer natural chart**.

* `tc_material_symm`: the inverse of the material map of a natural piece is the flow back to the
  anchor of the slot.
* `tc_dimFlux_native`: the dimensional sample of a transferred identity at the native context of
  a coarser piece of nonzero weight is `lam` times the sum over the active finer slots of the
  transports along the label changes of the coefficients of the finer native families
  (`IsActualSuccessor`, `dim_transferAt`, `tc_slot_jacobian`, `tc_slot_coeff`).
* `tc_piece_of_source`: step A for a source and its lift family (`tc_piece_eulerian` with the
  finite order of the finer outputs from `centeredCoefficient_expansion` (ii)).
* `transferPieceEulerian : TransferPieceEulerianStatement` (step A), and
  `transferChartCollapse : TransferChartCollapseStatement` (the transfer collapse, by
  `transferChartCollapse_of_eulerian`). -/

open Providers.QuietAtlas Providers.GenSem CovarianceTransport

/-- The inverse of the material map of a natural piece. -/
theorem tc_material_symm {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {M : ℕ}
    {G' : GenStage D hr Dm b j₀} (hnat : G'.IsNatural M) (p : OddSlot) (t : ℝ) :
    ⇑((G'.fam.piece p).material t).symm =
      fun x' => D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x' t := by
  funext x'
  apply ((G'.fam.piece p).material t).injective
  rw [Homeomorph.apply_symm_apply, (hnat.1 p).2.2.2.2 t]
  exact (flowOf_inv D (G'.level - 1) t (D.slotAnchor G'.level p.1) x').symm

open scoped Classical in
/-- **The dimensional sample of a transferred identity at the native context** of a coarser piece
of nonzero weight. -/
theorem tc_dimFlux_native
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (hin : StageSuccessor.Input P Mn G) (hsucc : IsActualSuccessor D P Mn G G')
    (hT : TransferInput Mn G) (s : SuccSource G) (hv : s.Valid Mn.A Mn.J) (hnd : ¬ s.IsDiag)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u')
    (hspec : ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux p c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level p.1 (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
          (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    (p : OddSlot) (t : ℝ) (hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0) (y : Vec 2) {d : ℕ}
    (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) :
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p (G'.actual p)
        v' u' γ' d I t y ((D.eps G'.level)⁻¹ • y) =
      s.lam G.level Mn.η0 • ∑ k ∈ activeSlots D hin.base G'.level t,
        ocCutoff D.α D.q D.Λ (G'.level + 1) k.1 t •
          transportedCoeff (fun h => chartInvJacobian (labelChange D G'.level p.1 k.1 t) (y + h))
            ((s.prov G.level).tags P).order
            (fun d J => fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc
              k.1 t (nativeChain G.level k.1)) d J (labelChange D G'.level p.1 k.1 t y))
            (d - 1) I 0 := by
  have hL : G.level = G'.level + 1 := by
    have h1 := hsucc.1
    have h2 := hsucc.2.1
    omega
  have hnat : G'.IsNatural Mn.M := hsucc.2.2.2.1
  have hΛ := hin.base
  have hζ := hin.profile
  have hlev := hin.level
  have hm1 : 1 ≤ G'.level := by omega
  have hjm : j₀ ≤ G'.level := by omega
  have hε : D.eps G'.level ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hεc : D.eps (G'.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hκ : D.kap G'.level ≠ 0 :=
    (EntryWeakProofs.weakData_kap_pos D hΛ hζ hin.band G'.level).ne'
  have hτp : 0 < ocTau D.α D.q D.Λ G'.level := Construction.Stream.ocTau_pos hΛ
  have htp : t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1 :=
    mem_ocPulseWindow_of_ocCutoff_ne_zero hτp hcp
  obtain ⟨Mtop, -⟩ := hT.history
  have hlv : transferAt D G.level p.1 = transferAt D (G'.level + 1) p.1 := by rw [hL]
  have e := dim_transferAt D hΛ hκ htp (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
    (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc)
    (⟨G'.level - 1, [p.1], y, []⟩ : RealChain) ((D.eps G'.level)⁻¹ • y) d I
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
  rw [hspec p (G'.actual p) d I t _ _ hd, smul_inv_smul₀ hεc, hnat.2.2.1 p,
    ite_eq_left (isAdmissibleChain_nativeChain_recenter hm1 hjm p y), nativeChain_recenter, hlv, e]
  refine congrArg (fun v => s.lam G.level Mn.η0 • v) (Finset.sum_congr rfl fun k hk => ?_)
  have hck : ocCutoff D.α D.q D.Λ (G'.level + 1) k.1 t ≠ 0 := by simpa [activeSlots] using hk
  have hsp := tc_single_pulse_avail hT.stream hζ hΛ hT.start Mtop hm1 hjm p.2 hcp hck
  have htav : t ∈ availInterval D Mtop (G'.level + 1) k.1 :=
    mem_availInterval_of_ocCutoff D hΛ hck
  have hsav : D.slotAnchor (G'.level + 1) k.1 ∈ availInterval D Mtop (G'.level + 1) k.1 :=
    slotAnchor_mem_availInterval D Mtop (G'.level + 1) k.1
  have hco : (fun (d : ℕ) (J : DerivativeWord2 (d - 1)) =>
      fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k.1 t
        ((⟨G'.level - 1, [p.1], y, []⟩ : RealChain).appendChild D k.1 t
          ((D.eps G'.level)⁻¹ • y))) d J 0) =
      fun d J => fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k.1 t
        (nativeChain G.level k.1)) d J (labelChange D G'.level p.1 k.1 t y) :=
    funext fun d => funext fun J =>
      tc_slot_coeff P Mn G hin hT hL s hv hnd Cc hLF p.2 k.2 hcp hck y d J
  rw [tc_slot_jacobian hζ hm1 hε p.1 k.1 t y
    (fun v hv' => hsp v (uIcc_subset_availInterval D Mtop (G'.level + 1) k.1 htav hsav hv')),
    hco]

open scoped Classical in
/-- **Step A of the transfer collapse for a source and its lift family.** -/
theorem tc_piece_of_source
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (hin : StageSuccessor.Input P Mn G) (hsucc : IsActualSuccessor D P Mn G G')
    (hT : TransferInput Mn G) (s : SuccSource G) (hv : s.Valid Mn.A Mn.J) (hnd : ¬ s.IsDiag)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = s.prov G.level)
    (hspec : ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux p c v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D G.level p.1 (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
          (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc) t
          (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    (p : OddSlot) (t : ℝ) (hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0)
    (f : Vec 2 → hr u'.1.root) (hf : ContDiff ℝ (Dm - 1 : ℕ) f) (x : Vec 2) (κ : Fin 2) :
    ∑ d ∈ Finset.Icc 2 Dm, ∑ A : DerivativeWord2 (d - 1),
        transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
          (G'.fam.identity v' u' γ').maxOrder
          (fun d' I => G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1)) p
            (G'.actual p) v' u' γ' d' I t (((G'.fam.piece p).material t).symm x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x))
          (d - 1) A x κ • (G'.fam.identity v' u' γ').map (orderedDerivative A f x) =
      s.lam G.level Mn.η0 •
        ∑ d ∈ Finset.Icc 2 Dm, ∑ I : DerivativeWord2 (d - 1),
          fluxCoeff (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s Cc t)
            d I x κ • (G'.fam.identity v' u' γ').map (orderedDerivative I f x) := by
  have hL : G.level = G'.level + 1 := by
    have h1 := hsucc.1
    have h2 := hsucc.2.1
    omega
  have hnat : G'.IsNatural Mn.M := hsucc.2.2.2.1
  have htags : G'.HasTags P := hsucc.2.2.2.2.1
  have hΛ := hin.base
  have hlev := hin.level
  have hτk : 0 < ocTau D.α D.q D.Λ (G'.level + 1) := Construction.Stream.ocTau_pos hΛ
  have hmax : (G'.fam.identity v' u' γ').maxOrder = ((s.prov G.level).tags P).order := by
    rw [(htags v' u' γ').2, hprov]
  have hsrc : sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s Cc t =
      gluedFluxOp D (G'.level + 1) (fun k => s.fluxOp (Mn.lenFactor * liftLength D G.level)
        Mn.anchor Cc k t (nativeChain G.level k)) t := by
    unfold sourceEulerOp
    rw [hL]
  -- the finer outputs have finite order at the finer labels of the point
  have hfo : ∀ k ∈ activeSlots D hΛ G'.level t, ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k.1 t (nativeChain G.level k.1)
          g (D.flowOf G'.level (D.slotAnchor (G'.level + 1) k.1) x t) =
        ∑ d ∈ Finset.Icc 1 ((s.prov G.level).tags P).order, ∑ J : DerivativeWord2 (d - 1),
          orderedDerivative J g (D.flowOf G'.level (D.slotAnchor (G'.level + 1) k.1) x t) •
            fluxCoeff (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor Cc k.1 t
              (nativeChain G.level k.1)) d J
              (D.flowOf G'.level (D.slotAnchor (G'.level + 1) k.1) x t) := by
    intro k hk g hg
    have hck : ocCutoff D.α D.q D.Λ (G'.level + 1) k.1 t ≠ 0 := by simpa [activeSlots] using hk
    have htk : t ∈ ocPulseWindow D.α D.q D.Λ (G'.level + 1) k.1 :=
      mem_ocPulseWindow_of_ocCutoff_ne_zero hτk hck
    have hN : IsAdmissibleChain D b j₀ (G'.level + 1) k.1 (nativeChain (G'.level + 1) k.1) :=
      nativeChain_isCarrier D b j₀ (G'.level + 1) k.1 2 (by omega) (by omega) k.2 0
    rw [← hL] at htk hN
    exact (centeredCoefficient_expansion P Mn G hin s hv hnd Cc hLF k.1 k.2 t htk
      (nativeChain G.level k.1) hN _
      (isAdmissibleChain_nativeChain_recenter (by omega) (by omega) k _)).2
      (hT.reserve s hv) g hg
  have key := tc_piece_eulerian D hΛ G'.level p.1 t x (s.lam G.level Mn.η0)
    ((s.prov G.level).tags P).order (fun k => s.fluxOp (Mn.lenFactor * liftLength D G.level)
      Mn.anchor Cc k t (nativeChain G.level k)) hfo (G'.fam.identity v' u' γ').map Dm hf κ
  rw [tc_material_symm hnat p t, hmax, hsrc]
  refine Eq.trans ?_ key
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun A _ => ?_
  have hd2 := (Finset.mem_Icc.mp hd).1
  refine congrArg (fun v : Vec 2 =>
    v κ • (G'.fam.identity v' u' γ').map (orderedDerivative A f x)) ?_
  exact transportedCoeff_congr _ _ (fun d' hd' _ I =>
    tc_dimFlux_native P Mn G G' hin hsucc hT s hv hnd Cc hLF v' u' γ' hspec p t hcp _
      (by omega) I) A x

/-- **Step A of the transfer collapse**: one coarser piece of nonzero weight gives the Eulerian operator of the
source. -/
theorem transferPieceEulerian : TransferPieceEulerianStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' hin hsucc hT W v' u' γ' hnd p t hcp f hf x κ
  exact tc_piece_of_source P Mn G G' hin hsucc hT (W.e v' u' γ').1 (W.e v' u' γ').2.1 hnd
    (W.Cc (W.e v' u' γ').1) (W.lifts (W.e v' u' γ').1) v' u' γ' (W.spec v' u' γ').1
    ((W.spec v' u' γ').2.2.1 hnd) p t hcp f hf x κ

/-- **Transfer collapse (the transfer to the coarser chart collapses to the finer natural chart).** -/
theorem transferChartCollapse : TransferChartCollapseStatement :=
  transferChartCollapse_of_eulerian transferPieceEulerian

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

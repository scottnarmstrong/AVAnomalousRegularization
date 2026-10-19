-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import AVRegularity.Statements.Definitions.IsWindowTestFunction
public import AVenhance.Statements.Roots.L2NormSq
public import Mathlib.Order.CompletePartialOrder
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import AVenhance.Statements.Roots.SpaceGrad
import AVenhance.Infra.Classical.GalerkinGenerator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization
namespace AVRegularity.Applications

/-! # Smooth periodic approximation in `H¹(𝕋²)`

For `u ∈ H¹(𝕋²)` (`IsPeriodicH1With u Du`) the Fourier projections `P_N u` are smooth, periodic,
and `P_N u → u`, `∂ᵢ P_N u → Du_i` in `L²(cube)`, hence weakly against every `L²` coefficient.
Extracted from the proof of `divFree_static_h1_cancellation`. -/

open AVenhance.Infra.Parabolic.WeakUniqueness AVenhance.Infra.Parabolic.FourierGalerkin
  AVenhance.Infra.Torus AVenhance.Infra.Classical

theorem torus_exists_smooth_approx {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : AVenhance.IsPeriodicH1With u Du) :
    ∃ P : ℕ → Vec 2 → ℝ, (∀ N, ContDiff ℝ (⊤ : ℕ∞) (P N)) ∧
      (∀ N, AVenhance.IsZ2Periodic (P N)) ∧
      (∀ g : Vec 2 → ℝ, MemL2On AVenhance.unitCube g →
        Tendsto (fun N => ∫ x in AVenhance.unitCube, P N x * g x) atTop
          (𝓝 (∫ x in AVenhance.unitCube, u x * g x)) ∧
        ∀ i : Fin 2, Tendsto (fun N => ∫ x in AVenhance.unitCube,
            AVenhance.spaceGrad (P N) x i * g x) atTop
          (𝓝 (∫ x in AVenhance.unitCube, Du x i * g x))) := by
  let upath : ℝ → Vec 2 → ℝ := fun _ => u
  let Dpath : ℝ → Vec 2 → Vec 2 := fun _ => Du
  let P (N : ℕ) : Vec 2 → ℝ := weakFourierModeProjection N upath 0
  let GradP (N : ℕ) (i : Fin 2) : Vec 2 → ℝ :=
    fun x => AVenhance.spaceGrad (P N) x i
  have hPCont (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (P N) := by
    have h := realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N upath 0)
    have h' : ContDiff ℝ (⊤ : ℕ∞)
        (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0)) :=
      h.of_le (m := (⊤ : ℕ∞)) (by simp)
    simpa [P, weakFourierModeProjection] using h'
  have hPPer (N : ℕ) : AVenhance.IsZ2Periodic (P N) := by
    change AVenhance.IsZ2Periodic
      (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0))
    exact realFourierModeAmbientExpansion_periodic N _
  have hgradCont (N : ℕ) (i : Fin 2) : Continuous (GradP N i) := by
    change Continuous (fun x => fderiv ℝ (P N) x (Homogenization.basisVec i))
    exact (hPCont N).continuous_fderiv (by simp) |>.clm_apply continuous_const
  have hPmem (N : ℕ) : MemL2On AVenhance.unitCube (P N) :=
    weak_continuous_memL2On (hPCont N).continuous
  have hgradMem (N : ℕ) (i : Fin 2) : MemL2On AVenhance.unitCube (GradP N i) :=
    weak_continuous_memL2On (hgradCont N i)
  have huMem : MemL2On AVenhance.unitCube u := hu.2.2.1
  have hDuMem (i : Fin 2) : MemL2On AVenhance.unitCube (fun x => Du x i) := hu.2.2.2.1 i
  have huH1 : AVenhance.IsPeriodicH1With (upath 0) (Dpath 0) := by simpa [upath, Dpath] using hu
  have hprojVal : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hPmem N)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (P N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp huMem).toLp
        (AVenhance.Infra.Torus.periodicToTorus u))) := by
    have h := weakFourierProjectionL2_tendsto (u := upath) (t := 0) huMem
    simpa [P, weakFourierProjectionL2_eq_expansionTransfer] using h
  have hprojGrad (i : Fin 2) : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hgradMem N i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (GradP N i))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp (hDuMem i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)))) := by
    have h := weakFourierProjectionGradientL2_tendsto huH1 i
    have h' : Tendsto (fun N => weakFourierProjectionGradientL2 N upath 0 i) atTop
        (𝓝 ((weakProjection_realCellToTorus_memLp (hDuMem i)).toLp
          (AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)))) := by
      simpa [weakFourierProjectionGradientL2] using h
    simpa [P, GradP, weakFourierProjectionGradientL2_eq_expansionTransfer] using h'
  refine ⟨P, hPCont, hPPer, fun g hg => ⟨?_, fun i => ?_⟩⟩
  · have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun N => hPmem N) huMem hg hprojVal
    simpa [integral_unitCell_eq_unitCube] using h
  · have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun N => hgradMem N i)
      (hDuMem i) hg (hprojGrad i)
    simpa [GradP, integral_unitCell_eq_unitCube] using h

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Unit cells of `ℤ²` in `ℝ²` and space-time translations

The half-open cells `n + [0,1)²`, `n ∈ ℤ²`, tile `ℝ²` exactly; a finite box of cells covers any
sup-norm ball. Integer translations in space preserve Lebesgue measure on `ℝ × ℝ²`. -/

/-- The half-open unit cube `[0,1)²`. -/
def cellI : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 1

/-- The cell `n + [0,1)²`. -/
def cellAt (n : Fin 2 → ℤ) : Set (Vec 2) := {x | x - latticeShift n ∈ cellI}

/-- The box of lattice points `[-M, M]²`. -/
def latBox (M : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- The closed sup-norm ball `{‖x‖ ≤ R}` in `ℝ²`. -/
def supBall (R : ℝ) : Set (Vec 2) := {x | ‖x‖ ≤ R}

/-- Spatial translation by a lattice vector, on space-time. -/
def trans (n : Fin 2 → ℤ) (p : ℝ × Vec 2) : ℝ × Vec 2 := (p.1, p.2 + latticeShift n)

theorem measurableSet_cellI : MeasurableSet cellI :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem measurableSet_cellAt (n : Fin 2 → ℤ) : MeasurableSet (cellAt n) :=
  measurableSet_cellI.preimage (measurable_id.sub measurable_const)

theorem measurableSet_supBall (R : ℝ) : MeasurableSet (supBall R) :=
  (isClosed_le continuous_norm continuous_const).measurableSet

theorem measurePreserving_trans (n : Fin 2 → ℤ) :
    MeasurePreserving (trans n) (volume : Measure (ℝ × Vec 2)) volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure (Vec 2)) (latticeShift n))
  rw [← Measure.volume_eq_prod] at h
  exact h

theorem measurePreserving_trans_restrict (n : Fin 2 → ℤ) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurePreserving (trans n) (volume.restrict (S ×ˢ cellI))
      (volume.restrict (S ×ˢ cellAt n)) := by
  have h := (measurePreserving_trans n).restrict_preimage
    (hS.prod (measurableSet_cellAt n))
  have hpre : trans n ⁻¹' (S ×ˢ cellAt n) = S ×ˢ cellI := by
    ext ⟨t, x⟩
    simp [trans, cellAt]
  rwa [hpre] at h

theorem mem_cellAt_floor (x : Vec 2) : x ∈ cellAt (fun i => ⌊x i⌋) := by
  simp only [cellAt, cellI, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
    forall_true_left, Pi.sub_apply, latticeShift]
  intro i
  exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩

theorem cellAt_disjoint {n m : Fin 2 → ℤ} (h : n ≠ m) : Disjoint (cellAt n) (cellAt m) := by
  rw [Set.disjoint_left]
  intro x hn hm
  apply h
  funext i
  simp only [cellAt, cellI, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
    forall_true_left, Pi.sub_apply, latticeShift] at hn hm
  have h1 := hn i
  have h2 := hm i
  have : (n i : ℝ) < m i + 1 := by linarith [h1.1, h2.2]
  have : (m i : ℝ) < n i + 1 := by linarith [h1.2, h2.1]
  have a : n i < m i + 1 := by exact_mod_cast ‹(n i : ℝ) < m i + 1›
  have b : m i < n i + 1 := by exact_mod_cast ‹(m i : ℝ) < n i + 1›
  omega

theorem supBall_subset_iUnion_cellAt {R : ℝ} {M : ℕ} (hM : R + 1 ≤ M) :
    supBall R ⊆ ⋃ n ∈ latBox M, cellAt n := by
  intro x hx
  simp only [Set.mem_iUnion]
  refine ⟨fun i => ⌊x i⌋, ?_, mem_cellAt_floor x⟩
  simp only [latBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hxi : |x i| ≤ R := (norm_le_pi_norm x i).trans hx
  have h1 := abs_le.1 hxi
  constructor
  · have : (-(M : ℤ) : ℝ) ≤ ⌊x i⌋ := by
      have := Int.lt_floor_add_one (x i)
      have h3 : (⌊x i⌋ : ℝ) > x i - 1 := by linarith
      push_cast
      linarith
    exact_mod_cast this
  · have : ((⌊x i⌋ : ℤ) : ℝ) ≤ (M : ℝ) := by linarith [Int.floor_le (x i)]
    exact_mod_cast this

/-- `cellI` and the open unit cube agree a.e. -/
theorem cellI_ae_eq_unitCube : cellI =ᵐ[volume] unitCube := by
  have h1 : cellI =ᵐ[volume] Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [cellI, volume_pi] using
      (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
        (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))
  have h2 : unitCube =ᵐ[volume] Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [unitCube, volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
        (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))
  exact h1.trans h2.symm

theorem restrict_prod_cellI_eq_unitCube (S : Set ℝ) :
    (volume : Measure (ℝ × Vec 2)).restrict (S ×ˢ cellI) =
      volume.restrict (S ×ˢ unitCube) := by
  apply Measure.restrict_congr_set
  have h : (S ×ˢ cellI : Set (ℝ × Vec 2)) =ᵐ[(volume : Measure ℝ).prod (volume : Measure (Vec 2))]
      (S ×ˢ unitCube : Set (ℝ × Vec 2)) :=
    Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) cellI_ae_eq_unitCube
  rwa [← Measure.volume_eq_prod] at h

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # Space-time periodization

For `ρ` jointly smooth with `ρ(t,x) = 0` for `‖x‖ > R`, the periodization
`ρ^per(t,x) = Σ_{n ∈ ℤ²} ρ(t, x + n)` is, on each sup-ball, a finite sum. Hence it is smooth,
`ℤ²`-periodic in space, and commutes with `∂ₜ` and `∇ₓ`. -/

/-- `ρ(t,x) ≠ 0` forces `‖x‖ ≤ R`. -/
def SupBdd (R : ℝ) (ρ : ℝ → Vec 2 → ℝ) : Prop := ∀ t x, ρ t x ≠ 0 → ‖x‖ ≤ R

/-- The (fiberwise) periodization of `ρ` in space. -/
def perST (ρ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑ᶠ n : Fin 2 → ℤ, ρ t (x + latticeShift n)

theorem latticeShift_add (n m : Fin 2 → ℤ) :
    latticeShift (n + m) = latticeShift n + latticeShift m := by
  funext i; simp [latticeShift]

theorem mem_latBox_of_norm_le {R r : ℝ} {M : ℕ} (hM : R + r ≤ M) {x : Vec 2}
    {n : Fin 2 → ℤ} (hx : ‖x‖ ≤ r) (hxn : ‖x + latticeShift n‖ ≤ R) : n ∈ latBox M := by
  simp only [latBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : |x i| ≤ r := (norm_le_pi_norm x i).trans hx
  have h2 : |x i + (n i : ℝ)| ≤ R := by
    have := norm_le_pi_norm (x + latticeShift n) i
    simpa [latticeShift] using this.trans hxn
  have h3 := abs_le.1 h1
  have h4 := abs_le.1 h2
  constructor
  · have : (-(M : ℝ)) ≤ n i := by linarith
    exact_mod_cast this
  · have : (n i : ℝ) ≤ M := by linarith
    exact_mod_cast this

theorem perST_eq_sum {R r : ℝ} {M : ℕ} (hM : R + r ≤ M) {ρ : ℝ → Vec 2 → ℝ}
    (hρ : SupBdd R ρ) (t : ℝ) {x : Vec 2} (hx : ‖x‖ ≤ r) :
    perST ρ t x = ∑ n ∈ latBox M, ρ t (x + latticeShift n) := by
  unfold perST
  apply finsum_eq_sum_of_support_subset
  intro n hn
  rw [Function.mem_support] at hn
  exact mem_latBox_of_norm_le hM hx (hρ t _ hn)

theorem perST_periodic (ρ : ℝ → Vec 2 → ℝ) (t : ℝ) : IsZ2Periodic (perST ρ t) := by
  intro k x
  unfold perST
  have := finsum_comp_equiv (Equiv.addRight k)
    (f := fun n : Fin 2 → ℤ => ρ t (x + latticeShift n))
  rw [← this]
  apply finsum_congr
  intro n
  simp only [Equiv.coe_addRight, latticeShift_add]
  congr 1
  abel

theorem exists_nat_ge_add (R r : ℝ) : ∃ M : ℕ, R + r ≤ M := exists_nat_ge _

theorem perST_contDiff {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ρ p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => perST ρ p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  obtain ⟨M, hM⟩ := exists_nat_ge_add R (‖x‖ + 1)
  have hnhds : {q : ℝ × Vec 2 | ‖q.2‖ ≤ ‖x‖ + 1} ∈ 𝓝 (t, x) := by
    have : {q : ℝ × Vec 2 | ‖q.2‖ < ‖x‖ + 1} ∈ 𝓝 (t, x) :=
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds
        (by simp)
    exact Filter.mem_of_superset this fun q hq => by
      simp only [Set.mem_ofPred_eq] at hq ⊢; exact le_of_lt hq
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => ∑ n ∈ latBox M, ρ p.1 (p.2 + latticeShift n)) := by
    apply ContDiff.sum
    intro n _
    exact hs.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hnhds] with q hq
  exact perST_eq_sum hM hρ q.1 hq

theorem supBdd_deriv_time {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ) :
    SupBdd R (fun s y => deriv (fun r => ρ r y) s) := by
  intro s y hne
  by_contra hy
  push Not at hy
  apply hne
  have : (fun r => ρ r y) = fun _ => 0 := by
    funext r
    by_contra h
    exact absurd (hρ r y h) (not_le.2 hy)
  simp [this]

theorem perST_deriv_time {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ρ p.1 p.2)) (t : ℝ) (x : Vec 2) :
    deriv (fun s => perST ρ s x) t = perST (fun s y => deriv (fun r => ρ r y) s) t x := by
  obtain ⟨M, hM⟩ := exists_nat_ge_add R (‖x‖)
  have h1 : (fun s => perST ρ s x) = fun s => ∑ n ∈ latBox M, ρ s (x + latticeShift n) := by
    funext s; exact perST_eq_sum hM hρ s le_rfl
  have hdiff : ∀ n : Fin 2 → ℤ, Differentiable ℝ (fun s => ρ s (x + latticeShift n)) := fun n =>
    (hs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  rw [h1, perST_eq_sum hM (supBdd_deriv_time hρ) t le_rfl]
  rw [deriv_fun_sum fun n _ => (hdiff n) t]

theorem supBdd_spaceGrad {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ) (i : Fin 2) :
    SupBdd R (fun s y => spaceGrad (ρ s) y i) := by
  intro s y hne
  by_contra hy
  push Not at hy
  apply hne
  have hopen : IsOpen {z : Vec 2 | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hev : ρ s =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    by_contra h
    exact absurd (hρ s z h) (not_le.2 hz)
  simp [spaceGrad, hev.fderiv_eq]

theorem spaceGrad_perST {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ρ p.1 p.2)) (t : ℝ) (x : Vec 2)
    (i : Fin 2) :
    spaceGrad (perST ρ t) x i = perST (fun s y => spaceGrad (ρ s) y i) t x := by
  obtain ⟨M, hM⟩ := exists_nat_ge_add R (‖x‖ + 1)
  have hnhds : {y : Vec 2 | ‖y‖ ≤ ‖x‖ + 1} ∈ 𝓝 x := by
    have : {y : Vec 2 | ‖y‖ < ‖x‖ + 1} ∈ 𝓝 x :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    exact Filter.mem_of_superset this fun q hq => by
      simp only [Set.mem_ofPred_eq] at hq ⊢; exact le_of_lt hq
  have hev : perST ρ t =ᶠ[𝓝 x] fun y => ∑ n ∈ latBox M, ρ t (y + latticeShift n) := by
    filter_upwards [hnhds] with y hy
    exact perST_eq_sum hM hρ t hy
  have hρt : ContDiff ℝ (⊤ : ℕ∞) (ρ t) := hs.comp (contDiff_const.prodMk contDiff_id)
  have hdiff : ∀ n : Fin 2 → ℤ, DifferentiableAt ℝ (fun y => ρ t (y + latticeShift n)) x :=
    fun n => ((hρt.differentiable (by simp)).comp (differentiable_id.add_const _)) x
  have hx : ‖x‖ ≤ ‖x‖ + 1 := by linarith
  rw [perST_eq_sum hM (supBdd_spaceGrad hρ i) t hx]
  simp only [spaceGrad]
  rw [hev.fderiv_eq, fderiv_fun_sum fun n _ => hdiff n]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fderiv_comp_add_right]

/-! # A square partition of unity

There is `ζ ∈ C_c^∞(ℝ²)` with `Σ_{n ∈ ℤ²} ζ(x + n)² = 1` for all `x`. Differentiating, 
`Σ_n ζ ∂ᵢζ (x + n) = 0`. -/

/-- The periodization (in `x`) of a time-independent function. -/
def perX (g : Vec 2 → ℝ) (x : Vec 2) : ℝ := perST (fun _ y => g y) 0 x

theorem perX_periodic (g : Vec 2 → ℝ) : IsZ2Periodic (perX g) := perST_periodic _ 0

/-- A smooth cutBump, `1` on the sup-ball of radius `2`, supported in the sup-ball of radius `3`. -/
def cutBump : ContDiffBump (0 : Vec 2) := ⟨2, 3, by norm_num, by norm_num⟩

theorem cutBump_norm_lt {y : Vec 2} (hy : (cutBump : Vec 2 → ℝ) y ≠ 0) : ‖y‖ < 3 := by
  have hy' : y ∈ Function.support (cutBump : Vec 2 → ℝ) := hy
  rw [cutBump.support_eq] at hy'
  have : ‖y‖ < cutBump.rOut := by simpa [Metric.mem_ball, dist_zero_right] using hy'
  exact this

private theorem cutBump_supBdd : SupBdd 3 (fun _ y => (cutBump : Vec 2 → ℝ) y ^ 2) := by
  intro t y hne
  have : (cutBump : Vec 2 → ℝ) y ≠ 0 := fun h => hne (by simp [h])
  exact (cutBump_norm_lt this).le

private theorem cutBump_sq_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (cutBump : Vec 2 → ℝ) p.2 ^ 2) :=
  (cutBump.contDiff.comp contDiff_snd).pow 2

private theorem perX_cutBump_ge_one (x : Vec 2) : 1 ≤ perX (fun y => (cutBump : Vec 2 → ℝ) y ^ 2) x := by
  obtain ⟨M, hM⟩ := exists_nat_ge_add (3 : ℝ) ‖x‖
  unfold perX
  rw [perST_eq_sum hM cutBump_supBdd 0 le_rfl]
  set n₀ : Fin 2 → ℤ := fun i => -⌊x i⌋ with hn₀
  have hxn : ‖x + latticeShift n₀‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have h1 := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [Pi.add_apply, latticeShift, hn₀, Int.cast_neg, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hmem : n₀ ∈ latBox M := mem_latBox_of_norm_le hM le_rfl (hxn.trans (by norm_num))
  have hone : (cutBump : Vec 2 → ℝ) (x + latticeShift n₀) = 1 := by
    apply cutBump.one_of_mem_closedBall
    simpa [cutBump, dist_eq_norm] using (hxn.trans (by norm_num : (1 : ℝ) ≤ 2))
  calc (1 : ℝ) = (cutBump : Vec 2 → ℝ) (x + latticeShift n₀) ^ 2 := by rw [hone]; norm_num
    _ ≤ ∑ n ∈ latBox M, (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2 :=
        Finset.single_le_sum (f := fun n => (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2)
          (fun n _ => sq_nonneg _) hmem

private theorem perX_cutBump_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (perX fun y => (cutBump : Vec 2 → ℝ) y ^ 2) := by
  have := (perST_contDiff cutBump_supBdd cutBump_sq_smooth).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec 2 => ((0 : ℝ), x))
  exact this

/-- The cutoff `ζ = χ / √(Σ_n χ(· + n)²)`. -/
def cutoffZ : Vec 2 → ℝ := fun x =>
  (cutBump : Vec 2 → ℝ) x / Real.sqrt (perX (fun y => (cutBump : Vec 2 → ℝ) y ^ 2) x)

theorem cutoffZ_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffZ := by
  unfold cutoffZ
  refine cutBump.contDiff.div (perX_cutBump_smooth.sqrt fun x => ?_) fun x => ?_
  · have := perX_cutBump_ge_one x
    linarith
  · have := perX_cutBump_ge_one x
    exact (Real.sqrt_pos.2 (by linarith)).ne'

theorem cutoffZ_hasCompactSupport : HasCompactSupport cutoffZ := by
  refine HasCompactSupport.intro (cutBump.hasCompactSupport.isCompact) fun x hx => ?_
  have : (cutBump : Vec 2 → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [cutoffZ, this]

theorem cutoffZ_supBdd : SupBdd 3 (fun _ y => cutoffZ y) := by
  intro t y hne
  have : (cutBump : Vec 2 → ℝ) y ≠ 0 := fun h => hne (by simp [cutoffZ, h])
  exact (cutBump_norm_lt this).le

theorem cutoffZ_sq_supBdd : SupBdd 3 (fun _ y => cutoffZ y ^ 2) := fun t y hne =>
  cutoffZ_supBdd t y fun h => hne (by simp [h])

theorem perX_cutoffZ_sq (x : Vec 2) : perX (fun y => cutoffZ y ^ 2) x = 1 := by
  set S := perX fun y => (cutBump : Vec 2 → ℝ) y ^ 2 with hS
  have hSpos : 0 < S x := by
    have := perX_cutBump_ge_one x
    linarith
  have hSper : ∀ n, S (x + latticeShift n) = S x := fun n => perX_periodic _ n x
  have h1 : (fun n : Fin 2 → ℤ => cutoffZ (x + latticeShift n) ^ 2) =
      fun n => (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2 / S x := by
    funext n
    simp only [cutoffZ, div_pow]
    rw [Real.sq_sqrt (by linarith [perX_cutBump_ge_one (x + latticeShift n)])]
    exact congrArg _ (hSper n)
  unfold perX perST
  simp only [h1]
  have h2 : ∑ᶠ n : Fin 2 → ℤ, (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2 / S x =
      (∑ᶠ n : Fin 2 → ℤ, (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2) / S x := by
    obtain ⟨M, hM⟩ := exists_nat_ge_add (3 : ℝ) ‖x‖
    have hsupp : Function.support (fun n : Fin 2 → ℤ =>
        (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2) ⊆ ↑(latBox M) := by
      intro n hn
      have hne : (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2 ≠ 0 := hn
      exact mem_latBox_of_norm_le hM le_rfl (cutBump_supBdd 0 _ (by simpa using hne))
    rw [finsum_eq_sum_of_support_subset _ hsupp, finsum_eq_sum_of_support_subset _ (by
      intro n hn
      apply hsupp
      intro h
      apply hn
      simp [h]), Finset.sum_div]
  rw [h2]
  have h3 : (∑ᶠ n : Fin 2 → ℤ, (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2) = S x := rfl
  rw [h3, div_self hSpos.ne']

/-! # Unfolding space-time integrals of periodic functions

For `G` that is `ℤ²`-periodic in space (for a.e. `t ∈ S`) and integrable on `S × (0,1)²`, and
`ρ` bounded, measurable, supported in `{‖x‖ ≤ R}`:
`∬_{S × ℝ²} G ρ = ∬_{S × (0,1)²} G ρ^per`. -/

theorem ae_periodic_prod {S : Set ℝ} {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t)) (A : Set (Vec 2)) :
    ∀ᵐ p ∂(volume.restrict (S ×ˢ A) : Measure (ℝ × Vec 2)), IsZ2Periodic (G p.1) := by
  have h1 : (volume.restrict (S ×ˢ A) : Measure (ℝ × Vec 2)) =
      (volume.restrict S).prod (volume.restrict A) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [h1]
  exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict S)
    (ν := volume.restrict A)).ae hper

theorem measurableEmbedding_trans (n : Fin 2 → ℤ) : MeasurableEmbedding (trans n) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight (latticeShift n))).measurableEmbedding

theorem integrableOn_cellAt {S : Set ℝ} (hS : MeasurableSet S) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ cellI)))
    (n : Fin 2 → ℤ) :
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ cellAt n)) := by
  have hmp := measurePreserving_trans_restrict n hS
  rw [← hmp.integrable_comp_emb (measurableEmbedding_trans n)]
  refine hG.congr ?_
  filter_upwards [ae_periodic_prod hper cellI] with p hp
  simp [trans, hp n p.2]

/-- **Unfolding.** -/
theorem integral_unfold {S : Set ℝ} (hS : MeasurableSet S) {R : ℝ} {G ρ : ℝ → Vec 2 → ℝ}
    (hρ : SupBdd R ρ) (hρm : Measurable (fun p : ℝ × Vec 2 => ρ p.1 p.2))
    (hρb : ∃ B : ℝ, ∀ t x, |ρ t x| ≤ B)
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ unitCube))) :
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * ρ p.1 p.2) (volume.restrict (S ×ˢ Set.univ)) ∧
    ∫ p in S ×ˢ Set.univ, G p.1 p.2 * ρ p.1 p.2 =
      ∫ p in S ×ˢ unitCube, G p.1 p.2 * perST ρ p.1 p.2 := by
  obtain ⟨B, hB⟩ := hρb
  obtain ⟨M, hM⟩ := exists_nat_ge_add R 1
  have hG' : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ cellI)) := by
    rwa [restrict_prod_cellI_eq_unitCube]
  set F : ℝ × Vec 2 → ℝ := fun p => G p.1 p.2 * ρ p.1 p.2 with hF
  -- the translated product on the base cell
  have hH : ∀ n : Fin 2 → ℤ, Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * ρ p.1 (p.2 + latticeShift n))
      (volume.restrict (S ×ˢ cellI)) := by
    intro n
    have hm : Measurable (fun p : ℝ × Vec 2 => ρ p.1 (p.2 + latticeShift n)) :=
      hρm.comp (measurable_fst.prodMk (measurable_snd.add_const _))
    exact hG'.mul_bdd hm.aestronglyMeasurable (c := B)
      (Eventually.of_forall fun p => by simpa using hB _ _)
  have hFtrans : ∀ n : Fin 2 → ℤ, (F ∘ trans n) =ᵐ[volume.restrict (S ×ˢ cellI)]
      fun p : ℝ × Vec 2 => G p.1 p.2 * ρ p.1 (p.2 + latticeShift n) := by
    intro n
    filter_upwards [ae_periodic_prod hper cellI] with p hp
    simp [hF, trans, hp n p.2]
  have hFint : ∀ n : Fin 2 → ℤ, IntegrableOn F (S ×ˢ cellAt n) := by
    intro n
    have hmp := measurePreserving_trans_restrict n hS
    unfold IntegrableOn
    rw [← hmp.integrable_comp_emb (measurableEmbedding_trans n)]
    exact (hH n).congr (hFtrans n).symm
  have hbox : (S ×ˢ (⋃ n ∈ latBox M, cellAt n) : Set (ℝ × Vec 2)) =
      ⋃ n ∈ latBox M, S ×ˢ cellAt n := by
    ext ⟨t, x⟩
    simp only [Set.mem_prod, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ht, n, hn, hx⟩; exact ⟨n, hn, ht, hx⟩
    · rintro ⟨n, hn, ht, hx⟩; exact ⟨ht, n, hn, hx⟩
  have hUint : IntegrableOn F (S ×ˢ ⋃ n ∈ latBox M, cellAt n) := by
    rw [hbox]; exact integrableOn_finset_iUnion.2 fun n _ => hFint n
  have hmeasU : MeasurableSet (⋃ n ∈ latBox M, cellAt n) :=
    (latBox M).measurableSet_biUnion fun n _ => measurableSet_cellAt n
  have hzero : ∀ p ∈ (S ×ˢ Set.univ : Set (ℝ × Vec 2)) \ (S ×ˢ ⋃ n ∈ latBox M, cellAt n),
      F p = 0 := by
    rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hn⟩
    have hx : x ∉ supBall R := fun hx =>
      hn ⟨ht, supBall_subset_iUnion_cellAt (by linarith) hx⟩
    have : ρ t x = 0 := by
      by_contra h
      exact hx (hρ t x h)
    simp [hF, this]
  have hsub : (S ×ˢ ⋃ n ∈ latBox M, cellAt n : Set (ℝ × Vec 2)) ⊆ S ×ˢ Set.univ :=
    Set.prod_mono le_rfl (Set.subset_univ _)
  refine ⟨hUint.of_forall_sdiff_eq_zero (hS.prod MeasurableSet.univ) hzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hS.prod MeasurableSet.univ) hsub hzero,
    hbox, integral_biUnion_finset (latBox M) (fun n _ => hS.prod (measurableSet_cellAt n))
      (fun n _ m _ hnm => Set.disjoint_left.2 fun p hp1 hp2 =>
        Set.disjoint_left.1 (cellAt_disjoint hnm) hp1.2 hp2.2) (fun n _ => hFint n)]
  have hterm : ∀ n : Fin 2 → ℤ, ∫ p in S ×ˢ cellAt n, F p =
      ∫ p in S ×ˢ cellI, G p.1 p.2 * ρ p.1 (p.2 + latticeShift n) := by
    intro n
    have hmp := measurePreserving_trans_restrict n hS
    rw [← hmp.integral_comp (measurableEmbedding_trans n) F]
    exact integral_congr_ae (hFtrans n)
  simp_rw [hterm]
  rw [← integral_finsetSum _ (fun n _ => hH n), ← restrict_prod_cellI_eq_unitCube]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (hS.prod measurableSet_cellI)] with p hp
  have hx1 : ‖p.2‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have := hp.2 i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  rw [perST_eq_sum hM hρ p.1 hx1, Finset.mul_sum]

theorem aestronglyMeasurable_of_cell {S : Set ℝ} (hS : MeasurableSet S) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : AEStronglyMeasurable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ Set.univ)) := by
  have hG' : AEStronglyMeasurable (fun p : ℝ × Vec 2 => G p.1 p.2)
      (volume.restrict (S ×ˢ cellI)) := by
    rwa [restrict_prod_cellI_eq_unitCube]
  have hU : (S ×ˢ Set.univ : Set (ℝ × Vec 2)) = ⋃ n : Fin 2 → ℤ, S ×ˢ cellAt n := by
    ext ⟨t, x⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_iUnion]
    constructor
    · intro ht; exact ⟨fun i => ⌊x i⌋, ht, mem_cellAt_floor x⟩
    · rintro ⟨n, ht, -⟩; exact ht
  rw [hU, aestronglyMeasurable_iUnion_iff]
  intro n
  have hmp := measurePreserving_trans_restrict n hS
  rw [← hmp.map_eq, (measurableEmbedding_trans n).aestronglyMeasurable_map_iff]
  refine hG'.congr ?_
  filter_upwards [ae_periodic_prod hper cellI] with p hp
  simp [Function.comp, trans, hp n p.2]

theorem integrableOn_supBall_of_cell {S : Set ℝ} (hS : MeasurableSet S) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ unitCube)))
    (R : ℝ) :
    IntegrableOn (fun p : ℝ × Vec 2 => G p.1 p.2) (S ×ˢ supBall R) := by
  obtain ⟨M, hM⟩ := exists_nat_ge_add R 1
  have hG' : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ cellI)) := by
    rwa [restrict_prod_cellI_eq_unitCube]
  have hbox : (S ×ˢ (⋃ n ∈ latBox M, cellAt n) : Set (ℝ × Vec 2)) =
      ⋃ n ∈ latBox M, S ×ˢ cellAt n := by
    ext ⟨t, x⟩
    simp only [Set.mem_prod, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨ht, n, hn, hx⟩; exact ⟨n, hn, ht, hx⟩
    · rintro ⟨n, hn, ht, hx⟩; exact ⟨ht, n, hn, hx⟩
  have hU : IntegrableOn (fun p : ℝ × Vec 2 => G p.1 p.2)
      (S ×ˢ ⋃ n ∈ latBox M, cellAt n) := by
    rw [hbox]
    exact integrableOn_finset_iUnion.2 fun n _ => integrableOn_cellAt hS hper hG' n
  exact hU.mono_set (Set.prod_mono le_rfl (supBall_subset_iUnion_cellAt (by linarith)))

theorem memLp_two_supBall_of_cell {S : Set ℝ} (hS : MeasurableSet S) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : MemLp (fun p : ℝ × Vec 2 => G p.1 p.2) 2 (volume.restrict (S ×ˢ unitCube)))
    (R : ℝ) :
    MemLp (fun p : ℝ × Vec 2 => G p.1 p.2) 2 (volume.restrict (S ×ˢ supBall R)) := by
  have hm := aestronglyMeasurable_of_cell hS hper hG.aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun p : ℝ × Vec 2 => G p.1 p.2)
      (volume.restrict (S ×ˢ supBall R)) :=
    hm.mono_measure (Measure.restrict_mono (Set.prod_mono le_rfl (Set.subset_univ _)) le_rfl)
  rw [memLp_two_iff_integrable_sq hm']
  have hsq : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 ^ 2) (volume.restrict (S ×ˢ unitCube)) :=
    hG.integrable_sq
  exact integrableOn_supBall_of_cell hS (G := fun t x => G t x ^ 2)
    (hper.mono fun t ht k x => by simp [ht k x]) hsq R

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Weak solutions on windows with the gradient field explicit

`IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ` is the body of the existential in `IsWeakSolutionOn`,
so `IsWeakSolutionOn` is, by definition, the existence of such a `Dθ`. The explicit
form is the one the energy tools consume, since the dissipation integral involves `Dθ`. -/

/-- `IsWeakSolutionOn` with the gradient field `Dθ` as a parameter. -/
def IsWeakSolutionOnWith (b : ℝ → Vec 2 → Vec 2) (κ t₁ t₂ : ℝ) (f : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
    (∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ C) ∧
    MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsPeriodicH1With (θ t) (Dθ t)) ∧
    Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc t₁ t₂)) ∧
    (∀ φ : ℝ → Vec 2 → ℝ, IsWindowTestFunction t₂ φ →
      ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
        = ∫ x in unitCube, f x * φ t₁ x)

end AVRegularity.Applications
end

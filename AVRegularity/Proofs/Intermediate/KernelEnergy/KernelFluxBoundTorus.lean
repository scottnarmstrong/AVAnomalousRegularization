-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionPlane
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.KernelEnergy.PlaneFluxTerm
import AVRegularity.KernelEnergy.TorusFactorialReadout
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

section
/-! Order consistency of the kernel-regularized system. A solution at order `k'`,
truncated, is a solution at every lower order `k ≤ k'`; with uniqueness at order `k` this identifies
it with the order-`k` solution. No analytic premises are needed. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers

private theorem truncate_valueIndex {m n : ℕ} (hmn : m ≤ n) :
    truncateJetIndex hmn (valueIndex2 m) = valueIndex2 n := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · simp [truncateJetIndex, valueIndex2, valueIndex]

private theorem truncate_index_same {m n : ℕ} (hmn : m ≤ n)
    (a : JetIndex2 m) :
    truncateJetIndex hmn a = ⟨⟨a.1.val, by omega⟩, a.2⟩ := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · rfl

private theorem truncatePlane_toFunction_jet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {m n : ℕ} (hmn : m ≤ n)
    (f : PlaneHk Set.univ n E) (a : JetIndex2 m) :
    (truncatePlaneHk hmn f).toFunction.jet a =
      f.toFunction.jet (truncateJetIndex hmn a) := by
  rfl

private theorem truncatePlane_toFunction_value {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {m n : ℕ} (hmn : m ≤ n) (f : PlaneHk Set.univ n E) :
    (truncatePlaneHk hmn f).toFunction.jet (valueIndex2 m) =
      f.toFunction.jet (valueIndex2 n) := by
  rw [truncatePlane_toFunction_jet, truncate_valueIndex]

private theorem truncatePlane_toFunction_sameIndex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {m n : ℕ} (hmn : m ≤ n) (f : PlaneHk Set.univ n E) (a : JetIndex2 m) :
    (truncatePlaneHk hmn f).toFunction.jet a =
      f.toFunction.jet ⟨⟨a.1.val, by omega⟩, a.2⟩ := by
  rw [truncatePlane_toFunction_jet]
  rfl

/-- Truncation of an order-`k'` kernel-regularized solution is an order-`k` solution. -/
theorem kernel_solution_truncate_plane (t₀ t₁ ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (k k' D : ℕ) (hkk' : k ≤ k')
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2)))) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict (Set.univ : Set (Vec 2)))))
    (f : ∀ i, PlaneHk Set.univ k' (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ k' (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ k' (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ k' (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (k' + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k' + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionPlane ν t₀ t₁ v k' D B C S f F g u w y) :
    IsKernelWeakSolutionPlane ν t₀ t₁ v k D B C S
      (fun i => truncatePlaneHk hkk' (f i))
      (fun i s => truncatePlaneHk hkk' (F i s))
      (fun i s => truncatePlaneHk hkk' (g i s))
      (fun i s => truncatePlaneHk hkk' (u i s))
      (fun i s => truncatePlaneHk (Nat.succ_le_succ hkk') (w i s))
      (fun i j α s => truncatePlaneHk (by omega) (y i j α s)) :=
by
  classical
  rcases hsol with ⟨hu, hw, htrace, hinit, hyMem, hyValue, hweak⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (truncatePlaneHk hkk').continuous.comp_continuousOn (hu i)
  · intro i
    exact (truncatePlaneHk (Nat.succ_le_succ hkk')).comp_memLp' (hw i)
  · intro i
    filter_upwards [htrace i] with s hs
    apply PlaneHk.ext_value isOpen_univ
    have hs' := congrArg (fun z : PlaneHk Set.univ k' (h i) =>
      z.val (truncateJetIndex hkk' (valueIndex2 k))) hs
    simpa [truncatePlaneHk_apply, truncate_valueIndex, truncate_index_same] using hs'
  · intro i
    exact congrArg (truncatePlaneHk hkk') (hinit i)
  · intro i j α
    exact (truncatePlaneHk (by omega : k + D - 1 ≤ k' + D - 1)).comp_memLp'
      (hyMem i j α)
  · intro i j α
    have hycut : k + D - 1 ≤ k' + D - 1 := by omega
    have hwcut : k + 1 ≤ k' + 1 := Nat.add_le_add_right hkk' 1
    have hyidx := truncate_valueIndex hycut
    have hwidx := truncate_valueIndex hwcut
    filter_upwards [hyValue i j α] with s hs
    simpa only [truncatePlaneHk_apply, hyidx, hwidx] using hs
  · intro i t ht φ
    have hs := hweak i t ht φ
    have hcutW : k + 1 ≤ k' + 1 := Nat.add_le_add_right hkk' 1
    have hcutY : k + D - 1 ≤ k' + D - 1 := by omega
    have hu : (truncatePlaneHk hkk' (u i t)).toFunction.jet (valueIndex2 k) =
        (u i t).toFunction.jet (valueIndex2 k') := truncatePlane_toFunction_value hkk' _
    have hf : (truncatePlaneHk hkk' (f i)).toFunction.jet (valueIndex2 k) =
        (f i).toFunction.jet (valueIndex2 k') := truncatePlane_toFunction_value hkk' _
    have hF (s : ℝ) : (truncatePlaneHk hkk' (F i s)).toFunction.jet (valueIndex2 k) =
        (F i s).toFunction.jet (valueIndex2 k') := truncatePlane_toFunction_value hkk' _
    have hg (s : ℝ) : (truncatePlaneHk hkk' (g i s)).toFunction.jet (valueIndex2 k) =
        (g i s).toFunction.jet (valueIndex2 k') := truncatePlane_toFunction_value hkk' _
    have hw' (s : ℝ) (m : Fin 2) :
        (truncatePlaneHk (Nat.succ_le_succ hkk') (w i s)).toFunction.jet
            ⟨⟨1, by omega⟩, fun _ => m⟩ =
          (w i s).toFunction.jet ⟨⟨1, by omega⟩, fun _ => m⟩ :=
      truncatePlane_toFunction_sameIndex hcutW _ _
    have hy' (j : ι) (α : Γ i j) (s : ℝ) (d : ↥(Finset.Icc 2 D))
        (a : DerivativeWord2 (d.1 - 1)) :
        (truncatePlaneHk hcutY (y i j α s)).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, a⟩ =
          (y i j α s).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, a⟩ :=
      truncatePlane_toFunction_sameIndex hcutY _ _
    simpa only [hu, hf, hF, hg, hw', hy'] using hs

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.KernelEnergy
namespace AVRegularity.Providers

private theorem castJetIndex_truncate {L H J r : ℕ} (hLH : L = H) (hJL : J ≤ L)
    (hrH : r < H + 1) (hrJ : r < J + 1) (word : DerivativeWord2 r) :
    cast (congrArg JetIndex2 hLH.symm) (⟨⟨r, hrH⟩, word⟩ : JetIndex2 H) =
      truncateJetIndex hJL (⟨⟨r, hrJ⟩, word⟩ : JetIndex2 J) := by
  cases hLH
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · rfl

private theorem schurRootProduct (pii pij z : ℝ) (hpii : 0 < pii) (hpij : 0 < pij) :
    Real.sqrt (pij / pii) * Real.sqrt (pij⁻¹ * z) =
      Real.sqrt (pii⁻¹) * Real.sqrt z := by
  have hratio : (pij / pii) * (pij⁻¹ * z) = pii⁻¹ * z := by
    field_simp [ne_of_gt hpii, ne_of_gt hpij]
  rw [← Real.sqrt_mul (div_nonneg hpij.le hpii.le) (pij⁻¹ * z), hratio,
    Real.sqrt_mul (inv_nonneg.mpr hpii.le) z]

private theorem schurRootScale (pii pij ν s c p n z : ℝ)
    (hpii : 0 < pii) (hpij : 0 < pij) (hν : 0 < ν) (hp : 0 < p) :
    Real.sqrt (pii⁻¹) * s * (c / p) * n * Real.sqrt z =
      ν * (Real.sqrt (pij / pii) * n * (s * c / (ν * p))) *
        Real.sqrt (pij⁻¹ * z) := by
  have hroot := schurRootProduct pii pij z hpii hpij
  calc
    Real.sqrt (pii⁻¹) * s * (c / p) * n * Real.sqrt z =
        ν * (Real.sqrt (pii⁻¹) * Real.sqrt z) * n * (s * c / (ν * p)) := by
          field_simp [ne_of_gt hν, ne_of_gt hp]
    _ = ν * (Real.sqrt (pij / pii) * Real.sqrt (pij⁻¹ * z)) * n *
        (s * c / (ν * p)) := by rw [← hroot]
    _ = ν * (Real.sqrt (pij / pii) * n * (s * c / (ν * p))) *
        Real.sqrt (pij⁻¹ * z) := by ring

private theorem torusHk_sum_value {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (f : α → TorusHk K E) (a : JetIndex2 K) :
    ((∑ i, f i : TorusHk K E).val).ofLp a =
      ∑ i, ((f i).val).ofLp a := by
  change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : JetIndex2 K =>
      Lp E 2 (volume.restrict AVenhance.unitCube)) a)
      ((torusHkGraph (E := E) K).toSubmodule.subtype (∑ i, f i)) = _
  rw [map_sum]
  rw [map_sum]
  rfl

private theorem kernelFluxMassSchur
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
    [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]
    {μ : Measure (Vec 2)} (ρ ν θ : ℝ) (hν : 0 < ν) (k D : ℕ)
    (t₀ t₁ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => E i)))
    (C : ∀ i j (α : Γ i j), E j →L[ℝ] G i j α)
    (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ) (hr : ∀ i j α, 0 < r i j α)
    (hc : ∀ (i j : ι) (_α : Γ i j) (m : ℕ), m + 2 ≤ D → 0 ≤ c m)
    (A : ∀ i, JetL2 μ k (PiLp 2 (fun _ : Fin 2 => E i)))
    (V : ∀ j, JetL2 μ (k + 1) (E j))
    (T : ∀ i j (_α : Γ i j) (_d : ↥(Finset.Icc 2 D)),
      JetL2 μ k (PiLp 2 (fun _ : Fin 2 => E i)))
    (hA : ∀ i, A i = ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)
    (hTerm : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)),
      Real.sqrt (factorialNormSq ρ (T i j α d)) ≤
        (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
          (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
            Real.sqrt (gradFactorialNormSq ρ (V j)))
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B)) :
    massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => E i)) (K := fun _ => k)
        ρ π A ≤ (ν * θ) ^ 2 * massGradNormSq (E := E) (K := fun _ => k) ρ π V := by
  classical
  let b : ι → ι → ℝ := kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B
  let x (j : ι) : ℝ := Real.sqrt ((π j)⁻¹ * gradFactorialNormSq ρ (V j))
  let y (i : ι) : ℝ := Real.sqrt ((π i)⁻¹ * factorialNormSq ρ (A i))
  let σ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : ℝ :=
    (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal
  let q (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : ℝ :=
    σ i j α d * c (d.1 - 2) / (ν * r i j α ^ (d.1 - 2))
  have hGradNonneg (j : ι) : 0 ≤ gradFactorialNormSq ρ (V j) := by
    unfold gradFactorialNormSq
    apply Finset.sum_nonneg
    intro n _
    apply mul_nonneg (factorialWeight_nonneg ρ n.val)
    apply Finset.sum_nonneg
    intro word _
    exact sq_nonneg _
  have hschur' : SchurBound θ b := by simpa only [b] using hschur
  rcases hschur' with ⟨hrow, hcol⟩
  have hb (i j : ι) : 0 ≤ b i j := by
    change 0 ≤ Real.sqrt (π j / π i) *
      ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro α _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro d _
    have hd := Finset.mem_Icc.1 d.2
    have hs : 0 ≤ σ i j α d := by dsimp [σ]; exact ENNReal.toReal_nonneg
    have hc' : 0 ≤ c (d.1 - 2) := hc i j α (d.1 - 2) (by omega)
    have hden : 0 < ν * r i j α ^ (d.1 - 2) :=
      mul_pos hν (pow_pos (hr i j α) _)
    exact div_nonneg (mul_nonneg hs hc') hden.le
  have hroot (i : ι) :
      Real.sqrt (factorialNormSq ρ (A i)) ≤
        ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
            (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
              Real.sqrt (gradFactorialNormSq ρ (V j)) := by
    calc
      _ = Real.sqrt (factorialNormSq ρ
            (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)) := by rw [hA i]
      _ ≤ ∑ j : ι, Real.sqrt (factorialNormSq ρ
            (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)) :=
        factorialNorm_root_sum_le ρ (Finset.univ : Finset ι)
          (fun j => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, Real.sqrt (factorialNormSq ρ
            (∑ d : ↥(Finset.Icc 2 D), T i j α d)) := by
        apply Finset.sum_le_sum
        intro j _
        exact factorialNorm_root_sum_le ρ (Finset.univ : Finset (Γ i j))
          (fun α => ∑ d : ↥(Finset.Icc 2 D), T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            Real.sqrt (factorialNormSq ρ (T i j α d)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro α _
        exact factorialNorm_root_sum_le ρ (Finset.univ : Finset (↥(Finset.Icc 2 D)))
          (fun d => T i j α d)
      _ ≤ ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                Real.sqrt (gradFactorialNormSq ρ (V j)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro α _
        apply Finset.sum_le_sum
        intro d _
        exact hTerm i j α d
  have hscale (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      Real.sqrt ((π i)⁻¹) * σ i j α d *
          (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
          Real.sqrt (gradFactorialNormSq ρ (V j)) =
        ν * (Real.sqrt (π j / π i) * ‖C i j α‖ * q i j α d) * x j := by
    dsimp only [x, σ, q]
    exact schurRootScale (π i) (π j) ν (coefficientSeminorm ρ k t₀ t₁
      (B i j α d)).toReal (c (d.1 - 2)) (r i j α ^ (d.1 - 2))
      ‖C i j α‖ (gradFactorialNormSq ρ (V j)) (hπ i) (hπ j) hν
      (pow_pos (hr i j α) _)
  have hpair (i j : ι) :
      Real.sqrt ((π i)⁻¹) *
          (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                Real.sqrt (gradFactorialNormSq ρ (V j))) = ν * b i j * x j := by
    calc
      _ = ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            Real.sqrt ((π i)⁻¹) * σ i j α d *
              (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
              Real.sqrt (gradFactorialNormSq ρ (V j)) := by
        simp_rw [Finset.mul_sum]
        dsimp only [σ]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            ν * (Real.sqrt (π j / π i) * ‖C i j α‖ * q i j α d) * x j := by
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro d _
        exact hscale i j α d
      _ = ν * (Real.sqrt (π j / π i) *
            ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d) * x j := by
        calc
          _ = ∑ α : Γ i j, (ν * Real.sqrt (π j / π i) * x j * ‖C i j α‖) *
                ∑ d : ↥(Finset.Icc 2 D), q i j α d := by
            apply Finset.sum_congr rfl
            intro α _
            calc
              _ = ∑ d : ↥(Finset.Icc 2 D),
                    (ν * Real.sqrt (π j / π i) * x j * ‖C i j α‖) * q i j α d := by
                apply Finset.sum_congr rfl
                intro d _
                ring
              _ = _ := by rw [Finset.mul_sum]
          _ = (ν * Real.sqrt (π j / π i) * x j) *
                ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D), q i j α d := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro α _
            ring
          _ = _ := by ring
      _ = ν * b i j * x j := by dsimp only [b, kernelSchurMatrix, q, σ]
  have hyBound (i : ι) : 0 ≤ y i ∧ y i ≤ ν * ∑ j : ι, b i j * x j := by
    constructor
    · exact Real.sqrt_nonneg _
    · have hInv : 0 ≤ (π i)⁻¹ := inv_nonneg.mpr (hπ i).le
      have hsplit : y i = Real.sqrt ((π i)⁻¹) * Real.sqrt (factorialNormSq ρ (A i)) := by
        dsimp [y]
        rw [Real.sqrt_mul hInv (factorialNormSq ρ (A i))]
      rw [hsplit]
      calc
        Real.sqrt ((π i)⁻¹) * Real.sqrt (factorialNormSq ρ (A i)) ≤
            Real.sqrt ((π i)⁻¹) *
              ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
                (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
                  (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
                    Real.sqrt (gradFactorialNormSq ρ (V j)) :=
          mul_le_mul_of_nonneg_left (hroot i) (Real.sqrt_nonneg _)
        _ = ∑ j : ι, ν * b i j * x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact hpair i j
        _ = ν * ∑ j : ι, b i j * x j := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  have hfinite := AVRegularity.KernelEnergy.finiteRootSchur b x y ν θ hν
    hb hrow hcol hyBound
  have hxSq : (∑ j : ι, x j ^ 2) = massGradNormSq (E := E) (K := fun _ => k) ρ π V := by
    unfold x massGradNormSq
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ j).le) (hGradNonneg j))]
  have hySq : (∑ i : ι, y i ^ 2) = massNormSq
      (E := fun i => PiLp 2 (fun _ : Fin 2 => E i)) (K := fun _ => k) ρ π A := by
    unfold y massNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ i).le)
      (factorialNormSq_nonneg ρ (A i)))]
  rw [← hySq]
  calc
    (∑ i : ι, y i ^ 2) ≤ (ν * θ) ^ 2 * ∑ j : ι, x j ^ 2 := hfinite
    _ = (ν * θ) ^ 2 * massGradNormSq (E := E) (K := fun _ => k) ρ π V := by rw [hxSq]

/-- **Kernel flux bound** on the torus: the source term (Lemma 7.4 of the paper). -/
theorem kernel_flux_bound_torus (t₀ t₁ : ℝ) (_ht : t₀ ≤ t₁) (ρ : ℝ) (hρ : 0 < ρ)
    (ν : ℝ) (hν : 0 < ν) (k : ℕ)
    (D : ℕ) (hD : 2 ≤ D)
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (_hB_meas : ∀ i j α d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 =>
      B i j α d p.1 p.2)
    (hB_smooth : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (B i j α d t))
    (hB_per : ∀ i j α d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (B i j α d t))
    (hB_fin : ∀ i j α d, coefficientSeminorm ρ k t₀ t₁ (B i j α d) ≠ ⊤)
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ →
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ) (hr : ∀ i j α, 0 < r i j α)
    (hS : ∀ i j α, IsSpatialRegularizerTorus ρ k D t₀ t₁ c (r i j α) (S i j α))
    (θ : ℝ) (_hθ : θ ≤ 1 / 8)
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B))
    (t : ℝ) (ht_mem : t ∈ Set.Icc t₀ t₁)
    (V : ∀ i, TorusHk (k + 1) (h i)) :
    ∃ (Y : ∀ i j (α : Γ i j), TorusHk (k + D - 1) (G i j α))
      (A : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))),
      (∀ i j α, (Y i j α).val (valueIndex2 (k + D - 1)) =
          S i j α t ((C i j α).compLp ((V j).val (valueIndex2 (k + 1))))) ∧
      (∀ i, (A i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y i j α).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)) ∧
      massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => k) ρ π
          (fun i => (A i).val)
        ≤ (ν * θ) ^ 2 * massGradNormSq (E := h) (K := fun _ => k) ρ π
          (fun i => (V i).val) := by
  classical
  let highBase : ℕ := k + (D - 2) + 1
  have hOrder : highBase = k + D - 1 := by dsimp [highBase]; omega
  have hLift : ∀ i j α, ∃ Y : TorusHk highBase (G i j α),
      Y.val (valueIndex2 highBase) = S i j α t
        ((C i j α).compLpL 2 (volume.restrict AVenhance.unitCube)
          ((V j).val (valueIndex2 (k + 1)))) ∧
      ∀ q m, (hm : m + 2 ≤ D) → ∃ Z : TorusHk (k + m) (G i j α),
        Z.val (valueIndex2 (k + m)) = S i j α t
          ((C i j α).compLpL 2 (volume.restrict AVenhance.unitCube)
            ((derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) (V j)).val
              (valueIndex2 k))) ∧
        derivFactorialNormSq m ρ Z.val ≤ (c m / r i j α ^ m) ^ 2 *
          factorialNormSq ρ ((mapTorusHk (C i j α)
            (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) (V j))).val) ∧
        truncateTorusHk (by omega : k + m ≤ k + (D - 2))
          (derivativeTorusHk (K := k + (D - 2)) (r := 1) (fun _ : Fin 1 => q) Y) = Z := by
    intro i j α
    simpa [highBase] using torusRegularizerLift ρ k D hD t₀ t₁ t ht_mem c
      (r i j α) (C i j α) (S i j α) (hS i j α) (V j)
  choose Ybase hYbase hLiftGrad using hLift
  let Y : ∀ i j (α : Γ i j), TorusHk (k + D - 1) (G i j α) :=
    fun i j α => castTorusHk hOrder (Ybase i j α)
  let lowJet (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      TorusHk (k + ((d.1 - 2) + 1)) (G i j α) :=
    truncateTorusHk (by have := Finset.mem_Icc.1 d.2; dsimp [highBase]; omega)
      (Ybase i j α)
  let term (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :=
    torusKernelFluxTerm (K := k) (m := d.1 - 2) (r := d.1 - 1)
      (by have := Finset.mem_Icc.1 d.2; omega) ρ hρ t₀ t₁
      (B i j α d) (hB_fin i j α d) t ht_mem (hB_smooth i j α d t ht_mem)
      (hB_per i j α d t ht_mem) (lowJet i j α d)
  let A : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
    fun i => ∑ j, ∑ α, ∑ d, term i j α d
  have hTermRoot (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      Real.sqrt (factorialNormSq ρ (term i j α d).val) ≤
        (coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal *
          (c (d.1 - 2) / r i j α ^ (d.1 - 2)) * ‖C i j α‖ *
            Real.sqrt (gradFactorialNormSq ρ (V j).val) := by
    have hd := Finset.mem_Icc.1 d.2
    let m := d.1 - 2
    have hm : m + 2 ≤ D := by dsimp [m]; omega
    have hKL : k + m ≤ k + (D - 2) := by dsimp [m]; omega
    have hZex : ∀ q : Fin 2, ∃ Z : TorusHk (k + m) (G i j α),
        derivFactorialNormSq m ρ Z.val ≤
          (c m / r i j α ^ m) ^ 2 * factorialNormSq ρ
            ((mapTorusHk (C i j α)
              (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) (V j))).val) ∧
        truncateTorusHk hKL
          (derivativeTorusHk (K := k + (D - 2)) (r := 1)
            (fun _ : Fin 1 => q) (Ybase i j α)) = Z := by
      intro q
      obtain ⟨Z, _, hZnorm, hZtrunc⟩ := hLiftGrad i j α q m hm
      exact ⟨Z, hZnorm, hZtrunc⟩
    choose Z hZnorm hZtrunc using hZex
    have hderiv (q : Fin 2) :
        derivativeTorusHk (K := k + m) (r := 1) (fun _ : Fin 1 => q)
            (lowJet i j α d) = Z q := by
      have hcomm := truncateTorus_derivative_commute hKL (Ybase i j α) q
      simpa [lowJet, m] using hcomm.trans (hZtrunc q)
    have hshift := torusDerivFactorialNormSq_succ ρ (lowJet i j α d) Z hderiv
    have hc : 0 ≤ c m := (hS i j α).2.2.1 m hm
    have hγ : 0 ≤ c m / r i j α ^ m :=
      div_nonneg hc (pow_nonneg (hr i j α).le _)
    have hmapSum :
        (∑ q : Fin 2, factorialNormSq ρ
          ((mapTorusHk (C i j α)
            (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) (V j))).val)) ≤
        ‖C i j α‖ ^ 2 * gradFactorialNormSq ρ (V j).val := by
      calc
        _ ≤ ∑ q : Fin 2, ‖C i j α‖ ^ 2 * factorialNormSq ρ
            ((derivativeTorusHk (K := k) (r := 1)
              (fun _ : Fin 1 => q) (V j)).val) := by
          apply Finset.sum_le_sum
          intro q _
          exact mapTorusHk_factorialNormSq_le ρ (C i j α)
            (derivativeTorusHk (K := k) (r := 1) (fun _ : Fin 1 => q) (V j))
        _ = ‖C i j α‖ ^ 2 * ∑ q : Fin 2, factorialNormSq ρ
            ((derivativeTorusHk (K := k) (r := 1)
              (fun _ : Fin 1 => q) (V j)).val) := by rw [← Finset.mul_sum]
        _ = ‖C i j α‖ ^ 2 * gradFactorialNormSq ρ (V j).val := by
          rw [torusGradientFactorialNormSq]
    have hYbound : derivFactorialNormSq (m + 1) ρ (lowJet i j α d).val ≤
        (c m / r i j α ^ m) ^ 2 * ‖C i j α‖ ^ 2 *
          gradFactorialNormSq ρ (V j).val := by
      rw [hshift]
      calc
        (∑ q : Fin 2, derivFactorialNormSq m ρ (Z q).val) ≤
            ∑ q : Fin 2, (c m / r i j α ^ m) ^ 2 *
              ‖C i j α‖ ^ 2 * factorialNormSq ρ
                ((derivativeTorusHk (K := k) (r := 1)
                  (fun _ : Fin 1 => q) (V j)).val) := by
          apply Finset.sum_le_sum
          intro q _
          calc
            derivFactorialNormSq m ρ (Z q).val ≤
                (c m / r i j α ^ m) ^ 2 * factorialNormSq ρ
                  ((mapTorusHk (C i j α)
                    (derivativeTorusHk (K := k) (r := 1)
                      (fun _ : Fin 1 => q) (V j))).val) := hZnorm q
            _ ≤ (c m / r i j α ^ m) ^ 2 *
                (‖C i j α‖ ^ 2 * factorialNormSq ρ
                  ((derivativeTorusHk (K := k) (r := 1)
                    (fun _ : Fin 1 => q) (V j)).val)) :=
              mul_le_mul_of_nonneg_left
                (mapTorusHk_factorialNormSq_le ρ (C i j α)
                  (derivativeTorusHk (K := k) (r := 1)
                    (fun _ : Fin 1 => q) (V j))) (sq_nonneg _)
            _ = _ := by ring
        _ = (c m / r i j α ^ m) ^ 2 * ‖C i j α‖ ^ 2 *
            (∑ q : Fin 2, factorialNormSq ρ
              ((derivativeTorusHk (K := k) (r := 1)
                (fun _ : Fin 1 => q) (V j)).val)) := by
          simp_rw [Finset.mul_sum]
        _ = (c m / r i j α ^ m) ^ 2 * ‖C i j α‖ ^ 2 *
            gradFactorialNormSq ρ (V j).val := by rw [torusGradientFactorialNormSq]
    have hCnonneg : 0 ≤ ‖C i j α‖ := norm_nonneg _
    have hgradNonneg : 0 ≤ gradFactorialNormSq ρ (V j).val := by
      unfold gradFactorialNormSq
      apply Finset.sum_nonneg
      intro q _
      apply mul_nonneg (factorialWeight_nonneg ρ q.val)
      apply Finset.sum_nonneg
      intro word _
      positivity
    have hrword : d.1 - 1 = m + 1 := by dsimp [m]; omega
    simpa [m] using torusKernelFluxTerm_factorialNorm_le
      (K := k) (m := m) (r := d.1 - 1) hrword ρ hρ t₀ t₁ (B i j α d)
      (hB_fin i j α d) t ht_mem (hB_smooth i j α d t ht_mem)
      (hB_per i j α d t ht_mem) (lowJet i j α d) (c m / r i j α ^ m) hγ ‖C i j α‖ hCnonneg
      (gradFactorialNormSq ρ (V j).val) hgradNonneg hYbound
  have hTermAE (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      (term i j α d).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Y i j α).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    have hd := Finset.mem_Icc.1 d.2
    have hm : d.1 - 1 = (d.1 - 2) + 1 := by omega
    let lowOrder := k + ((d.1 - 2) + 1)
    have hcut : lowOrder ≤ highBase := by dsimp [lowOrder, highBase]; omega
    let hiIdx (word : DerivativeWord2 (d.1 - 1)) : JetIndex2 (k + D - 1) :=
      ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩
    let loIdx (word : DerivativeWord2 (d.1 - 1)) : JetIndex2 lowOrder :=
      ⟨⟨d.1 - 1, by omega⟩, word⟩
    have hidx (word : DerivativeWord2 (d.1 - 1)) :
        cast (congrArg JetIndex2 hOrder.symm) (hiIdx word) =
          truncateJetIndex hcut (loIdx word) := by
      have hrHi : d.1 - 1 < (k + D - 1) + 1 := by
        have hd := Finset.mem_Icc.1 d.2
        omega
      have hrLo : d.1 - 1 < lowOrder + 1 := by
        dsimp [lowOrder]
        omega
      exact castJetIndex_truncate hOrder hcut hrHi hrLo word
    have hlow (word : DerivativeWord2 (d.1 - 1)) :
        (lowJet i j α d).toFunction.jet
            (loIdx word) =ᵐ[
              volume.restrict AVenhance.unitCube]
          (Ybase i j α).toFunction.jet
            (truncateJetIndex hcut (loIdx word)) := by
      simpa [lowJet, lowOrder] using
        truncateTorusHk_toFunction_jet_ae hcut (Ybase i j α) (loIdx word)
    have harray : (fun x => WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (lowJet i j α d).toFunction.jet
          ⟨⟨d.1 - 1, by omega⟩, word⟩ x) =ᵐ[
            volume.restrict AVenhance.unitCube]
        fun x => WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Y i j α).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x := by
      have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ word : DerivativeWord2 (d.1 - 1),
          (lowJet i j α d).toFunction.jet
              (loIdx word) x =
            (Y i j α).toFunction.jet
              (hiIdx word) x := by
        apply ae_all_iff.2
        intro word
        have hcast := castTorusHk_toFunction_jet hOrder (Ybase i j α) (hiIdx word)
        filter_upwards [hlow word] with x hx
        calc
          (lowJet i j α d).toFunction.jet
              (loIdx word) x =
            (Ybase i j α).toFunction.jet
              (truncateJetIndex hcut (loIdx word)) x := hx
          _ = (Ybase i j α).toFunction.jet
              (cast (congrArg JetIndex2 hOrder.symm) (hiIdx word)) x := by
                rw [← hidx word]
          _ = (Y i j α).toFunction.jet
              (hiIdx word) x :=
            congrFun hcast.symm x
      filter_upwards [hall] with x hx
      apply PiLp.ext
      intro word
      exact hx word
    have hterm := torusKernelFluxTerm_base_ae hm ρ hρ t₀ t₁ (B i j α d)
      (hB_fin i j α d) t ht_mem (hB_smooth i j α d t ht_mem) (hB_per i j α d t ht_mem) (lowJet i j α d)
    filter_upwards [hterm, harray] with x htermx harrayx
    exact htermx.trans (congrArg (B i j α d t x) harrayx)
  have hTermVal (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      (term i j α d).val (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Y i j α).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    exact (torusHk_toFunction_jet_ae (term i j α d) (valueIndex2 k)).symm.trans
      (hTermAE i j α d)
  have hInnerAE (i j : ι) (α : Γ i j) :
      (∑ d : ↥(Finset.Icc 2 D), (term i j α d).val (valueIndex2 k)) =ᵐ[
        volume.restrict AVenhance.unitCube]
      fun x => ∑ d : ↥(Finset.Icc 2 D),
        B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (Y i j α).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    have hsum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (↥(Finset.Icc 2 D)))
      (fun d => (term i j α d).val (valueIndex2 k))
    have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ d : ↥(Finset.Icc 2 D),
        (term i j α d).val (valueIndex2 k) x =
          B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y i j α).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
      apply ae_all_iff.2
      intro d
      exact hTermVal i j α d
    filter_upwards [hsum, hall] with x hsumx hallx
    rw [hsumx]
    apply Finset.sum_congr rfl
    intro d hd
    exact hallx d
  have hMiddleAE (i j : ι) :
      (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (term i j α d).val (valueIndex2 k)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y i j α).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    have hsum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Γ i j))
      (fun α => ∑ d : ↥(Finset.Icc 2 D), (term i j α d).val (valueIndex2 k))
    have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ α : Γ i j,
        (∑ d : ↥(Finset.Icc 2 D), (term i j α d).val (valueIndex2 k)) x =
          ∑ d : ↥(Finset.Icc 2 D),
            B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y i j α).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
      apply ae_all_iff.2
      intro α
      exact hInnerAE i j α
    filter_upwards [hsum, hall] with x hsumx hallx
    rw [hsumx]
    apply Finset.sum_congr rfl
    intro α hα
    exact hallx α
  have hOuterAE (i : ι) :
      (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (term i j α d).val (valueIndex2 k)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y i j α).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    have hsum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset ι)
      (fun j => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        (term i j α d).val (valueIndex2 k))
    have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j : ι,
        (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (term i j α d).val (valueIndex2 k)) x =
          ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y i j α).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
      apply ae_all_iff.2
      intro j
      exact hMiddleAE i j
    filter_upwards [hsum, hall] with x hsumx hallx
    rw [hsumx]
    apply Finset.sum_congr rfl
    intro j hj
    exact hallx j
  have hAfull (i : ι) : (A i).val =
      ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), (term i j α d).val := by
    change (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtype
      (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), term i j α d) = _
    simp only [map_sum]
    rfl
  refine ⟨Y, A, ?_, ?_, ?_⟩
  · intro i j α
    have hcomp : (C i j α).compLpL 2 (volume.restrict AVenhance.unitCube)
          ((V j).val (valueIndex2 (k + 1))) =
        (C i j α).compLp ((V j).val (valueIndex2 (k + 1))) := by
      apply Lp.ext
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (C i j α)
          ((V j).val (valueIndex2 (k + 1))),
        ContinuousLinearMap.coeFn_compLp (C i j α)
          ((V j).val (valueIndex2 (k + 1)))] with x hx hy
      exact hx.trans hy.symm
    simpa [Y, castTorusHk_valueIndex] using
      (hYbase i j α).trans (congrArg (S i j α t) hcomp)
  · intro i
    have hAVal : (A i).val (valueIndex2 k) =
        ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (term i j α d).val (valueIndex2 k) := by
      change (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        term i j α d).val (valueIndex2 k) = _
      calc
        _ = ∑ j : ι, (∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
              term i j α d).val (valueIndex2 k) :=
          torusHk_sum_value (f := fun j => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
            term i j α d) (valueIndex2 k)
        _ = ∑ j : ι, ∑ α : Γ i j, (∑ d : ↥(Finset.Icc 2 D),
              term i j α d).val (valueIndex2 k) := by
          apply Finset.sum_congr rfl
          intro j _
          exact torusHk_sum_value
            (f := fun α => ∑ d : ↥(Finset.Icc 2 D), term i j α d) (valueIndex2 k)
        _ = ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
              (term i j α d).val (valueIndex2 k) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro α _
          exact torusHk_sum_value
            (f := fun d => term i j α d) (valueIndex2 k)
    have hvalAE := Lp.ext_iff.mp hAVal
    have hrep := torusHk_toFunction_jet_ae (A i) (valueIndex2 k)
    filter_upwards [hrep, hvalAE, hOuterAE i] with x hrep hval hall
    calc
      (A i).toFunction.jet (valueIndex2 k) x = (A i).val (valueIndex2 k) x := hrep
      _ = (∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          (term i j α d).val (valueIndex2 k)) x := hval
      _ = ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
          B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y i j α).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := hall
  · exact kernelFluxMassSchur ρ ν θ hν k D t₀ t₁ π hπ B C c r hr
      (fun i j α m hm => (hS i j α).2.2.1 m hm)
      (fun i => (A i).val) (fun j => (V j).val)
      (fun i j α d => (term i j α d).val)
      (fun i => hAfull i) hTermRoot hschur

end AVRegularity.Providers
end
end

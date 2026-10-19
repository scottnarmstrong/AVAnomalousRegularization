-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
public import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive native assembly transfers raw normalized kernel prices to the literal coefficient seminorm. -/

open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_physical_kernel_price_of_raw_prices
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hν : 0 < D.kap G.level) (a b : ℝ)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (n d : ℕ) (ρ r P : ℝ) (hρ : 0 < ρ) (hrpos : 0 < r) (hP : 0 ≤ P)
    (hraw : ∀ t ∈ Set.Icc a b, ∀ p : OddSlot, t ∈ (G.fam.piece p).output →
      ∀ j, j ≤ n → ∀ y,
      (ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => nativeArrayAssembly (d - 1)
        (G.fam.identity v u γ).map
        (fun a A => transportedCoeff
          (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
          (G.fam.identity v u γ).maxOrder
          (fun d' I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
            p (G.actual p) v u γ d' I t
            (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) x t)
            ((D.eps G.level)⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) x t))
          (d - 1) A x a)) y‖) / (D.kap G.level * r ^ (d - 2)) ≤ P) :
    (coefficientSeminorm ρ n a b (G.physCoeff v u γ d)).toReal /
      (D.kap G.level * r ^ (d - 2)) ≤
        P * (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) := by
  let den := D.kap G.level * r ^ (d - 2)
  have hden : 0 < den := mul_pos hν (pow_pos hrpos _)
  let g := fun (t : ℝ) (p : OddSlot) (y : Vec 2) => nativeArrayAssembly (d - 1)
    (G.fam.identity v u γ).map
    (fun a A => transportedCoeff
      (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
      (G.fam.identity v u γ).maxOrder
      (fun d' I => G.fam.dimFlux (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
        p (G.actual p) v u γ d' I t
        (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
        ((D.eps G.level)⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t))
      (d - 1) A y a)
  have hs := native_physCoeff_seminorm_le_of_piece_jets hG hpar hnat hi hj hb hε a b v u γ
    hm hm2 n d ρ hρ (fun _ => P * den) (fun _ => mul_nonneg hP hden.le) g
    (fun _ _ _ => rfl)
    (fun t _ p hp => native_raw_piece_all_order_smooth hG hpar hnat hi hj hb hε p v u γ
      hm hm2 (D.kap G.level) (D.eps G.level) n (d - 1) t (by
        rwa [← (hnat.1 p).2.1]))
    (fun t ht p hp j hj y => (div_le_iff₀ hden).mp (hraw t ht p hp j hj y))
  have hn : 0 ≤ ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * (P * den) / (j.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro j _
    positivity
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  rw [ENNReal.toReal_ofReal hn] at ht
  apply (div_le_div_of_nonneg_right ht hden.le).trans_eq
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hden.ne']

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Assemble a literal native kernel operator from context calculus and quantitative kernel data. -/

open AVRegularity.Construction.Preservation.Buffer
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def nativeContextKernelOperator
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {kI : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hshift : G.IsShiftInvariant) (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    (a b ρ ν : ℝ) (n : ℕ) (hab : a ≤ b) (hρ : 0 < ρ)
    (hρε : ρ ≤ D.eps (G.level - 1)) (hν : 0 < ν) (hD : 2 ≤ Dm)
    (π : CompIn G.comps → ℝ) (hπ : ∀ v, 0 < π v)
    (c : ℕ → ℝ)
    (hwidth : ∀ v u γ, 0 < (G.kernelOf P seedK freshK v u γ).width)
    (hSzero : ∀ v u γ, IsSpatialRegularizerTorus ρ 0 Dm a b c
      (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ))
    (θ : ℝ) (hθ : θ ≤ 1 / 8)
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ π n Dm a b c
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1))) :
    KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν n Dm where
  htime := hab
  radius_pos := hρ
  diffusivity_pos := hν
  order_ge_two := hD
  π := π
  hπ := hπ
  B := fun v u γ d => G.physCoeff v u γ d.1
  hB_meas := fun v u γ d => native_physCoeff_joint_measurable_of_context hG hpar hnat
    hΛ hi hj hb hε a b hm hm2 v u γ d.1
  hB_smooth := fun v u γ d t ht => native_physCoeff_all_order_smooth hG hpar hnat
    hi hj hb hε a b v u γ (hm v) (hm2 v) n d.1 t ht
  hB_per := fun v u γ d t _ => native_physCoeff_periodic hnat hshift v u γ d.1 t
  hB_fin := fun v u γ d => native_physCoeff_all_order_seminorm_finite hG hpar hnat
    hi hj hb hε a b v u γ (hm v) (hm2 v) ρ hρ hρε n d.1
  C := fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root)
  S := G.sysS P seedK freshK φ₀ hφ₀
  c := c
  r := fun v u γ => (G.kernelOf P seedK freshK v u γ).width
  hr := hwidth
  hS := fun v u γ => spatial_regularizer_all_orders ρ Dm a b c
    (G.kernelOf P seedK freshK v u γ).width
    (G.sysS P seedK freshK φ₀ hφ₀ v u γ) (hSzero v u γ) n
  θ := θ
  hθ := hθ
  hschur := hschur

end AVRegularity.Construction.Preservation.FullLift
end

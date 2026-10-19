-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
public import AVRegularity.EntryWeakAssembly.Assembly.KernelPriceTransport
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonDescending
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Restriction of a kernel weak solution to a smaller cap**.

A kernel weak solution at the cap `D` whose coefficients vanish at the orders `D' < n ≤ D` is a
kernel weak solution at the cap `D'`, with the kernel lift truncated from the order `k + D − 1` to
`k + D' − 1`. The value of a truncation is the value, the jets of the orders `d − 1`, `d ≤ D'`, are
unchanged, and the flux sum over `[2, D]` is the sum over `[2, D']`.

It is used for the incoming family of a weak passage: the reduction gives the system of the
stage at the ambient cap `D_m`, and the comparison reads it at the cap `1 + J_wN_w`.

The degenerate cases are included: `D' = D` is the identity (the truncation is at equal orders); a
family without edges has an empty flux at every cap. -/

section
/-- The value index is preserved by the inclusion of jet indices. -/
theorem truncateJetIndex_valueIndex2 {m n : ℕ} (hmn : m ≤ n) :
    truncateJetIndex hmn (valueIndex2 m) = valueIndex2 n := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · simp [truncateJetIndex, valueIndex2, valueIndex]

/-- **The flux orders at a smaller cap.** If the order-`n` coefficients vanish for `D' < n ≤ D` and
the two jet families agree, the sum over `[2, D]` is the sum over `[2, D']`. -/
theorem kernel_orders_sum_cap {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {D D' : ℕ} (hD : D' ≤ D) {L₁ L₂ : ℕ}
    (P : ∀ n : ℕ, PiLp 2 (fun _ : DerivativeWord2 (n - 1) => G) →L[ℝ] H)
    (hP : ∀ n, D' < n → n ≤ D → P n = 0)
    (Y : JetIndex2 L₁ → G) (W : JetIndex2 L₂ → G)
    (hYW : ∀ (n : ℕ) (h₁ : n < L₁ + 1) (h₂ : n < L₂ + 1) (word : DerivativeWord2 n),
      Y ⟨⟨n, h₁⟩, word⟩ = W ⟨⟨n, h₂⟩, word⟩)
    (pf₁ : ∀ d : ↥(Finset.Icc 2 D), d.1 - 1 < L₁ + 1)
    (pf₂ : ∀ d : ↥(Finset.Icc 2 D'), d.1 - 1 < L₂ + 1) :
    ∑ d : ↥(Finset.Icc 2 D), P d.1 (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Y ⟨⟨d.1 - 1, pf₁ d⟩, word⟩) =
      ∑ d : ↥(Finset.Icc 2 D'), P d.1
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) => W ⟨⟨d.1 - 1, pf₂ d⟩, word⟩) := by
  classical
  let T : ℕ → H := fun n => if h : n - 1 < L₁ + 1 then
    P n (WithLp.toLp 2 fun word : DerivativeWord2 (n - 1) => Y ⟨⟨n - 1, h⟩, word⟩) else 0
  have hsub : Finset.Icc 2 D' ⊆ Finset.Icc 2 D := Finset.Icc_subset_Icc le_rfl hD
  have h1 : ∑ d : ↥(Finset.Icc 2 D), P d.1 (WithLp.toLp 2
      fun word : DerivativeWord2 (d.1 - 1) => Y ⟨⟨d.1 - 1, pf₁ d⟩, word⟩) =
      ∑ n ∈ Finset.Icc 2 D, T n := by
    rw [← Finset.sum_coe_sort (Finset.Icc 2 D)]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [T, dite_eq_left (pf₁ d)]
  have h2 : ∑ n ∈ Finset.Icc 2 D', T n = ∑ n ∈ Finset.Icc 2 D, T n := by
    refine Finset.sum_subset hsub fun n hn hna => ?_
    have hn' := Finset.mem_Icc.1 hn
    have hlt : D' < n := by
      by_contra hle
      exact hna (Finset.mem_Icc.2 ⟨hn'.1, not_lt.mp hle⟩)
    simp only [T, hP n hlt hn'.2, zero_apply, dite_eq_ite, ite_self]
  have h3 : ∑ d : ↥(Finset.Icc 2 D'), P d.1 (WithLp.toLp 2
      fun word : DerivativeWord2 (d.1 - 1) => W ⟨⟨d.1 - 1, pf₂ d⟩, word⟩) =
      ∑ n ∈ Finset.Icc 2 D', T n := by
    rw [← Finset.sum_coe_sort (Finset.Icc 2 D')]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd₁ : d.1 - 1 < L₁ + 1 := pf₁ ⟨d.1, hsub d.2⟩
    simp only [T, dite_eq_left hd₁]
    congr 2
    funext word
    exact (hYW _ hd₁ (pf₂ d) word).symm
  rw [h1, ← h2, h3]

/-- A weak identity with an equal total flux. -/
theorem coupledWeakIdentity_of_flux_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} {ν a t : ℝ} {v : ℝ → Vec 2 → Vec 2} {u f φ : Vec 2 → H}
    {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {A A' F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H} (hA : A = A')
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du A F g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du A' F g := hA ▸ h

/-- The jets of a truncation are the jets, at the same order. -/
theorem truncateTorusHk_jet_same {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {m n : ℕ} (hmn : m ≤ n)
    (f : TorusHk n E) (j : ℕ) (h₁ : j < n + 1) (h₂ : j < m + 1) (word : DerivativeWord2 j) :
    f.toFunction.jet ⟨⟨j, h₁⟩, word⟩ = (truncateTorusHk hmn f).toFunction.jet ⟨⟨j, h₂⟩, word⟩ :=
  rfl

section Restrict

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]
  {k D D' : ℕ}
  {P : ∀ i j (α : Γ i j) (n : ℕ), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (n - 1) => G i j α) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

/-- The total flux of a row at the cap `D` is the total flux at the cap `D'`, with the kernel lift
truncated. -/
theorem kernel_flux_restrict_cap (hD : D' ≤ D)
    (hP : ∀ i j α n, D' < n → n ≤ D → ∀ s x, P i j α n s x = 0)
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hcut : k + D' - 1 ≤ k + D - 1) (i : ι) :
    (fun (s : ℝ) (x : Vec 2) => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        P i j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α s).toFunction.jet
            ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.1 d.2
              omega⟩, word⟩ x)) =
      fun (s : ℝ) (x : Vec 2) => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D'),
        P i j α d.1 s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (truncateTorusHk hcut (y i j α s)).toFunction.jet
            ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.1 d.2
              omega⟩, word⟩ x) := by
  funext s x
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
  exact kernel_orders_sum_cap hD (fun n => P i j α n s x)
    (fun n h1 h2 => hP i j α n h1 h2 s x)
    (fun a => (y i j α s).toFunction.jet a x)
    (fun a => (truncateTorusHk hcut (y i j α s)).toFunction.jet a x)
    (fun n h₁ h₂ word => congrFun (truncateTorusHk_jet_same hcut (y i j α s) n h₁ h₂ word) x)
    _ _

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i j α, FiniteDimensional ℝ (G i j α)]

/-- **Restriction to a smaller cap.** -/
theorem kernelWeakSolutionTorus_restrict_cap {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2}
    (hD : D' ≤ D)
    (hP : ∀ i j α n, D' < n → n ≤ D → ∀ s x, P i j α n s x = 0)
    {C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α}
    {S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    {f : ∀ i, TorusHk k (h i)} {F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → TorusHk k (h i)} {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hs : IsKernelWeakSolutionTorus ν t₀ t₁ v k D (fun i j α d => P i j α d.1) C S f F g u w y) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D' (fun i j α d => P i j α d.1) C S f F g u w
      (fun i j α s => truncateTorusHk (by omega : k + D' - 1 ≤ k + D - 1) (y i j α s)) := by
  have hcut : k + D' - 1 ≤ k + D - 1 := by omega
  rcases hs with ⟨hu, hw, htrace, hinit, hyMem, hyValue, hweak⟩
  refine ⟨hu, hw, htrace, hinit, ?_, ?_, ?_⟩
  · intro i j α
    exact (truncateTorusHk hcut).comp_memLp' (hyMem i j α)
  · intro i j α
    filter_upwards [hyValue i j α] with s hs
    rw [truncateTorusHk_apply, truncateJetIndex_valueIndex2 hcut]
    exact hs
  · intro i t ht φ
    exact coupledWeakIdentity_of_flux_eq (kernel_flux_restrict_cap hD hP y hcut i)
      (hweak i t ht φ)

end Restrict
end

/-! **The weak identity of a difference**. Two weak identities subtract, and the
result transfers to any data that agree with the difference almost everywhere in space, at almost
every time, provided the right side of the target is integrable at every time. Generic. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The weak identity of a difference, transferred to data that agree with the difference almost
everywhere in space (the value and the pairing data) and, in time, almost everywhere (the gradient
of the lift) or everywhere (the flux, the forcing). -/
theorem coupledWeakIdentity_sub_transfer (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u₁ u₂ u f₁ f₂ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du₁ du₂ du : ℝ → Fin 2 → Vec 2 → H)
    (A₁ A₂ A F₁ F₂ F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g₁ g₂ g : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity μ ν a t v u₁ f₁ φ dφ du₁ A₁ F₁ g₁)
    (h₂ : CoupledWeakIdentity μ ν a t v u₂ f₂ φ dφ du₂ A₂ F₂ g₂)
    (hu : u =ᵐ[μ] fun x => u₁ x - u₂ x) (hf : f =ᵐ[μ] fun x => f₁ x - f₂ x)
    (hdu : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)), ∀ q, du s q =ᵐ[μ] fun x => du₁ s q x - du₂ s q x)
    (hfl : ∀ s, (fun x => A s x + F s x) =ᵐ[μ]
      fun x => (A₁ s x + F₁ s x) - (A₂ s x + F₂ s x))
    (hg : ∀ s, g s =ᵐ[μ] fun x => g₁ s x - g₂ s x)
    (hint : ∀ s ∈ Set.Ioc a t, Integrable (Weighted.weakIdentityRhs ν v φ dφ du A F g s) μ) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du A F g := by
  have hS := CycleWords.coupledWeakIdentity_sub μ ν a t v u₁ u₂ f₁ f₂ φ dφ du₁ du₂ A₁ A₂ F₁ F₂
    g₁ g₂ h₁ h₂
  have hA := CycleJointProofs.coupledWeakIdentity_integrands_congr μ ν a t v v (u₁ - u₂) u
    (f₁ - f₂) f φ φ dφ dφ (du₁ - du₂) (du₁ - du₂) (A₁ - A₂) (A₁ - A₂) (F₁ - F₂) (F₁ - F₂)
    (g₁ - g₂) (g₁ - g₂)
    (by filter_upwards [hu] with x hx; simp only [Pi.sub_apply, hx])
    (by filter_upwards [hf] with x hx; simp only [Pi.sub_apply, hx])
    (fun s _ => Filter.EventuallyEq.rfl) hS
  refine Weighted.coupledWeakIdentity_rhs_transfer μ ν a t v u f φ dφ (du₁ - du₂) du
    (A₁ - A₂) (F₁ - F₂) A F (g₁ - g₂) g hA hint ?_
  filter_upwards [hdu] with s hs
  have hq : ∀ q, ∀ᵐ x ∂μ, du s q x = (du₁ - du₂) s q x := fun q => by
    filter_upwards [hs q] with x hx
    simpa only [Pi.sub_apply] using hx
  have hq' : ∀ᵐ x ∂μ, ∀ q, du s q x = (du₁ - du₂) s q x := ae_all_iff.2 hq
  filter_upwards [hq', hfl s, hg s] with x h1 h2 h3
  refine Providers.WeakGen.Comparison.weakIdentityRhs_congr_at ν v φ dφ du (du₁ - du₂) A (A₁ - A₂)
    F (F₁ - F₂) g (g₁ - g₂) s x h1 ?_ ?_
  · simp only [Pi.sub_apply]
    rw [h2]
    abel
  · simpa only [Pi.sub_apply] using h3

/-- The right side splits along the gradient of the lift. -/
theorem weakIdentityRhs_add_du (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (d₀ d₁ : ℝ → Fin 2 → Vec 2 → H)
    (A F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H) (s : ℝ) (x : Vec 2) :
    Weighted.weakIdentityRhs ν v φ dφ (d₀ + d₁) A F g s x =
      Weighted.weakIdentityRhs ν v φ dφ d₀ A F g s x +
        Weighted.weakIdentityRhs ν v φ dφ d₁ 0 0 0 s x := by
  simp only [Weighted.weakIdentityRhs, Pi.add_apply, inner_add_left, mul_add,
    Finset.sum_add_distrib, Pi.zero_apply, PiLp.zero_apply, add_zero, inner_zero_left,
    Finset.sum_const_zero]
  ring

/-- The difference transfer on the unit cell: the integrability of the target right side at every
time is automatic from the spatial data (a bounded continuous drift, `L²` jets). -/
theorem coupledWeakIdentity_sub_transfer_cell (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u₁ u₂ u f₁ f₂ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du₁ du₂ du : ℝ → Fin 2 → Vec 2 → H)
    (A₁ A₂ A F₁ F₂ F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g₁ g₂ g : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u₁ f₁ φ dφ du₁ A₁ F₁ g₁)
    (h₂ : CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u₂ f₂ φ dφ du₂ A₂ F₂ g₂)
    (hu : u =ᵐ[volume.restrict AVenhance.unitCube] fun x => u₁ x - u₂ x)
    (hf : f =ᵐ[volume.restrict AVenhance.unitCube] fun x => f₁ x - f₂ x)
    (hdu : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)), ∀ q,
      du s q =ᵐ[volume.restrict AVenhance.unitCube] fun x => du₁ s q x - du₂ s q x)
    (hfl : ∀ s, (fun x => A s x + F s x) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (A₁ s x + F₁ s x) - (A₂ s x + F₂ s x))
    (hg : ∀ s, g s =ᵐ[volume.restrict AVenhance.unitCube] fun x => g₁ s x - g₂ s x)
    (hv : ∀ s ∈ Set.Ioc a t, Continuous (v s) ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖v s x‖ ≤ V)
    (hφ : MemLp φ 2 (volume.restrict AVenhance.unitCube))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict AVenhance.unitCube))
    (hd₁ : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (du₁ s k) 2 (volume.restrict AVenhance.unitCube))
    (hd₂ : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (du₂ s k) 2 (volume.restrict AVenhance.unitCube))
    (hd : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (du s k) 2 (volume.restrict AVenhance.unitCube)) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u f φ dφ du A F g := by
  refine coupledWeakIdentity_sub_transfer _ ν a t v u₁ u₂ u f₁ f₂ f φ dφ du₁ du₂ du A₁ A₂ A
    F₁ F₂ F g₁ g₂ g h₁ h₂ hu hf hdu hfl hg ?_
  intro s hs
  have hS := CycleWords.coupledWeakIdentity_sub _ ν a t v u₁ u₂ f₁ f₂ φ dφ du₁ du₂ A₁ A₂ F₁ F₂
    g₁ g₂ h₁ h₂
  have hI : Integrable (Weighted.weakIdentityRhs ν v φ dφ (du₁ - du₂) (A₁ - A₂) (F₁ - F₂)
      (g₁ - g₂) s) (volume.restrict AVenhance.unitCube) := hS.2.2.1 s hs
  obtain ⟨hvc, V, hV0, hV⟩ := hv s hs
  have hE : Integrable (Weighted.weakIdentityRhs ν v φ dφ (du - (du₁ - du₂)) 0 0 0 s)
      (volume.restrict AVenhance.unitCube) :=
    CycleJointProofs.cell_weakIdentityRhs_integrable ν s v φ dφ _ 0 0 0 hvc V hV0 hV hφ hdφ
      (fun k => (hd s hs k).sub ((hd₁ s hs k).sub (hd₂ s hs k))) (fun _ => MemLp.zero')
      (fun _ => MemLp.zero') MemLp.zero'
  have hsum : Integrable (Weighted.weakIdentityRhs ν v φ dφ du (A₁ - A₂) (F₁ - F₂) (g₁ - g₂) s)
      (volume.restrict AVenhance.unitCube) := by
    refine (hI.add hE).congr (Filter.Eventually.of_forall fun x => ?_)
    have := weakIdentityRhs_add_du ν v φ dφ (du₁ - du₂) (du - (du₁ - du₂)) (A₁ - A₂) (F₁ - F₂)
      (g₁ - g₂) s x
    rw [add_sub_cancel] at this
    exact this.symm
  refine hsum.congr ?_
  filter_upwards [hfl s, hg s] with x h2 h3
  refine (Providers.WeakGen.Comparison.weakIdentityRhs_congr_at ν v φ dφ du du A (A₁ - A₂) F
    (F₁ - F₂) g (g₁ - g₂) s x (fun _ => rfl) ?_ ?_).symm
  · simp only [Pi.sub_apply]
    rw [h2]
    abel
  · simpa only [Pi.sub_apply] using h3
end

/-! **The kernel-regularized system is linear and sees its data on the window only**.
Generic over the system `IsKernelWeakSolutionTorus`. -/

section
section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- The total kernel flux of a lift `y`, as it occurs in `IsKernelWeakSolutionTorus`. -/
def kernelFluxOf {k D : ℕ}
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) (i : ι) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h i) :=
  fun s x => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    B i j α d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (y i j α s).toFunction.jet
        ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] in
/-- The total flux of a difference of lifts is the difference of the total fluxes, in space. -/
theorem kernelFluxOf_sub_ae {k D : ℕ}
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (y y₁ y₂ : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hy : ∀ i j α t, y i j α t = y₁ i j α t - y₂ i j α t) (i : ι) (s : ℝ) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      kernelFluxOf B y i s x = kernelFluxOf B y₁ i s x - kernelFluxOf B y₂ i s x := by
  have key : ∀ (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) (word : DerivativeWord2 (d.1 - 1)),
      ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
        (y i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x =
        (y₁ i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x -
        (y₂ i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x := by
    intro j α d word
    rw [hy]
    exact Providers.WeakGen.Comparison.torusHk_jet_sub_ae _ _ _
  have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ (j : ι) (α : Γ i j)
      (d : ↥(Finset.Icc 2 D)) (word : DerivativeWord2 (d.1 - 1)),
        (y i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x =
        (y₁ i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x -
        (y₂ i j α s).toFunction.jet ⟨⟨d.1 - 1, by
          have := Finset.mem_Icc.1 d.2
          omega⟩, word⟩ x :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun α => ae_all_iff.2 fun d => ae_all_iff.2 fun word =>
      key j α d word
  filter_upwards [hall] with x hx
  simp only [kernelFluxOf, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [← map_sub]
  congr 1
  ext word
  simp [hx j α d word]

/-- **Generic case.** The kernel-regularized system is linear in its data and reads the value only
on the window and the `H^{k+1}` lift only almost everywhere on it. -/
theorem kernelWeakSolutionTorus_sub (ν t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (k D : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (hwin : t₀ ≤ t₁)
    (hv : ∀ s ∈ Set.Icc t₀ t₁, Continuous (v s) ∧ ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖v s x‖ ≤ V)
    (f₁ f₂ f : ∀ i, TorusHk k (h i))
    (F₁ F₂ F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g₁ g₂ g u₁ u₂ u : ∀ i, ℝ → TorusHk k (h i))
    (w₁ w₂ w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y₁ y₂ y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (h₁ : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f₁ F₁ g₁ u₁ w₁ y₁)
    (h₂ : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f₂ F₂ g₂ u₂ w₂ y₂)
    (hf : ∀ i, f i = f₁ i - f₂ i) (hF : ∀ i t, F i t = F₁ i t - F₂ i t)
    (hg : ∀ i t, g i t = g₁ i t - g₂ i t)
    (hu : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, u i t = u₁ i t - u₂ i t)
    (hw : ∀ i, ∀ᵐ t ∂(volume.restrict (Set.Icc t₀ t₁)), w i t = w₁ i t - w₂ i t)
    (hy : ∀ i j α t, y i j α t = y₁ i j α t - y₂ i j α t) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y := by
  have hmem : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc t₀ t₁)) := fun i =>
    ((h₁.2.1 i).sub (h₂.2.1 i)).ae_eq (by
      filter_upwards [hw i] with t ht
      exact ht.symm)
  refine ⟨fun i => ((h₁.1 i).sub (h₂.1 i)).congr fun t ht => hu i t ht, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [h₁.2.2.1 i, h₂.2.2.1 i, hw i, ae_restrict_mem measurableSet_Icc] with
      s a b c hs
    rw [c, map_sub, a, b, hu i s hs]
  · intro i
    rw [hu i t₀ ⟨le_rfl, hwin⟩, h₁.2.2.2.1 i, h₂.2.2.2.1 i]
    exact (hf i).symm
  · intro i j α
    have : y i j α = fun t => y₁ i j α t - y₂ i j α t := funext (hy i j α)
    rw [this]
    exact (h₁.2.2.2.2.1 i j α).sub (h₂.2.2.2.2.1 i j α)
  · intro i j α
    filter_upwards [h₁.2.2.2.2.2.1 i j α, h₂.2.2.2.2.2.1 i j α, hw j] with s a b c
    rw [hy, c]
    change (y₁ i j α s).val (valueIndex2 (k + D - 1)) - (y₂ i j α s).val (valueIndex2 (k + D - 1)) = _
    rw [a, b, ← map_sub]
    congr 1
    exact (map_sub ((C i j α).compLpL 2 (volume.restrict AVenhance.unitCube)) _ _).symm
  · intro i t ht φ
    have h1 := h₁.2.2.2.2.2.2 i t ht φ
    have h2 := h₂.2.2.2.2.2.2 i t ht φ
    have hsub : Set.Ioc t₀ t ⊆ Set.Icc t₀ t₁ := fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    have hIcc : ∀ s ∈ Set.Ioc t₀ t, s ∈ Set.Icc t₀ t₁ := fun s hs => hsub hs
    have hμ : ∀ i' : ι, ∀ᵐ s ∂(volume.restrict (Set.Ioc t₀ t)), w i' s = w₁ i' s - w₂ i' s :=
      fun i' => ae_restrict_of_ae_restrict_of_subset hsub (hw i')
    refine coupledWeakIdentity_sub_transfer_cell (h₁ := h1) (h₂ := h2) (hu := ?_) (hf := ?_)
      (hdu := ?_) (hfl := ?_) (hg := ?_) (hv := fun s hs => hv s (hIcc s hs))
      (hφ := φ.toFunction.hasPeriodicWeakJet.2.1 _)
      (hdφ := fun _ => φ.toFunction.hasPeriodicWeakJet.2.1 _)
      (hd₁ := fun s _ _ => (w₁ i s).toFunction.hasPeriodicWeakJet.2.1 _)
      (hd₂ := fun s _ _ => (w₂ i s).toFunction.hasPeriodicWeakJet.2.1 _)
      (hd := fun s _ _ => (w i s).toFunction.hasPeriodicWeakJet.2.1 _)
    · rw [hu i t ht]
      exact Providers.WeakGen.Comparison.torusHk_jet_sub_ae _ _ _
    · rw [hf i]
      exact Providers.WeakGen.Comparison.torusHk_jet_sub_ae _ _ _
    · filter_upwards [hμ i] with s hs q
      rw [hs]
      exact Providers.WeakGen.Comparison.torusHk_jet_sub_ae _ _ _
    · intro s
      filter_upwards [kernelFluxOf_sub_ae B y y₁ y₂ hy i s,
        Providers.WeakGen.Comparison.torusHk_jet_sub_ae (F₁ i s) (F₂ i s) (valueIndex2 k)] with
        x hA hFx
      rw [hF i s]
      change kernelFluxOf B y i s x + _ = (kernelFluxOf B y₁ i s x + _) - (kernelFluxOf B y₂ i s x + _)
      rw [hA, hFx]
      abel
    · intro s
      rw [hg i s]
      exact Providers.WeakGen.Comparison.torusHk_jet_sub_ae _ _ _

end Generic
end

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The equation of the incoming family (generic part): restarting and truncating a kernel-regularized solution**.

A solution on `[t₀, t₁]` restarts at any `s ∈ [t₀, t₁]` with the initial value `u(s)`
(`kernelWeakSolutionTorus_restart`, the version of `TorusKernelOperator.kernelWeakSolution_restart`
without the structure `TorusKernelOperator`). -/

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- A kernel-regularized solution restarts at any time of its window. -/
theorem kernelWeakSolutionTorus_restart (ν t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (k D : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (hsol : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y)
    (s : ℝ) (hs : s ∈ Set.Icc t₀ t₁) :
    IsKernelWeakSolutionTorus ν s t₁ v k D B C S (fun i => u i s) F g u w y := by
  have hsub : Set.Icc s t₁ ⊆ Set.Icc t₀ t₁ := Set.Icc_subset_Icc hs.1 le_rfl
  have hμ : volume.restrict (Set.Icc s t₁) ≤ volume.restrict (Set.Icc t₀ t₁) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨(fun i => (hsol.1 i).mono hsub), (fun i => (hsol.2.1 i).mono_measure hμ),
    (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 i)),
    (fun _ => rfl), (fun i j α => (hsol.2.2.2.2.1 i j α).mono_measure hμ),
    (fun i j α => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 i j α)), ?_⟩
  intro i t ht φ
  exact KernelEnergy.weakIdentity_restart (volume.restrict AVenhance.unitCube) ν t₀ s t hs.1 ht.1 v
    ((u i t).toFunction.jet (valueIndex2 k)) ((u i s).toFunction.jet (valueIndex2 k))
    ((f i).toFunction.jet (valueIndex2 k)) (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (kernelFluxOf B y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k))
    (hsol.2.2.2.2.2.2 i t (hsub ht) φ) (hsol.2.2.2.2.2.2 i s hs φ)

end Generic

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The exact residual equation: the named steps**.

The residual equation says that, for every time-measurable presentation `(F, g)` of the residual
source, the comparison error `h.e` solves the zero-data regularized system of the stage
`c.stage i` with the forcing `(trunc F, trunc g)`.

The route is `𝔢 = U − Λ_i g`, with `U = r.Ur i` and `g = 𝓡_i Ū`. It is cut into the following
steps over the same passage data.

* `WeakIncomingRegStatement`: `U`, restricted to the window `[t_i, T]` and
  truncated to order zero, solves the order-zero system of the stage with zero forcing and initial
  value `U(t_i)`, with some `H¹` lift. For `i < M + J_w` this is the passage `i + 1` of
  `r.reduction`, and the lift is the truncation of `r.Urw i`; for `i = M + J_w` it is the scalar
  root, whose lift comes from the scalar solution (`r.Urw (M + J_w)` is not constrained by
  `IsWeakReduction`).
* The equation of the glued lift: for every presentation `(F, g)` of the residual source,
  the glued lift `Λ_i g` is (the value of) a regularized solution with the forcing
  `(−trunc F, −trunc g)` and initial value `U(t_i)`. Its proof has three parts:
  - the *block sum*: with the readout weights, the coarse equations sum to
    `(L_{i−1} − 𝔐)g = −𝔇H` in the weak sense (this is the coefficient identification
    `𝔐 = 𝔈 + 𝔇` and uses the two degree lemmas below and the Piola form of
    `constituentPhysical`);
  - the *glued identity* (the slot identity `Res_k` = frozen-time defect, the product rule in time
    for `ϖ_k`, `∑ϖ_k = 1`, `∑ϖ'_k = 0`), run in distributions on the weak-in-time `Ū`;
  - the *packaging*: continuity in time, the `H¹` lift `wΛ`, and the kernel lift `YΛ`
    (`S = id` at width zero), at the regularity of `aU` (`IsClassicalRep`).
* The two degree lemmas (the diagonal and the inherited lift means vanish above the identity
  orders). They are parts of the proof of the equation of the glued lift (they justify that
  `weakSlotLiftMean`, summed to degree `N + D_m`, equals the stored coefficients, which stop at
  the identity orders), stated abstractly for `liftMean`; the second needs that the fibre edges
  stop at the identity orders.
* `RegSolutionCombineStatement`: the system is linear and sees its data on
  the window only. Generic, on a nonempty window.

The system is `WeakErrSol`: the kernel weak solution at the cap `1 + J_wN_w`, not at the ambient
cap `D_m`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

/-- The order-zero truncation of the incoming family at the start time. -/
def weakIncomingInit {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    (r : WeakPassageRun c) (i : ℕ) : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root) :=
  fun v => truncateTorusHk (Nat.zero_le _) (r.Ur i v (r.tq i))

/-- The order-zero truncation of the incoming family. -/
def weakIncomingVal {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    (r : WeakPassageRun c) (i : ℕ) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Nat.zero_le _) (r.Ur i v t)

/-- The order-one truncation of the `H¹` lift of the incoming family. -/
def weakIncomingLift {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    (r : WeakPassageRun c) (i : ℕ) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (r.Urw i v t)

/-- The order-zero truncation of a flux forcing, and its negative. -/
def weakTruncF {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (i : ℕ) {k : ℕ}
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  fun v t => truncateTorusHk (Nat.zero_le _) (F v t)

/-- The negative of `weakTruncF`. -/
def weakNegTruncF {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (i : ℕ) {k : ℕ}
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  fun v t => -truncateTorusHk (Nat.zero_le _) (F v t)

/-- The order-zero truncation of a scalar forcing. -/
def weakTruncG {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (i : ℕ) {k : ℕ}
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (ScalarH v.1.root)) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Nat.zero_le _) (g v t)

/-- The negative of `weakTruncG`. -/
def weakNegTruncG {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (i : ℕ) {k : ℕ}
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (ScalarH v.1.root)) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root) :=
  fun v t => -truncateTorusHk (Nat.zero_le _) (g v t)

/-- **Linearity and dependence on the window only.** If the data of a third system are, on
the window, the differences of the data of two solutions (the initial value, the forcing and the
kernel lift at every time; the value at every time of the window; the `H¹` lift at almost every
time), then it is a solution. The window is nonempty, `t_i ≤ T`: the system asks
`u t_i = f`, and on an empty window the value `u t_i` is not prescribed by the hypotheses. The
passage levels `M < i ≤ M + J_w` have `t_i ≤ T` (`weakRun_tq_le_window`). -/
def RegSolutionCombineStatement : Prop :=
  ∀ {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    r.tq i ≤ r.a + A.T₀ →
  ∀ (f₁ f₂ f : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root))
    (F₁ F₂ F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g₁ g₂ g u₁ u₂ u : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (w₁ w₂ w : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (Y₁ Y₂ Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
    WeakErrSol c r i f₁ F₁ g₁ u₁ w₁ Y₁ → WeakErrSol c r i f₂ F₂ g₂ u₂ w₂ Y₂ →
    (∀ v, f v = f₁ v - f₂ v) → (∀ v t, F v t = F₁ v t - F₂ v t) →
    (∀ v t, g v t = g₁ v t - g₂ v t) →
    (∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), u v t = u₁ v t - u₂ v t) →
    (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))), w v t = w₁ v t - w₂ v t) →
    (∀ v u γ t, Y v u γ t = Y₁ v u γ t - Y₂ v u γ t) →
    WeakErrSol c r i f F g u w Y

/-- **The equation of the incoming family.** `U = r.Ur i`, truncated to order zero, solves the
order-zero system of the stage on `[t_i, T]` with zero forcing and initial value `U(t_i)`, with
some `H¹` lift `w` and kernel lift `Y`. For `i < M + J_w` the lift is `weakIncomingLift r i`, the
truncation of `r.Urw i`. At the root `i = M + J_w` the field `r.Urw (M + J_w)` is free
(`IsWeakReduction` prescribes only the value of the root component of `r.Ur (M + J_w)`), and the
lift is that of the scalar solution (`weak_identification_core`). The assembly of the residual equation uses the lift
only through the system. -/
def WeakIncomingRegStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw →
    ∃ (w : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      WeakErrSol c r i (weakIncomingInit r i) (fun _ _ => 0) (fun _ _ => 0)
        (weakIncomingVal r i) w Y
end

/-! **The error equation from its steps**.

The error equation `WeakErrSol` follows (`weakErrSol_of_parts`) from the linearity and window
dependence of the system (`RegSolutionCombineStatement`), the equation of the incoming family
(`WeakIncomingRegStatement`) and the equation of the glued lift.

The window is nonempty at the passage levels (`weakRun_tq_le_window`), and the `H¹` lift of the
incoming family is the one provided by the passage case.

The error is `h.e = trunc U − Λ_i g`. By `h.identity` and the value of the glued lift they agree
at every time of the window, and by `h.truncation` the `H¹` lifts agree at almost every time
(truncation `TorusHk 1 → TorusHk 0` is injective: `TorusHk.ext_value`). The kernel lift is the
difference of the kernel lifts. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

section Ext

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Two carriers whose value jets agree almost everywhere on the cell are equal. -/
theorem torusHk_ext_of_value_jet_ae {K : ℕ} {f g : TorusHk K E}
    (h : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict unitCube]
      g.toFunction.jet (valueIndex2 K)) : f = g := by
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [periodicJetRepresentative_ae f.val (valueIndex2 K),
    periodicJetRepresentative_ae g.val (valueIndex2 K), h] with x h1 h2 h3
  rw [← h1, ← h2]
  exact h3

omit [FiniteDimensional ℝ E] in
/-- The jets of a difference of carriers. -/
theorem torusHk_jet_sub_ae {K : ℕ} (U V : TorusHk K E) (a : JetIndex2 K) :
    (U - V).toFunction.jet a =ᵐ[volume.restrict unitCube]
      fun x => U.toFunction.jet a x - V.toFunction.jet a x := by
  filter_upwards [periodicJetRepresentative_ae (U - V).val a,
    periodicJetRepresentative_ae U.val a, periodicJetRepresentative_ae V.val a,
    Lp.coeFn_sub (U.val a) (V.val a)] with x h1 h2 h3 h4
  change periodicJetRepresentative (U - V).val a x =
    periodicJetRepresentative U.val a x - periodicJetRepresentative V.val a x
  rw [h1, h2, h3]
  exact h4

/-- Truncation from order one to order zero is injective. -/
theorem truncateTorusHk_one_injective {f g : TorusHk 1 E}
    (h : truncateTorusHk (Nat.le_succ 0) f = truncateTorusHk (Nat.le_succ 0) g) : f = g := by
  apply TorusHk.ext_value
  exact congrArg (fun z : TorusHk 0 E => z.val (valueIndex2 0)) h

/-- The `H¹` lifts of a difference, from the truncations. -/
theorem eq_sub_of_truncate {ew wU wL : TorusHk 1 E} {e uU uL : TorusHk 0 E}
    (h1 : truncateTorusHk (Nat.le_succ 0) ew = e) (h2 : truncateTorusHk (Nat.le_succ 0) wL = uL)
    (h3 : truncateTorusHk (Nat.le_succ 0) wU = uU) (hu : e = uU - uL) : ew = wU - wL :=
  truncateTorusHk_one_injective (by rw [h1, map_sub, h2, h3, hu])

end Ext

/-- A solution links its `H¹` lift to its value: `trunc w = u` at almost every time. -/
theorem WeakErrSol.truncate_ae {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ}
    {f : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root)}
    {F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {g u : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root)}
    {w : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root)}
    {Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)}
    (h : WeakErrSol c r i f F g u w Y) (v : CompIn (c.stage i).comps) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ 0) (w v s) = u v s := by
  unfold WeakErrSol at h
  exact h.2.2.1 v

/-- The `H¹` lift of the error is the difference of the `H¹` lifts, at almost every time. -/
theorem ew_eq_of_sol {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ}
    {f : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root)}
    {F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {g uU : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root)}
    {wU : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root)}
    {Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)}
    (hU : WeakErrSol c r i f F g uU wU Y)
    (e uL : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (wL : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (hu : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), e v t = uU v t - uL v t)
    (hwtr : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ 0) (wL v t) = uL v t)
    (htr : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ 0) (ew v t) = e v t) :
    ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))), ew v t = wU v t - wL v t := by
  intro v
  filter_upwards [htr v, hwtr v, WeakErrSol.truncate_ae hU v,
    ae_restrict_mem measurableSet_Icc] with t h1 h2 h3 ht
  exact eq_sub_of_truncate h1 h2 h3 (hu v t ht)

/-- The window of a passage level is nonempty: `t_i ≤ T` for `M < i ≤ M + J_w`. The times
decrease in the level (`t_{i+1} + τ'_i ≤ t_i`) and `t_{M+1} ≤ T`. -/
theorem weakRun_tq_le_window {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    (r : WeakPassageRun c) {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    r.tq i ≤ r.a + A.T₀ := by
  have hΛ : 1 ≤ c.D.Λ := by
    have h1 := plan.base_ge B
    have h2 := c.base_ge
    have h3 := c.base_eq
    omega
  have key : ∀ n, c.M + 1 + n ≤ c.M + A.Jw → r.tq (c.M + 1 + n) ≤ r.a + A.T₀ := by
    intro n
    induction n with
    | zero => intro _; exact r.reduction.2.1
    | succ n ih =>
      intro hn
      have hstep := (r.reduction.2.2.2 (c.M + 1 + n) (by omega) (by omega)).2.1
      have hτ := Velocity.Jets.ocTauP_pos (α := c.D.α) (q := c.D.q) (m := c.M + 1 + n) hΛ
      have hle := ih (by omega)
      have he : c.M + 1 + (n + 1) = c.M + 1 + n + 1 := by omega
      rw [he]
      linarith
  have he : i = c.M + 1 + (i - (c.M + 1)) := by omega
  rw [he]
  exact key _ (by omega)

/-- The combination of the incoming solution and the glued lift, for a forcing of any order. -/
theorem weakErrSol_error {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (hcomb : RegSolutionCombineStatement)
    (hwin : r.tq i ≤ r.a + A.T₀) {k : ℕ}
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (ScalarH v.1.root))
    (fU : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root))
    (uU uL e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (wU wL ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (YU YL : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root))
    (hU : WeakErrSol c r i fU (fun _ _ => 0) (fun _ _ => 0) uU wU YU)
    (hL : WeakErrSol c r i fU (weakNegTruncF c i F) (weakNegTruncG c i g) uL wL YL)
    (hu : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), e v t = uU v t - uL v t)
    (hw : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))), ew v t = wU v t - wL v t) :
    WeakErrSol c r i (fun _ => 0) (weakTruncF c i F) (weakTruncG c i g) e ew
      (fun v u γ t => YU v u γ t - YL v u γ t) :=
  hcomb c r i hwin fU fU (fun _ => 0)
    (fun _ _ => 0) (weakNegTruncF c i F) (weakTruncF c i F)
    (fun _ _ => 0) (weakNegTruncG c i g) (weakTruncG c i g) uU uL e wU wL ew YU YL
    (fun v u γ t => YU v u γ t - YL v u γ t) hU hL (fun v => by simp)
    (fun v t => by simp [weakNegTruncF, weakTruncF]) (fun v t => by simp [weakNegTruncG, weakTruncG])
    hu hw (fun v u γ t => rfl)

/-- The error of the glued lift against the incoming family, from the two solutions. The error
`e` has the value `uU − Λ` (`hid`), where `Λ` is the value of the glued lift (`hjet`), and its
`H¹` lift truncates to `e` (`htr`). -/
theorem weakErrSol_of_parts {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (hcomb : RegSolutionCombineStatement)
    (hwin : r.tq i ≤ r.a + A.T₀) {k : ℕ}
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (ScalarH v.1.root))
    (fU : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root))
    (uU uL e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (wU wL ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (YU YL : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root))
    (Lam : ∀ v : CompIn (c.stage i).comps, ℝ → Vec 2 → ScalarH v.1.root)
    (hU : WeakErrSol c r i fU (fun _ _ => 0) (fun _ _ => 0) uU wU YU)
    (hL : WeakErrSol c r i fU (weakNegTruncF c i F) (weakNegTruncG c i g) uL wL YL)
    (hid : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      (e v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        fun x => (uU v t).toFunction.jet (valueIndex2 0) x - Lam v t x)
    (hjet : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      (uL v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun x => Lam v t x)
    (hwtr : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ 0) (wL v t) = uL v t)
    (htr : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ 0) (ew v t) = e v t) :
    WeakErrSol c r i (fun _ => 0) (weakTruncF c i F) (weakTruncG c i g) e ew
      (fun v u γ t => YU v u γ t - YL v u γ t) := by
  have hu : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), e v t = uU v t - uL v t := by
    intro v t ht
    apply torusHk_ext_of_value_jet_ae
    filter_upwards [hid v t ht, hjet v t ht, torusHk_jet_sub_ae (uU v t) (uL v t)
      (valueIndex2 0)] with x h1 h2 h3
    exact h1.trans (h3.trans (congrArg (fun y => _ - y) h2)).symm
  have hw := ew_eq_of_sol hU e uL ew wL hu hwtr htr
  exact weakErrSol_error c r i hcomb hwin F g fU uU uL e wU wL ew YU YL hU hL hu hw

/-- The system of the residual equation, with the truncated forcing of a presentation of any order. -/
theorem weakErrSol_to_body {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) {k : ℕ}
    (F : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk k (ScalarH v.1.root))
    (e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root))
    (key : WeakErrSol c r i (fun _ => 0) (weakTruncF c i F) (weakTruncG c i g) e ew Y) :
    WeakErrSol c r i (fun _ => 0) (fun v t => truncateTorusHk (Nat.zero_le _) (F v t))
      (fun v t => truncateTorusHk (Nat.zero_le _) (g v t)) e ew Y := key
end

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual

/-! **`WeakErrSol` is linear and reads its data on the window only**.

`RegSolutionCombineStatement` quantifies over every level `i`, but the clause `u t₀ = f` of the
system is not controlled when the window `[t_i, a + T₀]` is empty, and `r.tq i` is constrained by
`r.reduction` only for `M < i ≤ M + J_w + 1`. The statement proved here,
`RegSolutionCombineStatement`, adds the hypothesis `r.tq i ≤ r.a + A.T₀`, which holds for
`M < i ≤ M + J_w` (`weakRun_tq_le_window`). -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- **Linearity** (`RegSolutionCombineStatement`, with the window hypothesis). -/
theorem regSolutionCombine : RegSolutionCombineStatement := by
  intro plan B A R c r i hwin f₁ f₂ f F₁ F₂ F g₁ g₂ g u₁ u₂ u w₁ w₂ w Y₁ Y₂ Y h₁ h₂ hf hF hg hu hw hy
  obtain ⟨hs, -, -, ⟨V, hV⟩, -⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data
    (c.D.hΦ i) (r.tq i) (r.a + A.T₀)
  exact kernelWeakSolutionTorus_sub (c.D.κ c.M) (r.tq i) (r.a + A.T₀) (streamVel (c.D.Φ i)) 0
    (1 + A.Jw * A.Nw) _ _ _ hwin
    (fun s hs' => ⟨(hs s hs').continuous, max V 0, le_max_right _ _,
      fun x => (hV s hs' x).trans (le_max_left _ _)⟩)
    f₁ f₂ f F₁ F₂ F g₁ g₂ g u₁ u₂ u w₁ w₂ w Y₁ Y₂ Y h₁ h₂ hf hF hg hu hw hy

/-- The passage times decrease in the index on the weak levels. -/
theorem weakRun_tq_succ_le {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} {c : WeakPassageInstance plan R}
    (r : WeakPassageRun c) {j : ℕ} (hj : c.M < j) (hjt : j ≤ c.M + A.Jw) :
    r.tq (j + 1) ≤ r.tq j := by
  have h := (r.reduction.2.2.2 j hj hjt).2.1
  have h0 : 0 ≤ ocTauP c.D.α c.D.q c.D.Λ j := by
    unfold ocTauP ocTauPP
    exact div_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  linarith

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The equation of the incoming family, the passage case**: for `M < i < M + J_w` the incoming family `U^{(i)}`,
truncated to order zero and restarted at `t_i`, solves the order-zero system of the stage `i` with
zero forcing. It is the passage `i + 1` of `r.reduction`, restarted at `t_i ∈ [t_{i+1}, T]`
(`kernelWeakSolutionTorus_restart`) and truncated to order zero (`kernel_solution_truncate_torus`);
the level of the stage is `i` and `κ_i = κ_M` for `i ≥ M`. -/

open WeakEntryProofs WeakEntryProofs.Assembly

section Zero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- Truncation of zero. -/
theorem truncateTorusHk_zero_eq {k k' : ℕ} (hk : k' ≤ k) :
    truncateTorusHk hk (0 : TorusHk k E) = 0 :=
  (truncateTorusHk hk).map_zero

end Zero

/-- Replace the forcing of a kernel-regularized solution by an equal one. -/
theorem kernelWeakSolutionTorus_forcing_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {k D : ℕ}
    {B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α}
    {S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    {f : ∀ i, TorusHk k (h i)}
    {F F' : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g g' u : ∀ i, ℝ → TorusHk k (h i)} {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hF : F = F') (hg : g = g')
    (hs : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F' g' u w y := by
  subst hF hg; exact hs

/-- The passage `i + 1` of the reduction, as the system of the stage `i` at order `K_w`. -/
theorem weakIncoming_reg_at_order {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) {i : ℕ} (hi : c.M < i) (hit : i < c.M + A.Jw) :
    ∃ Ub₀ : ∀ v : CompIn (c.stage i).comps, TorusHk R.Kw (ScalarH v.1.root),
      (c.stage i).IsRegSolution c.P (fun _ => isoPairedKernel 0 R.nW)
        (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀ (c.D.κ c.M) (AVenhance.streamVel (c.D.Φ i)) R.Kw
        (r.tq (i + 1)) (r.a + A.T₀) Ub₀ (fun _ _ => 0) (fun _ _ => 0) (r.Ur i) (r.Urw i)
        (r.Urk i) := by
  have hp : IsWeakPassageSolution c.P A.φ₀ A.hφ₀ R.nW R.Kw (c.stage (i + 1)) (c.stage i)
      (r.tq (i + 1)) (r.a + A.T₀) (r.Ur (i + 1)) (r.Ur i) (r.Urw i) (r.Urk i) :=
    (r.reduction.2.2.2 (i + 1) (by omega) (by omega)).2.2.2.2.2
  obtain ⟨Ub₀, -, hreg⟩ := hp
  have hlev : (c.stage i).level = i :=
    EntryWeakProofs.weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le
      (by omega)
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [EntryWeakProofs.weakData_kap_terminal c.D i (by rw [c.terminal]; omega), c.terminal]
  rw [hlev, hkap] at hreg
  exact ⟨Ub₀, hreg⟩

/-- Truncation to order zero of a solution with zero forcing. -/
theorem kernelWeakSolutionTorus_truncate_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {k D : ℕ}
    {B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α}
    {S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    {f : ∀ i, TorusHk k (h i)} {u : ∀ i, ℝ → TorusHk k (h i)}
    {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hs : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f (fun _ _ => 0) (fun _ _ => 0) u w y) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v 0 D B C S (fun i => truncateTorusHk (Nat.zero_le _) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (fun i s => truncateTorusHk (Nat.zero_le _) (u i s))
      (fun i s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (w i s))
      (fun i j α s => truncateTorusHk (by omega) (y i j α s)) :=
  kernelWeakSolutionTorus_forcing_congr
    (funext fun _ => funext fun _ => truncateTorusHk_zero_eq _)
    (funext fun _ => funext fun _ => truncateTorusHk_zero_eq _)
    (Providers.kernel_solution_truncate_torus _ _ _ _ 0 k D (Nat.zero_le _) _ _ _ _ _ _ _ _ _ hs)

/-- **Incoming passage for `M < i < M + J_w`.** -/
theorem weakIncoming_passage {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) {i : ℕ} (hi : c.M < i) (hit : i < c.M + A.Jw) :
    ∃ Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root),
      WeakErrSol c r i (weakIncomingInit r i) (fun _ _ => 0) (fun _ _ => 0)
        (weakIncomingVal r i) (weakIncomingLift r i) Y := by
  obtain ⟨Ub₀, hreg⟩ := weakIncoming_reg_at_order c r hi hit
  unfold GenStage.IsRegSolution at hreg
  have hmem : r.tq i ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) :=
    ⟨weakRun_tq_succ_le r hi (by omega), weakRun_tq_le_window r hi (by omega)⟩
  have h2 := kernelWeakSolutionTorus_restart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreg (r.tq i) hmem
  have h3 := kernelWeakSolutionTorus_truncate_zero h2
  have h4 := kernelWeakSolutionTorus_restrict_cap (D' := 1 + A.Jw * A.Nw) c.order_ge
    (P := fun v u γ n => (c.stage i).physCoeff v u γ n)
    (fun v u γ n hn _ s x => congrFun (congrFun
      (weak_comparison_physCoeff_zero_above c i hi (by omega) v u γ n hn) s) x) h3
  have hcap := c.order_ge
  refine ⟨fun v u γ t => truncateTorusHk (by omega : 0 + (1 + A.Jw * A.Nw) - 1 ≤ 0 + c.Dm - 1)
    (truncateTorusHk (by omega : 0 + c.Dm - 1 ≤ R.Kw + c.Dm - 1) (r.Urk i v u γ t)), ?_⟩
  unfold WeakErrSol weakIncomingInit weakIncomingVal weakIncomingLift
  exact h4

end AVRegularity.Providers.WeakGen.Residual
end
end
end

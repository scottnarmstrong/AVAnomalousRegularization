-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity

/-! The solution class of the kernel-regularized system (7.2) of the paper on the torus
`𝕋² = ℝ²/ℤ²` (unit cell, `TorusHk`):
`U_i ∈ C(I;H^k) ∩ L²(I;H^{k+1})`, with the `L²`-duality identity whose flux is
`∑_{j,α,d} B_{α,d} ∇^{d-1} S_α C_α U_j + F_i`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(u, w, y)` is a solution on `I = [t₀, t₁]` of
`(∂ₜ + v·∇ - νΔ) U_i = div(∑_{j,α∈Γ_{ij},d} B_{α,d} ∇^{d-1} S_α(t) C_α U_j + F_i) + g_i` at the
common order `k`: `u i` is the `C(I;H^k)` trajectory, `w i` its `L²(I;H^{k+1})` lift, and
`y i j α` the `L²(I;H^{k+D-1})` lift of the regularized input `S_α C_α U_j` (for a.e. `s` its
value is `S_α(s)` applied to `C_α` of the value of `w j s`; its jets of order `d-1` are the
arrays `∇^{d-1} S_α C_α U_j` of the flux). The lift `y` is determined by `w` (weak jets are
unique); it carries the higher regularity that the kernel supplies. Initial value `f`, and the
identity holds for every `i`, `t ∈ I` and `H¹` test, by `CoupledWeakIdentity`. The flux sums over
`d ∈ [2,D]`. -/
def IsKernelWeakSolutionTorus {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    (ν t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (k D : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) : Prop :=
  (∀ i, ContinuousOn (u i) (Set.Icc t₀ t₁)) ∧
  (∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc t₀ t₁))) ∧
  (∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), truncateTorusHk (Nat.le_succ k) (w i s) = u i s) ∧
  (∀ i, u i t₀ = f i) ∧
  (∀ i j α, MemLp (y i j α) 2 (volume.restrict (Set.Icc t₀ t₁))) ∧
  (∀ i j α, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
    (y i j α s).val (valueIndex2 (k + D - 1)) =
      S i j α s ((C i j α).compLp ((w j s).val (valueIndex2 (k + 1))))) ∧
  ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ∀ φ : TorusHk 1 (h i),
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν t₀ t v
      ((u i t).toFunction.jet (valueIndex2 k))
      ((f i).toFunction.jet (valueIndex2 k))
      (φ.toFunction.jet (valueIndex2 1))
      (fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩)
      (fun s m => (w i s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩)
      (fun s x => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        B i j α d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α s).toFunction.jet
            ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.1 d.2
              omega⟩, word⟩ x))
      (fun s => (F i s).toFunction.jet (valueIndex2 k))
      (fun s => (g i s).toFunction.jet (valueIndex2 k))

end AVRegularity

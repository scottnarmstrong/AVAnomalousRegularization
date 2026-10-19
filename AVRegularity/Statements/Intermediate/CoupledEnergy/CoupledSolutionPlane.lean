-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity

/-! The solution class of the coupled system
`∂ₜu_i + v·∇u_i − νΔu_i = ∇·(∑_{i',d} A_{ii',d} ∇^{d-1}u_{i'} + F_i) + g_i` on the plane `ℝ²`
(`PlaneHk Set.univ`): `u_i ∈ C(I;H^{K_i}) ∩ L²(I;H^{K_i+1})`, initial value `f_i`, and
the integrated `L²`-duality identity against every `H¹` test at every time. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(u, w)` is a solution of the coupled system on `I = [t₀, t₁]`: `u i` is the
`C(I;H^{K_i})` trajectory and `w i` its `L²(I;H^{K_i+1})` lift (`w i s` truncates to `u i s`
for a.e. `s ∈ I`), `u i t₀ = f i`, and for every `i`, `t ∈ I` and `H¹` test `φ` the
`CoupledWeakIdentity` holds with the representatives of the carrier. The flux term
`∑_{i',d} A_{ii',d} ∇^{d-1} u_{i'}` sums over `d ∈ admissibleOrders K D i i'`; pairs outside
this set are the zero coefficients of the paper. The torus is the unit cell `ℝ²/ℤ²`.
Every quantity in the identity is an `x`-integral of an a.e.-class, hence independent of the
chosen representative. -/
def IsCoupledWeakSolutionPlane {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (ν t₀ t₁ : ℝ) (v : ℝ → Vec 2 → Vec 2) (D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) : Prop :=
  (∀ i, ContinuousOn (u i) (Set.Icc t₀ t₁)) ∧
  (∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc t₀ t₁))) ∧
  (∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), truncatePlaneHk (Nat.le_succ (K i)) (w i s) = u i s) ∧
  (∀ i, u i t₀ = f i) ∧
  ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ∀ φ : PlaneHk Set.univ 1 (h i),
    CoupledWeakIdentity (volume.restrict Set.univ) ν t₀ t v
      ((u i t).toFunction.jet (valueIndex2 (K i)))
      ((f i).toFunction.jet (valueIndex2 (K i)))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (fun s k => (w i s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun s x => ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        A i i' d s x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (w i' s).toFunction.jet
            ⟨⟨d.1 - 1, by
              have h := Finset.mem_filter.1 d.2
              have := Finset.mem_Icc.1 h.1
              omega⟩, word⟩ x))
      (fun s => (F i s).toFunction.jet (valueIndex2 (K i)))
      (fun s => (g i s).toFunction.jet (valueIndex2 (K i)))

end AVRegularity

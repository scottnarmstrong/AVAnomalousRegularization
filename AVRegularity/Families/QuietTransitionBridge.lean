-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsQuietTransition

/-! Bridge for the quiet transition.

`ChartedFamily.IsQuietTransition` states the transport identity summed over the permutations of the
word. Proofs construct and consume the transition only through the lemmas of this module; their
proofs are the only places that unfold the second conjunct of the definition.

* `isQuietTransition_of_wordwise`: from the word-by-word identity (transfers satisfy it).
* `isQuietTransition_of_summed`: from the summed identity (families with the first source).
* `IsQuietTransition.fastIndependent`: fast independence on the overlap.
* `IsQuietTransition.summed`: the identity summed over permutations; the only form a consumer
  may use. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The quiet transition from fast independence and the word-by-word transport identity. -/
theorem isQuietTransition_of_wordwise {F : ChartedFamily ι h D P Ctx} {ν e E : ℝ} {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hind : ∀ tY ∈ tr.overlap, ∀ v u (γ : F.Γ v u) d I, ∀ z z' : Vec 2,
      F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z = F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z' ∧
      F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z = F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z')
    (hword : ∀ tY ∈ tr.overlap, ∀ z : Vec 2, ∀ v u (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r),
      (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) A tY.1 (E⁻¹ • tY.2) z =
        transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
          (fun d I => F.dimFlux ν e E p c v u γ d I tY.1 (tr.Υ tY.2) z) r A tY.2) :
    F.IsQuietTransition ν e E tr c c' :=
  ⟨hind, fun tY htY z v u γ r A =>
    Finset.sum_congr rfl fun σ _ => hword tY htY z v u γ r (A ∘ σ)⟩

/-- The quiet transition from fast independence and the summed transport identity. -/
theorem isQuietTransition_of_summed {F : ChartedFamily ι h D P Ctx} {ν e E : ℝ} {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hind : ∀ tY ∈ tr.overlap, ∀ v u (γ : F.Γ v u) d I, ∀ z z' : Vec 2,
      F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z = F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z' ∧
      F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z = F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z')
    (hsum : ∀ tY ∈ tr.overlap, ∀ z : Vec 2, ∀ v u (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r),
      ∑ σ : Equiv.Perm (Fin r),
          (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) (A ∘ σ) tY.1 (E⁻¹ • tY.2) z =
        ∑ σ : Equiv.Perm (Fin r),
          transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
            (fun d I => F.dimFlux ν e E p c v u γ d I tY.1 (tr.Υ tY.2) z) r (A ∘ σ) tY.2) :
    F.IsQuietTransition ν e E tr c c' :=
  ⟨hind, hsum⟩

/-- Fast independence of both field families on the overlap of a quiet transition. -/
theorem IsQuietTransition.fastIndependent {F : ChartedFamily ι h D P Ctx} {ν e E : ℝ} {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hq : F.IsQuietTransition ν e E tr c c') :
    ∀ tY ∈ tr.overlap, ∀ v u (γ : F.Γ v u) d I, ∀ z z' : Vec 2,
      F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z = F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z' ∧
      F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z = F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z' :=
  hq.1

/-- The transport identity of a quiet transition, summed over the permutations of the word. -/
theorem IsQuietTransition.summed {F : ChartedFamily ι h D P Ctx} {ν e E : ℝ} {p q : P}
    {tr : ChartTransition (F.piece p) (F.piece q)} {c : Ctx p} {c' : Ctx q}
    (hq : F.IsQuietTransition ν e E tr c c') :
    ∀ tY ∈ tr.overlap, ∀ z : Vec 2, ∀ v u (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r),
      ∑ σ : Equiv.Perm (Fin r),
          (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) (A ∘ σ) tY.1 (E⁻¹ • tY.2) z =
        ∑ σ : Equiv.Perm (Fin r),
          transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
            (fun d I => F.dimFlux ν e E p c v u γ d I tY.1 (tr.Υ tY.2) z) r (A ∘ σ) tY.2 :=
  hq.2

end ChartedFamily

end AVRegularity

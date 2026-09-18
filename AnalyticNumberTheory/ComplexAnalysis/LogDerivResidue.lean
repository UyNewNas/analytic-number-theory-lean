import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Generic logarithmic-derivative residue atoms

This module is a provenance-preserving extraction of the project-neutral local residue
lemmas used by the same-Mathlib-pin Liu--Wang explicit-formula development
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
notably `PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` and
`PrimeNumberTheoremAnd/IEANTN/KadiriEq12Foundations.lean`.

The statements are independent of Dirichlet characters, GRH, and any downstream
application.  They identify the principal part of a logarithmic derivative from the
meromorphic order, and show that multiplying a simple principal part by a continuous
cofactor multiplies its residue by the value of that cofactor.
-/

open Complex Filter Topology Set BigOperators Asymptotics

noncomputable section

namespace AnalyticNumberTheory.ComplexAnalysis

/-- A `c/(z-p) + O(1)` principal-part expansion determines the punctured-neighbourhood
limit of `(z-p) f z`. -/
theorem tendsto_mul_self_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hp_small :
      (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : ℂ => (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p] fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p))) (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal.symm
  have hsum_tendsto :
      Tendsto
        (fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hsum :
      (fun z : ℂ => (z - p) * f z) =ᶠ[𝓝[≠] p]
        fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z) := by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hsum.symm

/-- Multiplying a `c/(z-p) + O(1)` principal part by a continuous cofactor multiplies
its residue by the cofactor value at `p`. -/
theorem residue_mul_eq_of_sub_principal_isBigO_one
    {f Ψ : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hΨ : ContinuousAt Ψ p) :
    residue (fun z : ℂ => f z * Ψ z) p = c * Ψ p := by
  refine residue_eq_of_tendsto ?_
  have hf := tendsto_mul_self_of_sub_principal_isBigO_one h
  have hΨ' : Tendsto Ψ (𝓝[≠] p) (𝓝 (Ψ p)) :=
    hΨ.tendsto.mono_left nhdsWithin_le_nhds
  simpa [mul_assoc] using hf.mul hΨ'

/-- At a point where `f` has finite meromorphic order `n`, the logarithmic derivative
has principal part `n/(s-p)` up to an `O(1)` remainder. -/
theorem logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  let F : ℂ → ℂ := fun s => (s - p) ^ n * g s
  have hfg_ne : f =ᶠ[𝓝[≠] p] F := by
    filter_upwards [hfg] with s hs
    simpa [F, smul_eq_mul] using hs
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv F := hfg_ne.nhdsNE_deriv
  have hg_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := by
    exact (hg_analytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne
      |>.filter_mono nhdsWithin_le_nhds
  have hg_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ g s := by
    exact hg_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_eq :
      (logDeriv f - fun s : ℂ => (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [hfg_ne, hderiv_ne, self_mem_nhdsWithin, hg_nonzero_ne, hg_analytic_ne]
      with s hfs hderiv hs_ne hgs_ne hgs_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 := zpow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow : DifferentiableAt ℂ (fun z : ℂ => (z - p) ^ n) s := by
      exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p) s)).zpow
        (Or.inl (sub_ne_zero.mpr hs_ne))
    have hlogF :
        logDeriv F s =
          logDeriv (fun z : ℂ => (z - p) ^ n) s + logDeriv g s := by
      exact logDeriv_mul (f := fun z : ℂ => (z - p) ^ n) (g := g) s
        hpow_ne hgs_ne hdiff_pow hgs_analytic.differentiableAt
    have hlogpow : logDeriv (fun z : ℂ => (z - p) ^ n) s = (n : ℂ) / (s - p) := by
      rw [logDeriv_fun_zpow (f := fun z : ℂ => z - p) (x := s) (by fun_prop) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : ℂ) / (s - p)
          = logDeriv F s - (n : ℂ) / (s - p) := by
            simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv g s := by
            rw [hlogF, hlogpow]
            ring
  have hderiv_bounded : deriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    hg_analytic.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hinv_bounded : g⁻¹ =O[𝓝 p] (1 : ℂ → ℂ) :=
    (hg_analytic.continuousAt.inv₀ hg_ne).norm.isBoundedUnder_le.isBigO_one ℂ
  have hlog_bounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) := by
    have hmul_bounded :
        (deriv g * g⁻¹) =O[𝓝 p] ((1 : ℂ → ℂ) * (1 : ℂ → ℂ)) :=
      Asymptotics.IsBigO.mul hderiv_bounded hinv_bounded
    have hmul_bounded' :
        (fun x => deriv g x * (g x)⁻¹) =O[𝓝 p] (1 : ℂ → ℂ) := by
      refine hmul_bounded.congr ?_ ?_
      · intro x
        rfl
      · intro x
        simp
    change (fun x => deriv g x / g x) =O[𝓝 p] (1 : ℂ → ℂ)
    simpa only [div_eq_mul_inv] using hmul_bounded'
  exact hlog_eq.trans_isBigO (hlog_bounded.mono nhdsWithin_le_nhds)

end AnalyticNumberTheory.ComplexAnalysis

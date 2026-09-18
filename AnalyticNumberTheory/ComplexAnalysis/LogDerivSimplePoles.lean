import AnalyticNumberTheory.ComplexAnalysis.LogDerivResidue

/-!
# Simple-pole bookkeeping for logarithmic derivatives

This module is a minimal, project-neutral source adaptation of the simple-pole
bookkeeping in `PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` from the
same analytic-number-theory lineage used by Liu--Wang.  ANT already contains the
principal-part estimate in `LogDerivResidue`; this file adds only the order
bookkeeping needed to turn finite meromorphic order of `f` into at-most-simple
poles of `logDeriv f`.
-/

set_option autoImplicit false

open Complex Filter Topology Set BigOperators Asymptotics

noncomputable section

namespace AnalyticNumberTheory.ComplexAnalysis

private lemma meromorphicOrderAt_nonneg_of_isBigO_one
    {f : ℂ → ℂ} {p : ℂ} (_hf : MeromorphicAt f p)
    (hO : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    0 ≤ meromorphicOrderAt f p := by
  by_contra hnonneg
  have hneg : meromorphicOrderAt f p < 0 := lt_of_not_ge hnonneg
  have hnorm :
      Tendsto (fun z : ℂ => ‖f z‖) (𝓝[≠] p) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hO.isBoundedUnder_le

private lemma meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  let principal : ℂ → ℂ := fun z => c / (z - p)
  let rem : ℂ → ℂ := f - principal
  have hconst_mero : MeromorphicAt (fun _ : ℂ => c) p := MeromorphicAt.const c p
  have hlin_mero : MeromorphicAt (fun z : ℂ => z - p) p := by fun_prop
  have hprincipal_mero : MeromorphicAt principal p := hconst_mero.div hlin_mero
  have hrem_mero : MeromorphicAt rem p := hf.sub hprincipal_mero
  have hrem_nonneg : 0 ≤ meromorphicOrderAt rem p :=
    meromorphicOrderAt_nonneg_of_isBigO_one hrem_mero (by simpa [rem, principal] using h)
  have hprincipal_order : meromorphicOrderAt principal p = (-1 : ℤ) := by
    dsimp [principal]
    change meromorphicOrderAt ((fun _ : ℂ => c) / fun z : ℂ => z - p) p = (-1 : ℤ)
    rw [meromorphicOrderAt_div hconst_mero hlin_mero, meromorphicOrderAt_const,
      if_neg hc, meromorphicOrderAt_id_sub_const]
    norm_num
  have hlt : meromorphicOrderAt principal p < meromorphicOrderAt rem p := by
    rw [hprincipal_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)) hrem_nonneg
  have hsum_order :
      meromorphicOrderAt (principal + rem) p = meromorphicOrderAt principal p :=
    meromorphicOrderAt_add_eq_left_of_lt hrem_mero hlt
  have hcongr : f =ᶠ[𝓝[≠] p] principal + rem := by
    filter_upwards with z
    dsimp [principal, rem]
    ring
  calc
    meromorphicOrderAt f p = meromorphicOrderAt (principal + rem) p :=
      meromorphicOrderAt_congr hcongr
    _ = meromorphicOrderAt principal p := hsum_order
    _ = (-1 : ℤ) := hprincipal_order

private lemma logDeriv_meromorphicOrderAt_nonneg_of_order_zero
    {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hlog : MeromorphicAt (logDeriv f) p)
    (hord : meromorphicOrderAt f p = (0 : WithTop ℤ)) :
    0 ≤ meromorphicOrderAt (logDeriv f) p := by
  have hO := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord
  have hO' : logDeriv f =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    exact hO.congr_left (by intro z; simp)
  exact meromorphicOrderAt_nonneg_of_isBigO_one hlog hO'

private lemma logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p) (hlog : MeromorphicAt (logDeriv f) p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) (hn : n ≠ 0) :
    meromorphicOrderAt (logDeriv f) p = (-1 : ℤ) := by
  have hO := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord
  exact meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one hlog
    (by exact_mod_cast hn) hO

/-- If `f` and its logarithmic derivative are meromorphic on `R`, and `f` has finite
meromorphic order at every point of `R`, then the logarithmic derivative has at most
simple poles on `R`. -/
theorem logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    {f : ℂ → ℂ} {R : Set ℂ}
    (hf : MeromorphicOn f R) (hlog : MeromorphicOn (logDeriv f) R)
    (hfinite_order : ∀ p ∈ R, meromorphicOrderAt f p ≠ ⊤) :
    HasSimplePolesOn (logDeriv f) R := by
  intro p hpR
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite_order p hpR)
  by_cases hn0 : n = 0
  · have hord0 : meromorphicOrderAt f p = (0 : WithTop ℤ) := by
      simpa [hn0] using hn.symm
    have hnonneg :=
      logDeriv_meromorphicOrderAt_nonneg_of_order_zero (hf p hpR) (hlog p hpR) hord0
    exact le_trans (WithTop.coe_le_coe.2 (by norm_num : (-1 : ℤ) ≤ 0)) hnonneg
  · have hneg_one :=
      logDeriv_meromorphicOrderAt_eq_neg_one_of_order_ne_zero (hf p hpR) (hlog p hpR)
        hn.symm hn0
    rw [hneg_one]

end AnalyticNumberTheory.ComplexAnalysis

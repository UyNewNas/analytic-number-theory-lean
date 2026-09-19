import AnalyticNumberTheory.Dirichlet.LocalLogDerivative

/-!
# Fixed-radius local logarithmic-derivative geometry

A project-neutral Borel--Carathéodory/Cauchy bridge for the tight nested radii
`83/100 < 21/25 < 17/20`.  This is the minimal neutral seam needed by a downstream
Landau-style regular-part estimate; it does not mention Dirichlet characters, GRH,
zeros, or any application-specific function.
-/

open Complex Metric Set
open scoped Topology

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- If the real part of a holomorphic function oscillates by at most `A` on the
`17/20`-ball around `a`, then its derivative is bounded by `16800 * A` throughout
the closed `83/100`-ball.  The proof uses Borel--Carathéodory on radius `21/25`
and a Cauchy circle of radius `1/100` around the target point. -/
theorem norm_deriv_le_fixed_radii_83_100
    (h : ℂ → ℂ) (a z : ℂ) {A : ℝ} (hA : 0 < A)
    (hh : DifferentiableOn ℂ h (ball a ((17 : ℝ) / 20)))
    (hosc : ∀ w ∈ ball a ((17 : ℝ) / 20), (h w).re - (h a).re ≤ A)
    (hz : dist z a ≤ (83 : ℝ) / 100) :
    ‖deriv h z‖ ≤ 16800 * A := by
  let H : ℂ → ℂ := fun w ↦ h (a + w) - h a
  have hR : 0 < (17 : ℝ) / 20 := by norm_num
  have hHd : DifferentiableOn ℂ H (ball 0 ((17 : ℝ) / 20)) := by
    intro w hw
    have haw : a + w ∈ ball a ((17 : ℝ) / 20) := by
      simpa [mem_ball, dist_comm] using hw
    have hhat := (hh (a + w) haw).differentiableAt (isOpen_ball.mem_nhds haw)
    exact ((hhat.comp w (by fun_prop)).sub
      (differentiableAt_const (h a))).differentiableWithinAt
  have hHre : MapsTo H (ball 0 ((17 : ℝ) / 20)) {w : ℂ | w.re ≤ A} := by
    intro w hw
    change (h (a + w) - h a).re ≤ A
    simpa only [sub_re] using hosc (a + w) (by simpa [mem_ball, dist_comm] using hw)
  have hH0 : H 0 = 0 := by simp [H]
  have hBC : ∀ w : ℂ, dist w a ≤ (21 : ℝ) / 25 → ‖h w - h a‖ ≤ 168 * A := by
    intro w hw
    have hn : ‖w - a‖ ≤ (21 : ℝ) / 25 := by simpa only [dist_eq_norm] using hw
    have hmem : w - a ∈ ball 0 ((17 : ℝ) / 20) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    have hbc := borelCaratheodory_zero hA hHd hHre hR hmem hH0
    have hden : 0 < (17 : ℝ) / 20 - ‖w - a‖ := by linarith
    have hrat :
        2 * ‖w - a‖ / ((17 : ℝ) / 20 - ‖w - a‖) * A ≤ 168 * A := by
      apply mul_le_mul_of_nonneg_right _ hA.le
      apply (div_le_iff₀ hden).2
      linarith
    have heval : H (w - a) = h w - h a := by simp [H]
    rw [heval] at hbc
    apply hbc.trans
    calc
      _ = 2 * ‖w - a‖ / ((17 : ℝ) / 20 - ‖w - a‖) * A := by ring
      _ ≤ 168 * A := hrat
  have hsmall : 0 < (1 : ℝ) / 100 := by norm_num
  have hdist : ∀ w ∈ closedBall z ((1 : ℝ) / 100), dist w a ≤ (21 : ℝ) / 25 := by
    intro w hw
    calc
      dist w a ≤ dist w z + dist z a := dist_triangle w z a
      _ ≤ (1 : ℝ) / 100 + 83 / 100 := add_le_add (mem_closedBall.mp hw) hz
      _ = (21 : ℝ) / 25 := by norm_num
  have hsub : closedBall z ((1 : ℝ) / 100) ⊆ ball a ((17 : ℝ) / 20) := by
    intro w hw
    exact mem_ball.mpr ((hdist w hw).trans_lt (by norm_num))
  let F : ℂ → ℂ := fun w ↦ h w - h a
  have hFd : DifferentiableOn ℂ F (ball a ((17 : ℝ) / 20)) :=
    hh.sub (differentiableOn_const _)
  have hcont : DiffContOnCl ℂ F (ball z ((1 : ℝ) / 100)) := by
    refine ⟨hFd.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z hsmall.ne']
    exact hFd.continuousOn.mono hsub
  have hcircle : ∀ w ∈ sphere z ((1 : ℝ) / 100), ‖F w‖ ≤ 168 * A := by
    intro w hw
    exact hBC w (hdist w (mem_closedBall.mpr (mem_sphere.mp hw).le))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hsmall hcont hcircle
  have hd : deriv F z = deriv h z := deriv_sub_const _
  rw [hd] at hc
  convert hc using 1
  field_simp
  ring

end
end Dirichlet
end AnalyticNumberTheory
